use ruff_python_ast::{self as ast, ExceptHandler, Stmt, Expr};

use ruff_diagnostics::{Diagnostic, Violation};
use ruff_macros::{derive_message_formats, ViolationMetadata};
use ruff_text_size::Ranged;

/// ## What it does
/// Checks for functions with a high complexity.
#[derive(ViolationMetadata)]
pub(crate) struct ComplexStructure {
    name: String,
    complexity: usize,
    max_complexity: usize,
}

impl Violation for ComplexStructure {
    #[derive_message_formats]
    fn message(&self) -> String {
        let ComplexStructure {
            name,
            complexity,
            max_complexity,
        } = self;
        format!("`{name}` is too complex ({complexity} > {max_complexity})")
    }
}

/// Get the complexity contribution from a logical expression by counting transitions
/// between different boolean operators (and/or).
fn get_expression_complexity(expr: &Expr) -> usize {
    use ruff_python_ast::BoolOp;
    
    fn count_bool_op_sequences(expr: &Expr, current_op_kind: Option<&BoolOp>, mut count: usize) -> usize {
        if let Expr::BoolOp(ast::ExprBoolOp { op, values, .. }) = expr {
            // If this is a different operator than the current one, increment count
            if current_op_kind.is_none() || core::mem::discriminant(current_op_kind.unwrap()) != core::mem::discriminant(op) {
                count += 1;
            }
            
            // Recursively check values with the current operator kind
            for value in values {
                count = count_bool_op_sequences(value, Some(op), count);
            }
        }
        
        count
    }
    
    count_bool_op_sequences(expr, None, 0)
}

fn get_complexity_number(stmts: &[Stmt]) -> usize {
    let mut complexity = 0;
    for stmt in stmts {
        match stmt {
            Stmt::If(ast::StmtIf {
                test,
                body,
                elif_else_clauses,
                ..
            }) => {
                complexity += 1;
                complexity += get_expression_complexity(test);
                complexity += get_complexity_number(body);
                
                for clause in elif_else_clauses {
                    complexity += 1;
                    
                    if let Some(test) = &clause.test {
                        complexity += get_expression_complexity(test);
                    }
                    
                    complexity += get_complexity_number(&clause.body);
                }
            }
            Stmt::For(ast::StmtFor { body, orelse, .. }) => {
                complexity += 1;
                complexity += get_complexity_number(body);

                if !orelse.is_empty() {
                    complexity += 1;
                }

                complexity += get_complexity_number(orelse);
            }
            Stmt::With(ast::StmtWith { body, .. }) => {
                complexity += get_complexity_number(body);
            }
            Stmt::While(ast::StmtWhile { test, body, orelse, .. }) => {
                complexity += 1;
                complexity += get_expression_complexity(test);
                complexity += get_complexity_number(body);

                if !orelse.is_empty() {
                    complexity += 1;
                }

                complexity += get_complexity_number(orelse);
            }
            Stmt::Match(ast::StmtMatch { cases, .. }) => {
                complexity += 1;
                
                for case in cases {
                    if case.pattern.is_irrefutable() {
                        complexity += 1;
                    }
                    
                    if let Some(guard) = &case.guard {
                        complexity += get_expression_complexity(guard);
                    }
                    
                    complexity += get_complexity_number(&case.body);
                }
            }
            Stmt::Try(ast::StmtTry {
                body,
                handlers,
                orelse,
                finalbody,
                ..
            }) => {
                complexity += get_complexity_number(body);
                
                if !handlers.is_empty() {
                    complexity += 1;
                }
                
                if !orelse.is_empty() {
                    complexity += 1;
                }
                
                // Process the bodies of all handlers and clauses
                complexity += get_complexity_number(orelse);
                complexity += get_complexity_number(finalbody);
                
                for handler in handlers {
                    let ExceptHandler::ExceptHandler(ast::ExceptHandlerExceptHandler {
                        body, ..
                    }) = handler;
                    complexity += get_complexity_number(body);
                }
            }
            Stmt::FunctionDef(ast::StmtFunctionDef { body, .. }) => {
                complexity += get_complexity_number(body);
            }
            Stmt::ClassDef(ast::StmtClassDef { body, .. }) => {
                complexity += get_complexity_number(body);
            }
            _ => {}
        }
    }
    complexity
}

pub(crate) fn function_is_too_complex(
    stmt: &Stmt,
    name: &str,
    body: &[Stmt],
    max_complexity: usize,
) -> Option<Diagnostic> {
    let complexity = get_complexity_number(body) + 1;
    if complexity > max_complexity {
        Some(Diagnostic::new(
            ComplexStructure {
                name: name.to_string(),
                complexity,
                max_complexity,
            },
            stmt.range(),
        ))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use ruff_python_ast::Suite;
    use ruff_python_parser::parse_module;

    use super::get_complexity_number;

    fn parse_suite(source: &str) -> Result<Suite> {
        Ok(parse_module(source)?.into_suite())
    }

    #[test]
    fn trivial() -> Result<()> {
        let source = r"
def trivial():
    pass
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 0);
        Ok(())
    }

    #[test]
    fn expr_as_statement() -> Result<()> {
        let source = r"
def expr_as_statement():
    0xF00D
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 0);
        Ok(())
    }

    #[test]
    fn sequential() -> Result<()> {
        let source = r"
def sequential(n):
    k = n + 4
    s = k + n
    return s
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 0);
        Ok(())
    }

    #[test]
    fn if_elif_else_dead_path() -> Result<()> {
        let source = r#"
def if_elif_else_dead_path(n):
    if n > 3:                       # +1
        return "bigger than three" 
    elif n > 4:                     # +1
        return "is never executed"
    else:                           # +1
        return "smaller than or equal to three"
"#;
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 3);
        Ok(())
    }

    #[test]
    fn nested_ifs() -> Result<()> {
        let source = r#"
def nested_ifs():
    if n > 3:                                   # +1
        if n > 4:                               # +1
            return "bigger than four"
        else:                                   # +1
            return "bigger than three"
    else:                                       # +1
        return "smaller than or equal to three"
"#;
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 4);
        Ok(())
    }

    #[test]
    fn for_loop() -> Result<()> {
        let source = r"
def for_loop():
    for i in range(10):
        print(i)
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 1);
        Ok(())
    }

    #[test]
    fn for_else() -> Result<()> {
        let source = r"
def for_else(mylist):
    for i in mylist:  # +1
        print(i)
    else:             # +1
        print(None)
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn recursive() -> Result<()> {
        let source = r"
def recursive(n):
    if n > 4:           # +1
        return f(n - 1)
    else:               # +1
        return n
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn nested_functions() -> Result<()> {
        let source = r"
def nested_functions():
    def a():
        def b():
            pass

        b()

    a()
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 0);
        Ok(())
    }

    #[test]
    fn nested_try_finally() -> Result<()> {
        let source = r"
def nested_try_finally():
    try:
        try:
            print(1)
        finally:
            print(2)
    finally:
        print(3)
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 0);
        Ok(())
    }

    #[test]
    fn foobar() -> Result<()> {
        let source = r"
async def foobar(a, b, c):
    await whatever(a, b, c)
    if await b:             # +1
        pass
    async with c:
        pass
    async for x in a:       # +1
        pass
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn annotated_assign() -> Result<()> {
        let source = r"
def annotated_assign():
    x: Any = None
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 0);
        Ok(())
    }

    #[test]
    fn class() -> Result<()> {
        let source = r"
class Class:
    def handle(self, *args, **options):
        if args:                        # +1
            return

        class ServiceProvider:
            def a(self):
                pass

            def b(self, data):
                if not args:            # +1
                    pass

        return ServiceProvider(Logger())
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn finally() -> Result<()> {
        let source = r"
def process_detect_lines():
    try:
        pass
    finally:
        pass
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 0);
        Ok(())
    }

    #[test]
    fn if_in_finally() -> Result<()> {
        let source = r#"
def process_detect_lines():
    try:
        pass
    finally:
        if res:
            errors.append(f"Non-zero exit code {res}")
"#;
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 1);
        Ok(())
    }

    #[test]
    fn with() -> Result<()> {
        let source = r"
def with_lock():
    with lock:
        if foo:
            print('bar')
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 1);
        Ok(())
    }

    #[test]
    fn simple_match_case() -> Result<()> {
        let source = r"
def f():
    match subject:
        case 2:
            print('foo')
        case _:
            print('bar')
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn multiple_match_case() -> Result<()> {
        let source = r"
def f():
    match subject:
        case 2:
            print('foo')
        case 3:
            print('bar')
        case 4:
            print('bar')            
        case _:
            print('baz')
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn named_catch_all_match_case() -> Result<()> {
        let source = r"
def f():
    match subject:
        case 2:
            print('hello')
        case x:
            print(x)
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn match_case_catch_all_with_sequence() -> Result<()> {
        let source = r"
def f():
    match subject:          # +1
        case 2:
            print('hello')
        case 5 | _:         # +1 for _
            print(x)
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn counts_multiple_same_logical_expression_sequences_as_one() -> Result<()> {
        let source = r"
class C:
    def M(self, a, b, c):
        if a and b and c:  # +1 for if; +1 for all and
            # no-op
            pass
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn counts_multiple_mixed_logical_expression_sequences_separately() -> Result<()> {
        let source = r"
class C:
    def M(self, a, b, c, d, e):
        if (a and b and c) or d or e:  # +1 for if; +1 for all and; +1 for all or
            # no-op
            pass
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 3);
        Ok(())
    }    

    #[test]
    fn counts_for_each_new_logical_expression_sequence_even_if_it_was_used_before() -> Result<()> {
        let source = r"
class C:
    def M(self, a, b, c, d):
        if (a and b) or (c and d):   # +1 for if; +1 for and; +1 for or; +1 for and (new)
            # no-op
            pass
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 4);
        Ok(())
    }

    #[test]
    fn while_with_logical_expression() -> Result<()> {
        let source = r"
def test_while():
    while a and b:  # +1 for while, +1 for and
        pass
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    } 

    #[test]
    fn match_with_guard_logical_expression() -> Result<()> {
        let source = r"
def test_match(value):
    match value:                   # +1
        case 1 if (a and b) or c:  # +1 for and, +1 for or
            pass
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 3);
        Ok(())
    }

    #[test]
    fn else_in_while() -> Result<()> {
        let source = r"
def while_else(condition):
    while condition:       # +1
        print('in while')
    else:                  # +1
        print('in else')
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }

    #[test]
    fn else_in_try() -> Result<()> {
        let source = r"
def try_else():
    try:
        print(1)
    except TypeA: # +1
        print(2)
    except TypeB: # 0
        print(3)
    else:         # +1
        print(4)
";
        let stmts = parse_suite(source)?;
        assert_eq!(get_complexity_number(&stmts), 2);
        Ok(())
    }
}