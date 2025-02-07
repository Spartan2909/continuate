use crate::Expr;
use crate::Ident;
use crate::Item;
use crate::Path;
use crate::Program;

use std::collections::HashMap;
use std::mem;

use continuate_error::Span;

#[derive(Default)]
struct Scope<'a> {
    parent: Option<Box<Scope<'a>>>,
    idents: HashMap<Ident<'a>, Span>,
    paths: HashMap<Path<'a>, Span>,
}

impl<'a> Scope<'a> {
    fn new() -> Scope<'a> {
        Scope {
            parent: None,
            idents: HashMap::new(),
            paths: HashMap::new(),
        }
    }

    fn with_parent(parent: Scope<'a>) -> Scope<'a> {
        Scope {
            parent: Some(Box::new(parent)),
            idents: HashMap::new(),
            paths: HashMap::new(),
        }
    }

    fn get_ident(&self, ident: &Ident) -> Option<Span> {
        self.idents
            .get(ident)
            .copied()
            .or_else(|| self.parent.as_ref()?.get_ident(ident))
    }

    fn get_path(&self, path: &Path) -> Option<Span> {
        self.paths
            .get(path)
            .copied()
            .or_else(|| self.parent.as_ref()?.get_path(path))
    }

    fn define_ident(&mut self, ident: Ident<'a>) {
        let span = ident.span;
        self.idents.insert(ident, span);
    }

    fn define_path(&mut self, path: Path<'a>) {
        let span = path.span;
        self.paths.insert(path, span);
    }
}

struct Resolver<'a> {
    map: HashMap<Span, Span>,
    scope: Scope<'a>,
}

impl<'a> Resolver<'a> {
    fn new() -> Resolver<'a> {
        Resolver {
            map: HashMap::new(),
            scope: Scope::new(),
        }
    }

    fn resolve_ident(&mut self, ident: &Ident) {
        self.map
            .insert(ident.span, self.scope.get_ident(ident).unwrap());
    }

    fn resolve_path(&mut self, path: &Path) {
        self.map
            .insert(path.span, self.scope.get_path(path).unwrap());
    }

    fn with_scope(&mut self, f: impl FnOnce(&mut Self)) {
        self.scope = Scope::with_parent(mem::take(&mut self.scope));
        f(self);
        self.scope = *self.scope.parent.take().unwrap();
    }

    fn expr(&mut self, expr: &'a Expr<'a>) {
        match expr {
            Expr::Literal(_) => {}
            Expr::Path(path) => self.resolve_path(path),
            Expr::Block {
                exprs,
                tail,
                span: _,
            } => {
                self.with_scope(|this| {
                    this.exprs(exprs);
                    if let Some(tail) = tail {
                        this.expr(tail);
                    }
                });
            }
            Expr::Tuple { exprs, span: _ } | Expr::Array { exprs, span: _ } => self.exprs(exprs),
            Expr::NamedConstructor {
                path,
                fields,
                brace_span: _,
            } => {
                self.resolve_path(path);
                self.exprs(fields.iter().filter_map(|(_, expr)| expr.as_ref()));
            }
            Expr::Match {
                scrutinee,
                arms,
                brace_span: _,
            } => {
                self.expr(scrutinee);
                self.exprs(arms.iter().map(|(_, expr)| expr));
            }
            Expr::Get { object, field: _ } => {
                self.expr(object);
            }
            Expr::Set {
                object,
                field: _,
                value,
            } => {
                self.expr(object);
                self.expr(value);
            }
            Expr::Call {
                callee,
                arguments,
                paren_span: _,
            } => {
                self.expr(callee);
                self.exprs(arguments);
            }
            Expr::ContApplication {
                callee,
                arguments,
                bracket_span: _,
            } => {
                self.expr(callee);
                self.exprs(arguments.iter().filter_map(|(_, expr)| expr.as_ref()));
            }
            Expr::Unary {
                operator: _,
                operand,
            } => self.expr(operand),
            Expr::Binary {
                left,
                operator: _,
                right,
            } => {
                self.expr(left);
                self.expr(right);
            }
            Expr::Declare {
                name,
                ty: _,
                value,
                span: _,
            } => {
                self.expr(value);
                self.scope.define_ident(name.clone());
            }
            Expr::Assign { name, value } => {
                self.resolve_ident(name);
                self.expr(value);
            }
        }
    }

    fn exprs<I: IntoIterator<Item = &'a Expr<'a>>>(&mut self, iter: I) {
        for expr in iter {
            self.expr(expr);
        }
    }

    fn resolve(mut self, program: &'a Program<'a>) -> HashMap<Span, Span> {
        for item in &program.items {
            self.scope.define_path(Path::from(item.name().clone()));
        }

        for function in program.items.iter().filter_map(Item::as_function) {
            self.with_scope(|this| {
                for (param, _) in &function.params {
                    this.scope.define_ident(param.clone());
                }
                for (cont, _) in &function.continuations {
                    this.scope.define_ident(cont.clone());
                }
                this.exprs(&function.body);
            });
        }

        self.map
    }
}

pub fn resolve_names(program: &Program) -> HashMap<Span, Span> {
    Resolver::new().resolve(program)
}
