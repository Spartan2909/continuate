use crate::Expr;
use crate::Ident;
use crate::Item;
use crate::Path;
use crate::Program;

use std::collections::HashMap;
use std::collections::HashSet;
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
        assert!(self.paths.insert(path, span).is_none(), "path shadowed");
    }
}

#[derive(Debug)]
pub struct NameMap {
    ident_definitions: HashSet<Span>,
    idents: HashMap<Span, Span>,
    path_definitions: HashSet<Span>,
    paths: HashMap<Span, Span>,
}

impl NameMap {
    fn new() -> NameMap {
        NameMap {
            ident_definitions: HashSet::new(),
            idents: HashMap::new(),
            path_definitions: HashSet::new(),
            paths: HashMap::new(),
        }
    }

    fn define_ident(&mut self, ident: &Ident) {
        self.ident_definitions.insert(ident.span);
    }

    fn define_path(&mut self, path: &Path) {
        self.path_definitions.insert(path.span);
    }

    fn insert_ident(&mut self, ident: &Ident, target_span: Span) {
        self.idents.insert(ident.span, target_span);
    }

    fn insert_path(&mut self, path: &Path, target_span: Span) {
        self.paths.insert(path.span, target_span);
    }

    pub fn get_ident(&self, ident: &Ident) -> Option<Span> {
        self.idents.get(&ident.span).copied()
    }

    pub fn ident_definitions(&self) -> impl Iterator<Item = Span> + use<'_> {
        self.ident_definitions.iter().copied()
    }

    pub fn get_path(&self, path: &Path) -> Option<Span> {
        self.paths.get(&path.span).copied()
    }

    pub fn path_definitions(&self) -> impl Iterator<Item = Span> + use<'_> {
        self.path_definitions.iter().copied()
    }
}

struct Resolver<'a> {
    map: NameMap,
    scope: Scope<'a>,
}

impl<'a> Resolver<'a> {
    fn new() -> Resolver<'a> {
        Resolver {
            map: NameMap::new(),
            scope: Scope::new(),
        }
    }

    fn define_ident(&mut self, ident: Ident<'a>) {
        self.map.define_ident(&ident);
        self.scope.define_ident(ident.clone());
        self.resolve_ident(&ident);
    }

    fn define_path(&mut self, path: Path<'a>) {
        self.map.define_path(&path);
        self.scope.define_path(path.clone());
        self.resolve_path(&path);
    }

    fn try_resolve_ident(&mut self, ident: &Ident) -> Result<(), ()> {
        self.map
            .insert_ident(ident, self.scope.get_ident(ident).ok_or(())?);
        Ok(())
    }

    #[track_caller]
    fn resolve_ident(&mut self, ident: &Ident) {
        self.try_resolve_ident(ident).unwrap()
    }

    #[track_caller]
    fn resolve_path(&mut self, path: &Path) {
        self.map
            .insert_path(path, self.scope.get_path(path).unwrap());
    }

    #[track_caller]
    fn resolve_ident_or_path(&mut self, path: &Path) {
        if let Some(ident) = path.as_ident() {
            if self.try_resolve_ident(ident).is_ok() {
                return;
            }
        }

        self.resolve_path(path);
    }

    fn with_scope(&mut self, f: impl FnOnce(&mut Self)) {
        self.scope = Scope::with_parent(mem::take(&mut self.scope));
        f(self);
        self.scope = *self.scope.parent.take().unwrap();
    }

    fn expr(&mut self, expr: &'a Expr<'a>) {
        match expr {
            Expr::Literal(_) => {}
            Expr::Path(path) => self.resolve_ident_or_path(path),
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
                self.define_ident(name.clone());
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

    fn resolve(mut self, program: &'a Program<'a>) -> NameMap {
        for item in &program.items {
            self.define_path(Path::from(item.name().clone()));
        }

        for function in program.items.iter().filter_map(Item::as_function) {
            self.with_scope(|this| {
                for (param, _) in &function.params {
                    this.define_ident(param.clone());
                }
                for (cont, _) in &function.continuations {
                    this.define_ident(cont.clone());
                }
                this.exprs(&function.body);
            });
        }

        self.map
    }
}

pub fn resolve_names(program: &Program) -> NameMap {
    Resolver::new().resolve(program)
}
