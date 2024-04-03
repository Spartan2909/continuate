use crate::high_level_ir::Function;
use crate::high_level_ir::Ident;
use crate::high_level_ir::Intrinsic;
use crate::high_level_ir::Type;
use crate::high_level_ir::TypeConstructor;
use crate::high_level_ir::UserDefinedType;
use crate::ir_interpreter::Value;
use crate::ir_interpreter::ValueRef;

use std::fmt;

use continuate_arena::Arena;

#[non_exhaustive]
pub struct StdLib<'arena> {
    pub ty_bool: &'arena Type<'arena>,
    pub ty_int: &'arena Type<'arena>,

    pub b_true: ValueRef<'arena>,
    pub b_false: ValueRef<'arena>,

    pub fn_termination: &'arena Function<'arena>,
    pub fn_discriminant: &'arena Function<'arena>,
}

impl<'arena> StdLib<'arena> {
    pub(crate) const fn clone(&self) -> StdLib<'arena> {
        StdLib {
            ty_bool: self.ty_bool,
            ty_int: self.ty_int,
            b_true: self.b_true,
            b_false: self.b_false,
            fn_termination: self.fn_termination,
            fn_discriminant: self.fn_discriminant,
        }
    }
}

impl<'arena> fmt::Debug for StdLib<'arena> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("StdLib").finish_non_exhaustive()
    }
}

pub(crate) fn standard_library<'arena>(arena: &'arena Arena<'arena>) -> StdLib<'arena> {
    let ty_bool = arena.allocate(UserDefinedType {
        constructor: TypeConstructor::Sum(vec![vec![], vec![]]),
    });
    let ty_bool = arena.allocate(Type::UserDefined(ty_bool));
    let ty_int = arena.allocate(Type::Int);

    let b_true = arena.allocate(Value::user_defined(Some(1), vec![]));
    let b_false = arena.allocate(Value::user_defined(Some(0), vec![]));

    let fn_termination = arena.allocate(Function::new());
    let param = Ident(0);
    fn_termination.params.insert(param, ty_int);
    fn_termination.intrinsic = Some(Intrinsic::Terminate);

    let int_fn = arena.allocate(Type::Function {
        params: vec![ty_int],
        continuations: vec![],
    });

    let fn_discriminant = arena.allocate(Function::new());
    let param = Ident(0);
    fn_discriminant.params.insert(param, ty_bool);
    let cont = Ident(1);
    fn_discriminant.continuations.insert(cont, int_fn);
    fn_discriminant.intrinsic = Some(Intrinsic::Discriminant);

    StdLib {
        ty_bool,
        ty_int,
        b_true,
        b_false,
        fn_termination,
        fn_discriminant,
    }
}
