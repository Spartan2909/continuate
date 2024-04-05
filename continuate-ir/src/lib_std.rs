use std::collections::HashMap;

use crate::common::FuncRef;
use crate::common::Ident;
use crate::common::Intrinsic;
use crate::common::Literal;
use crate::common::TypeRef;
use crate::high_level_ir::Function;
use crate::high_level_ir::Program;
use crate::high_level_ir::Type;
use crate::high_level_ir::TypeConstructor;
use crate::high_level_ir::UserDefinedType;
use crate::ir_interpreter::Value;
use crate::ir_interpreter::ValueRef;

use continuate_arena::Arena;

#[derive(Debug, Clone, Copy)]
#[non_exhaustive]
pub struct StdLib<'arena> {
    pub ty_bool: TypeRef,
    pub ty_int: TypeRef,
    pub ty_float: TypeRef,
    pub ty_string: TypeRef,

    pub b_true: ValueRef<'arena>,
    pub b_false: ValueRef<'arena>,

    pub fn_termination: FuncRef,
    pub fn_discriminant: FuncRef,
}

impl<'arena> StdLib<'arena> {
    pub const fn ty_for(&self, literal: &Literal) -> TypeRef {
        match literal {
            Literal::Int(_) => self.ty_int,
            Literal::Float(_) => self.ty_float,
            Literal::String(_) => self.ty_string,
        }
    }
}

pub(crate) fn standard_library<'arena>(
    program: &mut Program<'arena>,
    arena: &'arena Arena<'arena>,
) -> StdLib<'arena> {
    let ty_bool = UserDefinedType {
        constructor: TypeConstructor::Sum(vec![vec![], vec![]]),
    };
    let ty_bool = arena.allocate(Type::UserDefined(ty_bool));
    let ty_bool_ref = program.ty();
    program.types.insert(ty_bool_ref, ty_bool);

    let ty_int = arena.allocate(Type::Int);
    let ty_int_ref = program.ty();
    program.types.insert(ty_int_ref, ty_int);

    let ty_float = arena.allocate(Type::Float);
    let ty_float_ref = program.ty();
    program.types.insert(ty_float_ref, ty_float);

    let ty_string = arena.allocate(Type::String);
    let ty_string_ref = program.ty();
    program.types.insert(ty_string_ref, ty_string);

    let b_true = arena.allocate(Value::user_defined(Some(1), vec![]));
    let b_false = arena.allocate(Value::user_defined(Some(0), vec![]));

    let fn_termination = arena.allocate(Function::new());
    let param = Ident(0);
    fn_termination.params.push((param, ty_int_ref));
    fn_termination.intrinsic = Some(Intrinsic::Terminate);

    let fn_termination_ref = program.function();
    program.functions.insert(fn_termination_ref, fn_termination);

    let int_fn = Type::function(vec![ty_int_ref], HashMap::new());
    let int_fn_ref = program.insert_type(int_fn, arena);

    let fn_discriminant = arena.allocate(Function::new());
    let param = Ident(0);
    fn_discriminant.params.push((param, ty_bool_ref)); // TODO: Should be generic.
    let cont = Ident(1);
    fn_discriminant.continuations.insert(cont, int_fn_ref);
    fn_discriminant.intrinsic = Some(Intrinsic::Discriminant);

    let fn_discriminant_ref = program.function();
    program
        .functions
        .insert(fn_discriminant_ref, fn_discriminant);

    StdLib {
        ty_bool: ty_bool_ref,
        ty_int: ty_int_ref,
        ty_float: ty_float_ref,
        ty_string: ty_string_ref,
        b_true,
        b_false,
        fn_termination: fn_termination_ref,
        fn_discriminant: fn_discriminant_ref,
    }
}
