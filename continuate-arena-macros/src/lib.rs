mod handle_self;
use handle_self::handle_self_ty;
use proc_macro2::Span;
use syn::Lifetime;

use std::collections::HashSet;
use std::iter;

use proc_macro::TokenStream;

use quote::quote;

use syn::parse_macro_input;
use syn::parse_quote_spanned;
use syn::punctuated::Punctuated;
use syn::Data;
use syn::DeriveInput;
use syn::Field;
use syn::Fields;
use syn::Path;
use syn::PredicateType;
use syn::Token;
use syn::TraitBound;
use syn::TraitBoundModifier;
use syn::Type;
use syn::TypeParamBound;
use syn::WhereClause;
use syn::WherePredicate;

#[proc_macro_derive(ArenaSafe)]
pub fn derive_arena_safe(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let mut impl_where_clause = where_clause.cloned().unwrap_or_else(|| WhereClause {
        where_token: Token![where](name.span()),
        predicates: Punctuated::new(),
    });

    for ty in data(&input.data) {
        let ty = handle_self_ty(ty, &name);
        impl_where_clause.predicates.push(predicate_trait(
            ty,
            parse_quote_spanned!(name.span()=> continuate_arena::ArenaSafe),
        ));
    }

    quote! {
        #[allow(unsafe_code)]
        unsafe impl #impl_generics continuate_arena::ArenaSafe for #name #ty_generics #impl_where_clause {}

        impl #impl_generics ::core::ops::Drop for #name #ty_generics #where_clause {
            #[inline]
            fn drop(&mut self) {}
        }
    }.into()
}

#[proc_macro_derive(ArenaSafeCopy)]
pub fn derive_arena_safe_copy(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let mut where_clause = where_clause.cloned().unwrap_or_else(|| WhereClause {
        where_token: Token![where](name.span()),
        predicates: Punctuated::new(),
    });
    where_clause.predicates.push(predicate_trait(
        parse_quote_spanned!(name.span()=> Self),
        parse_quote_spanned!(name.span()=> ::core::marker::Copy),
    ));

    quote! {
        #[allow(unsafe_code)]
        unsafe impl #impl_generics continuate_arena::ArenaSafe for #name #ty_generics #where_clause {}
    }.into()
}

#[proc_macro_derive(ArenaSafeStatic)]
pub fn derive_arena_safe_static(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = input.ident;

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    let mut where_clause = where_clause.cloned().unwrap_or_else(|| WhereClause {
        where_token: Token![where](name.span()),
        predicates: Punctuated::new(),
    });

    let bound = Lifetime::new("'static", Span::call_site());

    let predicate = PredicateType {
        lifetimes: None,
        bounded_ty: parse_quote_spanned!(name.span()=> Self),
        colon_token: <Token![:]>::default(),
        bounds: iter::once(TypeParamBound::Lifetime(bound)).collect(),
    };

    where_clause
        .predicates
        .push(WherePredicate::Type(predicate));

    quote! {
        #[allow(unsafe_code)]
        unsafe impl #impl_generics continuate_arena::ArenaSafe for #name #ty_generics #where_clause {}
    }.into()
}

fn predicate_trait(ty: Type, path: Path) -> WherePredicate {
    let bound = TraitBound {
        paren_token: None,
        modifier: TraitBoundModifier::None,
        lifetimes: None,
        path,
    };

    let predicate = PredicateType {
        lifetimes: None,
        bounded_ty: ty,
        colon_token: <Token![:]>::default(),
        bounds: iter::once(TypeParamBound::Trait(bound)).collect(),
    };

    WherePredicate::Type(predicate)
}

fn data(data: &Data) -> HashSet<Type> {
    match data {
        Data::Struct(data) => fields(&data.fields),
        Data::Enum(data) => {
            let mut types = HashSet::new();
            for variant in &data.variants {
                types.extend(fields(&variant.fields));
            }
            types
        }
        Data::Union(data) => field_iter(data.fields.named.iter()),
    }
}

fn fields(fields: &Fields) -> HashSet<Type> {
    match fields {
        Fields::Named(fields) => field_iter(fields.named.iter()),
        Fields::Unnamed(fields) => field_iter(fields.unnamed.iter()),
        Fields::Unit => HashSet::new(),
    }
}

fn field_iter<'a, I: Iterator<Item = &'a Field>>(iter: I) -> HashSet<Type> {
    let mut types = HashSet::new();
    for field in iter {
        types.insert(field.ty.clone());
    }
    types
}
