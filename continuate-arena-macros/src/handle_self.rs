use syn::parse_quote_spanned;
use syn::spanned::Spanned;
use syn::visit_mut::VisitMut;
use syn::Ident;
use syn::Path;
use syn::Type;

struct HandleSelf<'a> {
    name: &'a Ident,
}

impl<'a> HandleSelf<'a> {
    const fn new(name: &'a Ident) -> HandleSelf<'a> {
        HandleSelf { name }
    }
}

impl<'a> VisitMut for HandleSelf<'a> {
    fn visit_path_mut(&mut self, i: &mut Path) {
        if &i.segments.last().unwrap().ident == self.name
            || i.get_ident().is_some_and(|ident| ident == "Self")
        {
            *i = parse_quote_spanned!(i.span()=> u8);
        } else {
            for segment in &mut i.segments {
                self.visit_path_segment_mut(segment);
            }
        }
    }
}

pub(crate) fn handle_self_ty(mut ty: Type, name: &Ident) -> Type {
    HandleSelf::new(name).visit_type_mut(&mut ty);
    ty
}
