use crate::slice::Slice;

/// The layout of a primitive type, a product type, or a single variant of a sum type.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SingleLayout<'a> {
    pub size: u64,
    /// The value of this field must not be greater than one word on the target.
    pub align: u64,
    pub field_locations: Slice<'a, u64>,
    pub gc_pointer_locations: Slice<'a, u64>,
}

impl<'a> SingleLayout<'a> {
    #[inline]
    pub const fn primitive(size: u64, align: u64) -> SingleLayout<'a> {
        SingleLayout {
            size,
            align,
            field_locations: Slice::new(&[]),
            gc_pointer_locations: Slice::new(&[]),
        }
    }
}

/// The layout of a type.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyLayout<'a> {
    Single(SingleLayout<'a>) = 0,
    Sum {
        layouts: Slice<'a, SingleLayout<'a>>,
        /// The size required to hold the largest variant layout, in bytes.
        size: u64,
        /// The highest alignment required by a variant layout, in bytes.
        align: u64,
    } = 1,
    String = 2,
}

impl<'a> TyLayout<'a> {
    #[inline]
    pub const fn size(&self) -> Option<u64> {
        match *self {
            TyLayout::Single(ref layout) => Some(layout.size),
            TyLayout::Sum { size, .. } => Some(size),
            TyLayout::String => None,
        }
    }

    #[inline]
    pub const fn align(&self) -> u64 {
        match *self {
            TyLayout::Single(ref layout) => layout.align,
            TyLayout::Sum { align, .. } => align,
            TyLayout::String => 1,
        }
    }

    #[inline]
    pub const fn as_single(&self) -> Option<&SingleLayout<'a>> {
        if let TyLayout::Single(layout) = self {
            Some(layout)
        } else {
            None
        }
    }

    #[inline]
    pub const fn as_sum(&self) -> Option<Slice<'a, SingleLayout<'a>>> {
        if let TyLayout::Sum { layouts, .. } = *self {
            Some(layouts)
        } else {
            None
        }
    }
}

impl<'a> From<SingleLayout<'a>> for TyLayout<'a> {
    #[inline]
    fn from(value: SingleLayout<'a>) -> Self {
        TyLayout::Single(value)
    }
}
