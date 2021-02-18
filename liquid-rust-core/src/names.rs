use std::fmt;

newtype_index! {
    struct Location
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "l{}", self.as_usize())
    }
}

newtype_index! {
    struct Local
}

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.as_usize())
    }
}

newtype_index! {
    struct Field
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "@{}", self.as_usize())
    }
}

newtype_index! {
    struct ContId
}

impl fmt::Display for ContId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "k{}", self.as_usize())
    }
}

newtype_index! {
    struct FnId
}

impl fmt::Display for FnId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "f{}", self.as_usize())
    }
}
