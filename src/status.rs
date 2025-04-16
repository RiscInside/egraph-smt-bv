#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SATStatus {
    UnSat,
    #[allow(dead_code)]
    Sat,
    Unknown,
}

impl std::fmt::Display for SATStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SATStatus::UnSat => write!(f, "unsat"),
            SATStatus::Sat => write!(f, "sat"),
            SATStatus::Unknown => write!(f, "unknown"),
        }
    }
}
