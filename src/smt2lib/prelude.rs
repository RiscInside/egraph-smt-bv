use im_rc::{hashmap, HashMap};

use crate::smt2lib::{sort::Sort, Context};

use super::fun::{
    FunctionDef as Def, FunctionLoweringSpec as Lowering, FunctionSortCheckSpec as SortCheck,
};

impl Context {
    pub(crate) fn new() -> Context {
        use Sort::*;
        use SortCheck::*;

        let functions: HashMap<String, Def> = hashmap! {
            "true".to_owned() => Def::simple(SortCheck::fixed([], Bool), Lowering::variable("tt")),
            "false".to_owned() => Def::simple(SortCheck::fixed([], Bool), Lowering::variable("ff")),

            "not".to_owned() => Def::simple(SortCheck::fixed([Bool], Bool), Lowering::direct("Not")),
            "and".to_owned() => Def::simple(BooleanFold, Lowering::left_associative("And")),
            "or".to_owned() => Def::simple(BooleanFold, Lowering::left_associative("Or")),
            "xor".to_owned() => Def::simple(BooleanFold, Lowering::left_associative("Xor")),
            "=>".to_owned() => Def::simple(BooleanFold, Lowering::right_associative("Implies")),

            "=".to_owned() => Def::simple(EqualOrDistinct, Lowering::variadic("AllEqual")),
            "distinct".to_owned() => Def::simple(EqualOrDistinct, Lowering::variadic("AllDistinct")),

            "ite".to_owned() => Def::simple(ITE, Lowering::direct("ITE")),

            "concat".to_owned() => Def::simple(Concat, Lowering::left_associative("Concat")),

            "extract".to_owned() => Def { expected_indices: 2, sort_check: Extract, lowering: Lowering::direct("Extract") },
            "repeat".to_owned() => Def { expected_indices: 1, sort_check: Repeat, lowering: Lowering::direct("Repeat") },
            "rotate_left".to_owned() => Def { expected_indices: 1, sort_check: Rotate, lowering: Lowering::direct("RotateLeft") },
            "rotate_right".to_owned() => Def { expected_indices: 1, sort_check: Rotate, lowering: Lowering::direct("RotateRight") },
            "zero_extend".to_owned() => Def { expected_indices: 1, sort_check: Extension, lowering: Lowering::direct("ZeroExtend") },
            "sign_extend".to_owned() => Def { expected_indices: 1, sort_check: Extension, lowering: Lowering::direct("SignExtend") },

            "bvnot".to_owned() => Def::simple(BVUnary, Lowering::direct("BvNot")),
            "bvneg".to_owned() => Def::simple(BVUnary, Lowering::direct("BvNeg")),

            "bvand".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("BvAnd")),
            "bvor".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("BvOr")),
            "bvxor".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("BvXor")),

            "bvnand".to_owned() => Def::simple(BVBinary, Lowering::left_associative("BvNand")),

            "bvadd".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("BvAdd")),
            "bvmul".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("BvMul")),

            "bvsub".to_owned() => Def::simple(BVBinary, Lowering::direct("BvSub")),

            "bvudiv".to_owned() => Def::simple(BVBinary, Lowering::direct("BvUDiv")),
            "bvurem".to_owned() => Def::simple(BVBinary, Lowering::direct("BvURem")),
            "bvsdiv".to_owned() => Def::simple(BVBinary, Lowering::direct("BvSDiv")),
            "bvsmod".to_owned() => Def::simple(BVBinary, Lowering::direct("BvSmod")),
            "bvsrem".to_owned() => Def::simple(BVBinary, Lowering::direct("BvSrem")),
            "bvshl".to_owned() => Def::simple(BVBinary, Lowering::direct("BvShl")),
            "bvlshr".to_owned() => Def::simple(BVBinary, Lowering::direct("BvLShr")),
            "bvashr".to_owned() => Def::simple(BVBinary, Lowering::direct("BvAShr")),

            "bvule".to_owned() => Def::simple(BVCompare, Lowering::direct("BvUle")),
            "bvult".to_owned() => Def::simple(BVCompare, Lowering::direct("BvUlt")),
            "bvuge".to_owned() => Def::simple(BVCompare, Lowering::direct("BvUge")),
            "bvugt".to_owned() => Def::simple(BVCompare, Lowering::direct("BvUgt")),
            "bvsle".to_owned() => Def::simple(BVCompare, Lowering::direct("BvSle")),
            "bvslt".to_owned() => Def::simple(BVCompare, Lowering::direct("BvSlt")),
            "bvsge".to_owned() => Def::simple(BVCompare, Lowering::direct("BvSge")),
            "bvsgt".to_owned() => Def::simple(BVCompare, Lowering::direct("BvSgt")),
        };

        Context {
            fresh_vars_count: 0,
            functions,
        }
    }
}
