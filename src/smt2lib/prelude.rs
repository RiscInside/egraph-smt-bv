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

            "bvnot".to_owned() => Def::simple(BVUnary, Lowering::direct("Not")),
            "bvneg".to_owned() => Def::simple(BVUnary, Lowering::direct("Neg")),

            "bvand".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("And")),
            "bvor".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("Or")),
            "bvxor".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("Xor")),

            "bvnand".to_owned() => Def::simple(BVBinary, Lowering::left_associative("Nand")),

            "bvadd".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("Add")),
            "bvmul".to_owned() => Def::simple(IdenticalBVFold, Lowering::left_associative("Mul")),

            "bvsub".to_owned() => Def::simple(BVBinary, Lowering::direct("Sub")),

            "bvudiv".to_owned() => Def::simple(BVBinary, Lowering::direct("UDiv")),
            "bvurem".to_owned() => Def::simple(BVBinary, Lowering::direct("URem")),
            "bvsdiv".to_owned() => Def::simple(BVBinary, Lowering::direct("SDiv")),
            "bvsmod".to_owned() => Def::simple(BVBinary, Lowering::direct("Smod")),
            "bvsrem".to_owned() => Def::simple(BVBinary, Lowering::direct("Srem")),
            "bvshl".to_owned() => Def::simple(BVBinary, Lowering::direct("Shl")),
            "bvlshr".to_owned() => Def::simple(BVBinary, Lowering::direct("LShr")),
            "bvashr".to_owned() => Def::simple(BVBinary, Lowering::direct("AShr")),

            "bvule".to_owned() => Def::simple(BVCompare, Lowering::direct("Ule")),
            "bvult".to_owned() => Def::simple(BVCompare, Lowering::direct("Ult")),
            "bvuge".to_owned() => Def::simple(BVCompare, Lowering::direct("Uge")),
            "bvugt".to_owned() => Def::simple(BVCompare, Lowering::direct("Ugt")),
            "bvsle".to_owned() => Def::simple(BVCompare, Lowering::direct("Sle")),
            "bvslt".to_owned() => Def::simple(BVCompare, Lowering::direct("Slt")),
            "bvsge".to_owned() => Def::simple(BVCompare, Lowering::direct("Sge")),
            "bvsgt".to_owned() => Def::simple(BVCompare, Lowering::direct("Sgt")),
        };

        Context {
            sorts: hashmap! { "Bool".to_owned() => Sort::Bool },
            fresh_vars_count: 0,
            functions,
        }
    }
}
