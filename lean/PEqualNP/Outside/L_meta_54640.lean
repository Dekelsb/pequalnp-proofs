import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54640_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [4, 11]⟩,
    ⟨GateOp.and, [2, 12]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [5, 14]⟩,
    ⟨GateOp.and, [1, 15]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [14, 17]⟩,
    ⟨GateOp.and, [0, 18]⟩,
    ⟨GateOp.or, [10, 19]⟩,
    ⟨GateOp.or, [13, 16]⟩,
    ⟨GateOp.or, [20, 21]⟩], 22⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

end PEqualNP.Outside.L_meta_54640_aux

theorem PEqualNP.Outside.L_meta_54640 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292542 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_54640_aux.witness, PEqualNP.Outside.L_meta_54640_aux.witness_mono, by decide, ?_⟩
  decide +kernel
