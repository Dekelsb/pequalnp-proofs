import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54560

open PEqualNP.CircuitLowerBounds

private def witnessCircuit : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [0, 5] }
      , { op := GateOp.or, inputs := [1, 6] }
      , { op := GateOp.or, inputs := [2, 11] }
      , { op := GateOp.and, inputs := [2, 7] }
      , { op := GateOp.or, inputs := [13, 4] }
      , { op := GateOp.or, inputs := [10, 11] }
      , { op := GateOp.and, inputs := [10, 12] }
      , { op := GateOp.or, inputs := [16, 14] }
      , { op := GateOp.or, inputs := [8, 9] }
      , { op := GateOp.or, inputs := [18, 3] }
      , { op := GateOp.and, inputs := [15, 19] }
      , { op := GateOp.or, inputs := [17, 20] }
      ]
    output := 21 }

end PEqualNP.Outside.L_meta_54560

theorem PEqualNP.Outside.L_meta_54560 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883381 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54560.witnessCircuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54560.witnessCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
