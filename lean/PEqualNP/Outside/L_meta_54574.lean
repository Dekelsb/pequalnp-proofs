import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54574

open PEqualNP.CircuitLowerBounds

private def witnessCircuit : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [0, 4] }
      , { op := GateOp.or, inputs := [1, 4] }
      , { op := GateOp.or, inputs := [2, 8] }
      , { op := GateOp.or, inputs := [10, 7] }
      , { op := GateOp.or, inputs := [11, 5] }
      , { op := GateOp.or, inputs := [14, 6] }
      , { op := GateOp.or, inputs := [15, 13] }
      , { op := GateOp.or, inputs := [15, 9] }
      , { op := GateOp.or, inputs := [13, 3] }
      , { op := GateOp.and, inputs := [17, 18] }
      , { op := GateOp.or, inputs := [12, 19] }
      , { op := GateOp.and, inputs := [16, 20] }
      ]
    output := 21 }

end PEqualNP.Outside.L_meta_54574

theorem PEqualNP.Outside.L_meta_54574 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898103 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54574.witnessCircuit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_54574.witnessCircuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
