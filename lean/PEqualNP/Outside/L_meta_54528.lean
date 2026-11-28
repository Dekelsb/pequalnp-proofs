import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54528 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1040254 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [11, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [3, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 20] }], output := 21 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
