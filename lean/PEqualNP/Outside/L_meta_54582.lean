import PEqualNP.Defs

-- Proof pattern of the merged L_meta_22289 (Arthur Ariel Sabintsev); circuit from the 4x6 class table of
-- notes/tools/improve/gen/rep46.py (annealing search over all 3250 row/column classes, relabelled to this mask).
theorem PEqualNP.Outside.L_meta_54582 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1939439 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [13, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 20] }], output := 21 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
