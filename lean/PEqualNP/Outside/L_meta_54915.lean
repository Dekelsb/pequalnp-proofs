import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54915 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50351 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [7, 1]⟩, ⟨.or, [8, 5]⟩, ⟨.not, [9]⟩, ⟨.and, [2, 6]⟩, ⟨.and, [0, 6]⟩, ⟨.and, [11, 10]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [15, 13]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
