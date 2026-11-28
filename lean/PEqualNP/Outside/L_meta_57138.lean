import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57138 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2182841 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [3, 0]⟩, ⟨.or, [2, 0]⟩, ⟨.not, [6]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [12, 2]⟩, ⟨.or, [13, 1]⟩, ⟨.and, [14, 8]⟩, ⟨.not, [15]⟩, ⟨.and, [11, 16]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
