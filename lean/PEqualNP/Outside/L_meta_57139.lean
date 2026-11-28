import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_57139 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2182845 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.or, [3, 1]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [6, 13]⟩, ⟨.not, [15]⟩, ⟨.and, [14, 16]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
