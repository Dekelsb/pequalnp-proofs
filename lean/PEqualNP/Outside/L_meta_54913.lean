import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54913 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50349 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [3, 7]⟩, ⟨.not, [5]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [6, 10]⟩, ⟨.not, [13]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [8, 15]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
