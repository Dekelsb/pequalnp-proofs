import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_58658 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6507710 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [7, 0]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [10, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [12, 8]⟩, ⟨.or, [11, 3]⟩, ⟨.not, [13]⟩, ⟨.and, [15, 14]⟩], 16⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
