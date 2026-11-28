import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54881 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17960 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [7, 15]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
