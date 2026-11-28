import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55132 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197419 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [4, 2]⟩, ⟨.not, [8]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.and, [7, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
