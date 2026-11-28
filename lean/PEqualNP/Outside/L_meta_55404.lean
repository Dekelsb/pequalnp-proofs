import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55404 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4294590 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.not, [5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
