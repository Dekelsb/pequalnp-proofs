import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54988 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114751 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [7, 12]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [0, 15]⟩], 16⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
  · decide +kernel
