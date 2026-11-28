import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_55641 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6375599 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [3, 2]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [1, 0]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.not, [7]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [6, 13]⟩,
    ⟨.and, [8, 12]⟩,
    ⟨.or, [14, 15]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
