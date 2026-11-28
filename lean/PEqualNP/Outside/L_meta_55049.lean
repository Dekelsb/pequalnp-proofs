import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55049

open PEqualNP.CircuitLowerBounds

private def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [6, 4]⟩, ⟨.not, [7]⟩, ⟨.and, [3, 8]⟩,
    ⟨.or, [1, 9]⟩, ⟨.not, [5]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [0, 5]⟩,
    ⟨.and, [2, 4]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [12, 15]⟩], 16⟩

end PEqualNP.Outside.L_meta_55049


-- Finite replay follows lean/PEqualNP/Outside/L_meta_24157.lean
-- at d667e87931366d16a0380297f19024953d7b1db3, with six inputs and eleven gates.
theorem PEqualNP.Outside.L_meta_55049 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164642 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_55049.witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_55049.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
