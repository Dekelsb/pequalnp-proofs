import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_56881 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164652 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.and, [4, 2]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [4, 2]⟩,
    ⟨.not, [1]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [5, 12]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.not, [14]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [6, 16]⟩], 17⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · simp [C, PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
  · decide +kernel
