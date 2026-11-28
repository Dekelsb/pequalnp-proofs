import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54628 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (288762 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨⟨[
    ⟨.or, [1, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [7, 8]⟩,
    ⟨.or, [5, 9]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [10, 4]⟩, ⟨.and, [11, 12]⟩,
    ⟨.and, [0, 15]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩,
    ⟨.or, [20, 21]⟩], 22⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
