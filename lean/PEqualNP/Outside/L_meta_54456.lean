import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54456 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (388094 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [5, 6]⟩,
      ⟨.or, [10, 7]⟩,
      ⟨.or, [0, 1]⟩,
      ⟨.or, [0, 2]⟩,
      ⟨.or, [1, 11]⟩,
      ⟨.or, [13, 4]⟩,
      ⟨.or, [11, 9]⟩,
      ⟨.and, [12, 16]⟩,
      ⟨.or, [14, 8]⟩,
      ⟨.or, [18, 3]⟩,
      ⟨.and, [15, 19]⟩,
      ⟨.or, [17, 20]⟩], 21⟩
  exact ⟨C, by simp [C, PEqualNP.MetaComplexity.Monotone2], by decide, by decide⟩
