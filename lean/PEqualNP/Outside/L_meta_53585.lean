import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53585 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903996 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [4, 5]⟩,
      ⟨.or, [0, 10]⟩,
      ⟨.or, [6, 3]⟩,
      ⟨.or, [12, 7]⟩,
      ⟨.or, [1, 0]⟩,
      ⟨.or, [2, 11]⟩,
      ⟨.or, [13, 8]⟩,
      ⟨.or, [9, 13]⟩,
      ⟨.and, [16, 15]⟩,
      ⟨.and, [14, 17]⟩,
      ⟨.or, [19, 18]⟩], 20⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
