import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54452

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [5, 7]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [13, 9]⟩,
    ⟨.or, [11, 8]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.and, [12, 15]⟩,
    ⟨.and, [0, 14]⟩,
    ⟨.or, [17, 16]⟩,
    ⟨.or, [19, 18]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54452

theorem PEqualNP.Outside.L_meta_54452 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (386991 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_54452.circuit, PEqualNP.Outside.L_meta_54452.monotone, by decide +kernel, by decide +kernel⟩
