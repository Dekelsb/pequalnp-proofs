import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54460

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [6, 8]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.or, [18, 17]⟩,
    ⟨.or, [19, 16]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54460

theorem PEqualNP.Outside.L_meta_54460 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (800636 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_54460.circuit, PEqualNP.Outside.L_meta_54460.monotone, by decide +kernel, by decide +kernel⟩
