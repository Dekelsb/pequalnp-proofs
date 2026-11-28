import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54516

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [7, 8]⟩,
    ⟨.or, [6, 10]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.and, [0, 15]⟩,
    ⟨.and, [14, 13]⟩,
    ⟨.or, [18, 16]⟩,
    ⟨.or, [19, 17]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54516

theorem PEqualNP.Outside.L_meta_54516 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (907132 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_54516.circuit, PEqualNP.Outside.L_meta_54516.monotone, by decide +kernel, by decide +kernel⟩
