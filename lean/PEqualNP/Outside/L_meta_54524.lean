import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54524

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [2, 5]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 11]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [3, 13]⟩,
    ⟨.or, [7, 14]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.and, [10, 16]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.and, [12, 18]⟩,
    ⟨.or, [17, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54524

theorem PEqualNP.Outside.L_meta_54524 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (909118 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54524.circuit, PEqualNP.Outside.L_meta_54524.monotone, by decide, ?_⟩
  decide +kernel
