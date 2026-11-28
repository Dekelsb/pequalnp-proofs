import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54416

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [3, 5]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [5, 14]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.and, [13, 16]⟩,
    ⟨.and, [15, 17]⟩,
    ⟨.or, [18, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54416

theorem PEqualNP.Outside.L_meta_54416 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292536 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54416.circuit, PEqualNP.Outside.L_meta_54416.monotone, by decide, ?_⟩
  decide +kernel
