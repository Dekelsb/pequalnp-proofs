import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54423

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [10, 14]⟩,
    ⟨.or, [3, 15]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.and, [11, 17]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.or, [18, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54423

theorem PEqualNP.Outside.L_meta_54423 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (294522 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54423.circuit, PEqualNP.Outside.L_meta_54423.monotone, by decide, ?_⟩
  decide +kernel
