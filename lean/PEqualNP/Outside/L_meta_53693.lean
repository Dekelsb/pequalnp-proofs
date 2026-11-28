import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53693

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [3, 14]⟩,
    ⟨.and, [12, 15]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.and, [10, 18]⟩,
    ⟨.or, [16, 19]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_53693

theorem PEqualNP.Outside.L_meta_53693 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275381 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_53693.circuit, PEqualNP.Outside.L_meta_53693.monotone, by decide, ?_⟩
  decide +kernel
