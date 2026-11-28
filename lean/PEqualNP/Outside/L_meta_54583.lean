import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [5, 6]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.and, [3, 11]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [4, 13]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.and, [16, 18]⟩,
    ⟨.or, [15, 19]⟩,
    ⟨.or, [12, 20]⟩], 21⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54583

theorem PEqualNP.Outside.L_meta_54583 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940398 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_54583.circuit, PEqualNP.Outside.L_meta_54583.monotone, by decide, ?_⟩
  decide +kernel
