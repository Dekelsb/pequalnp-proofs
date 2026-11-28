import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53601

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [0, 10]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.and, [0, 9]⟩,
    ⟨.and, [14, 5]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.or, [15, 17]⟩,
    ⟨.or, [18, 4]⟩,
    ⟨.or, [19, 16]⟩], 20⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_53601

theorem PEqualNP.Outside.L_meta_53601 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (915453 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_53601.circuit, PEqualNP.Outside.L_meta_53601.monotone, by decide +kernel, by decide +kernel⟩
