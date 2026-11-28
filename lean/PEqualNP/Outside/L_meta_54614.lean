import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54614

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [0, 10]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.and, [14, 7]⟩,
    ⟨.and, [15, 6]⟩,
    ⟨.and, [12, 11]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [19, 16]⟩,
    ⟨.or, [20, 13]⟩], 21⟩

theorem monotone : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

end PEqualNP.Outside.L_meta_54614

theorem PEqualNP.Outside.L_meta_54614 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4161019 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_54614.circuit, PEqualNP.Outside.L_meta_54614.monotone, by decide +kernel, by decide +kernel⟩
