import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54540_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (1881325 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [3, 7] }, { op := GateOp.or, inputs := [2, 6] },
      { op := GateOp.and, inputs := [1, 8] }, { op := GateOp.or, inputs := [0, 5] },
      { op := GateOp.or, inputs := [4, 12] }, { op := GateOp.and, inputs := [10, 11] },
      { op := GateOp.or, inputs := [1, 10] }, { op := GateOp.or, inputs := [9, 11] },
      { op := GateOp.or, inputs := [14, 15] }, { op := GateOp.or, inputs := [16, 17] },
      { op := GateOp.and, inputs := [13, 19] }, { op := GateOp.or, inputs := [18, 20] }],
    output := 21 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_54540_aux

theorem PEqualNP.Outside.L_meta_54540 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881325 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  exact ⟨PEqualNP.Outside.L_meta_54540_aux.upperC, PEqualNP.Outside.L_meta_54540_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_54540_aux.upper_rep⟩
