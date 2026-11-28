import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54396_aux

def ckt : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 12]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 11]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [11, 13]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 15]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 17]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 16]⟩,
    ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [18, 19]⟩], 20⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sz : ckt.size ≤ 11 := by decide

theorem rep : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (325566 : ℕ).testBit (6 * u.val + v.val)) ckt := by decide

end PEqualNP.Outside.L_meta_54396_aux

theorem PEqualNP.Outside.L_meta_54396 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (325566 : ℕ).testBit (6 * u.val + v.val)) 11) :=
  ⟨PEqualNP.Outside.L_meta_54396_aux.ckt, PEqualNP.Outside.L_meta_54396_aux.mono, PEqualNP.Outside.L_meta_54396_aux.sz, PEqualNP.Outside.L_meta_54396_aux.rep⟩
