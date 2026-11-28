import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54490

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [6, 11]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.or, [13, 2]⟩,
      ⟨GateOp.or, [15, 8]⟩,
      ⟨GateOp.and, [12, 16]⟩,
      ⟨GateOp.and, [10, 14]⟩,
      ⟨GateOp.and, [9, 0]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.or, [20, 19]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (808621 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54490

theorem PEqualNP.Outside.L_meta_54490 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808621 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54490.ckt, PEqualNP.Outside.L_meta_54490.mono, by decide, PEqualNP.Outside.L_meta_54490.rep⟩
