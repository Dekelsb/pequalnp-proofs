import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54401

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [1, 10]⟩,
      ⟨GateOp.or, [2, 10]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [7, 13]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.and, [17, 12]⟩,
      ⟨GateOp.and, [11, 15]⟩,
      ⟨GateOp.or, [18, 19]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (388030 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54401

theorem PEqualNP.Outside.L_meta_54401 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (388030 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_54401.ckt, PEqualNP.Outside.L_meta_54401.mono, by decide, PEqualNP.Outside.L_meta_54401.rep⟩
