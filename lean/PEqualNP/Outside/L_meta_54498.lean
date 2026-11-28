import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54498

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [4, 6]⟩,
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [12, 15]⟩,
      ⟨GateOp.and, [11, 2]⟩,
      ⟨GateOp.and, [10, 16]⟩,
      ⟨GateOp.and, [15, 12]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.or, [20, 19]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (810618 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54498

theorem PEqualNP.Outside.L_meta_54498 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (810618 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54498.ckt, PEqualNP.Outside.L_meta_54498.mono, by decide, PEqualNP.Outside.L_meta_54498.rep⟩
