import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54348

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [5, 7]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.and, [2, 12]⟩,
      ⟨GateOp.and, [10, 15]⟩,
      ⟨GateOp.and, [11, 4]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [19, 18]⟩
    ],
    output := 20 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (290491 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54348

theorem PEqualNP.Outside.L_meta_54348 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (290491 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_54348.ckt, PEqualNP.Outside.L_meta_54348.mono, by decide, PEqualNP.Outside.L_meta_54348.rep⟩
