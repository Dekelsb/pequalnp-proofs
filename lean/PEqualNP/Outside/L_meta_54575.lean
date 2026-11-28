import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54575

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [7, 10]⟩,
      ⟨GateOp.or, [2, 8]⟩,
      ⟨GateOp.or, [3, 12]⟩,
      ⟨GateOp.or, [1, 6]⟩,
      ⟨GateOp.or, [10, 14]⟩,
      ⟨GateOp.or, [1, 9]⟩,
      ⟨GateOp.or, [12, 16]⟩,
      ⟨GateOp.and, [15, 13]⟩,
      ⟨GateOp.and, [11, 17]⟩,
      ⟨GateOp.or, [18, 19]⟩,
      ⟨GateOp.or, [20, 4]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1898225 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_54575

theorem PEqualNP.Outside.L_meta_54575 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898225 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_54575.ckt, PEqualNP.Outside.L_meta_54575.mono, by decide, PEqualNP.Outside.L_meta_54575.rep⟩
