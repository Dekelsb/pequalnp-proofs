import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54370

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [4, 0]⟩, ⟨GateOp.or, [13, 1]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.and, [12, 14]⟩, ⟨GateOp.or, [16, 5]⟩, ⟨GateOp.and, [18, 15]⟩, ⟨GateOp.or, [17, 19]⟩], 20⟩

theorem ok0 : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_54370

theorem PEqualNP.Outside.L_meta_54370 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292856 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_54370.C0, PEqualNP.Outside.L_meta_54370.ok0, by decide, by decide +kernel⟩
