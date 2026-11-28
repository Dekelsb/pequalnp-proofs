import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54305

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.or, [7, 2]⟩, ⟨GateOp.or, [3, 1]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [4, 0]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.and, [14, 13]⟩, ⟨GateOp.or, [16, 1]⟩, ⟨GateOp.or, [17, 15]⟩, ⟨GateOp.and, [19, 18]⟩], 20⟩

theorem ok0 : Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_54305

theorem PEqualNP.Outside.L_meta_54305 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (276348 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_54305.C0, PEqualNP.Outside.L_meta_54305.ok0, by decide, by decide +kernel⟩
