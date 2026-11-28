import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55643

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.not, [13]⟩, ⟨GateOp.and, [14, 15]⟩], 16⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_55643

theorem PEqualNP.Outside.L_meta_55643 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6375871 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_55643.C0, PEqualNP.Outside.L_meta_55643.ok0, by decide, by decide +kernel⟩
