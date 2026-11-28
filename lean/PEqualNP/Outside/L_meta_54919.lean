import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54919

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C0 : Circuit := ⟨[⟨GateOp.and, [0, 2]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.or, [3, 5]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.or, [13, 15]⟩], 16⟩

theorem ok0 : FanInTwo C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_54919

theorem PEqualNP.Outside.L_meta_54919 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50603 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_54919.C0, PEqualNP.Outside.L_meta_54919.ok0, by decide, by decide +kernel⟩
