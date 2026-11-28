import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_55088

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.not, [1]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [0, 10]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [13, 15]⟩], 16⟩

theorem wit_ok : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

set_option maxRecDepth 100000 in
theorem main_aux : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181053 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨wit, wit_ok, by decide, ?_⟩
  decide +kernel

end PEqualNP.Outside.L_meta_55088

theorem PEqualNP.Outside.L_meta_55088 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181053 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_55088.main_aux
