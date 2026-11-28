import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_56069
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.or, [2, 1]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270700223 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_56069

theorem PEqualNP.Outside.L_meta_56069 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270700223 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := @PEqualNP.Outside.L_meta_56069.checked
