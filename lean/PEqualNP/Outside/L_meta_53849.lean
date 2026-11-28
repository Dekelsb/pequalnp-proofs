import PEqualNP.Defs

-- Explicit circuit checked by the kernel on all promise inputs. Template: the merged two-lit files on
-- upstream main (L_meta_21449 by Leg0shii, L_meta_21605 by odinfree), Apache-2.0. Circuit found by SAT.

namespace PEqualNP.Outside.L_meta_53849_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [8, 13]⟩], 14⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) && Nat.ble g.inputs.length 2

theorem okB_sound (C : Circuit) (h : okB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_53849_aux

theorem PEqualNP.Outside.L_meta_53849 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33956 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_53849_aux.ckt, PEqualNP.Outside.L_meta_53849_aux.okB_sound _ (by decide +kernel), by decide +kernel, by decide +kernel⟩
