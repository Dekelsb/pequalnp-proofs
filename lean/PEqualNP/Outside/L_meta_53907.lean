import PEqualNP.Defs

-- Explicit circuit checked by the kernel on all promise inputs. Template: the merged two-lit files on
-- upstream main (L_meta_21449 by Leg0shii, L_meta_21605 by odinfree), Apache-2.0. Circuit found by SAT.

namespace PEqualNP.Outside.L_meta_53907_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.and, [1, 11]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) && Nat.ble g.inputs.length 2

theorem okB_sound (C : Circuit) (h : okB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_53907_aux

theorem PEqualNP.Outside.L_meta_53907 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (51006 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_53907_aux.ckt, PEqualNP.Outside.L_meta_53907_aux.okB_sound _ (by decide +kernel), by decide +kernel, by decide +kernel⟩
