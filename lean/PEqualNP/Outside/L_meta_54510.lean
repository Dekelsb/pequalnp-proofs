import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54510

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [12, 15]⟩, ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.and, [0, 17]⟩, ⟨GateOp.or, [19, 20]⟩], 21⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903151 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨wit, monoTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_54510

theorem PEqualNP.Outside.L_meta_54510 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (903151 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_54510.main_aux
