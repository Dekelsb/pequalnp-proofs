import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54567

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [12, 11]⟩,
    ⟨GateOp.or, [12, 7]⟩,
    ⟨GateOp.and, [13, 15]⟩,
    ⟨GateOp.or, [16, 4]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [18, 3]⟩,
    ⟨GateOp.and, [14, 19]⟩,
    ⟨GateOp.or, [17, 20]⟩
  ], 21⟩

lemma witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma witness_size : witness.size ≤ 12 := by
  decide

lemma witness_rep :
    Represents (fun (u : Fin 4) (v : Fin 6) => (1883515 : ℕ).testBit (6 * u.val + v.val)) witness := by
  decide

end PEqualNP.Outside.L_meta_54567

theorem PEqualNP.Outside.L_meta_54567 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883515 : ℕ).testBit (6 * u.val + v.val)) 12) :=
  ⟨PEqualNP.Outside.L_meta_54567.witness,
   PEqualNP.Outside.L_meta_54567.witness_mono,
   PEqualNP.Outside.L_meta_54567.witness_size,
   PEqualNP.Outside.L_meta_54567.witness_rep⟩
