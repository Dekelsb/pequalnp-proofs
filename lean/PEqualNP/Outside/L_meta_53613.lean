import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53613.Aux

open PEqualNP.CircuitLowerBounds

/-- Wires 0 through 3 select a row, and wires 4 through 9 select a column.
    Each subsequent wire is the output of the next gate in this list. -/
def witness : Circuit :=
  ⟨[⟨.or, [2, 3]⟩,
     ⟨.or, [7, 8]⟩,
     ⟨.or, [11, 9]⟩,
     ⟨.or, [4, 5]⟩,
     ⟨.or, [13, 6]⟩,
     ⟨.or, [12, 13]⟩,
     ⟨.and, [0, 15]⟩,
     ⟨.and, [1, 12]⟩,
     ⟨.and, [10, 14]⟩,
     ⟨.or, [16, 17]⟩,
     ⟨.or, [19, 18]⟩], 20⟩

end PEqualNP.Outside.L_meta_53613.Aux

theorem PEqualNP.Outside.L_meta_53613 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1867323 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨PEqualNP.Outside.L_meta_53613.Aux.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_53613.Aux.witness, PEqualNP.MetaComplexity.Monotone2]
