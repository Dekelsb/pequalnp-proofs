import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53704.Aux

open PEqualNP.CircuitLowerBounds

/-- Wires 0 through 3 select a row, and wires 4 through 9 select a column.
    Each subsequent wire is the output of the next gate in this list. -/
def witness : Circuit :=
  ⟨[⟨.or, [1, 3]⟩,
     ⟨.or, [1, 2]⟩,
     ⟨.or, [5, 6]⟩,
     ⟨.or, [5, 7]⟩,
     ⟨.or, [13, 8]⟩,
     ⟨.or, [14, 9]⟩,
     ⟨.and, [0, 15]⟩,
     ⟨.and, [11, 12]⟩,
     ⟨.and, [10, 4]⟩,
     ⟨.or, [16, 17]⟩,
     ⟨.or, [19, 18]⟩], 20⟩

end PEqualNP.Outside.L_meta_53704.Aux

theorem PEqualNP.Outside.L_meta_53704 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (287226 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_53704.Aux.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_53704.Aux.witness, PEqualNP.MetaComplexity.Monotone2]
