import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54421.Aux

open PEqualNP.CircuitLowerBounds

/-- Wires 0 through 3 select a row, and wires 4 through 9 select a column.
    Each subsequent wire is the output of the next gate in this list. -/
def witness : Circuit :=
  ⟨[⟨.and, [0, 9]⟩,
     ⟨.or, [1, 2]⟩,
     ⟨.or, [5, 6]⟩,
     ⟨.and, [11, 12]⟩,
     ⟨.or, [0, 1]⟩,
     ⟨.or, [7, 8]⟩,
     ⟨.or, [5, 15]⟩,
     ⟨.and, [14, 16]⟩,
     ⟨.or, [13, 17]⟩,
     ⟨.or, [10, 18]⟩,
     ⟨.or, [4, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_54421.Aux

theorem PEqualNP.Outside.L_meta_54421 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (292859 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨PEqualNP.Outside.L_meta_54421.Aux.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_54421.Aux.witness, PEqualNP.MetaComplexity.Monotone2]
