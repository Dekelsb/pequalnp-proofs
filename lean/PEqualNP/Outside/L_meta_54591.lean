import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54591.Aux

open PEqualNP.CircuitLowerBounds

/-- Wires 0 through 3 select a row, and wires 4 through 9 select a column.
    Each subsequent wire is the output of the next gate in this list. -/
def witness : Circuit :=
  ⟨[⟨.or, [7, 9]⟩,
     ⟨.and, [0, 10]⟩,
     ⟨.or, [1, 3]⟩,
     ⟨.and, [6, 12]⟩,
     ⟨.or, [1, 2]⟩,
     ⟨.or, [7, 8]⟩,
     ⟨.and, [14, 15]⟩,
     ⟨.or, [13, 16]⟩,
     ⟨.or, [11, 17]⟩,
     ⟨.or, [5, 18]⟩,
     ⟨.or, [4, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_54591.Aux

theorem PEqualNP.Outside.L_meta_54591 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947627 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_54591.Aux.witness, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.Outside.L_meta_54591.Aux.witness, PEqualNP.MetaComplexity.Monotone2]
