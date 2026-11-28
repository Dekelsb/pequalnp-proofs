import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54529.Helpers

open PEqualNP.CircuitLowerBounds

-- Rows 2 and 3 have identical neighborhoods. The OR of columns 1 and 2
-- is shared between that common neighborhood and row 0.
def circuit : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [10, 11]⟩,
    ⟨.and, [0, 12]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [2, 3]⟩,
    ⟨.and, [14, 15]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [4, 17]⟩,
    ⟨.and, [1, 18]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [19, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_54529.Helpers

theorem PEqualNP.Outside.L_meta_54529 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (1865326 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  refine ⟨PEqualNP.Outside.L_meta_54529.Helpers.circuit, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_54529.Helpers.circuit]
