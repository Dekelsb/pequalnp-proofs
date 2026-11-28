import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53592

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [4, 9]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [6, 15]⟩,
    ⟨.and, [14, 16]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [11, 18]⟩,
    ⟨.or, [0, 19]⟩], 20⟩

end PEqualNP.Outside.L_meta_53592

theorem PEqualNP.Outside.L_meta_53592 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (905087 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨PEqualNP.Outside.L_meta_53592.circuit, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_53592.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
