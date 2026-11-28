import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54196

def witness : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
  ⟨.or, [0, 5]⟩,
  ⟨.or, [10, 6]⟩,
  ⟨.or, [10, 7]⟩,
  ⟨.or, [1, 4]⟩,
  ⟨.or, [12, 3]⟩,
  ⟨.and, [13, 14]⟩,
  ⟨.or, [2, 8]⟩,
  ⟨.or, [16, 9]⟩,
  ⟨.and, [11, 17]⟩,
  ⟨.or, [18, 15]⟩], 19⟩

end PEqualNP.Outside.L_meta_54196

open PEqualNP.Outside.L_meta_54196 in
theorem PEqualNP.Outside.L_meta_54196 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (287409 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  refine ⟨witness, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
