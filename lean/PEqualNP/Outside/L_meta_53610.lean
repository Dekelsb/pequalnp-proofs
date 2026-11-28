import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53610 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1865464 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [0, 14]⟩, ⟨.and, [1, 15]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [19, 18]⟩], 20⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
