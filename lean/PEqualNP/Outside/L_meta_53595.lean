import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53595 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (908157 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [8, 10]⟩,
    ⟨.or, [0, 2]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 5]⟩,
    ⟨.and, [11, 14]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [4, 15]⟩,
    ⟨.or, [16, 18]⟩, ⟨.or, [17, 19]⟩], 20⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
