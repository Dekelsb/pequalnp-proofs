import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_54821 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (281235263 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [1, 12]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.or, [0, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
