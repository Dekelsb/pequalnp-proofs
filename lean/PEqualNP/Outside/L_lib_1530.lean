import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1530_aux

def pairs {n : ℕ} (u : Finset (Fin n) → ℕ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun x : Finset (Fin n) => i ∉ x)).sum (fun x => min (u x) (u (insert i x)))

def comp {n : ℕ} (i : Fin n) (u : Finset (Fin n) → ℕ) (x : Finset (Fin n)) : ℕ :=
  if i ∈ x then min (u x) (u (x.erase i)) else max (u x) (u (insert i x))

def partner {n : ℕ} (i : Fin n) (x : Finset (Fin n)) : Finset (Fin n) :=
  if i ∈ x then x.erase i else insert i x

theorem partner_erase {n : ℕ} (i : Fin n) (x : Finset (Fin n)) : (partner i x).erase i = x.erase i := by
  unfold partner
  split_ifs with h
  · exact Finset.erase_eq_of_notMem (Finset.notMem_erase i x)
  · exact Finset.erase_insert_eq_erase x i

theorem partner_partner {n : ℕ} (i : Fin n) (x : Finset (Fin n)) : partner i (partner i x) = x := by
  by_cases h : i ∈ x
  · have hp : partner i x = x.erase i := if_pos h
    rw [hp]
    unfold partner
    rw [if_neg (Finset.notMem_erase i x), Finset.insert_erase h]
  · have hp : partner i x = insert i x := if_neg h
    rw [hp]
    unfold partner
    rw [if_pos (Finset.mem_insert_self i x), Finset.erase_insert h]

def flip {n : ℕ} (i : Fin n) (u : Finset (Fin n) → ℕ) (x : Finset (Fin n)) : Finset (Fin n) :=
  if u (x.erase i) < u (insert i (x.erase i)) then partner i x else x

theorem flip_inv {n : ℕ} (i : Fin n) (u : Finset (Fin n) → ℕ) (x : Finset (Fin n)) :
    flip i u (flip i u x) = x := by
  by_cases h : u (x.erase i) < u (insert i (x.erase i))
  · have hfx : flip i u x = partner i x := if_pos h
    rw [hfx]
    unfold flip
    rw [partner_erase, if_pos h, partner_partner]
  · have hfx : flip i u x = x := if_neg h
    rw [hfx, hfx]

theorem comp_eq {n : ℕ} (i : Fin n) (u : Finset (Fin n) → ℕ) (x : Finset (Fin n)) :
    comp i u x = u (flip i u x) := by
  unfold comp flip
  by_cases hx : i ∈ x
  · have hb : insert i (x.erase i) = x := Finset.insert_erase hx
    have hp : partner i x = x.erase i := if_pos hx
    rw [if_pos hx, hb, hp]
    split_ifs with h <;> omega
  · have hb : x.erase i = x := Finset.erase_eq_of_notMem hx
    have hp : partner i x = insert i x := if_neg hx
    rw [if_neg hx, hb, hp]
    split_ifs with h <;> omega

def sig {n : ℕ} (i : Fin n) (u : Finset (Fin n) → ℕ) : Equiv.Perm (Finset (Fin n)) :=
  Function.Involutive.toPerm (flip i u) (fun x => flip_inv i u x)

theorem pairs_self {n : ℕ} (i : Fin n) (u : Finset (Fin n) → ℕ) : pairs (comp i u) i = pairs u i := by
  unfold pairs
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_filter] at hx
  have h1 : comp i u x = max (u x) (u (insert i x)) := by
    unfold comp
    rw [if_neg hx.2]
  have h2 : comp i u (insert i x) = min (u (insert i x)) (u x) := by
    unfold comp
    rw [if_pos (Finset.mem_insert_self i x), Finset.erase_insert hx.2]
  rw [h1, h2]
  omega

theorem pairs_split {n : ℕ} (u : Finset (Fin n) → ℕ) (i j : Fin n) (hij : i ≠ j) :
    pairs u j = ∑ x ∈ (Finset.univ.filter (fun x : Finset (Fin n) => j ∉ x)).filter (fun x => i ∉ x),
      (min (u x) (u (insert j x)) + min (u (insert i x)) (u (insert j (insert i x)))) := by
  unfold pairs
  have hB : ∑ x ∈ (Finset.univ.filter (fun x : Finset (Fin n) => j ∉ x)).filter (fun x => i ∈ x),
      min (u x) (u (insert j x)) =
      ∑ x ∈ (Finset.univ.filter (fun x : Finset (Fin n) => j ∉ x)).filter (fun x => i ∉ x),
      min (u (insert i x)) (u (insert j (insert i x))) := by
    apply Finset.sum_nbij' (fun x => x.erase i) (fun x => insert i x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨fun h => hx.1 (Finset.mem_of_mem_erase h), Finset.notMem_erase i x⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨?_, Finset.mem_insert_self i x⟩
      rw [Finset.mem_insert]
      push_neg
      exact ⟨fun h => hij h.symm, hx.1⟩
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.insert_erase hx.2
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.erase_insert hx.2
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.insert_erase hx.2]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun x : Finset (Fin n) => j ∉ x))
    (fun x => i ∈ x), hB, Finset.sum_add_distrib, add_comm]

theorem pairs_le {n : ℕ} (u : Finset (Fin n) → ℕ) (i j : Fin n) (hij : i ≠ j) :
    pairs u j ≤ pairs (comp i u) j := by
  rw [pairs_split u i j hij, pairs_split (comp i u) i j hij]
  apply Finset.sum_le_sum
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hjx, hix⟩ := hx
  have hjne : j ≠ i := fun h => hij h.symm
  have hi_jx : i ∉ insert j x := by
    rw [Finset.mem_insert]
    push_neg
    exact ⟨hij, hix⟩
  have e1 : comp i u x = max (u x) (u (insert i x)) := by
    unfold comp
    rw [if_neg hix]
  have e2 : comp i u (insert j x) = max (u (insert j x)) (u (insert j (insert i x))) := by
    unfold comp
    rw [if_neg hi_jx, Finset.insert_comm]
  have e3 : comp i u (insert i x) = min (u (insert i x)) (u x) := by
    unfold comp
    rw [if_pos (Finset.mem_insert_self i x), Finset.erase_insert hix]
  have e4 : comp i u (insert j (insert i x)) = min (u (insert j (insert i x))) (u (insert j x)) := by
    unfold comp
    rw [if_pos (Finset.mem_insert_of_mem (Finset.mem_insert_self i x)), Finset.erase_insert_of_ne hjne,
      Finset.erase_insert hix]
  rw [e1, e2, e3, e4]
  omega

def anti {n : ℕ} (j : Fin n) (u : Finset (Fin n) → ℕ) : Prop := ∀ x, j ∉ x → u (insert j x) ≤ u x

theorem anti_self {n : ℕ} (i : Fin n) (u : Finset (Fin n) → ℕ) : anti i (comp i u) := by
  intro x hx
  have e1 : comp i u x = max (u x) (u (insert i x)) := by
    unfold comp
    rw [if_neg hx]
  have e3 : comp i u (insert i x) = min (u (insert i x)) (u x) := by
    unfold comp
    rw [if_pos (Finset.mem_insert_self i x), Finset.erase_insert hx]
  rw [e1, e3]
  omega

theorem anti_keep {n : ℕ} (i j : Fin n) (hij : i ≠ j) (u : Finset (Fin n) → ℕ) (h : anti j u) :
    anti j (comp i u) := by
  intro x hjx
  by_cases hix : i ∈ x
  · have e1 : comp i u x = min (u x) (u (x.erase i)) := by
      unfold comp
      rw [if_pos hix]
    have e2 : comp i u (insert j x) = min (u (insert j x)) (u (insert j (x.erase i))) := by
      unfold comp
      rw [if_pos (Finset.mem_insert_of_mem hix), Finset.erase_insert_of_ne (fun h' => hij h'.symm)]
    rw [e1, e2]
    have h1 := h x hjx
    have h2 := h (x.erase i) (fun h' => hjx (Finset.mem_of_mem_erase h'))
    omega
  · have hi_jx : i ∉ insert j x := by
      rw [Finset.mem_insert]
      push_neg
      exact ⟨hij, hix⟩
    have e1 : comp i u x = max (u x) (u (insert i x)) := by
      unfold comp
      rw [if_neg hix]
    have e2 : comp i u (insert j x) = max (u (insert j x)) (u (insert j (insert i x))) := by
      unfold comp
      rw [if_neg hi_jx, Finset.insert_comm]
    rw [e1, e2]
    have h1 := h x hjx
    have h2 := h (insert i x) (by
      rw [Finset.mem_insert]
      push_neg
      exact ⟨fun h' => hij h'.symm, hjx⟩)
    omega

def compAll {n : ℕ} (L : List (Fin n)) (u : Finset (Fin n) → ℕ) : Finset (Fin n) → ℕ :=
  L.foldl (fun acc i => comp i acc) u

theorem compAll_spec {n : ℕ} (L : List (Fin n)) : ∀ u : Finset (Fin n) → ℕ,
    (∃ σ : Equiv.Perm (Finset (Fin n)), ∀ x, compAll L u x = u (σ x)) ∧
    (∀ j, pairs u j ≤ pairs (compAll L u) j) ∧
    (∀ j, (j ∈ L ∨ anti j u) → anti j (compAll L u)) := by
  induction L with
  | nil =>
    intro u
    exact ⟨⟨Equiv.refl _, fun x => rfl⟩, fun j => le_refl _, fun j h => h.resolve_left (by simp)⟩
  | cons i L ih =>
    intro u
    obtain ⟨⟨τ, hτ⟩, hp, ha⟩ := ih (comp i u)
    have e : compAll (i :: L) u = compAll L (comp i u) := rfl
    rw [e]
    refine ⟨⟨τ.trans (sig i u), fun x => ?_⟩, fun j => ?_, fun j hj => ?_⟩
    · rw [hτ, comp_eq]
      rfl
    · refine le_trans ?_ (hp j)
      by_cases hij : i = j
      · subst hij
        exact (pairs_self i u).ge
      · exact pairs_le u i j hij
    · apply ha
      rcases hj with hj | hj
      · rcases List.mem_cons.1 hj with rfl | hj
        · exact Or.inr (anti_self j u)
        · exact Or.inl hj
      · by_cases hij : i = j
        · subst hij
          exact Or.inr (anti_self i u)
        · exact Or.inr (anti_keep i j hij u hj)

theorem main (n : ℕ) (w : Finset (Fin n) → ℕ) :
    ∃ v : Finset (Fin n) → ℕ,
      (∀ x y : Finset (Fin n), x ⊆ y → v y ≤ v x) ∧
      (∃ σ : Equiv.Perm (Finset (Fin n)), ∀ x, v x = w (σ x)) ∧
      (∑ x, v x) = (∑ x, w x) ∧
      ∀ i : Fin n, pairs w i ≤ pairs v i := by
  obtain ⟨⟨σ, hσ⟩, hp, ha⟩ := compAll_spec (List.finRange n) w
  have hanti : ∀ j, anti j (compAll (List.finRange n) w) := fun j => ha j (Or.inl (List.mem_finRange j))
  refine ⟨compAll (List.finRange n) w, ?_, ⟨σ, hσ⟩, ?_, hp⟩
  · have key : ∀ d, ∀ x y : Finset (Fin n), x ⊆ y → (y \ x).card = d →
        compAll (List.finRange n) w y ≤ compAll (List.finRange n) w x := by
      intro d
      induction d with
      | zero =>
        intro x y hxy hd
        have h1 : y ⊆ x := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hd)
        have h2 := Finset.Subset.antisymm h1 hxy
        subst h2
        exact le_refl _
      | succ d ih =>
        intro x y hxy hd
        obtain ⟨j, hj⟩ : (y \ x).Nonempty := Finset.card_pos.1 (by omega)
        rw [Finset.mem_sdiff] at hj
        have hx' : x ⊆ y.erase j := fun a ha => Finset.mem_erase.2 ⟨fun h => hj.2 (h ▸ ha), hxy ha⟩
        have hd' : (y.erase j \ x).card = d := by
          rw [Finset.erase_sdiff_comm, Finset.card_erase_of_mem (Finset.mem_sdiff.2 hj)]
          omega
        have h1 : compAll (List.finRange n) w y ≤ compAll (List.finRange n) w (y.erase j) := by
          have := hanti j (y.erase j) (Finset.notMem_erase j y)
          rwa [Finset.insert_erase hj.1] at this
        exact le_trans h1 (ih x (y.erase j) hx' hd')
    intro x y hxy
    exact key _ x y hxy rfl
  · rw [show (∑ x, compAll (List.finRange n) w x) = ∑ x, w (σ x) from
      Finset.sum_congr rfl (fun x _ => hσ x)]
    exact Equiv.sum_comp σ w

end PEqualNP.Outside.L_lib_1530_aux

theorem PEqualNP.Outside.L_lib_1530 : (∀ (n : Nat) (w : Finset (Fin n) → Nat),
  let W := Finset (Fin n)
  let pairs := fun (u : W → Nat) (i : Fin n) =>
    (Finset.univ.filter (fun x : W => i ∉ x)).sum
      (fun x => min (u x) (u (insert i x)))
  ∃ v : W → Nat,
    (∀ x y : W, x ⊆ y → v y ≤ v x) ∧
    (∃ σ : Equiv.Perm W, ∀ x, v x = w (σ x)) ∧
    (∑ x, v x) = (∑ x, w x) ∧
    ∀ i : Fin n, pairs w i ≤ pairs v i) := by
  intro n w W pairs
  exact PEqualNP.Outside.L_lib_1530_aux.main n w
