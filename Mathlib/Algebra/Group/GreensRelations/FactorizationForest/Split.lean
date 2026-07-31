/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import GreensRelations.FactorizationForest.Regular
import GreensRelations.FactorizationForest.Irregular

/-!
# The Factorization Forest Theorem

## References
* [T. Colcombet, *The Factorization Forest Theorem*][colombet2008]
-/

namespace FactorizationForest

section SimonSplit

variable {S : Type*} [Semigroup S] [Fintype S]

/-- Auxiliary lemma for the induction step of Simon's split theorem. -/
lemma simon_split_induction_aux {S : Type*} [Semigroup S] [Fintype S]
    (n : ℕ) :
    ∀ (a : S) (_hn : nSElement a ≤ n)
    {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α)
    (_h_img : labelingIn σ (jUp a)),
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s := by
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro a _ α _ _ _ σ h_img
    have ih : ∀ b : S, nSElement b < nSElement a →
        ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
        (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
        ∃ (s : Split (OpenIntervalType xs i) (nSElement b)), IsNormalized s ∧ IsRamsey σ_β s :=
      fun b _ xs i _ σ_β h_img_β ↦ ihn (nSElement b) (by omega) b le_rfl σ_β h_img_β
    by_cases h_reg : IsRegularDClass (IsGreenD.eqvClass a)
    · exact simon_split_regular_case a σ h_img h_reg ih
    · exact simon_split_irregular_case a σ h_img h_reg ih

/-- The induction step of Simon's split theorem,
producing a split for elements up to a given Simon complexity. -/
lemma simon_split_induction (a : S) {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α)
    (h_img : labelingIn σ (jUp a)) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s :=
  simon_split_induction_aux (nSElement a) a le_rfl σ h_img

/-- The main Factorization Forest Theorem (Simon's Theorem),
stating that any multiplicative labeling over a finite linear order
admits a normalized Ramsey split bounded by the semigroup's Simon complexity. -/
theorem simon_split {S α : Type*} [Semigroup S] [Fintype S]
    [LinearOrder α] [Fintype α] [Nonempty α] [Nonempty (Fin (nS S))]
    (σ : MultiplicativeLabeling S α) :
    ∃ (s : Split α (nS S)), IsNormalized s ∧ IsRamsey σ s := by
  let x₀ := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
  let y₀ := Finset.max' (Finset.univ : Finset α) Finset.univ_nonempty
  let a := σ.σ x₀ y₀
  have ha : labelingIn σ (jUp a) := fun x y hlt ↦ by
    have hx0 : x₀ ≤ x := Finset.min'_le _ _ (Finset.mem_univ _)
    have hy0 : y ≤ y₀ := Finset.le_max' _ _ (Finset.mem_univ _)
    change IsGreenJRel (σ.σ x₀ y₀) (σ.σ x y)
    rcases hx0.eq_or_lt with rfl | hx0_lt
    · rcases hy0.eq_or_lt with rfl | hy0_lt
      · exact IsGreenJRel.refl _
      · exact IsGreenJRel.mul_right (σ.σ y y₀) (σ.prop _ y y₀ hlt hy0_lt).symm
    · rcases hy0.eq_or_lt with rfl | hy0_lt
      · exact IsGreenJRel.mul_left (σ.σ x₀ x) (σ.prop x₀ x _ hx0_lt hlt).symm
      · exact IsGreenJRel.mul_both (σ.σ x₀ x) (σ.σ y y₀)
          (by rw [← σ.prop x₀ y y₀ (hx0_lt.trans hlt) hy0_lt, ← σ.prop x₀ x y hx0_lt hlt])
  obtain ⟨s_a, h_norm, h_ramsey⟩ := simon_split_induction a σ ha
  have h_le : nSElement a ≤ nS S := by
    unfold nS
    have h_ne : (Finset.univ.image (fun (x : S) ↦ nSElement x)).Nonempty :=
      ⟨nSElement a, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
    exact (dif_pos h_ne).symm ▸ Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  let Δ := nS S - nSElement a
  let s : Split α (nS S) := fun x ↦ ⟨(s_a x).val + Δ, by have h_bound := (s_a x).isLt; omega⟩
  have hsr_iff : ∀ u v, SplitRelation s u v ↔ SplitRelation s_a u v := by grind
  exact ⟨s, by
      ext; simp only [h_norm, s]
      exact (congrArg Fin.val ((Finset.max'_eq_iff _ _
        (⟨nS S - 1, by have : 0 < nS S := Fin.pos_iff_nonempty.mpr inferInstance; omega⟩ :
        Fin (nS S))).mpr ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr
        (Nat.le_pred_of_lt w.isLt)⟩)).symm ▸ (congrArg Fin.val ((Finset.max'_eq_iff _ _
        (⟨nSElement a - 1, by have : 0 < nSElement a := nSElement_pos a; omega⟩ :
        Fin (nSElement a))).mpr ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr
        (Nat.le_pred_of_lt w.isLt)⟩)).symm ▸ (by have : 0 < nSElement a := nSElement_pos a; grind),
    fun x y hlt hsr ↦ h_ramsey.1 x y hlt ((hsr_iff x y).mp hsr),
    fun x y u v hxy huv hsr_xy hsr_uv hsr_xu ↦
      h_ramsey.2 x y u v hxy huv ((hsr_iff x y).mp hsr_xy)
        ((hsr_iff u v).mp hsr_uv) ((hsr_iff x u).mp hsr_xu)⟩

end SimonSplit

section SimonWord

/-- Simon's split theorem applied to word labelings. -/
theorem simon_word {A S : Type*} [Semigroup S] [Fintype S] [Nonempty (Fin (nS S))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) :
    ∃ s : Split (Fin (u.length + 1)) (nS S),
      IsNormalized s ∧ IsRamsey (wordLabeling eval hmul u) s :=
  simon_split (wordLabeling eval hmul u)

end SimonWord

end FactorizationForest
