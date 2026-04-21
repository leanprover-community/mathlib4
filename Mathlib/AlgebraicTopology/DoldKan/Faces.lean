/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Homotopies
public import Mathlib.Tactic.Ring

/-!

# Study of face maps for the Dold-Kan correspondence

In this file, we obtain the technical lemmas that are used in the file
`Projections.lean` in order to get basic properties of the endomorphisms
`P q : K[X] ⟶ K[X]` with respect to face maps (see `Homotopies.lean` for the
role of these endomorphisms in the overall strategy of proof).

The main lemma in this file is `HigherFacesVanish.induction`. It is based
on two technical lemmas `HigherFacesVanish.comp_Hσ_eq` and
`HigherFacesVanish.comp_Hσ_eq_zero`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
  CategoryTheory.Preadditive CategoryTheory.SimplicialObject Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C]
variable {X : SimplicialObject C}

/-- A morphism `φ : Y ⟶ X _⦋n+1⦌` satisfies `HigherFacesVanish q φ`
when the compositions `φ ≫ X.δ j` are `0` for `j ≥ max 1 (n+2-q)`. When `q ≤ n+1`,
it basically means that the composition `φ ≫ X.δ j` are `0` for the `q` highest
possible values of a nonzero `j`. Otherwise, when `q ≥ n+2`, all the compositions
`φ ≫ X.δ j` for nonzero `j` vanish. See also the lemma `comp_P_eq_self_iff` in
`Projections.lean` which states that `HigherFacesVanish q φ` is equivalent to
the identity `φ ≫ (P q).f (n+1) = φ`. -/
def HigherFacesVanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _⦋n + 1⦌) : Prop :=
  ∀ j : Fin (n + 1), n + 1 ≤ (j : ℕ) + q → φ ≫ X.δ j.succ = 0

namespace HigherFacesVanish

@[reassoc]
theorem comp_δ_eq_zero {Y : C} {n : ℕ} {q : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
    (j : Fin (n + 2)) (hj₁ : j ≠ 0) (hj₂ : n + 2 ≤ (j : ℕ) + q) : φ ≫ X.δ j = 0 := by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj₁
  apply v i
  simp only [Fin.val_succ] at hj₂
  lia

theorem of_succ {Y : C} {n q : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish (q + 1) φ) :
    HigherFacesVanish q φ := fun j hj => v j (by simpa only [← add_assoc] using le_add_right hj)

theorem of_comp {Y Z : C} {q n : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) (f : Z ⟶ Y) :
    HigherFacesVanish q (f ≫ φ) := fun j hj => by rw [assoc, v j hj, comp_zero]

set_option backward.isDefEq.respectTransparency false in
theorem comp_Hσ_eq {Y : C} {n a q : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
    (hnaq : n = a + q) :
    φ ≫ (Hσ q).f (n + 1) = -φ ≫ X.δ ⟨a + 1, by lia⟩ ≫ X.σ ⟨a, by lia⟩ := by
  have hnaq_shift (d : ℕ) : n + d = a + d + q := by lia
  rw [Hσ, Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl),
    hσ'_eq hnaq (c_mk (n + 1) n rfl), hσ'_eq (hnaq_shift 1) (c_mk (n + 2) (n + 1) rfl)]
  simp only [AlternatingFaceMapComplex.obj_d_eq, eqToHom_refl, comp_id, comp_sum, sum_comp,
    comp_add]
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul]
  -- cleaning up the first sum
  rw [← Fin.sum_congr' _ (hnaq_shift 2).symm, Fin.sum_trunc]
  swap
  · rintro ⟨k, hk⟩
    suffices φ ≫ X.δ (⟨a + 2 + k, by lia⟩ : Fin (n + 2)) = 0 by
      simp only [this, Fin.natAdd_mk, Fin.cast_mk, zero_comp, smul_zero]
    convert v ⟨a + k + 1, by lia⟩ (by rw [Fin.val_mk]; lia)
    dsimp
    lia
  -- cleaning up the second sum
  rw [← Fin.sum_congr' _ (hnaq_shift 3).symm, @Fin.sum_trunc _ _ (a + 3)]
  swap
  · rintro ⟨k, hk⟩
    rw [assoc, X.δ_comp_σ_of_gt', v.comp_δ_eq_zero_assoc, zero_comp, zsmul_zero]
    · intro h
      replace h : a + 3 + k = 1 := by simp [Fin.ext_iff] at h
      lia
    · dsimp [Fin.cast, Fin.pred]
      rw [Nat.add_right_comm, Nat.add_sub_assoc (by simp : 1 ≤ 3)]
      lia
    · simp only [Fin.lt_def]
      dsimp [Fin.natAdd, Fin.cast]
      lia
  simp only [assoc]
  conv_lhs =>
    congr
    · rw [Fin.sum_univ_castSucc]
    · rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  dsimp [Fin.cast, Fin.castLE, Fin.castLT]
  /- the purpose of the following `simplif` is to create three subgoals in order
      to finish the proof -/
  have simplif :
    ∀ a b c d e f : Y ⟶ X _⦋n + 1⦌, b = f → d + e = 0 → c + a = 0 → a + b + (c + d + e) = f := by
    intro a b c d e f h1 h2 h3
    rw [add_assoc c d e, h2, add_zero, add_comm a, add_assoc, add_comm a, h3, add_zero, h1]
  apply simplif
  · -- b = f
    rw [← pow_add, Odd.neg_one_pow, neg_smul, one_zsmul]
    exact ⟨a, by lia⟩
  · -- d + e = 0
    rw [X.δ_comp_σ_self' (Fin.castSucc_mk _ _ _).symm,
      X.δ_comp_σ_succ' (Fin.succ_mk _ _ _).symm]
    simp only [comp_id, pow_add _ (a + 1) 1, pow_one, mul_neg, mul_one, neg_mul, neg_smul,
      add_neg_cancel]
  · -- c + a = 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    rintro ⟨i, hi⟩ _
    simp only
    have hia : (⟨i, by lia⟩ : Fin (n + 2)) ≤
        Fin.castSucc (⟨a, by lia⟩ : Fin (n + 1)) := by
      rw [Fin.le_iff_val_le_val]
      dsimp
      lia
    generalize_proofs
    rw [← Fin.succ_mk (n + 1) a ‹_›, ← Fin.castSucc_mk (n + 2) i ‹_›,
      δ_comp_σ_of_le X hia, add_eq_zero_iff_eq_neg, ← neg_zsmul]
    congr 2
    ring

set_option backward.isDefEq.respectTransparency false in
theorem comp_Hσ_eq_zero {Y : C} {n q : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ)
    (hqn : n < q) : φ ≫ (Hσ q).f (n + 1) = 0 := by
  simp only [Hσ, Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]
  rw [hσ'_eq_zero hqn (c_mk (n + 1) n rfl), comp_zero, zero_add]
  by_cases hqn' : n + 1 < q
  · rw [hσ'_eq_zero hqn' (c_mk (n + 2) (n + 1) rfl), zero_comp, comp_zero]
  · simp only [hσ'_eq (show n + 1 = 0 + q by lia) (c_mk (n + 2) (n + 1) rfl), pow_zero,
      Fin.mk_zero, one_zsmul, eqToHom_refl, comp_id, comp_sum,
      AlternatingFaceMapComplex.obj_d_eq]
    -- All terms of the sum but the first two are zeros
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fintype.sum_eq_zero, add_zero]
    · simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, zero_add, pow_zero, one_smul,
        pow_one, neg_smul, comp_neg, ← Fin.castSucc_zero (n := n + 2), δ_comp_σ_self, δ_comp_σ_succ,
        add_neg_cancel]
    · intro j
      rw [comp_zsmul, comp_zsmul, δ_comp_σ_of_gt', v.comp_δ_eq_zero_assoc, zero_comp, zsmul_zero]
      · simp [Fin.succ_ne_zero]
      · dsimp
        lia
      · simp only [Fin.succ_lt_succ_iff, j.succ_pos]

set_option backward.isDefEq.respectTransparency false in
theorem induction {Y : C} {n q : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) :
    HigherFacesVanish (q + 1) (φ ≫ (𝟙 _ + Hσ q).f (n + 1)) := by
  intro j hj₁
  dsimp
  simp only [comp_add, add_comp, comp_id]
  -- when n < q, the result follows immediately from the assumption
  by_cases! hqn : n < q
  · rw [v.comp_Hσ_eq_zero hqn, zero_comp, add_zero, v j (by lia)]
  -- we now assume that n≥q, and write n=a+q
  obtain ⟨a, ha⟩ := Nat.le.dest hqn
  rw [v.comp_Hσ_eq (show n = a + q by lia), neg_comp, add_neg_eq_zero, assoc, assoc]
  rcases n with - | m
  -- the boundary case n=0
  · simp only [Nat.eq_zero_of_add_eq_zero_left ha, Fin.eq_zero j, Fin.mk_zero,
      δ_comp_σ_succ, comp_id]
    rfl
  -- in the other case, we need to write n as m+1
  -- then, we first consider the particular case j = a
  by_cases hj₂ : a = (j : ℕ)
  · simp only [hj₂, Fin.eta, δ_comp_σ_succ, comp_id]
    rfl
  -- now, we assume j ≠ a (i.e. a < j)
  have haj : a < j := (Ne.le_iff_lt hj₂).mp (by lia)
  have ham : a ≤ m := by grind
  rw [X.δ_comp_σ_of_gt', j.pred_succ]
  swap
  · rw [Fin.lt_def]
    simpa only [Fin.val_mk, Fin.val_succ, add_lt_add_iff_right] using haj
  obtain _ | ham'' := ham.lt_or_eq
  · -- case where `a<m`
    rw [← X.δ_comp_δ''_assoc]
    swap
    · rw [Fin.le_iff_val_le_val]
      dsimp
      lia
    simp only [← assoc, v j (by lia), zero_comp]
  · -- in the last case, a=m, q=1 and j=a+1
    rw [X.δ_comp_δ_self'_assoc]
    swap
    · ext
      cases j
      dsimp
      dsimp only [Nat.succ_eq_add_one] at *
      lia
    simp only [← assoc, v j (by lia), zero_comp]

end HigherFacesVanish

end DoldKan

end AlgebraicTopology
