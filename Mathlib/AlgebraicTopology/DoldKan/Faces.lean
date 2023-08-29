/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.DoldKan.Homotopies

#align_import algebraic_topology.dold_kan.faces from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

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


open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
  CategoryTheory.Preadditive CategoryTheory.SimplicialObject Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category C] [Preadditive C]

variable {X : SimplicialObject C}

/-- A morphism `φ : Y ⟶ X _[n+1]` satisfies `HigherFacesVanish q φ`
when the compositions `φ ≫ X.δ j` are `0` for `j ≥ max 1 (n+2-q)`. When `q ≤ n+1`,
it basically means that the composition `φ ≫ X.δ j` are `0` for the `q` highest
possible values of a nonzero `j`. Otherwise, when `q ≥ n+2`, all the compositions
`φ ≫ X.δ j` for nonzero `j` vanish. See also the lemma `comp_P_eq_self_iff` in
`Projections.lean` which states that `HigherFacesVanish q φ` is equivalent to
the identity `φ ≫ (P q).f (n+1) = φ`. -/
def HigherFacesVanish {Y : C} {n : ℕ} (q : ℕ) (φ : Y ⟶ X _[n + 1]) : Prop :=
  ∀ j : Fin (n + 1), n + 1 ≤ (j : ℕ) + q → φ ≫ X.δ j.succ = 0
#align algebraic_topology.dold_kan.higher_faces_vanish AlgebraicTopology.DoldKan.HigherFacesVanish

namespace HigherFacesVanish

@[reassoc]
theorem comp_δ_eq_zero {Y : C} {n : ℕ} {q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ)
    (j : Fin (n + 2)) (hj₁ : j ≠ 0) (hj₂ : n + 2 ≤ (j : ℕ) + q) : φ ≫ X.δ j = 0 := by
  obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hj₁
  -- ⊢ φ ≫ δ X (Fin.succ i) = 0
  apply v i
  -- ⊢ n + 1 ≤ ↑i + q
  simp only [Fin.val_succ] at hj₂
  -- ⊢ n + 1 ≤ ↑i + q
  linarith
  -- 🎉 no goals
#align algebraic_topology.dold_kan.higher_faces_vanish.comp_δ_eq_zero AlgebraicTopology.DoldKan.HigherFacesVanish.comp_δ_eq_zero

theorem of_succ {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish (q + 1) φ) :
    HigherFacesVanish q φ := fun j hj => v j (by simpa only [← add_assoc] using le_add_right hj)
                                                 -- 🎉 no goals
#align algebraic_topology.dold_kan.higher_faces_vanish.of_succ AlgebraicTopology.DoldKan.HigherFacesVanish.of_succ

theorem of_comp {Y Z : C} {q n : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) (f : Z ⟶ Y) :
    HigherFacesVanish q (f ≫ φ) := fun j hj => by rw [assoc, v j hj, comp_zero]
                                                  -- 🎉 no goals
#align algebraic_topology.dold_kan.higher_faces_vanish.of_comp AlgebraicTopology.DoldKan.HigherFacesVanish.of_comp

theorem comp_Hσ_eq {Y : C} {n a q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ)
    (hnaq : n = a + q) :
    φ ≫ (Hσ q).f (n + 1) =
      -φ ≫ X.δ ⟨a + 1, Nat.succ_lt_succ (Nat.lt_succ_iff.mpr (Nat.le.intro hnaq.symm))⟩ ≫
        X.σ ⟨a, Nat.lt_succ_iff.mpr (Nat.le.intro hnaq.symm)⟩ := by
  have hnaq_shift : ∀ d : ℕ, n + d = a + d + q := by
    intro d
    rw [add_assoc, add_comm d, ← add_assoc, hnaq]
  rw [Hσ, Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl),
    hσ'_eq hnaq (c_mk (n + 1) n rfl), hσ'_eq (hnaq_shift 1) (c_mk (n + 2) (n + 1) rfl)]
  simp only [AlternatingFaceMapComplex.obj_d_eq, eqToHom_refl, comp_id, comp_sum, sum_comp,
    comp_add]
  simp only [comp_zsmul, zsmul_comp, ← assoc, ← mul_zsmul]
  -- ⊢ ((Finset.sum Finset.univ fun x => ((-1) ^ a * (-1) ^ ↑x) • (φ ≫ δ X x) ≫ σ X …
  -- cleaning up the first sum
  rw [← Fin.sum_congr' _ (hnaq_shift 2).symm, Fin.sum_trunc]
  -- ⊢ ((Finset.sum Finset.univ fun i => ((-1) ^ a * (-1) ^ ↑(↑(Fin.castIso (_ : a  …
  swap
  -- ⊢ ∀ (j : Fin q), ((-1) ^ a * (-1) ^ ↑(↑(Fin.castIso (_ : a + 2 + q = n + 2)) ( …
  · rintro ⟨k, hk⟩
    -- ⊢ ((-1) ^ a * (-1) ^ ↑(↑(Fin.castIso (_ : a + 2 + q = n + 2)) (Fin.natAdd (a + …
    suffices φ ≫ X.δ (⟨a + 2 + k, by linarith⟩ : Fin (n + 2)) = 0 by
      simp only [this, Fin.natAdd_mk, Fin.castIso_mk, zero_comp, smul_zero]
    convert v ⟨a + k + 1, by linarith⟩ (by rw [Fin.val_mk]; linarith)
    -- ⊢ a + 2 + k = ↑(Fin.succ { val := a + k + 1, isLt := (_ : a + k + 1 < n + 1) })
    dsimp
    -- ⊢ a + 2 + k = a + k + 1 + 1
    linarith
    -- 🎉 no goals
  -- cleaning up the second sum
  rw [← Fin.sum_congr' _ (hnaq_shift 3).symm, @Fin.sum_trunc _ _ (a + 3)]
  -- ⊢ ((Finset.sum Finset.univ fun i => ((-1) ^ a * (-1) ^ ↑(↑(Fin.castIso (_ : a  …
  swap
  -- ⊢ ∀ (j : Fin q), ((-1) ^ ↑(↑(Fin.castIso (_ : a + 3 + q = n + 3)) (Fin.natAdd  …
  · rintro ⟨k, hk⟩
    -- ⊢ ((-1) ^ ↑(↑(Fin.castIso (_ : a + 3 + q = n + 3)) (Fin.natAdd (a + 3) { val : …
    rw [assoc, X.δ_comp_σ_of_gt', v.comp_δ_eq_zero_assoc, zero_comp, zsmul_zero]
    · simp only [Fin.lt_iff_val_lt_val]
      -- ⊢ ↑(Fin.succ { val := a + 1, isLt := (_ : a + 1 < Nat.succ (n + 1)) }) < ↑(↑(F …
      dsimp [Fin.natAdd, Fin.castIso]
      -- ⊢ a + 1 + 1 < a + 3 + k
      linarith
      -- 🎉 no goals
    · intro h
      -- ⊢ False
      rw [Fin.pred_eq_iff_eq_succ, Fin.ext_iff] at h
      -- ⊢ False
      dsimp [Fin.castIso] at h
      -- ⊢ False
      linarith
      -- 🎉 no goals
    · dsimp [Fin.castIso, Fin.pred]
      -- ⊢ n + 2 ≤ a + 3 + k - 1 + q
      rw [Nat.add_right_comm, Nat.add_sub_assoc (by norm_num : 1 ≤ 3)]
      -- ⊢ n + 2 ≤ a + k + (3 - 1) + q
      linarith
      -- 🎉 no goals
  simp only [assoc]
  -- ⊢ ((Finset.sum Finset.univ fun x => ((-1) ^ a * (-1) ^ ↑(↑(Fin.castIso (_ : a  …
  conv_lhs =>
    congr
    · rw [Fin.sum_univ_castSucc]
    · rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  dsimp [Fin.castIso, Fin.castLE, Fin.castLT]
  -- ⊢ (Finset.sum Finset.univ fun i => ((-1) ^ a * (-1) ^ ↑i) • φ ≫ δ X { val := ↑ …
  /- the purpose of the following `simplif` is to create three subgoals in order
      to finish the proof -/
  have simplif :
    ∀ a b c d e f : Y ⟶ X _[n + 1], b = f → d + e = 0 → c + a = 0 → a + b + (c + d + e) = f := by
    intro a b c d e f h1 h2 h3
    rw [add_assoc c d e, h2, add_zero, add_comm a, add_assoc, add_comm a, h3, add_zero, h1]
  apply simplif
  · -- b = f
    rw [← pow_add, Odd.neg_one_pow, neg_smul, one_zsmul]
    -- ⊢ Odd (a + (a + 1))
    exact ⟨a, by linarith⟩
    -- 🎉 no goals
  · -- d + e = 0
    rw [X.δ_comp_σ_self' (Fin.castSucc_mk _ _ _).symm,
      X.δ_comp_σ_succ' (Fin.succ_mk _ _ _).symm]
    simp only [comp_id, pow_add _ (a + 1) 1, pow_one, mul_neg, mul_one, neg_mul, neg_smul,
      add_right_neg]
  · -- c + a = 0
    rw [← Finset.sum_add_distrib]
    -- ⊢ (Finset.sum Finset.univ fun x => ((-1) ^ ↑x * (-1) ^ (a + 1)) • φ ≫ σ X { va …
    apply Finset.sum_eq_zero
    -- ⊢ ∀ (x : Fin (a + 1)), x ∈ Finset.univ → ((-1) ^ ↑x * (-1) ^ (a + 1)) • φ ≫ σ  …
    rintro ⟨i, hi⟩ _
    -- ⊢ ((-1) ^ ↑{ val := i, isLt := hi } * (-1) ^ (a + 1)) • φ ≫ σ X { val := a + 1 …
    simp only
    -- ⊢ ((-1) ^ i * (-1) ^ (a + 1)) • φ ≫ σ X { val := a + 1, isLt := (_ : a + 1 < N …
    have hia : (⟨i, by linarith⟩ : Fin (n + 2)) ≤
        Fin.castSucc (⟨a, by linarith⟩ : Fin (n + 1)) := by
      rw [Fin.le_iff_val_le_val]
      dsimp
      linarith
    erw [δ_comp_σ_of_le X hia, add_eq_zero_iff_eq_neg, ← neg_zsmul]
    -- ⊢ ((-1) ^ i * (-1) ^ (a + 1)) • φ ≫ δ X { val := i, isLt := (_ : i < n + 2) }  …
    congr 2
    -- ⊢ (-1) ^ i * (-1) ^ (a + 1) = -((-1) ^ a * (-1) ^ i)
    ring
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.higher_faces_vanish.comp_Hσ_eq AlgebraicTopology.DoldKan.HigherFacesVanish.comp_Hσ_eq

theorem comp_Hσ_eq_zero {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ)
    (hqn : n < q) : φ ≫ (Hσ q).f (n + 1) = 0 := by
  simp only [Hσ, Homotopy.nullHomotopicMap'_f (c_mk (n + 2) (n + 1) rfl) (c_mk (n + 1) n rfl)]
  -- ⊢ φ ≫ (HomologicalComplex.d (AlternatingFaceMapComplex.obj X) (n + 1) n ≫ hσ'  …
  rw [hσ'_eq_zero hqn (c_mk (n + 1) n rfl), comp_zero, zero_add]
  -- ⊢ φ ≫ hσ' q (n + 1) (n + 2) (_ : ComplexShape.Rel c (n + 2) (n + 1)) ≫ Homolog …
  by_cases hqn' : n + 1 < q
  -- ⊢ φ ≫ hσ' q (n + 1) (n + 2) (_ : ComplexShape.Rel c (n + 2) (n + 1)) ≫ Homolog …
  · rw [hσ'_eq_zero hqn' (c_mk (n + 2) (n + 1) rfl), zero_comp, comp_zero]
    -- 🎉 no goals
  · simp only [hσ'_eq (show n + 1 = 0 + q by linarith) (c_mk (n + 2) (n + 1) rfl), pow_zero,
      Fin.mk_zero, one_zsmul, eqToHom_refl, comp_id, comp_sum,
      AlternatingFaceMapComplex.obj_d_eq]
    rw [← Fin.sum_congr' _ (show 2 + (n + 1) = n + 1 + 2 by linarith), Fin.sum_trunc]
    -- ⊢ (Finset.sum Finset.univ fun i => φ ≫ σ X 0 ≫ ((-1) ^ ↑(↑(Fin.castIso (_ : 2  …
    · simp only [Fin.sum_univ_castSucc, Fin.sum_univ_zero, zero_add, Fin.last, Fin.castLE_mk,
        Fin.castIso_mk, Fin.castSucc_mk]
      simp only [Fin.mk_zero, Fin.val_zero, pow_zero, one_zsmul, Fin.mk_one, Fin.val_one, pow_one,
        neg_smul, comp_neg]
      erw [δ_comp_σ_self, δ_comp_σ_succ, add_right_neg]
      -- 🎉 no goals
    · intro j
      -- ⊢ φ ≫ σ X 0 ≫ ((-1) ^ ↑(↑(Fin.castIso (_ : 2 + (n + 1) = n + 1 + 2)) (Fin.natA …
      dsimp [Fin.castIso, Fin.castLE, Fin.castLT]
      -- ⊢ φ ≫ σ X 0 ≫ ((-1) ^ (2 + ↑j) • δ X { val := 2 + ↑j, isLt := (_ : ↑(Fin.natAd …
      rw [comp_zsmul, comp_zsmul, δ_comp_σ_of_gt', v.comp_δ_eq_zero_assoc, zero_comp, zsmul_zero]
      · simp only [Fin.lt_iff_val_lt_val]
        -- ⊢ ↑(Fin.succ 0) < 2 + ↑j
        dsimp [Fin.succ]
        -- ⊢ 0 + 1 < 2 + ↑j
        linarith
        -- 🎉 no goals
      · intro h
        -- ⊢ False
        simp only [Fin.pred, Fin.subNat, Fin.ext_iff, Nat.succ_add_sub_one,
          Fin.val_zero, add_eq_zero, false_and] at h
      · simp only [Fin.pred, Fin.subNat, Nat.pred_eq_sub_one, Nat.succ_add_sub_one]
        -- ⊢ n + 2 ≤ 1 + ↑j + q
        linarith
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.higher_faces_vanish.comp_Hσ_eq_zero AlgebraicTopology.DoldKan.HigherFacesVanish.comp_Hσ_eq_zero

theorem induction {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) :
    HigherFacesVanish (q + 1) (φ ≫ (𝟙 _ + Hσ q).f (n + 1)) := by
  intro j hj₁
  -- ⊢ (φ ≫ HomologicalComplex.Hom.f (𝟙 (AlternatingFaceMapComplex.obj X) + Hσ q) ( …
  dsimp
  -- ⊢ (φ ≫ (𝟙 (X.obj (Opposite.op [n + 1])) + HomologicalComplex.Hom.f (Hσ q) (n + …
  simp only [comp_add, add_comp, comp_id]
  -- ⊢ φ ≫ δ X (Fin.succ j) + (φ ≫ HomologicalComplex.Hom.f (Hσ q) (n + 1)) ≫ δ X ( …
  -- when n < q, the result follows immediately from the assumption
  by_cases hqn : n < q
  -- ⊢ φ ≫ δ X (Fin.succ j) + (φ ≫ HomologicalComplex.Hom.f (Hσ q) (n + 1)) ≫ δ X ( …
  · rw [v.comp_Hσ_eq_zero hqn, zero_comp, add_zero, v j (by linarith)]
    -- 🎉 no goals
  -- we now assume that n≥q, and write n=a+q
  cases' Nat.le.dest (not_lt.mp hqn) with a ha
  -- ⊢ φ ≫ δ X (Fin.succ j) + (φ ≫ HomologicalComplex.Hom.f (Hσ q) (n + 1)) ≫ δ X ( …
  rw [v.comp_Hσ_eq (show n = a + q by linarith), neg_comp, add_neg_eq_zero, assoc, assoc]
  -- ⊢ φ ≫ δ X (Fin.succ j) = φ ≫ δ X { val := a + 1, isLt := (_ : Nat.succ a < Nat …
  cases' n with m hm
  -- ⊢ φ ≫ δ X (Fin.succ j) = φ ≫ δ X { val := a + 1, isLt := (_ : Nat.succ a < Nat …
  -- the boundary case n=0
  · simp only [Nat.eq_zero_of_add_eq_zero_left ha, Fin.eq_zero j, Fin.mk_zero, Fin.mk_one,
      δ_comp_σ_succ, comp_id]
    rfl
    -- 🎉 no goals
  -- in the other case, we need to write n as m+1
  -- then, we first consider the particular case j = a
  by_cases hj₂ : a = (j : ℕ)
  -- ⊢ φ ≫ δ X (Fin.succ j) = φ ≫ δ X { val := a + 1, isLt := (_ : Nat.succ a < Nat …
  · simp only [hj₂, Fin.eta, δ_comp_σ_succ, comp_id]
    -- ⊢ φ ≫ δ X (Fin.succ j) = φ ≫ δ X { val := ↑j + 1, isLt := (_ : ↑j + 1 < Nat.su …
    rfl
    -- 🎉 no goals
  -- now, we assume j ≠ a (i.e. a < j)
  have haj : a < j := (Ne.le_iff_lt hj₂).mp (by linarith)
  -- ⊢ φ ≫ δ X (Fin.succ j) = φ ≫ δ X { val := a + 1, isLt := (_ : Nat.succ a < Nat …
  have hj₃ := j.is_lt
  -- ⊢ φ ≫ δ X (Fin.succ j) = φ ≫ δ X { val := a + 1, isLt := (_ : Nat.succ a < Nat …
  have ham : a ≤ m := by
    by_contra h
    rw [not_le, ← Nat.succ_le_iff] at h
    linarith
  rw [X.δ_comp_σ_of_gt', j.pred_succ]
  swap
  · rw [Fin.lt_iff_val_lt_val]
    -- ⊢ ↑(Fin.succ { val := a, isLt := (_ : a < Nat.succ (Nat.succ m)) }) < ↑(Fin.su …
    simpa only [Fin.val_mk, Fin.val_succ, add_lt_add_iff_right] using haj
    -- 🎉 no goals
  obtain _ | ham'' := ham.lt_or_eq
  -- ⊢ φ ≫ δ X (Fin.succ j) = φ ≫ δ X { val := a + 1, isLt := (_ : Nat.succ a < Nat …
  · -- case where `a<m`
    rw [← X.δ_comp_δ''_assoc]
    -- ⊢ φ ≫ δ X (Fin.succ j) = φ ≫ δ X (Fin.succ j) ≫ δ X (Fin.castLT { val := a + 1 …
    swap
    -- ⊢ { val := a + 1, isLt := (_ : Nat.succ a < Nat.succ (Nat.succ m + 1)) } ≤ Fin …
    · rw [Fin.le_iff_val_le_val]
      -- ⊢ ↑{ val := a + 1, isLt := (_ : Nat.succ a < Nat.succ (Nat.succ m + 1)) } ≤ ↑( …
      dsimp
      -- ⊢ a + 1 ≤ ↑j
      linarith
      -- 🎉 no goals
    simp only [← assoc, v j (by linarith), zero_comp]
    -- 🎉 no goals
  · -- in the last case, a=m, q=1 and j=a+1
    rw [X.δ_comp_δ_self'_assoc]
    -- ⊢ φ ≫ δ X (Fin.succ j) = φ ≫ δ X (Fin.succ j) ≫ δ X j ≫ σ X (Fin.castLT { val  …
    swap
    -- ⊢ { val := a + 1, isLt := (_ : Nat.succ a < Nat.succ (Nat.succ m + 1)) } = Fin …
    · ext
      -- ⊢ ↑{ val := a + 1, isLt := (_ : Nat.succ a < Nat.succ (Nat.succ m + 1)) } = ↑( …
      dsimp
      -- ⊢ a + 1 = ↑j
      linarith
      -- 🎉 no goals
    simp only [← assoc, v j (by linarith), zero_comp]
    -- 🎉 no goals
#align algebraic_topology.dold_kan.higher_faces_vanish.induction AlgebraicTopology.DoldKan.HigherFacesVanish.induction

end HigherFacesVanish

end DoldKan

end AlgebraicTopology
