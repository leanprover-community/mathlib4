/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Faces
public import Mathlib.CategoryTheory.Idempotents.Basic

/-!

# Construction of projections for the Dold-Kan correspondence

In this file, we construct endomorphisms `P q : K[X] ⟶ K[X]` for all
`q : ℕ`. We study how they behave with respect to face maps with the lemmas
`HigherFacesVanish.of_P`, `HigherFacesVanish.comp_P_eq_self` and
`comp_P_eq_self_iff`.

Then, we show that they are projections (see `P_f_idem`
and `P_idem`). They are natural transformations (see `natTransP`
and `P_f_naturality`) and are compatible with the application
of additive functors (see `map_P`).

By passing to the limit, these endomorphisms `P q` shall be used in `PInfty.lean`
in order to define `PInfty : K[X] ⟶ K[X]`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject Opposite CategoryTheory.Idempotents

open Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X : SimplicialObject C}

/-- This is the inductive definition of the projections `P q : K[X] ⟶ K[X]`,
with `P 0 := 𝟙 _` and `P (q+1) := P q ≫ (𝟙 _ + Hσ q)`. -/
noncomputable def P : ℕ → (K[X] ⟶ K[X])
  | 0 => 𝟙 _
  | q + 1 => P q ≫ (𝟙 _ + Hσ q)

lemma P_zero : (P 0 : K[X] ⟶ K[X]) = 𝟙 _ := rfl
lemma P_succ (q : ℕ) : (P (q + 1) : K[X] ⟶ K[X]) = P q ≫ (𝟙 _ + Hσ q) := rfl

/-- All the `P q` coincide with `𝟙 _` in degree 0. -/
@[simp]
theorem P_f_0_eq (q : ℕ) : ((P q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _ := by
  induction q with
  | zero => rfl
  | succ q hq =>
    simp only [P_succ, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      HomologicalComplex.id_f, id_comp, hq, Hσ_eq_zero, add_zero]

/-- `Q q` is the complement projection associated to `P q` -/
def Q (q : ℕ) : K[X] ⟶ K[X] :=
  𝟙 _ - P q

theorem P_add_Q (q : ℕ) : P q + Q q = 𝟙 K[X] := by
  rw [Q]
  abel

theorem P_add_Q_f (q n : ℕ) : (P q).f n + (Q q).f n = 𝟙 (X _⦋n⦌) :=
  HomologicalComplex.congr_hom (P_add_Q q) n

@[simp]
theorem Q_zero : (Q 0 : K[X] ⟶ _) = 0 :=
  sub_self _

theorem Q_succ (q : ℕ) : (Q (q + 1) : K[X] ⟶ _) = Q q - P q ≫ Hσ q := by
  simp only [Q, P_succ, comp_add, comp_id]
  abel

/-- All the `Q q` coincide with `0` in degree 0. -/
@[simp]
theorem Q_f_0_eq (q : ℕ) : ((Q q).f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0 := by
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Q, P_f_0_eq, sub_self]

namespace HigherFacesVanish

/-- This lemma expresses the vanishing of
`(P q).f (n+1) ≫ X.δ k : X _⦋n+1⦌ ⟶ X _⦋n⦌` when `k≠0` and `k≥n-q+2` -/
theorem of_P : ∀ q n : ℕ, HigherFacesVanish q ((P q).f (n + 1) : X _⦋n + 1⦌ ⟶ X _⦋n + 1⦌)
  | 0 => fun n j hj₁ => by lia
  | q + 1 => fun n => by
    simp only [P_succ]
    exact (of_P q n).induction

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem comp_P_eq_self {Y : C} {n q : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} (v : HigherFacesVanish q φ) :
    φ ≫ (P q).f (n + 1) = φ := by
  induction q with
  | zero =>
    simp only [P_zero]
    apply comp_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, ← assoc, hq v.of_succ, add_eq_left]
    by_cases! hqn : n < q
    · exact v.of_succ.comp_Hσ_eq_zero hqn
    · obtain ⟨a, ha⟩ := Nat.le.dest hqn
      have hnaq : n = a + q := by lia
      simp only [v.of_succ.comp_Hσ_eq hnaq, neg_eq_zero, ← assoc]
      have eq := v ⟨a, by lia⟩ (by
        simp only [hnaq, add_assoc]
        rfl)
      simp only [Fin.succ_mk] at eq
      simp only [eq, zero_comp]

end HigherFacesVanish

theorem comp_P_eq_self_iff {Y : C} {n q : ℕ} {φ : Y ⟶ X _⦋n + 1⦌} :
    φ ≫ (P q).f (n + 1) = φ ↔ HigherFacesVanish q φ := by
  constructor
  · intro hφ
    rw [← hφ]
    apply HigherFacesVanish.of_comp
    apply HigherFacesVanish.of_P
  · exact HigherFacesVanish.comp_P_eq_self

@[reassoc (attr := simp)]
theorem P_f_idem (q n : ℕ) : ((P q).f n : X _⦋n⦌ ⟶ _) ≫ (P q).f n = (P q).f n := by
  rcases n with (_ | n)
  · rw [P_f_0_eq q, comp_id]
  · exact (HigherFacesVanish.of_P q n).comp_P_eq_self

@[reassoc (attr := simp)]
theorem Q_f_idem (q n : ℕ) : ((Q q).f n : X _⦋n⦌ ⟶ _) ≫ (Q q).f n = (Q q).f n :=
  idem_of_id_sub_idem _ (P_f_idem q n)

@[reassoc (attr := simp)]
theorem P_idem (q : ℕ) : (P q : K[X] ⟶ K[X]) ≫ P q = P q := by
  ext n
  exact P_f_idem q n

@[reassoc (attr := simp)]
theorem Q_idem (q : ℕ) : (Q q : K[X] ⟶ K[X]) ≫ Q q = Q q := by
  ext n
  exact Q_f_idem q n

set_option backward.isDefEq.respectTransparency false in
/-- For each `q`, `P q` is a natural transformation. -/
@[simps]
def natTransP (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := P q
  naturality _ _ f := by
    induction q with
    | zero =>
      dsimp [alternatingFaceMapComplex]
      simp only [P_zero, id_comp, comp_id]
    | succ q hq =>
      simp only [P_succ, add_comp, comp_add, assoc, comp_id, hq, reassoc_of% hq]
      -- `erw` is needed to see through `natTransHσ q).app = Hσ q`
      erw [(natTransHσ q).naturality f]
      rfl

set_option backward.isDefEq.respectTransparency false in -- This is needed in AlgebraicTopology/DoldKan/Decomposition.lean
@[reassoc (attr := simp)]
theorem P_f_naturality (q n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ (P q).f n = (P q).f n ≫ f.app (op ⦋n⦌) :=
  HomologicalComplex.congr_hom ((natTransP q).naturality f) n

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem Q_f_naturality (q n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ (Q q).f n = (Q q).f n ≫ f.app (op ⦋n⦌) := by
  simp only [Q, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, P_f_naturality,
    sub_comp, sub_left_inj]
  dsimp
  simp only [comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- For each `q`, `Q q` is a natural transformation. -/
@[simps]
def natTransQ (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := Q q

set_option backward.isDefEq.respectTransparency false in
theorem map_P {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    G.map ((P q : K[X] ⟶ _).f n) = (P q : K[((whiskering C D).obj G).obj X] ⟶ _).f n := by
  induction q with
  | zero =>
    simp only [P_zero]
    apply G.map_id
  | succ q hq =>
    simp only [P_succ, comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply,
      comp_id, Functor.map_add, Functor.map_comp, hq, map_Hσ]

set_option backward.isDefEq.respectTransparency false in
theorem map_Q {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    G.map ((Q q : K[X] ⟶ _).f n) = (Q q : K[((whiskering C D).obj G).obj X] ⟶ _).f n := by
  rw [← add_right_inj (G.map ((P q : K[X] ⟶ _).f n)), ← G.map_add, map_P G X q n, P_add_Q_f,
    P_add_Q_f]
  apply G.map_id

end DoldKan

end AlgebraicTopology
