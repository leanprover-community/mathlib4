/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.projections
! leanprover-community/mathlib commit ed98c07faf6d9de3e52771d5b00394c4294ccb4d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.Faces
import Mathbin.CategoryTheory.Idempotents.Basic

/-!

# Construction of projections for the Dold-Kan correspondence

TODO (@joelriou) continue adding the various files referenced below

In this file, we construct endomorphisms `P q : K[X] ⟶ K[X]` for all
`q : ℕ`. We study how they behave with respect to face maps with the lemmas
`higher_faces_vanish.of_P`, `higher_faces_vanish.comp_P_eq_self` and
`comp_P_eq_self_iff`.

Then, we show that they are projections (see `P_f_idem`
and `P_idem`). They are natural transformations (see `nat_trans_P`
and `P_f_naturality`) and are compatible with the application
of additive functors (see `map_P`).

By passing to the limit, these endomorphisms `P q` shall be used in `p_infty.lean`
in order to define `P_infty : K[X] ⟶ K[X]`, see `equivalence.lean` for the general
strategy of proof of the Dold-Kan equivalence.

-/


open
  CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive CategoryTheory.SimplicialObject Opposite CategoryTheory.Idempotents

open Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] {X : SimplicialObject C}

/-- This is the inductive definition of the projections `P q : K[X] ⟶ K[X]`,
with `P 0 := 𝟙 _` and `P (q+1) := P q ≫ (𝟙 _ + Hσ q)`. -/
noncomputable def p : ℕ → (K[X] ⟶ K[X])
  | 0 => 𝟙 _
  | q + 1 => P q ≫ (𝟙 _ + hσ q)
#align algebraic_topology.dold_kan.P AlgebraicTopology.DoldKan.p

/-- All the `P q` coincide with `𝟙 _` in degree 0. -/
@[simp]
theorem p_f_0_eq (q : ℕ) : ((p q).f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
  by
  induction' q with q hq
  · rfl
  · unfold P
    simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, HomologicalComplex.id_f,
      id_comp, hq, Hσ_eq_zero, add_zero]
#align algebraic_topology.dold_kan.P_f_0_eq AlgebraicTopology.DoldKan.p_f_0_eq

/-- `Q q` is the complement projection associated to `P q` -/
def q (q : ℕ) : K[X] ⟶ K[X] :=
  𝟙 _ - p q
#align algebraic_topology.dold_kan.Q AlgebraicTopology.DoldKan.q

theorem p_add_q (q : ℕ) : p q + q q = 𝟙 K[X] :=
  by
  rw [Q]
  abel
#align algebraic_topology.dold_kan.P_add_Q AlgebraicTopology.DoldKan.p_add_q

theorem p_add_q_f (q n : ℕ) : (p q).f n + (q q).f n = 𝟙 (X _[n]) :=
  HomologicalComplex.congr_hom (p_add_q q) n
#align algebraic_topology.dold_kan.P_add_Q_f AlgebraicTopology.DoldKan.p_add_q_f

@[simp]
theorem q_eq_zero : (q 0 : K[X] ⟶ _) = 0 :=
  sub_self _
#align algebraic_topology.dold_kan.Q_eq_zero AlgebraicTopology.DoldKan.q_eq_zero

theorem q_eq (q : ℕ) : (q (q + 1) : K[X] ⟶ _) = q q - p q ≫ hσ q :=
  by
  unfold Q P
  simp only [comp_add, comp_id]
  abel
#align algebraic_topology.dold_kan.Q_eq AlgebraicTopology.DoldKan.q_eq

/-- All the `Q q` coincide with `0` in degree 0. -/
@[simp]
theorem q_f_0_eq (q : ℕ) : ((q q).f 0 : X _[0] ⟶ X _[0]) = 0 := by
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Q, P_f_0_eq, sub_self]
#align algebraic_topology.dold_kan.Q_f_0_eq AlgebraicTopology.DoldKan.q_f_0_eq

namespace HigherFacesVanish

/-- This lemma expresses the vanishing of
`(P q).f (n+1) ≫ X.δ k : X _[n+1] ⟶ X _[n]` when `k≠0` and `k≥n-q+2` -/
theorem of_p : ∀ q n : ℕ, HigherFacesVanish q ((p q).f (n + 1) : X _[n + 1] ⟶ X _[n + 1])
  | 0 => fun n j hj₁ => by
    exfalso
    have hj₂ := Fin.is_lt j
    linarith
  | q + 1 => fun n => by
    unfold P
    exact (of_P q n).induction
#align algebraic_topology.dold_kan.higher_faces_vanish.of_P AlgebraicTopology.DoldKan.HigherFacesVanish.of_p

@[reassoc.1]
theorem comp_p_eq_self {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} (v : HigherFacesVanish q φ) :
    φ ≫ (p q).f (n + 1) = φ := by
  induction' q with q hq
  · unfold P
    apply comp_id
  · unfold P
    simp only [comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply, comp_id, ←
      assoc, hq v.of_succ, add_right_eq_self]
    by_cases hqn : n < q
    · exact v.of_succ.comp_Hσ_eq_zero hqn
    · cases' Nat.le.dest (not_lt.mp hqn) with a ha
      have hnaq : n = a + q := by linarith
      simp only [v.of_succ.comp_Hσ_eq hnaq, neg_eq_zero, ← assoc]
      have eq :=
        v ⟨a, by linarith⟩ (by simp only [hnaq, Fin.val_mk, Nat.succ_eq_add_one, add_assoc])
      simp only [Fin.succ_mk] at eq
      simp only [Eq, zero_comp]
#align algebraic_topology.dold_kan.higher_faces_vanish.comp_P_eq_self AlgebraicTopology.DoldKan.HigherFacesVanish.comp_p_eq_self

end HigherFacesVanish

theorem comp_p_eq_self_iff {Y : C} {n q : ℕ} {φ : Y ⟶ X _[n + 1]} :
    φ ≫ (p q).f (n + 1) = φ ↔ HigherFacesVanish q φ :=
  by
  constructor
  · intro hφ
    rw [← hφ]
    apply higher_faces_vanish.of_comp
    apply higher_faces_vanish.of_P
  · exact higher_faces_vanish.comp_P_eq_self
#align algebraic_topology.dold_kan.comp_P_eq_self_iff AlgebraicTopology.DoldKan.comp_p_eq_self_iff

@[simp, reassoc.1]
theorem p_f_idem (q n : ℕ) : ((p q).f n : X _[n] ⟶ _) ≫ (p q).f n = (p q).f n :=
  by
  cases n
  · rw [P_f_0_eq q, comp_id]
  · exact (higher_faces_vanish.of_P q n).comp_p_eq_self
#align algebraic_topology.dold_kan.P_f_idem AlgebraicTopology.DoldKan.p_f_idem

@[simp, reassoc.1]
theorem q_f_idem (q n : ℕ) : ((q q).f n : X _[n] ⟶ _) ≫ (q q).f n = (q q).f n :=
  idem_of_id_sub_idem _ (p_f_idem q n)
#align algebraic_topology.dold_kan.Q_f_idem AlgebraicTopology.DoldKan.q_f_idem

@[simp, reassoc.1]
theorem p_idem (q : ℕ) : (p q : K[X] ⟶ K[X]) ≫ p q = p q :=
  by
  ext n
  exact P_f_idem q n
#align algebraic_topology.dold_kan.P_idem AlgebraicTopology.DoldKan.p_idem

@[simp, reassoc.1]
theorem q_idem (q : ℕ) : (q q : K[X] ⟶ K[X]) ≫ q q = q q :=
  by
  ext n
  exact Q_f_idem q n
#align algebraic_topology.dold_kan.Q_idem AlgebraicTopology.DoldKan.q_idem

/-- For each `q`, `P q` is a natural transformation. -/
@[simps]
def natTransP (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C
    where
  app X := p q
  naturality' X Y f := by
    induction' q with q hq
    · unfold P
      dsimp only [alternating_face_map_complex]
      rw [id_comp, comp_id]
    · unfold P
      simp only [add_comp, comp_add, assoc, comp_id, hq]
      congr 1
      rw [← assoc, hq, assoc]
      congr 1
      exact (nat_trans_Hσ q).naturality' f
#align algebraic_topology.dold_kan.nat_trans_P AlgebraicTopology.DoldKan.natTransP

@[simp, reassoc.1]
theorem p_f_naturality (q n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op [n]) ≫ (p q).f n = (p q).f n ≫ f.app (op [n]) :=
  HomologicalComplex.congr_hom ((natTransP q).naturality f) n
#align algebraic_topology.dold_kan.P_f_naturality AlgebraicTopology.DoldKan.p_f_naturality

@[simp, reassoc.1]
theorem q_f_naturality (q n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op [n]) ≫ (q q).f n = (q q).f n ≫ f.app (op [n]) :=
  by
  simp only [Q, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, P_f_naturality,
    sub_comp, sub_left_inj]
  dsimp
  simp only [comp_id, id_comp]
#align algebraic_topology.dold_kan.Q_f_naturality AlgebraicTopology.DoldKan.q_f_naturality

/-- For each `q`, `Q q` is a natural transformation. -/
@[simps]
def natTransQ (q : ℕ) : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where app X := q q
#align algebraic_topology.dold_kan.nat_trans_Q AlgebraicTopology.DoldKan.natTransQ

theorem map_p {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    G.map ((p q : K[X] ⟶ _).f n) = (p q : K[((whiskering C D).obj G).obj X] ⟶ _).f n :=
  by
  induction' q with q hq
  · unfold P
    apply G.map_id
  · unfold P
    simp only [comp_add, HomologicalComplex.comp_f, HomologicalComplex.add_f_apply, comp_id,
      functor.map_add, functor.map_comp, hq, map_Hσ]
#align algebraic_topology.dold_kan.map_P AlgebraicTopology.DoldKan.map_p

theorem map_q {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (q n : ℕ) :
    G.map ((q q : K[X] ⟶ _).f n) = (q q : K[((whiskering C D).obj G).obj X] ⟶ _).f n :=
  by
  rw [← add_right_inj (G.map ((P q : K[X] ⟶ _).f n)), ← G.map_add, map_P G X q n, P_add_Q_f,
    P_add_Q_f]
  apply G.map_id
#align algebraic_topology.dold_kan.map_Q AlgebraicTopology.DoldKan.map_q

end DoldKan

end AlgebraicTopology

