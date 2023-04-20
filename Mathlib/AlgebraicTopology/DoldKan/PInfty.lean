/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.p_infty
! leanprover-community/mathlib commit 31019c2504b17f85af7e0577585fad996935a317
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.AlgebraicTopology.DoldKan.Projections
import Mathlib.CategoryTheory.Idempotents.FunctorCategories
import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-!

# Construction of the projection `PInfty` for the Dold-Kan correspondence

In this file, we construct the projection `PInfty : K[X] ⟶ K[X]` by passing
to the limit the projections `P q` defined in `Projections.lean`. This
projection is a critical tool in this formalisation of the Dold-Kan correspondence,
because in the case of abelian categories, `PInfty` corresponds to the
projection on the normalized Moore subcomplex, with kernel the degenerate subcomplex.
(See `Equivalence.lean` for the general strategy of proof.)

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject CategoryTheory.Idempotents Opposite Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] {X : SimplicialObject C}

theorem P_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
    ((P (q + 1)).f n : X _[n] ⟶ _) = (P q).f n := by
  rcases n with (_|n)
  · simp only [Nat.zero_eq, P_f_0_eq]
  · simp only [P_succ, add_right_eq_self, comp_add, HomologicalComplex.comp_f,
      HomologicalComplex.add_f_apply, comp_id]
    exact (HigherFacesVanish.of_P q n).comp_Hσ_eq_zero (Nat.succ_le_iff.mp hqn)
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.P_is_eventually_constant AlgebraicTopology.DoldKan.P_is_eventually_constant

theorem Q_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
    ((Q (q + 1)).f n : X _[n] ⟶ _) = (Q q).f n := by
  simp only [Q, HomologicalComplex.sub_f_apply, P_is_eventually_constant hqn]
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.Q_is_eventually_constant AlgebraicTopology.DoldKan.Q_is_eventually_constant

/-- The endomorphism `PInfty : K[X] ⟶ K[X]` obtained from the `P q` by passing to the limit. -/
noncomputable def PInfty : K[X] ⟶ K[X] :=
  ChainComplex.ofHom _ _ _ _ _ _ (fun n => ((P n).f n : X _[n] ⟶ _)) fun n => by
    simpa only [← P_is_eventually_constant (show n ≤ n by rfl),
      AlternatingFaceMapComplex.obj_d_eq] using (P (n + 1) : K[X] ⟶ _).comm (n + 1) n
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.P_infty AlgebraicTopology.DoldKan.PInfty

/-- The endomorphism `QInfty : K[X] ⟶ K[X]` obtained from the `Q q` by passing to the limit. -/
noncomputable def QInfty : K[X] ⟶ K[X] :=
  𝟙 _ - PInfty
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.Q_infty AlgebraicTopology.DoldKan.QInfty

@[simp]
theorem PInfty_f_0 : (PInfty.f 0 : X _[0] ⟶ X _[0]) = 𝟙 _ :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.P_infty_f_0 AlgebraicTopology.DoldKan.PInfty_f_0

theorem PInfty_f (n : ℕ) : (PInfty.f n : X _[n] ⟶ X _[n]) = (P n).f n :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.P_infty_f AlgebraicTopology.DoldKan.PInfty_f

@[simp]
theorem QInfty_f_0 : (QInfty.f 0 : X _[0] ⟶ X _[0]) = 0 := by
  dsimp [QInfty]
  simp only [sub_self]
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.Q_infty_f_0 AlgebraicTopology.DoldKan.QInfty_f_0

theorem qInfty_f (n : ℕ) : (QInfty.f n : X _[n] ⟶ X _[n]) = (Q n).f n :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebraic_topology.dold_kan.Q_infty_f AlgebraicTopology.DoldKan.qInfty_f

@[simp, reassoc.1]
theorem pInfty_f_naturality (n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op [n]) ≫ pInfty.f n = pInfty.f n ≫ f.app (op [n]) :=
  p_f_naturality n n f
#align algebraic_topology.dold_kan.P_infty_f_naturality AlgebraicTopology.DoldKan.pInfty_f_naturality

@[simp, reassoc.1]
theorem qInfty_f_naturality (n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op [n]) ≫ qInfty.f n = qInfty.f n ≫ f.app (op [n]) :=
  q_f_naturality n n f
#align algebraic_topology.dold_kan.Q_infty_f_naturality AlgebraicTopology.DoldKan.qInfty_f_naturality

@[simp, reassoc.1]
theorem pInfty_f_idem (n : ℕ) : (pInfty.f n : X _[n] ⟶ _) ≫ pInfty.f n = pInfty.f n := by
  simp only [P_infty_f, P_f_idem]
#align algebraic_topology.dold_kan.P_infty_f_idem AlgebraicTopology.DoldKan.pInfty_f_idem

@[simp, reassoc.1]
theorem pInfty_idem : (pInfty : K[X] ⟶ _) ≫ pInfty = pInfty := by
  ext n
  exact P_infty_f_idem n
#align algebraic_topology.dold_kan.P_infty_idem AlgebraicTopology.DoldKan.pInfty_idem

@[simp, reassoc.1]
theorem qInfty_f_idem (n : ℕ) : (qInfty.f n : X _[n] ⟶ _) ≫ qInfty.f n = qInfty.f n :=
  q_f_idem _ _
#align algebraic_topology.dold_kan.Q_infty_f_idem AlgebraicTopology.DoldKan.qInfty_f_idem

@[simp, reassoc.1]
theorem qInfty_idem : (qInfty : K[X] ⟶ _) ≫ qInfty = qInfty := by
  ext n
  exact Q_infty_f_idem n
#align algebraic_topology.dold_kan.Q_infty_idem AlgebraicTopology.DoldKan.qInfty_idem

@[simp, reassoc.1]
theorem pInfty_f_comp_qInfty_f (n : ℕ) : (pInfty.f n : X _[n] ⟶ _) ≫ qInfty.f n = 0 := by
  dsimp only [Q_infty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, comp_id,
    P_infty_f_idem, sub_self]
#align algebraic_topology.dold_kan.P_infty_f_comp_Q_infty_f AlgebraicTopology.DoldKan.pInfty_f_comp_qInfty_f

@[simp, reassoc.1]
theorem pInfty_comp_qInfty : (pInfty : K[X] ⟶ _) ≫ qInfty = 0 := by
  ext n
  apply P_infty_f_comp_Q_infty_f
#align algebraic_topology.dold_kan.P_infty_comp_Q_infty AlgebraicTopology.DoldKan.pInfty_comp_qInfty

@[simp, reassoc.1]
theorem qInfty_f_comp_pInfty_f (n : ℕ) : (qInfty.f n : X _[n] ⟶ _) ≫ pInfty.f n = 0 := by
  dsimp only [Q_infty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, sub_comp, id_comp,
    P_infty_f_idem, sub_self]
#align algebraic_topology.dold_kan.Q_infty_f_comp_P_infty_f AlgebraicTopology.DoldKan.qInfty_f_comp_pInfty_f

@[simp, reassoc.1]
theorem qInfty_comp_pInfty : (qInfty : K[X] ⟶ _) ≫ pInfty = 0 := by
  ext n
  apply Q_infty_f_comp_P_infty_f
#align algebraic_topology.dold_kan.Q_infty_comp_P_infty AlgebraicTopology.DoldKan.qInfty_comp_pInfty

@[simp]
theorem pInfty_add_qInfty : (pInfty : K[X] ⟶ _) + qInfty = 𝟙 _ := by
  dsimp only [Q_infty]
  simp only [add_sub_cancel'_right]
#align algebraic_topology.dold_kan.P_infty_add_Q_infty AlgebraicTopology.DoldKan.pInfty_add_qInfty

theorem pInfty_f_add_qInfty_f (n : ℕ) : (pInfty.f n : X _[n] ⟶ _) + qInfty.f n = 𝟙 _ :=
  HomologicalComplex.congr_hom pInfty_add_qInfty n
#align algebraic_topology.dold_kan.P_infty_f_add_Q_infty_f AlgebraicTopology.DoldKan.pInfty_f_add_qInfty_f

variable (C)

/-- `P_infty` induces a natural transformation, i.e. an endomorphism of
the functor `alternating_face_map_complex C`. -/
@[simps]
def natTransPInfty : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := pInfty
  naturality' X Y f := by
    ext n
    exact P_infty_f_naturality n f
#align algebraic_topology.dold_kan.nat_trans_P_infty AlgebraicTopology.DoldKan.natTransPInfty

/-- The natural transformation in each degree that is induced by `nat_trans_P_infty`. -/
@[simps]
def natTransPInftyF (n : ℕ) :=
  natTransPInfty C ◫ 𝟙 (HomologicalComplex.eval _ _ n)
#align algebraic_topology.dold_kan.nat_trans_P_infty_f AlgebraicTopology.DoldKan.natTransPInftyF

variable {C}

@[simp]
theorem map_pInfty_f {D : Type _} [Category D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (n : ℕ) :
    (pInfty : K[((whiskering C D).obj G).obj X] ⟶ _).f n =
      G.map ((pInfty : AlternatingFaceMapComplex.obj X ⟶ _).f n) :=
  by simp only [P_infty_f, map_P]
#align algebraic_topology.dold_kan.map_P_infty_f AlgebraicTopology.DoldKan.map_pInfty_f

/-- Given an object `Y : karoubi (simplicial_object C)`, this lemma
computes `P_infty` for the associated object in `simplicial_object (karoubi C)`
in terms of `P_infty` for `Y.X : simplicial_object C` and `Y.p`. -/
theorem karoubi_pInfty_f {Y : Karoubi (SimplicialObject C)} (n : ℕ) :
    ((pInfty : K[(karoubiFunctorCategoryEmbedding _ _).obj Y] ⟶ _).f n).f =
      Y.p.app (op [n]) ≫ (pInfty : K[Y.pt] ⟶ _).f n := by
  -- We introduce P_infty endomorphisms P₁, P₂, P₃, P₄ on various objects Y₁, Y₂, Y₃, Y₄.
  let Y₁ := (karoubi_functor_category_embedding _ _).obj Y
  let Y₂ := Y.X
  let Y₃ := ((whiskering _ _).obj (to_karoubi C)).obj Y.X
  let Y₄ := (karoubi_functor_category_embedding _ _).obj ((to_karoubi _).obj Y.X)
  let P₁ : K[Y₁] ⟶ _ := P_infty
  let P₂ : K[Y₂] ⟶ _ := P_infty
  let P₃ : K[Y₃] ⟶ _ := P_infty
  let P₄ : K[Y₄] ⟶ _ := P_infty
  -- The statement of lemma relates P₁ and P₂.
  change (P₁.f n).f = Y.p.app (op [n]) ≫ P₂.f n
  -- The proof proceeds by obtaining relations h₃₂, h₄₃, h₁₄.
  have h₃₂ : (P₃.f n).f = P₂.f n := karoubi.hom_ext.mp (map_P_infty_f (to_karoubi C) Y₂ n)
  have h₄₃ : P₄.f n = P₃.f n := by
    have h := functor.congr_obj (to_karoubi_comp_karoubi_functor_category_embedding _ _) Y₂
    simp only [← nat_trans_P_infty_f_app]
    congr
  let τ₁ := 𝟙 (karoubi_functor_category_embedding SimplexCategoryᵒᵖ C)
  let τ₂ := nat_trans_P_infty_f (karoubi C) n
  let τ := τ₁ ◫ τ₂
  have h₁₄ := idempotents.nat_trans_eq τ Y
  dsimp [τ, τ₁, τ₂, nat_trans_P_infty_f] at h₁₄
  rw [id_comp, id_comp, comp_id, comp_id] at h₁₄
  -- We use the three equalities h₃₂, h₄₃, h₁₄.
  rw [← h₃₂, ← h₄₃, h₁₄]
  simp only [karoubi_functor_category_embedding.map_app_f, karoubi.decomp_id_p_f,
    karoubi.decomp_id_i_f, karoubi.comp_f]
  let π : Y₄ ⟶ Y₄ := (to_karoubi _ ⋙ karoubi_functor_category_embedding _ _).map Y.p
  have eq := karoubi.hom_ext.mp (P_infty_f_naturality n π)
  simp only [karoubi.comp_f] at eq
  dsimp [π] at eq
  rw [← Eq, reassoc_of (app_idem Y (op [n]))]
#align algebraic_topology.dold_kan.karoubi_P_infty_f AlgebraicTopology.DoldKan.karoubi_pInfty_f

end DoldKan

end AlgebraicTopology
