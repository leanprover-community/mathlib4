/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Projections
public import Mathlib.CategoryTheory.Idempotents.FunctorCategories
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension

/-!

# Construction of the projection `PInfty` for the Dold-Kan correspondence

In this file, we construct the projection `PInfty : K[X] ⟶ K[X]` by passing
to the limit the projections `P q` defined in `Projections.lean`. This
projection is a critical tool in this formalisation of the Dold-Kan correspondence,
because in the case of abelian categories, `PInfty` corresponds to the
projection on the normalized Moore subcomplex, with kernel the degenerate subcomplex.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
  CategoryTheory.SimplicialObject CategoryTheory.Idempotents Opposite Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] {X : SimplicialObject C}

theorem P_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
    ((P (q + 1)).f n : X _⦋n⦌ ⟶ _) = (P q).f n := by
  cases n with
  | zero => simp only [P_f_0_eq]
  | succ n =>
    simp only [P_succ, comp_add, comp_id, HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
      add_eq_left]
    exact (HigherFacesVanish.of_P q n).comp_Hσ_eq_zero (Nat.succ_le_iff.mp hqn)

theorem Q_is_eventually_constant {q n : ℕ} (hqn : n ≤ q) :
    ((Q (q + 1)).f n : X _⦋n⦌ ⟶ _) = (Q q).f n := by
  simp only [Q, HomologicalComplex.sub_f_apply, P_is_eventually_constant hqn]

/-- The endomorphism `PInfty : K[X] ⟶ K[X]` obtained from the `P q` by passing to the limit. -/
noncomputable def PInfty : K[X] ⟶ K[X] :=
  ChainComplex.ofHom _ _ (AlternatingFaceMapComplex.d_squared X) _ _
    (AlternatingFaceMapComplex.d_squared X) (fun n => ((P n).f n : X _⦋n⦌ ⟶ _)) fun n => by
    simpa only [← P_is_eventually_constant (show n ≤ n by rfl),
      AlternatingFaceMapComplex.obj_d_eq] using (P (n + 1) : K[X] ⟶ _).comm (n + 1) n

/-- The endomorphism `QInfty : K[X] ⟶ K[X]` obtained from the `Q q` by passing to the limit. -/
noncomputable def QInfty : K[X] ⟶ K[X] :=
  𝟙 _ - PInfty

@[simp]
theorem PInfty_f_0 : (PInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 𝟙 _ := rfl

theorem PInfty_f (n : ℕ) : (PInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (P n).f n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem QInfty_f_0 : (QInfty.f 0 : X _⦋0⦌ ⟶ X _⦋0⦌) = 0 := by
  dsimp [QInfty]
  simp only [sub_self]

theorem QInfty_f (n : ℕ) : (QInfty.f n : X _⦋n⦌ ⟶ X _⦋n⦌) = (Q n).f n :=
  rfl

@[reassoc (attr := simp)]
theorem PInfty_f_naturality (n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ PInfty.f n = PInfty.f n ≫ f.app (op ⦋n⦌) :=
  P_f_naturality n n f

@[reassoc (attr := simp)]
theorem QInfty_f_naturality (n : ℕ) {X Y : SimplicialObject C} (f : X ⟶ Y) :
    f.app (op ⦋n⦌) ≫ QInfty.f n = QInfty.f n ≫ f.app (op ⦋n⦌) :=
  Q_f_naturality n n f

@[reassoc (attr := simp)]
theorem PInfty_f_idem (n : ℕ) : (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = PInfty.f n := by
  simp only [PInfty_f, P_f_idem]

@[reassoc (attr := simp)]
theorem PInfty_idem : (PInfty : K[X] ⟶ _) ≫ PInfty = PInfty := by
  ext n
  exact PInfty_f_idem n

@[reassoc (attr := simp)]
theorem QInfty_f_idem (n : ℕ) : (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = QInfty.f n :=
  Q_f_idem _ _

@[reassoc (attr := simp)]
theorem QInfty_idem : (QInfty : K[X] ⟶ _) ≫ QInfty = QInfty := by
  ext n
  exact QInfty_f_idem n

@[reassoc (attr := simp)]
theorem PInfty_f_comp_QInfty_f (n : ℕ) : (PInfty.f n : X _⦋n⦌ ⟶ _) ≫ QInfty.f n = 0 := by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, comp_sub, comp_id,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]
theorem PInfty_comp_QInfty : (PInfty : K[X] ⟶ _) ≫ QInfty = 0 := by
  ext n
  apply PInfty_f_comp_QInfty_f

@[reassoc (attr := simp)]
theorem QInfty_f_comp_PInfty_f (n : ℕ) : (QInfty.f n : X _⦋n⦌ ⟶ _) ≫ PInfty.f n = 0 := by
  dsimp only [QInfty]
  simp only [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, sub_comp, id_comp,
    PInfty_f_idem, sub_self]

@[reassoc (attr := simp)]
theorem QInfty_comp_PInfty : (QInfty : K[X] ⟶ _) ≫ PInfty = 0 := by
  ext n
  apply QInfty_f_comp_PInfty_f

@[simp]
theorem PInfty_add_QInfty : (PInfty : K[X] ⟶ _) + QInfty = 𝟙 _ := by
  dsimp only [QInfty]
  simp only [add_sub_cancel]

theorem PInfty_f_add_QInfty_f (n : ℕ) : (PInfty.f n : X _⦋n⦌ ⟶ _) + QInfty.f n = 𝟙 _ :=
  HomologicalComplex.congr_hom PInfty_add_QInfty n

variable (C)

/-- `PInfty` induces a natural transformation, i.e. an endomorphism of
the functor `alternatingFaceMapComplex C`. -/
@[simps]
noncomputable def natTransPInfty : alternatingFaceMapComplex C ⟶ alternatingFaceMapComplex C where
  app _ := PInfty
  naturality X Y f := by
    ext n
    exact PInfty_f_naturality n f

/-- The natural transformation in each degree that is induced by `natTransPInfty`. -/
@[simps!]
noncomputable def natTransPInfty_f (n : ℕ) :=
  natTransPInfty C ◫ 𝟙 (HomologicalComplex.eval _ _ n)

variable {C}

@[simp]
theorem map_PInfty_f {D : Type*} [Category* D] [Preadditive D] (G : C ⥤ D) [G.Additive]
    (X : SimplicialObject C) (n : ℕ) :
    (PInfty : K[((whiskering C D).obj G).obj X] ⟶ _).f n =
      G.map ((PInfty : AlternatingFaceMapComplex.obj X ⟶ _).f n) := by
  simp only [PInfty_f, map_P]

set_option backward.isDefEq.respectTransparency false in
/-- Given an object `Y : Karoubi (SimplicialObject C)`, this lemma
computes `PInfty` for the associated object in `SimplicialObject (Karoubi C)`
in terms of `PInfty` for `Y.X : SimplicialObject C` and `Y.p`. -/
theorem karoubi_PInfty_f {Y : Karoubi (SimplicialObject C)} (n : ℕ) :
    ((PInfty : K[(karoubiFunctorCategoryEmbedding _ _).obj Y] ⟶ _).f n).f =
      Y.p.app (op ⦋n⦌) ≫ (PInfty : K[Y.X] ⟶ _).f n := by
  -- We introduce P_infty endomorphisms P₁, P₂, P₃, P₄ on various objects Y₁, Y₂, Y₃, Y₄.
  let Y₁ := (karoubiFunctorCategoryEmbedding _ _).obj Y
  let Y₂ := Y.X
  let Y₃ := ((whiskering _ _).obj (toKaroubi C)).obj Y.X
  let Y₄ := (karoubiFunctorCategoryEmbedding _ _).obj ((toKaroubi _).obj Y.X)
  let P₁ : K[Y₁] ⟶ _ := PInfty
  let P₂ : K[Y₂] ⟶ _ := PInfty
  let P₃ : K[Y₃] ⟶ _ := PInfty
  let P₄ : K[Y₄] ⟶ _ := PInfty
  -- The statement of lemma relates P₁ and P₂.
  change (P₁.f n).f = Y.p.app (op ⦋n⦌) ≫ P₂.f n
  -- The proof proceeds by obtaining relations h₃₂, h₄₃, h₁₄.
  have h₃₂ : (P₃.f n).f = P₂.f n := Karoubi.hom_ext_iff.mp (map_PInfty_f (toKaroubi C) Y₂ n)
  have h₄₃ : P₄.f n = P₃.f n := by
    have h := Functor.congr_obj (toKaroubi_comp_karoubiFunctorCategoryEmbedding _ _) Y₂
    simp only [P₃, P₄, ← natTransPInfty_f_app]
    congr 1
  have h₁₄ := Idempotents.natTrans_eq
    ((𝟙 (karoubiFunctorCategoryEmbedding SimplexCategoryᵒᵖ C)) ◫
      (natTransPInfty_f (Karoubi C) n)) Y
  dsimp [natTransPInfty_f] at h₁₄
  rw [id_comp, id_comp, comp_id, comp_id] at h₁₄
  -- We use the three equalities h₃₂, h₄₃, h₁₄.
  rw [← h₃₂, ← h₄₃, h₁₄]
  simp only [KaroubiFunctorCategoryEmbedding.map_app_f, Karoubi.decompId_p_f,
    Karoubi.decompId_i_f, Karoubi.comp_f]
  let π : Y₄ ⟶ Y₄ := (toKaroubi _ ⋙ karoubiFunctorCategoryEmbedding _ _).map Y.p
  have eq := Karoubi.hom_ext_iff.mp (PInfty_f_naturality n π)
  simp only [Karoubi.comp_f] at eq
  dsimp [π] at eq
  rw [← eq, app_idem_assoc Y (op ⦋n⦌)]

end DoldKan

end AlgebraicTopology
