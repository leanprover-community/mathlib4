/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Data.Matrix.DMatrix
import Mathlib.Data.Matrix.Basic
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Preadditive.SingleObj
import Mathlib.Algebra.Opposites

#align_import category_theory.preadditive.Mat from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# Matrices over a category.

When `C` is a preadditive category, `Mat_ C` is the preadditive category
whose objects are finite tuples of objects in `C`, and
whose morphisms are matrices of morphisms from `C`.

There is a functor `Mat_.embedding : C ⥤ Mat_ C` sending morphisms to one-by-one matrices.

`Mat_ C` has finite biproducts.

## The additive envelope

We show that this construction is the "additive envelope" of `C`,
in the sense that any additive functor `F : C ⥤ D` to a category `D` with biproducts
lifts to a functor `Mat_.lift F : Mat_ C ⥤ D`,
Moreover, this functor is unique (up to natural isomorphisms) amongst functors `L : Mat_ C ⥤ D`
such that `embedding C ⋙ L ≅ F`.
(As we don't have 2-category theory, we can't explicitly state that `Mat_ C` is
the initial object in the 2-category of categories under `C` which have biproducts.)

As a consequence, when `C` already has finite biproducts we have `Mat_ C ≌ C`.

## Future work

We should provide a more convenient `Mat R`, when `R` is a ring,
as a category with objects `n : FinType`,
and whose morphisms are matrices with components in `R`.

Ideally this would conveniently interact with both `Mat_` and `Matrix`.

-/


open CategoryTheory CategoryTheory.Preadditive

open scoped BigOperators Classical

noncomputable section

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]

/-- An object in `Mat_ C` is a finite tuple of objects in `C`.
-/
structure Mat_ where
  ι : Type
  [F : Fintype ι]
  X : ι → C
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_ CategoryTheory.Mat_

attribute [instance] Mat_.F

namespace Mat_

variable {C}

-- porting note: removed @[nolint has_nonempty_instance]
/-- A morphism in `Mat_ C` is a dependently typed matrix of morphisms. -/
def Hom (M N : Mat_ C) : Type v₁ :=
  DMatrix M.ι N.ι fun i j => M.X i ⟶ N.X j
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.hom CategoryTheory.Mat_.Hom

namespace Hom

/-- The identity matrix consists of identity morphisms on the diagonal, and zeros elsewhere. -/
def id (M : Mat_ C) : Hom M M := fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.hom.id CategoryTheory.Mat_.Hom.id

/-- Composition of matrices using matrix multiplication. -/
def comp {M N K : Mat_ C} (f : Hom M N) (g : Hom N K) : Hom M K := fun i k =>
  ∑ j : N.ι, f i j ≫ g j k
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.hom.comp CategoryTheory.Mat_.Hom.comp

end Hom

section

attribute [local simp] Hom.id Hom.comp

instance : Category.{v₁} (Mat_ C) where
  Hom := Hom
  id := Hom.id
  comp f g := f.comp g
  id_comp f := by simp [dite_comp]
                  -- 🎉 no goals
  comp_id f := by simp [comp_dite]
                  -- 🎉 no goals
  assoc f g h := by
    apply DMatrix.ext
    -- ⊢ ∀ (i : W✝.ι) (j : Z✝.ι), ((f ≫ g) ≫ h) i j = (f ≫ g ≫ h) i j
    intros
    -- ⊢ ((f ≫ g) ≫ h) i✝ j✝ = (f ≫ g ≫ h) i✝ j✝
    simp_rw [Hom.comp, sum_comp, comp_sum, Category.assoc]
    -- ⊢ ∑ x : Y✝.ι, ∑ x_1 : X✝.ι, f i✝ x_1 ≫ g x_1 x ≫ h x j✝ = ∑ x : X✝.ι, ∑ j : Y✝ …
    rw [Finset.sum_comm]
    -- 🎉 no goals

-- porting note: added because `DMatrix.ext` is not triggered automatically
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
theorem hom_ext {M N : Mat_ C} (f g : M ⟶ N) (H : ∀ i j, f i j = g i j) : f = g :=
  DMatrix.ext_iff.mp H

theorem id_def (M : Mat_ C) :
    (𝟙 M : Hom M M) = fun i j => if h : i = j then eqToHom (congr_arg M.X h) else 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.id_def CategoryTheory.Mat_.id_def

theorem id_apply (M : Mat_ C) (i j : M.ι) :
    (𝟙 M : Hom M M) i j = if h : i = j then eqToHom (congr_arg M.X h) else 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.id_apply CategoryTheory.Mat_.id_apply

@[simp]
theorem id_apply_self (M : Mat_ C) (i : M.ι) : (𝟙 M : Hom M M) i i = 𝟙 _ := by simp [id_apply]
                                                                               -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.id_apply_self CategoryTheory.Mat_.id_apply_self

@[simp]
theorem id_apply_of_ne (M : Mat_ C) (i j : M.ι) (h : i ≠ j) : (𝟙 M : Hom M M) i j = 0 := by
  simp [id_apply, h]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.id_apply_of_ne CategoryTheory.Mat_.id_apply_of_ne

theorem comp_def {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N.ι, f i j ≫ g j k :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.comp_def CategoryTheory.Mat_.comp_def

@[simp]
theorem comp_apply {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.comp_apply CategoryTheory.Mat_.comp_apply

instance (M N : Mat_ C) : Inhabited (M ⟶ N) :=
  ⟨fun i j => (0 : M.X i ⟶ N.X j)⟩

end

-- porting note: to ease the construction of the preadditive structure, the `AddCommGroup`
-- was introduced separately and the lemma `add_apply` was moved upwards
instance (M N : Mat_ C) : AddCommGroup (M ⟶ N) := by
  change AddCommGroup (DMatrix M.ι N.ι _)
  -- ⊢ AddCommGroup (DMatrix M.ι N.ι fun i j => (fun i j => X M i ⟶ X N j) i j)
  infer_instance
  -- 🎉 no goals

@[simp]
theorem add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.add_apply CategoryTheory.Mat_.add_apply

instance : Preadditive (Mat_ C) where
  add_comp M N K f f' g := by ext; simp [Finset.sum_add_distrib]
                              -- ⊢ ((f + f') ≫ g) i✝ j✝ = (f ≫ g + f' ≫ g) i✝ j✝
                                   -- 🎉 no goals
  comp_add M N K f g g' := by ext; simp [Finset.sum_add_distrib]
                              -- ⊢ (f ≫ (g + g')) i✝ j✝ = (f ≫ g + f ≫ g') i✝ j✝
                                   -- 🎉 no goals

open CategoryTheory.Limits

/-- We now prove that `Mat_ C` has finite biproducts.

Be warned, however, that `Mat_ C` is not necessarily Krull-Schmidt,
and so the internal indexing of a biproduct may have nothing to do with the external indexing,
even though the construction we give uses a sigma type.
See however `isoBiproductEmbedding`.
-/
instance hasFiniteBiproducts : HasFiniteBiproducts (Mat_ C)
    where out n :=
    { has_biproduct := fun f =>
        hasBiproduct_of_total
          { pt := ⟨Σ j, (f j).ι, fun p => (f p.1).X p.2⟩
            π := fun j x y => by
              refine' if h : x.1 = j then _ else 0
              -- ⊢ (fun i j_1 => X (mk ((j : Fin n) × (f j).ι) fun p => X (f p.fst) p.snd) i ⟶  …
              refine' if h' : @Eq.ndrec (Fin n) x.1 (fun j => (f j).ι) x.2 _ h = y then _ else 0
              -- ⊢ (fun i j_1 => X (mk ((j : Fin n) × (f j).ι) fun p => X (f p.fst) p.snd) i ⟶  …
              apply eqToHom
              -- ⊢ X (mk ((j : Fin n) × (f j).ι) fun p => X (f p.fst) p.snd) x = X (f j) y
              substs h h'
              -- ⊢ X (mk ((j : Fin n) × (f j).ι) fun p => X (f p.fst) p.snd) x = X (f x.fst) (( …
              rfl
              -- 🎉 no goals
            -- Notice we were careful not to use `subst` until we had a goal in `Prop`.
            ι := fun j x y => by
              refine' if h : y.1 = j then _ else 0
              -- ⊢ (fun i j_1 => X (f j) i ⟶ X (mk ((j : Fin n) × (f j).ι) fun p => X (f p.fst) …
              refine' if h' : @Eq.ndrec _ y.1 (fun j => (f j).ι) y.2 _ h = x then _ else 0
              -- ⊢ (fun i j_1 => X (f j) i ⟶ X (mk ((j : Fin n) × (f j).ι) fun p => X (f p.fst) …
              apply eqToHom
              -- ⊢ X (f j) x = X (mk ((j : Fin n) × (f j).ι) fun p => X (f p.fst) p.snd) y
              substs h h'
              -- ⊢ X (f y.fst) ((_ : y.fst = y.fst) ▸ y.snd) = X (mk ((j : Fin n) × (f j).ι) fu …
              rfl
              -- 🎉 no goals
            ι_π := fun j j' => by
              ext x y
              -- ⊢ ((fun j x y => if h : y.fst = j then if h' : h ▸ y.snd = x then eqToHom (_ : …
              dsimp
              -- ⊢ (∑ j_1 : (j : Fin n) × (f j).ι, (if h : j_1.fst = j then if h' : h ▸ j_1.snd …
              simp_rw [dite_comp, comp_dite]
              -- ⊢ (∑ x_1 : (j : Fin n) × (f j).ι, if h : x_1.fst = j then if h_1 : (_ : x_1.fs …
              simp only [ite_self, dite_eq_ite, dif_ctx_congr, Limits.comp_zero, Limits.zero_comp,
                eqToHom_trans, Finset.sum_congr]
              erw [Finset.sum_sigma]
              -- ⊢ (∑ a : Fin n, ∑ s in (fun x => Finset.univ) a, if h : { fst := a, snd := s } …
              dsimp
              -- ⊢ (∑ a : Fin n, ∑ s : (f a).ι, if h : a = j then if h_1 : (_ : a = j) ▸ s = x  …
              simp only [if_congr, if_true, dif_ctx_congr, Finset.sum_dite_irrel, Finset.mem_univ,
                Finset.sum_const_zero, Finset.sum_congr, Finset.sum_dite_eq']
              split_ifs with h h'
              · substs h h'
                -- ⊢ eqToHom (_ : X (f j) x = X (f j) ((_ : j = j) ▸ x)) = eqToHom (_ : f j = f j …
                simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Mat_.id_apply_self]
                -- 🎉 no goals
              · subst h
                -- ⊢ 0 = eqToHom (_ : f j = f j) x y
                rw [eqToHom_refl, id_apply_of_ne _ _ _ h']
                -- 🎉 no goals
              · rfl }
                -- 🎉 no goals
          (by
            dsimp
            -- ⊢ (∑ j : Fin n, (fun x y => if h : x.fst = j then if h' : h ▸ x.snd = y then e …
            ext1 ⟨i, j⟩
            -- ⊢ ∀ (j_1 : (mk ((j : Fin n) × (f j).ι) fun p => X (f p.fst) p.snd).ι), Finset. …
            rintro ⟨i', j'⟩
            -- ⊢ Finset.sum Finset.univ (fun j => (fun x y => if h : x.fst = j then if h' : h …
            rw [Finset.sum_apply, Finset.sum_apply]
            -- ⊢ ∑ c : Fin n, ((fun x y => if h : x.fst = c then if h' : h ▸ x.snd = y then e …
            dsimp
            -- ⊢ (∑ c : Fin n, ∑ j_1 : (f c).ι, (if h : i = c then if h' : h ▸ j = j_1 then e …
            rw [Finset.sum_eq_single i]; rotate_left
            · intro b _ hb
              -- ⊢ (∑ j_1 : (f b).ι, (if h : i = b then if h' : h ▸ j = j_1 then eqToHom (_ : X …
              apply Finset.sum_eq_zero
              -- ⊢ ∀ (x : (f b).ι), x ∈ Finset.univ → ((if h : i = b then if h' : h ▸ j = x the …
              intro x _
              -- ⊢ ((if h : i = b then if h' : h ▸ j = x then eqToHom (_ : X (f i) j = X (f b)  …
              rw [dif_neg hb.symm, zero_comp]
              -- 🎉 no goals
            · intro hi
              -- ⊢ (∑ j_1 : (f i).ι, (if h : i = i then if h' : h ▸ j = j_1 then eqToHom (_ : X …
              simp at hi
              -- 🎉 no goals
            rw [Finset.sum_eq_single j]; rotate_left
            · intro b _ hb
              -- ⊢ ((if h : i = i then if h' : h ▸ j = b then eqToHom (_ : X (f i) j = X (f i)  …
              rw [dif_pos rfl, dif_neg, zero_comp]
              -- ⊢ ¬(_ : i = i) ▸ j = b
              simp only
              -- ⊢ ¬j = b
              tauto
              -- 🎉 no goals
            · intro hj
              -- ⊢ ((if h : i = i then if h' : h ▸ j = j then eqToHom (_ : X (f i) j = X (f i)  …
              simp at hj
              -- 🎉 no goals
            simp only [eqToHom_refl, dite_eq_ite, ite_true, Category.id_comp, ne_eq,
              Sigma.mk.inj_iff, not_and, id_def]
            by_cases i' = i
            -- ⊢ (if h : i' = i then if h' : h ▸ j' = j then eqToHom (_ : X (f i) j = X (f i' …
            -- ⊢ (if h : i' = i then if h' : h ▸ j' = j then eqToHom (_ : X (f i) j = X (f i' …
            · subst h
              -- ⊢ (if h : i' = i' then if h' : h ▸ j' = j then eqToHom (_ : X (f i') j = X (f  …
              rw [dif_pos rfl]
              -- ⊢ (if h' : (_ : i' = i') ▸ j' = j then eqToHom (_ : X (f i') j = X (f i') j')  …
              simp only [heq_eq_eq, true_and]
              -- ⊢ (if h' : j' = j then eqToHom (_ : X (f i') j = X (f i') j') else 0) = if h : …
              by_cases j' = j
              -- ⊢ (if h' : j' = j then eqToHom (_ : X (f i') j = X (f i') j') else 0) = if h : …
              -- ⊢ (if h' : j' = j then eqToHom (_ : X (f i') j = X (f i') j') else 0) = if h : …
              · subst h
                -- ⊢ (if h' : j' = j' then eqToHom (_ : X (f i') j' = X (f i') j') else 0) = if h …
                simp
                -- 🎉 no goals
              · rw [dif_neg h, dif_neg (Ne.symm h)]
                -- 🎉 no goals
            · rw [dif_neg h, dif_neg]
              -- ⊢ ¬(i = i' ∧ HEq j j')
              tauto ) }
              -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.has_finite_biproducts CategoryTheory.Mat_.hasFiniteBiproducts

end Mat_

namespace Functor

variable {C} {D : Type*} [Category.{v₁} D] [Preadditive D]

attribute [local simp] Mat_.id_apply eqToHom_map

/-- A functor induces a functor of matrix categories.
-/
@[simps]
def mapMat_ (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ Mat_ D where
  obj M := ⟨M.ι, fun i => F.obj (M.X i)⟩
  map f i j := F.map (f i j)
set_option linter.uppercaseLean3 false in
#align category_theory.functor.map_Mat_ CategoryTheory.Functor.mapMat_

/-- The identity functor induces the identity functor on matrix categories.
-/
@[simps!]
def mapMatId : (𝟭 C).mapMat_ ≅ 𝟭 (Mat_ C) :=
  NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
                                            -- ⊢ (mapMat_ (𝟭 C)).obj (Mat_.mk ι✝ X✝) = (𝟭 (Mat_ C)).obj (Mat_.mk ι✝ X✝)
                                                     -- 🎉 no goals
    ext
    -- ⊢ ((mapMat_ (𝟭 C)).map f ≫ ((fun M => eqToIso (_ : (mapMat_ (𝟭 C)).obj M = (𝟭  …
    cases M; cases N
    -- ⊢ ((mapMat_ (𝟭 C)).map f ≫ ((fun M => eqToIso (_ : (mapMat_ (𝟭 C)).obj M = (𝟭  …
             -- ⊢ ((mapMat_ (𝟭 C)).map f ≫ ((fun M => eqToIso (_ : (mapMat_ (𝟭 C)).obj M = (𝟭  …
    simp [comp_dite, dite_comp]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.functor.map_Mat_id CategoryTheory.Functor.mapMatId

/-- Composite functors induce composite functors on matrix categories.
-/
@[simps!]
def mapMatComp {E : Type*} [Category.{v₁} E] [Preadditive E] (F : C ⥤ D) [Functor.Additive F]
    (G : D ⥤ E) [Functor.Additive G] : (F ⋙ G).mapMat_ ≅ F.mapMat_ ⋙ G.mapMat_ :=
  NatIso.ofComponents (fun M => eqToIso (by cases M; rfl)) fun {M N} f => by
                                            -- ⊢ (mapMat_ (F ⋙ G)).obj (Mat_.mk ι✝ X✝) = (mapMat_ F ⋙ mapMat_ G).obj (Mat_.mk …
                                                     -- 🎉 no goals
    ext
    -- ⊢ ((mapMat_ (F ⋙ G)).map f ≫ ((fun M => eqToIso (_ : (mapMat_ (F ⋙ G)).obj M = …
    cases M; cases N
    -- ⊢ ((mapMat_ (F ⋙ G)).map f ≫ ((fun M => eqToIso (_ : (mapMat_ (F ⋙ G)).obj M = …
             -- ⊢ ((mapMat_ (F ⋙ G)).map f ≫ ((fun M => eqToIso (_ : (mapMat_ (F ⋙ G)).obj M = …
    simp [comp_dite, dite_comp]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.functor.map_Mat_comp CategoryTheory.Functor.mapMatComp

end Functor

namespace Mat_

/-- The embedding of `C` into `Mat_ C` as one-by-one matrices.
(We index the summands by `punit`.) -/
@[simps]
def embedding : C ⥤ Mat_ C where
  obj X := ⟨PUnit, fun _ => X⟩
  map f _ _ := f
  map_id _ := by ext ⟨⟩; simp
                 -- ⊢ { obj := fun X => mk PUnit fun x => X, map := fun {X Y} f x x => f }.map (𝟙  …
                         -- 🎉 no goals
  map_comp _ _ := by ext ⟨⟩; simp
                     -- ⊢ { obj := fun X => mk PUnit fun x => X, map := fun {X Y} f x x => f }.map (x✝ …
                             -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.embedding CategoryTheory.Mat_.embedding

namespace Embedding

instance : Faithful (embedding C)
    where map_injective h := congr_fun (congr_fun h PUnit.unit) PUnit.unit

instance : Full (embedding C) where preimage f := f PUnit.unit PUnit.unit

instance : Functor.Additive (embedding C) where

end Embedding

instance [Inhabited C] : Inhabited (Mat_ C) :=
  ⟨(embedding C).obj default⟩

open CategoryTheory.Limits

variable {C}

/-- Every object in `Mat_ C` is isomorphic to the biproduct of its summands.
-/
@[simps]
def isoBiproductEmbedding (M : Mat_ C) : M ≅ ⨁ fun i => (embedding C).obj (M.X i) where
  hom := biproduct.lift fun i j k => if h : j = i then eqToHom (congr_arg M.X h) else 0
  inv := biproduct.desc fun i j k => if h : i = k then eqToHom (congr_arg M.X h) else 0
  hom_inv_id := by
    simp only [biproduct.lift_desc]
    -- ⊢ (∑ j : M.ι, (fun j_1 k => if h : j_1 = j then eqToHom (_ : X M j_1 = X M j)  …
    funext i j
    -- ⊢ Finset.sum Finset.univ (fun j => (fun j_1 k => if h : j_1 = j then eqToHom ( …
    dsimp [id_def]
    -- ⊢ Finset.sum Finset.univ (fun j => (fun j_1 k => if h : j_1 = j then eqToHom ( …
    rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single i]; rotate_left
    · intro b _ hb
      -- ⊢ ((fun j k => if h : j = b then eqToHom (_ : X M j = X M b) else 0) ≫ fun j k …
      dsimp
      -- ⊢ (∑ j_1 in {PUnit.unit}, (if h : i = b then eqToHom (_ : X M i = X M b) else  …
      simp only [Finset.sum_const, Finset.card_singleton, one_smul]
      -- ⊢ ((if h : i = b then eqToHom (_ : X M i = X M b) else 0) ≫ if h : b = j then  …
      rw [dif_neg hb.symm, zero_comp]
      -- 🎉 no goals
    · intro h
      -- ⊢ ((fun j k => if h : j = i then eqToHom (_ : X M j = X M i) else 0) ≫ fun j k …
      simp at h
      -- 🎉 no goals
    simp
    -- 🎉 no goals
  inv_hom_id := by
    apply biproduct.hom_ext
    -- ⊢ ∀ (j : M.ι), ((biproduct.desc fun i j k => if h : i = k then eqToHom (_ : X  …
    intro i
    -- ⊢ ((biproduct.desc fun i j k => if h : i = k then eqToHom (_ : X M i = X M k)  …
    apply biproduct.hom_ext'
    -- ⊢ ∀ (j : M.ι), biproduct.ι (fun i => (embedding C).obj (X M i)) j ≫ ((biproduc …
    intro j
    -- ⊢ biproduct.ι (fun i => (embedding C).obj (X M i)) j ≫ ((biproduct.desc fun i  …
    simp only [Category.id_comp, Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      biproduct.ι_π]
    ext ⟨⟩ ⟨⟩
    -- ⊢ ((fun j_1 k => if h : j = k then eqToHom (_ : X M j = X M k) else 0) ≫ fun j …
    simp only [embedding, comp_apply, comp_dite, dite_comp, comp_zero, zero_comp,
      Finset.sum_dite_eq', Finset.mem_univ, ite_true, eqToHom_refl, Category.comp_id]
    split_ifs with h
    -- ⊢ eqToHom (_ : X M j = X M i) = eqToHom (_ : (embedding C).obj (X M j) = (embe …
    · subst h
      -- ⊢ eqToHom (_ : X M j = X M j) = eqToHom (_ : (embedding C).obj (X M j) = (embe …
      simp
      -- 🎉 no goals
    · rfl
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.iso_biproduct_embedding CategoryTheory.Mat_.isoBiproductEmbedding

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D]

-- porting note: added because it was not found automatically
instance (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) :
    HasBiproduct (fun i => F.obj ((embedding C).obj (M.X i))) :=
  F.hasBiproduct_of_preserves _

-- porting note: removed the @[simps] attribute as the automatically generated lemmas
-- are not very useful; two more useful lemmas have been added just after this
-- definition in order to ease the proof of `additiveObjIsoBiproduct_naturality`
/-- Every `M` is a direct sum of objects from `C`, and `F` preserves biproducts. -/
def additiveObjIsoBiproduct (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) :
    F.obj M ≅ ⨁ fun i => F.obj ((embedding C).obj (M.X i)) :=
  F.mapIso (isoBiproductEmbedding M) ≪≫ F.mapBiproduct _
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.additive_obj_iso_biproduct CategoryTheory.Mat_.additiveObjIsoBiproduct

@[reassoc (attr := simp)]
lemma additiveObjIsoBiproduct_hom_π (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι) :
    (additiveObjIsoBiproduct F M).hom ≫ biproduct.π _ i =
      F.map (M.isoBiproductEmbedding.hom ≫ biproduct.π _ i) := by
  dsimp [additiveObjIsoBiproduct]
  -- ⊢ (F.map (biproduct.lift fun i j k => if h : j = i then eqToHom (_ : X M j = X …
  rw [biproduct.lift_π, Category.assoc]
  -- ⊢ F.map (biproduct.lift fun i j k => if h : j = i then eqToHom (_ : X M j = X  …
  erw [biproduct.lift_π, ← F.map_comp]
  -- ⊢ F.map ((biproduct.lift fun i j k => if h : j = i then eqToHom (_ : X M j = X …
  simp
  -- 🎉 no goals

@[reassoc (attr := simp)]
lemma ι_additiveObjIsoBiproduct_inv (F : Mat_ C ⥤ D) [Functor.Additive F] (M : Mat_ C) (i : M.ι) :
    biproduct.ι _ i ≫ (additiveObjIsoBiproduct F M).inv =
      F.map (biproduct.ι _ i ≫ M.isoBiproductEmbedding.inv) := by
  dsimp [additiveObjIsoBiproduct, Functor.mapBiproduct, Functor.mapBicone]
  -- ⊢ biproduct.ι (fun i => F.obj ((embedding C).obj (X M i))) i ≫ (biproduct.desc …
  simp only [biproduct.ι_desc, biproduct.ι_desc_assoc, ← F.map_comp]
  -- 🎉 no goals

variable [HasFiniteBiproducts D]

@[reassoc]
theorem additiveObjIsoBiproduct_naturality (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C}
    (f : M ⟶ N) :
    F.map f ≫ (additiveObjIsoBiproduct F N).hom =
      (additiveObjIsoBiproduct F M).hom ≫
        biproduct.matrix fun i j => F.map ((embedding C).map (f i j)) := by
  ext i : 1
  -- ⊢ (F.map f ≫ (additiveObjIsoBiproduct F N).hom) ≫ biproduct.π (fun i => F.obj  …
  simp only [Category.assoc, additiveObjIsoBiproduct_hom_π, isoBiproductEmbedding_hom,
    embedding_obj_ι, embedding_obj_X, biproduct.lift_π, biproduct.matrix_π,
    ← cancel_epi (additiveObjIsoBiproduct F M).inv, Iso.inv_hom_id_assoc]
  ext j : 1
  -- ⊢ (biproduct.ι (fun i => F.obj ((embedding C).obj (X M i))) j ≫ (additiveObjIs …
  simp only [ι_additiveObjIsoBiproduct_inv_assoc, isoBiproductEmbedding_inv,
    biproduct.ι_desc, ← F.map_comp]
  congr 1
  -- ⊢ ((fun j_1 k => if h : j = k then eqToHom (_ : X M j = X M k) else 0) ≫ f ≫ f …
  funext ⟨⟩ ⟨⟩
  -- ⊢ ((fun j_1 k => if h : j = k then eqToHom (_ : X M j = X M k) else 0) ≫ f ≫ f …
  simp [comp_apply, dite_comp, comp_dite]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.additive_obj_iso_biproduct_naturality CategoryTheory.Mat_.additiveObjIsoBiproduct_naturality

@[reassoc]
theorem additiveObjIsoBiproduct_naturality' (F : Mat_ C ⥤ D) [Functor.Additive F] {M N : Mat_ C}
    (f : M ⟶ N) :
    (additiveObjIsoBiproduct F M).inv ≫ F.map f =
      biproduct.matrix (fun i j => F.map ((embedding C).map (f i j)) : _) ≫
        (additiveObjIsoBiproduct F N).inv :=
  by rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, additiveObjIsoBiproduct_naturality]
     -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.additive_obj_iso_biproduct_naturality' CategoryTheory.Mat_.additiveObjIsoBiproduct_naturality'

attribute [local simp] biproduct.lift_desc

/-- Any additive functor `C ⥤ D` to a category `D` with finite biproducts extends to
a functor `Mat_ C ⥤ D`. -/
@[simps]
def lift (F : C ⥤ D) [Functor.Additive F] : Mat_ C ⥤ D where
  obj X := ⨁ fun i => F.obj (X.X i)
  map f := biproduct.matrix fun i j => F.map (f i j)
  map_id X := by
    dsimp
    -- ⊢ (biproduct.matrix fun i j => F.map (𝟙 X i j)) = 𝟙 (⨁ fun i => F.obj (Categor …
    ext i j
    -- ⊢ biproduct.ι (fun i => F.obj (CategoryTheory.Mat_.X X i)) j ≫ (biproduct.matr …
    by_cases h : j = i
    -- ⊢ biproduct.ι (fun i => F.obj (CategoryTheory.Mat_.X X i)) j ≫ (biproduct.matr …
    · subst h; simp
      -- ⊢ biproduct.ι (fun i => F.obj (CategoryTheory.Mat_.X X i)) j ≫ (biproduct.matr …
               -- 🎉 no goals
    · simp [h]
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.lift CategoryTheory.Mat_.lift

instance lift_additive (F : C ⥤ D) [Functor.Additive F] : Functor.Additive (lift F) where
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.lift_additive CategoryTheory.Mat_.lift_additive

/-- An additive functor `C ⥤ D` factors through its lift to `Mat_ C ⥤ D`. -/
@[simps!]
def embeddingLiftIso (F : C ⥤ D) [Functor.Additive F] : embedding C ⋙ lift F ≅ F :=
  NatIso.ofComponents
    (fun X =>
      { hom := biproduct.desc fun _ => 𝟙 (F.obj X)
        inv := biproduct.lift fun _ => 𝟙 (F.obj X) })
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.embedding_lift_iso CategoryTheory.Mat_.embeddingLiftIso

/-- `Mat_.lift F` is the unique additive functor `L : Mat_ C ⥤ D` such that `F ≅ embedding C ⋙ L`.
-/
def liftUnique (F : C ⥤ D) [Functor.Additive F] (L : Mat_ C ⥤ D) [Functor.Additive L]
    (α : embedding C ⋙ L ≅ F) : L ≅ lift F :=
  NatIso.ofComponents
    (fun M =>
      additiveObjIsoBiproduct L M ≪≫
        (biproduct.mapIso fun i => α.app (M.X i)) ≪≫
          (biproduct.mapIso fun i => (embeddingLiftIso F).symm.app (M.X i)) ≪≫
            (additiveObjIsoBiproduct (lift F) M).symm)
    fun f => by
      dsimp only [Iso.trans_hom, Iso.symm_hom, biproduct.mapIso_hom]
      -- ⊢ L.map f ≫ (additiveObjIsoBiproduct L Y✝).hom ≫ (biproduct.map fun b => (α.ap …
      simp only [additiveObjIsoBiproduct_naturality_assoc]
      -- ⊢ (additiveObjIsoBiproduct L X✝).hom ≫ (biproduct.matrix fun i j => L.map ((em …
      simp only [biproduct.matrix_map_assoc, Category.assoc]
      -- ⊢ (additiveObjIsoBiproduct L X✝).hom ≫ (biproduct.matrix fun j k => L.map ((em …
      simp only [additiveObjIsoBiproduct_naturality']
      -- ⊢ (additiveObjIsoBiproduct L X✝).hom ≫ (biproduct.matrix fun j k => L.map ((em …
      simp only [biproduct.map_matrix_assoc, Category.assoc]
      -- ⊢ (additiveObjIsoBiproduct L X✝).hom ≫ (biproduct.matrix fun j k => L.map ((em …
      congr 3
      -- ⊢ (fun j k => L.map ((embedding C).map (f j k)) ≫ (α.app (X Y✝ k)).hom ≫ ((emb …
      ext j k
      -- ⊢ L.map ((embedding C).map (f j k)) ≫ (α.app (X Y✝ k)).hom ≫ ((embeddingLiftIs …
      apply biproduct.hom_ext
      -- ⊢ ∀ (j_1 : ((embedding C).obj (X Y✝ k)).ι), (L.map ((embedding C).map (f j k)) …
      rintro ⟨⟩
      -- ⊢ (L.map ((embedding C).map (f j k)) ≫ (α.app (X Y✝ k)).hom ≫ ((embeddingLiftI …
      dsimp
      -- ⊢ (L.map ((embedding C).map (f j k)) ≫ NatTrans.app α.hom (X Y✝ k) ≫ biproduct …
      simpa using α.hom.naturality (f j k)
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.lift_unique CategoryTheory.Mat_.liftUnique

-- porting note: removed @[ext] as the statement is not an equality
-- TODO is there some uniqueness statement for the natural isomorphism in `liftUnique`?
/-- Two additive functors `Mat_ C ⥤ D` are naturally isomorphic if
their precompositions with `embedding C` are naturally isomorphic as functors `C ⥤ D`. -/
def ext {F G : Mat_ C ⥤ D} [Functor.Additive F] [Functor.Additive G]
    (α : embedding C ⋙ F ≅ embedding C ⋙ G) : F ≅ G :=
  liftUnique (embedding C ⋙ G) _ α ≪≫ (liftUnique _ _ (Iso.refl _)).symm
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.ext CategoryTheory.Mat_.ext

/-- Natural isomorphism needed in the construction of `equivalenceSelfOfHasFiniteBiproducts`.
-/
def equivalenceSelfOfHasFiniteBiproductsAux [HasFiniteBiproducts C] :
    embedding C ⋙ 𝟭 (Mat_ C) ≅ embedding C ⋙ lift (𝟭 C) ⋙ embedding C :=
  Functor.rightUnitor _ ≪≫
    (Functor.leftUnitor _).symm ≪≫
      isoWhiskerRight (embeddingLiftIso _).symm _ ≪≫ Functor.associator _ _ _
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.equivalence_self_of_has_finite_biproducts_aux CategoryTheory.Mat_.equivalenceSelfOfHasFiniteBiproductsAux

/--
A preadditive category that already has finite biproducts is equivalent to its additive envelope.

Note that we only prove this for a large category;
otherwise there are universe issues that I haven't attempted to sort out.
-/
def equivalenceSelfOfHasFiniteBiproducts (C : Type (u₁ + 1)) [LargeCategory C] [Preadditive C]
    [HasFiniteBiproducts C] : Mat_ C ≌ C :=
  Equivalence.mk
    (-- I suspect this is already an adjoint equivalence, but it seems painful to verify.
      lift
      (𝟭 C))
    (embedding C) (ext equivalenceSelfOfHasFiniteBiproductsAux) (embeddingLiftIso (𝟭 C))
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.equivalence_self_of_has_finite_biproducts CategoryTheory.Mat_.equivalenceSelfOfHasFiniteBiproducts

@[simp]
theorem equivalenceSelfOfHasFiniteBiproducts_functor {C : Type (u₁ + 1)} [LargeCategory C]
    [Preadditive C] [HasFiniteBiproducts C] :
    (equivalenceSelfOfHasFiniteBiproducts C).functor = lift (𝟭 C) :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.equivalence_self_of_has_finite_biproducts_functor CategoryTheory.Mat_.equivalenceSelfOfHasFiniteBiproducts_functor

@[simp]
theorem equivalenceSelfOfHasFiniteBiproducts_inverse {C : Type (u₁ + 1)} [LargeCategory C]
    [Preadditive C] [HasFiniteBiproducts C] :
    (equivalenceSelfOfHasFiniteBiproducts C).inverse = embedding C :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat_.equivalence_self_of_has_finite_biproducts_inverse CategoryTheory.Mat_.equivalenceSelfOfHasFiniteBiproducts_inverse

end Mat_

universe u

/-- A type synonym for `Fintype`, which we will equip with a category structure
where the morphisms are matrices with components in `R`. -/
@[nolint unusedArguments]
def Mat (_ : Type u) :=
  FintypeCat.{u}
set_option linter.uppercaseLean3 false in
#align category_theory.Mat CategoryTheory.Mat

instance (R : Type u) : Inhabited (Mat R) := by
  dsimp [Mat]
  -- ⊢ Inhabited FintypeCat
  infer_instance
  -- 🎉 no goals

instance (R : Type u) : CoeSort (Mat R) (Type u) :=
  Bundled.coeSort

open Matrix

instance (R : Type u) [Semiring R] : Category (Mat R) where
  Hom X Y := Matrix X Y R
  id X := (1 : Matrix X X R)
  comp {X Y Z} f g := (show Matrix X Y R from f) * (show Matrix Y Z R from g)
  assoc := by intros; simp [Matrix.mul_assoc]
              -- ⊢ (f✝ ≫ g✝) ≫ h✝ = f✝ ≫ g✝ ≫ h✝
                      -- 🎉 no goals

namespace Mat

section

variable {R : Type u} [Semiring R]

-- porting note: added because `Matrix.ext` is not triggered automatically
-- See https://github.com/leanprover-community/mathlib4/issues/5229
@[ext]
theorem hom_ext {X Y : Mat R} (f g : X ⟶ Y) (h : ∀ i j, f i j = g i j) : f = g :=
  Matrix.ext_iff.mp h

variable (R)

theorem id_def (M : Mat R) : 𝟙 M = fun i j => if i = j then 1 else 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat.id_def CategoryTheory.Mat.id_def

theorem id_apply (M : Mat R) (i j : M) : (𝟙 M : Matrix M M R) i j = if i = j then 1 else 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat.id_apply CategoryTheory.Mat.id_apply

@[simp]
theorem id_apply_self (M : Mat R) (i : M) : (𝟙 M : Matrix M M R) i i = 1 := by simp [id_apply]
                                                                               -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat.id_apply_self CategoryTheory.Mat.id_apply_self

@[simp]
theorem id_apply_of_ne (M : Mat R) (i j : M) (h : i ≠ j) : (𝟙 M : Matrix M M R) i j = 0 := by
  simp [id_apply, h]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat.id_apply_of_ne CategoryTheory.Mat.id_apply_of_ne

theorem comp_def {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) :
    f ≫ g = fun i k => ∑ j : N, f i j * g j k :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat.comp_def CategoryTheory.Mat.comp_def

@[simp]
theorem comp_apply {M N K : Mat R} (f : M ⟶ N) (g : N ⟶ K) (i k) :
    (f ≫ g) i k = ∑ j : N, f i j * g j k :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Mat.comp_apply CategoryTheory.Mat.comp_apply

instance (M N : Mat R) : Inhabited (M ⟶ N) :=
  ⟨fun (_ : M) (_ : N) => (0 : R)⟩

end

variable (R : Type) [Ring R]

open Opposite

/-- Auxiliary definition for `CategoryTheory.Mat.equivalenceSingleObj`. -/
@[simps]
def equivalenceSingleObjInverse : Mat_ (SingleObj Rᵐᵒᵖ) ⥤ Mat R where
  obj X := FintypeCat.of X.ι
  map f i j := MulOpposite.unop (f i j)
  map_id X := by
    ext
    -- ⊢ { obj := fun X => FintypeCat.of X.ι, map := fun {X Y} f i j => MulOpposite.u …
    simp only [Mat_.id_def, id_def]
    -- ⊢ MulOpposite.unop (if h : i✝ = j✝ then eqToHom (_ : Mat_.X X i✝ = Mat_.X X j✝ …
    split_ifs <;> rfl
    -- ⊢ MulOpposite.unop (eqToHom (_ : Mat_.X X i✝ = Mat_.X X j✝)) = 1
                  -- 🎉 no goals
                  -- 🎉 no goals
  map_comp f g := by
    -- Porting note: this proof was automatic in mathlib3
    ext
    -- ⊢ { obj := fun X => FintypeCat.of X.ι, map := fun {X Y} f i j => MulOpposite.u …
    simp only [Mat_.comp_apply, comp_apply]
    -- ⊢ MulOpposite.unop (∑ j : Y✝.ι, f i✝ j ≫ g j j✝) = ∑ j : ↑(FintypeCat.of Y✝.ι) …
    apply Finset.unop_sum
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align category_theory.Mat.equivalence_single_obj_inverse CategoryTheory.Mat.equivalenceSingleObjInverse

instance : Faithful (equivalenceSingleObjInverse R) where
  map_injective w := by
    ext
    -- ⊢ a₁✝ i✝ j✝ = a₂✝ i✝ j✝
    apply_fun MulOpposite.unop using MulOpposite.unop_injective
    -- ⊢ MulOpposite.unop (a₁✝ i✝ j✝) = MulOpposite.unop (a₂✝ i✝ j✝)
    exact congr_fun (congr_fun w _) _
    -- 🎉 no goals

instance : Full (equivalenceSingleObjInverse R) where
  preimage f i j := MulOpposite.op (f i j)

instance : EssSurj (equivalenceSingleObjInverse R)
    where mem_essImage X :=
    ⟨{  ι := X
        X := fun _ => PUnit.unit }, ⟨eqToIso (by dsimp; cases X; congr)⟩⟩
                                                 -- ⊢ FintypeCat.of ↑X = X
                                                        -- ⊢ FintypeCat.of ↑(Bundled.mk α✝) = Bundled.mk α✝
                                                                 -- 🎉 no goals

/-- The categorical equivalence between the category of matrices over a ring,
and the category of matrices over that ring considered as a single-object category. -/
def equivalenceSingleObj : Mat R ≌ Mat_ (SingleObj Rᵐᵒᵖ) :=
  haveI := Equivalence.ofFullyFaithfullyEssSurj (equivalenceSingleObjInverse R)
  (equivalenceSingleObjInverse R).asEquivalence.symm
set_option linter.uppercaseLean3 false in
#align category_theory.Mat.equivalence_single_obj CategoryTheory.Mat.equivalenceSingleObj

-- porting note: added as this was not found automatically
instance (X Y : Mat R) : AddCommGroup (X ⟶ Y) := by
  change AddCommGroup (Matrix X Y R)
  -- ⊢ AddCommGroup (Matrix (↑X) (↑Y) R)
  infer_instance
  -- 🎉 no goals

variable {R}

-- porting note: added to ease automation
@[simp]
theorem add_apply {M N : Mat R} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j :=
  rfl

attribute [local simp] add_mul mul_add Finset.sum_add_distrib

instance : Preadditive (Mat R) where

-- TODO show `Mat R` has biproducts, and that `biprod.map` "is" forming a block diagonal matrix.
end Mat

end CategoryTheory
