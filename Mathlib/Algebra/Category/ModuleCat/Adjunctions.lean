/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin

! This file was ported from Lean 3 source module algebra.category.Module.adjunctions
! leanprover-community/mathlib commit 95a87616d63b3cb49d3fe678d416fbe9c4217bf4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Functorial
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
The functor of forming finitely supported functions on a type with values in a `[Ring R]`
is the left adjoint of
the forgetful functor from `R`-modules to types.
-/

set_option linter.uppercaseLean3 false -- `Module`

noncomputable section

open CategoryTheory

namespace ModuleCat

universe u

open Classical

variable (R : Type u)

section

variable [Ring R]

/-- The free functor `Type u ⥤ ModuleCat R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the type `X →₀ R`.
-/
@[simps]
def free : Type u ⥤ ModuleCat R where
  obj X := ModuleCat.of R (X →₀ R)
  map {X} {Y} f := Finsupp.lmapDomain _ _ f
  map_id := by intros ; exact Finsupp.lmapDomain_id _ _
  map_comp := by intros ; exact Finsupp.lmapDomain_comp _ _ _ _
#align Module.free ModuleCat.free

/-- The free-forgetful adjunction for R-modules.
-/
def adj : free R ⊣ forget (ModuleCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X M => (Finsupp.lift M R X).toEquiv.symm
      homEquiv_naturality_left_symm := fun {_} {_} M f g =>
        Finsupp.lhom_ext' fun x =>
          LinearMap.ext_ring
            (Finsupp.sum_mapDomain_index_addMonoidHom fun y => (smulAddHom R M).flip (g y)).symm }
#align Module.adj ModuleCat.adj

instance : IsRightAdjoint (forget (ModuleCat.{u} R)) :=
  ⟨_, adj R⟩

end

namespace Free

variable [CommRing R]

attribute [local ext] TensorProduct.ext

/-- (Implementation detail) The unitor for `Free R`. -/
def ε : 𝟙_ (ModuleCat.{u} R) ⟶ (free R).obj (𝟙_ (Type u)) :=
  Finsupp.lsingle PUnit.unit
#align Module.free.ε ModuleCat.Free.ε

@[simp]
theorem ε_apply (r : R) : ε R r = Finsupp.single PUnit.unit r :=
  rfl
#align Module.free.ε_apply ModuleCat.Free.ε_apply

/-- (Implementation detail) The tensorator for `Free R`. -/
def μ (α β : Type u) : (free R).obj α ⊗ (free R).obj β ≅ (free R).obj (α ⊗ β) :=
  (finsuppTensorFinsupp' R α β).toModuleIso
#align Module.free.μ ModuleCat.Free.μ

theorem μ_natural {X Y X' Y' : Type u} (f : X ⟶ Y) (g : X' ⟶ Y') :
    ((free R).map f ⊗ (free R).map g) ≫ (μ R Y Y').hom = (μ R X X').hom ≫ (free R).map (f ⊗ g) := by
  intros
  -- Porting note: broken ext
  apply TensorProduct.ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.lhom_ext'
  intro x'
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro ⟨y, y'⟩
  -- Porting note: used to be dsimp [μ]
  change (finsuppTensorFinsupp' R Y Y')
    (Finsupp.mapDomain f (Finsupp.single x 1) ⊗ₜ[R] Finsupp.mapDomain g (Finsupp.single x' 1)) _
    = (Finsupp.mapDomain (f ⊗ g) (finsuppTensorFinsupp' R X X'
    (Finsupp.single x 1 ⊗ₜ[R] Finsupp.single x' 1))) _
  simp_rw [Finsupp.mapDomain_single, finsuppTensorFinsupp'_single_tmul_single, mul_one,
    Finsupp.mapDomain_single, CategoryTheory.tensor_apply]
#align Module.free.μ_natural ModuleCat.Free.μ_natural

theorem left_unitality (X : Type u) :
    (λ_ ((free R).obj X)).hom =
      (ε R ⊗ 𝟙 ((free R).obj X)) ≫ (μ R (𝟙_ (Type u)) X).hom ≫ map (free R).obj (λ_ X).hom := by
  intros
  -- Porting note: broken ext
  apply TensorProduct.ext
  apply LinearMap.ext_ring
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro x'
  -- Porting note: used to be dsimp [ε, μ]
  let q : X →₀ R := ((λ_ (of R (X →₀ R))).hom) (1 ⊗ₜ[R] Finsupp.single x 1)
  change q x' = Finsupp.mapDomain (λ_ X).hom (finsuppTensorFinsupp' R (𝟙_ (Type u)) X
    (Finsupp.single PUnit.unit 1 ⊗ₜ[R] Finsupp.single x 1)) x'
  simp_rw [finsuppTensorFinsupp'_single_tmul_single,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply, Finsupp.smul_single', mul_one,
    Finsupp.mapDomain_single, CategoryTheory.leftUnitor_hom_apply, one_smul]
#align Module.free.left_unitality ModuleCat.Free.left_unitality

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem right_unitality (X : Type u) :
    (ρ_ ((free R).obj X)).Hom =
      (𝟙 ((free R).obj X) ⊗ ε R) ≫ (μ R X (𝟙_ (Type u))).Hom ≫ map (free R).obj (ρ_ X).Hom := by
  intros
  ext
  dsimp [ε, μ]
  simp_rw [finsuppTensorFinsupp'_single_tmul_single,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply, Finsupp.smul_single', mul_one,
    Finsupp.mapDomain_single, CategoryTheory.rightUnitor_hom_apply]
#align Module.free.right_unitality ModuleCat.free.right_unitality

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem associativity (X Y Z : Type u) :
    ((μ R X Y).Hom ⊗ 𝟙 ((free R).obj Z)) ≫ (μ R (X ⊗ Y) Z).Hom ≫ map (free R).obj (α_ X Y Z).Hom =
      (α_ ((free R).obj X) ((free R).obj Y) ((free R).obj Z)).Hom ≫
        (𝟙 ((free R).obj X) ⊗ (μ R Y Z).Hom) ≫ (μ R X (Y ⊗ Z)).Hom := by
  intros
  ext
  dsimp [μ]
  simp_rw [finsuppTensorFinsupp'_single_tmul_single, Finsupp.mapDomain_single, mul_one,
    CategoryTheory.associator_hom_apply]
#align Module.free.associativity ModuleCat.free.associativity

-- In fact, it's strong monoidal, but we don't yet have a typeclass for that.
/-- The free R-module functor is lax monoidal. -/
@[simps]
instance : LaxMonoidal.{u} (free R).obj where
  -- Send `R` to `punit →₀ R`
  ε := ε R
  -- Send `(α →₀ R) ⊗ (β →₀ R)` to `α × β →₀ R`
  μ X Y := (μ R X Y).Hom
  μ_natural' X Y X' Y' f g := μ_natural R f g
  left_unitality' := left_unitality R
  right_unitality' := right_unitality R
  associativity' := associativity R

instance : IsIso (LaxMonoidal.ε (free R).obj) :=
  ⟨⟨Finsupp.lapply PUnit.unit, ⟨by ext; simp, by ext (⟨⟩⟨⟩); simp⟩⟩⟩

end Free

variable [CommRing R]

/-- The free functor `Type u ⥤ Module R`, as a monoidal functor. -/
def monoidalFree : MonoidalFunctor (Type u) (ModuleCat.{u} R) :=
  {
    LaxMonoidalFunctor.of
      (free R).obj with
    ε_isIso := by dsimp; infer_instance
    μ_isIso := fun X Y => by dsimp; infer_instance }
#align Module.monoidal_free ModuleCat.monoidalFree

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
example (X Y : Type u) : (free R).obj (X × Y) ≅ (free R).obj X ⊗ (free R).obj Y :=
  ((monoidalFree R).μIso X Y).symm

end ModuleCat

namespace CategoryTheory

universe v u

/-- `Free R C` is a type synonym for `C`, which, given `[comm_ring R]` and `[category C]`,
we will equip with a category structure where the morphisms are formal `R`-linear combinations
of the morphisms in `C`.
-/
@[nolint unused_arguments has_nonempty_instance]
def Free (R : Type _) (C : Type u) :=
  C
#align category_theory.Free CategoryTheory.Free

/-- Consider an object of `C` as an object of the `R`-linear completion.

It may be preferable to use `(Free.embedding R C).obj X` instead;
this functor can also be used to lift morphisms.
-/
def Free.of (R : Type _) {C : Type u} (X : C) : Free R C :=
  X
#align category_theory.Free.of CategoryTheory.Free.of

variable (R : Type _) [CommRing R] (C : Type u) [Category.{v} C]

open Finsupp

-- Conceptually, it would be nice to construct this via "transport of enrichment",
-- using the fact that `Module.free R : Type ⥤ Module R` and `Module.forget` are both lax monoidal.
-- This still seems difficult, so we just do it by hand.
instance categoryFree : Category (Free R C) where
  Hom := fun X Y : C => (X ⟶ Y) →₀ R
  id := fun X : C => Finsupp.single (𝟙 X) 1
  comp (X Y Z : C) f g := f.Sum fun f' s => g.Sum fun g' t => Finsupp.single (f' ≫ g') (s * t)
  assoc' W X Y Z f g h := by
    dsimp
    -- This imitates the proof of associativity for `monoid_algebra`.
    simp only [sum_sum_index, sum_single_index, single_zero, single_add, eq_self_iff_true,
      forall_true_iff, forall₃_true_iff, add_mul, mul_add, category.assoc, mul_assoc,
      MulZeroClass.zero_mul, MulZeroClass.mul_zero, sum_zero, sum_add]
#align category_theory.category_Free CategoryTheory.categoryFree

namespace Free

section

attribute [local reducible] CategoryTheory.categoryFree

instance : Preadditive (Free R C) where
  homGroup X Y := Finsupp.addCommGroup
  add_comp X Y Z f f' g := by
    dsimp
    rw [Finsupp.sum_add_index'] <;> · simp [add_mul]
  comp_add X Y Z f g g' := by
    dsimp
    rw [← Finsupp.sum_add]
    congr ; ext (r h)
    rw [Finsupp.sum_add_index'] <;> · simp [mul_add]

instance : Linear R (Free R C) where
  homModule X Y := Finsupp.module (X ⟶ Y) R
  smul_comp' X Y Z r f g := by
    dsimp
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_assoc]
  comp_smul' X Y Z f r g := by
    dsimp
    simp_rw [Finsupp.smul_sum]
    congr ; ext (h s)
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_left_comm]

theorem single_comp_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R) :
    (single f r ≫ single g s : Free.of R X ⟶ Free.of R Z) = single (f ≫ g) (r * s) := by dsimp; simp
#align category_theory.Free.single_comp_single CategoryTheory.Free.single_comp_single

end

attribute [local simp] single_comp_single

/-- A category embeds into its `R`-linear completion.
-/
@[simps]
def embedding : C ⥤ Free R C where
  obj X := X
  map X Y f := Finsupp.single f 1
  map_id' X := rfl
  map_comp' X Y Z f g := by simp
#align category_theory.Free.embedding CategoryTheory.Free.embedding

variable (R) {C} {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]

open Preadditive Linear

/-- A functor to an `R`-linear category lifts to a functor from its `R`-linear completion.
-/
@[simps]
def lift (F : C ⥤ D) : Free R C ⥤ D where
  obj X := F.obj X
  map X Y f := f.Sum fun f' r => r • F.map f'
  map_id' := by dsimp [CategoryTheory.categoryFree]; simp
  map_comp' X Y Z f g := by
    apply Finsupp.induction_linear f
    · simp only [limits.zero_comp, sum_zero_index]
    · intro f₁ f₂ w₁ w₂
      rw [add_comp]
      rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
      · simp only [w₁, w₂, add_comp]
      · intros ; rw [zero_smul]
      · intros ; simp only [add_smul]
      · intros ; rw [zero_smul]
      · intros ; simp only [add_smul]
    · intro f' r
      apply Finsupp.induction_linear g
      · simp only [limits.comp_zero, sum_zero_index]
      · intro f₁ f₂ w₁ w₂
        rw [comp_add]
        rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
        · simp only [w₁, w₂, comp_add]
        · intros ; rw [zero_smul]
        · intros ; simp only [add_smul]
        · intros ; rw [zero_smul]
        · intros ; simp only [add_smul]
      · intro g' s
        erw [single_comp_single]
        simp [mul_comm r s, mul_smul]
#align category_theory.Free.lift CategoryTheory.Free.lift

@[simp]
theorem lift_map_single (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R) :
    (lift R F).map (single f r) = r • F.map f := by simp
#align category_theory.Free.lift_map_single CategoryTheory.Free.lift_map_single

instance lift_additive (F : C ⥤ D) : (lift R F).Additive
    where map_add' X Y f g := by
    dsimp
    rw [Finsupp.sum_add_index'] <;> simp [add_smul]
#align category_theory.Free.lift_additive CategoryTheory.Free.lift_additive

instance lift_linear (F : C ⥤ D) : (lift R F).Linear R
    where map_smul' X Y f r := by
    dsimp
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]
#align category_theory.Free.lift_linear CategoryTheory.Free.lift_linear

/-- The embedding into the `R`-linear completion, followed by the lift,
is isomorphic to the original functor.
-/
def embeddingLiftIso (F : C ⥤ D) : embedding R C ⋙ lift R F ≅ F :=
  NatIso.ofComponents (fun X => Iso.refl _) (by tidy)
#align category_theory.Free.embedding_lift_iso CategoryTheory.Free.embeddingLiftIso

/-- Two `R`-linear functors out of the `R`-linear completion are isomorphic iff their
compositions with the embedding functor are isomorphic.
-/
@[ext]
def ext {F G : Free R C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (α : embedding R C ⋙ F ≅ embedding R C ⋙ G) : F ≅ G :=
  NatIso.ofComponents (fun X => α.app X)
    (by
      intro X Y f
      apply Finsupp.induction_linear f
      · simp
      · intro f₁ f₂ w₁ w₂
        simp only [F.map_add, G.map_add, add_comp, comp_add, w₁, w₂]
      · intro f' r
        rw [iso.app_hom, iso.app_hom, ← smul_single_one, F.map_smul, G.map_smul, smul_comp,
          comp_smul]
        change r • (Embedding R C ⋙ F).map f' ≫ _ = r • _ ≫ (Embedding R C ⋙ G).map f'
        rw [α.hom.naturality f']
        infer_instance
        -- Why are these not picked up automatically when we rewrite?
        infer_instance)
#align category_theory.Free.ext CategoryTheory.Free.ext

/-- `Free.lift` is unique amongst `R`-linear functors `Free R C ⥤ D`
which compose with `embedding ℤ C` to give the original functor.
-/
def liftUnique (F : C ⥤ D) (L : Free R C ⥤ D) [L.Additive] [L.Linear R]
    (α : embedding R C ⋙ L ≅ F) : L ≅ lift R F :=
  ext R (α.trans (embeddingLiftIso R F).symm)
#align category_theory.Free.lift_unique CategoryTheory.Free.liftUnique

end Free

end CategoryTheory
