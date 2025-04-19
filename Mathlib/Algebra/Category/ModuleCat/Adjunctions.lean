/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
The functor of forming finitely supported functions on a type with values in a `[Ring R]`
is the left adjoint of
the forgetful functor from `R`-modules to types.
-/


assert_not_exists Cardinal

noncomputable section

open CategoryTheory

namespace ModuleCat

universe u

variable (R : Type u)

section

variable [Ring R]

/-- The free functor `Type u ⥤ ModuleCat R` sending a type `X` to the
free `R`-module with generators `x : X`, implemented as the type `X →₀ R`.
-/
def free : Type u ⥤ ModuleCat R where
  obj X := ModuleCat.of R (X →₀ R)
  map {_ _} f := ofHom <| Finsupp.lmapDomain _ _ f
  map_id := by intros; ext : 1; exact Finsupp.lmapDomain_id _ _
  map_comp := by intros; ext : 1; exact Finsupp.lmapDomain_comp _ _ _ _

variable {R}

/-- Constructor for elements in the module `(free R).obj X`. -/
noncomputable def freeMk {X : Type u} (x : X) : (free R).obj X := Finsupp.single x 1

@[ext 1200]
lemma free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (free R).obj X ⟶ M}
    (h : ∀ (x : X), f (freeMk x) = g (freeMk x)) :
    f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

/-- The morphism of modules `(free R).obj X ⟶ M` corresponding
to a map `f : X ⟶ M`. -/
noncomputable def freeDesc {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) :
    (free R).obj X ⟶ M :=
  ofHom <| Finsupp.lift M R X f

@[simp]
lemma freeDesc_apply {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) (x : X) :
    freeDesc f (freeMk x) = f x := by
  dsimp [freeDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

@[simp]
lemma free_map_apply {X Y : Type u} (f : X → Y) (x : X) :
    (free R).map f (freeMk x) = freeMk (f x) := by
  apply Finsupp.mapDomain_single

/-- The bijection `((free R).obj X ⟶ M) ≃ (X → M)` when `X` is a type and `M` a module. -/
@[simps]
def freeHomEquiv {X : Type u} {M : ModuleCat.{u} R} :
    ((free R).obj X ⟶ M) ≃ (X → M) where
  toFun φ x := φ (freeMk x)
  invFun ψ := freeDesc ψ
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

variable (R)

/-- The free-forgetful adjunction for R-modules.
-/
def adj : free R ⊣ forget (ModuleCat.{u} R) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun _ _ => freeHomEquiv
      homEquiv_naturality_left_symm := fun {X Y M} f g ↦ by ext; simp [freeHomEquiv] }

@[simp]
lemma adj_homEquiv (X : Type u) (M : ModuleCat.{u} R) :
    (adj R).homEquiv X M = freeHomEquiv := by
  simp only [adj, Adjunction.mkOfHomEquiv_homEquiv]

instance : (forget (ModuleCat.{u} R)).IsRightAdjoint  :=
  (adj R).isRightAdjoint

end

section Free

open MonoidalCategory

variable [CommRing R]

namespace FreeMonoidal

/-- The canonical isomorphism `𝟙_ (ModuleCat R) ≅ (free R).obj (𝟙_ (Type u))`.
(This should not be used directly: it is part of the implementation of the
monoidal structure on the functor `free R`.) -/
def εIso : 𝟙_ (ModuleCat R) ≅ (free R).obj (𝟙_ (Type u)) where
  hom := ofHom <| Finsupp.lsingle PUnit.unit
  inv := ofHom <| Finsupp.lapply PUnit.unit
  hom_inv_id := by
    ext
    simp [free]
  inv_hom_id := by
    ext ⟨⟩
    dsimp [freeMk]
    erw [Finsupp.lapply_apply, Finsupp.lsingle_apply]
    rw [Finsupp.single_eq_same]

@[simp]
lemma εIso_hom_one : (εIso R).hom 1 = freeMk PUnit.unit := rfl

@[simp]
lemma εIso_inv_freeMk (x : PUnit) : (εIso R).inv (freeMk x) = 1 := by
  dsimp [εIso, freeMk]
  erw [Finsupp.lapply_apply]
  rw [Finsupp.single_eq_same]

/-- The canonical isomorphism `(free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⊗ Y)`
for two types `X` and `Y`.
(This should not be used directly: it is is part of the implementation of the
monoidal structure on the functor `free R`.) -/
def μIso (X Y : Type u) :
    (free R).obj X ⊗ (free R).obj Y ≅ (free R).obj (X ⊗ Y) :=
  (finsuppTensorFinsupp' R _ _).toModuleIso

@[simp]
lemma μIso_hom_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    (μIso R X Y).hom (freeMk x ⊗ₜ freeMk y) = freeMk ⟨x, y⟩ := by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_single_tmul_single]
  rw [mul_one]

@[simp]
lemma μIso_inv_freeMk {X Y : Type u} (z : X ⊗ Y) :
    (μIso R X Y).inv (freeMk z) = freeMk z.1 ⊗ₜ freeMk z.2 := by
  dsimp [μIso, freeMk]
  erw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

end FreeMonoidal

open FreeMonoidal in
/-- The free functor `Type u ⥤ ModuleCat R` is a monoidal functor. -/
instance : (free R).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := εIso R
      μIso := μIso R
      μIso_hom_natural_left := fun {X Y} f X' ↦ by
        rw [← cancel_epi (μIso R X X').inv]
        aesop
      μIso_hom_natural_right := fun {X Y} X' f ↦ by
        rw [← cancel_epi (μIso R X' X).inv]
        aesop
      associativity := fun X Y Z ↦ by
        rw [← cancel_epi ((μIso R X Y).inv ▷ _), ← cancel_epi (μIso R _ _).inv]
        ext ⟨⟨x, y⟩, z⟩
        dsimp
        rw [μIso_inv_freeMk, MonoidalCategory.whiskerRight_apply, μIso_inv_freeMk,
          MonoidalCategory.whiskerRight_apply, μIso_hom_freeMk_tmul_freeMk,
          μIso_hom_freeMk_tmul_freeMk, free_map_apply,
          CategoryTheory.associator_hom_apply, MonoidalCategory.associator_hom_apply,
          MonoidalCategory.whiskerLeft_apply, μIso_hom_freeMk_tmul_freeMk,
          μIso_hom_freeMk_tmul_freeMk]
      left_unitality := fun X ↦ by
        rw [← cancel_epi (λ_ _).inv, Iso.inv_hom_id]
        aesop
      right_unitality := fun X ↦ by
        rw [← cancel_epi (ρ_ _).inv, Iso.inv_hom_id]
        aesop }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp]
lemma free_ε_one : ε (free R) 1 = freeMk PUnit.unit := rfl

@[simp]
lemma free_η_freeMk (x : PUnit) : η (free R) (freeMk x) = 1 := by
  apply FreeMonoidal.εIso_inv_freeMk

@[simp]
lemma free_μ_freeMk_tmul_freeMk {X Y : Type u} (x : X) (y : Y) :
    μ (free R) _ _ (freeMk x ⊗ₜ freeMk y) = freeMk ⟨x, y⟩ := by
  apply FreeMonoidal.μIso_hom_freeMk_tmul_freeMk

@[simp]
lemma free_δ_freeMk {X Y : Type u} (z : X ⊗ Y) :
    δ (free R) _ _ (freeMk z) = freeMk z.1 ⊗ₜ freeMk z.2 := by
  apply FreeMonoidal.μIso_inv_freeMk

end Free

end ModuleCat

namespace CategoryTheory

universe v u

/-- `Free R C` is a type synonym for `C`, which, given `[CommRing R]` and `[Category C]`,
we will equip with a category structure where the morphisms are formal `R`-linear combinations
of the morphisms in `C`.
-/
@[nolint unusedArguments]
def Free (_ : Type*) (C : Type u) :=
  C

/-- Consider an object of `C` as an object of the `R`-linear completion.

It may be preferable to use `(Free.embedding R C).obj X` instead;
this functor can also be used to lift morphisms.
-/
def Free.of (R : Type*) {C : Type u} (X : C) : Free R C :=
  X

variable (R : Type*) [CommRing R] (C : Type u) [Category.{v} C]

open Finsupp

-- Conceptually, it would be nice to construct this via "transport of enrichment",
-- using the fact that `ModuleCat.Free R : Type ⥤ ModuleCat R` and `ModuleCat.forget` are both lax
-- monoidal. This still seems difficult, so we just do it by hand.
instance categoryFree : Category (Free R C) where
  Hom := fun X Y : C => (X ⟶ Y) →₀ R
  id := fun X : C => Finsupp.single (𝟙 X) 1
  comp {X _ Z : C} f g :=
    (f.sum (fun f' s => g.sum (fun g' t => Finsupp.single (f' ≫ g') (s * t))) : (X ⟶ Z) →₀ R)
  assoc {W X Y Z} f g h := by
    -- This imitates the proof of associativity for `MonoidAlgebra`.
    simp only [sum_sum_index, sum_single_index, single_zero, single_add, eq_self_iff_true,
      forall_true_iff, forall₃_true_iff, add_mul, mul_add, Category.assoc, mul_assoc,
      zero_mul, mul_zero, sum_zero, sum_add]

namespace Free

section

instance : Preadditive (Free R C) where
  homGroup _ _ := Finsupp.instAddCommGroup
  add_comp X Y Z f f' g := by
    dsimp [CategoryTheory.categoryFree]
    rw [Finsupp.sum_add_index'] <;> · simp [add_mul]
  comp_add X Y Z f g g' := by
    dsimp [CategoryTheory.categoryFree]
    rw [← Finsupp.sum_add]
    congr; ext r h
    rw [Finsupp.sum_add_index'] <;> · simp [mul_add]

instance : Linear R (Free R C) where
  homModule _ _ := Finsupp.module _ R
  smul_comp X Y Z r f g := by
    dsimp [CategoryTheory.categoryFree]
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_assoc]
  comp_smul X Y Z f r g := by
    dsimp [CategoryTheory.categoryFree]
    simp_rw [Finsupp.smul_sum]
    congr; ext h s
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_left_comm]

theorem single_comp_single {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (r s : R) :
    (single f r ≫ single g s : Free.of R X ⟶ Free.of R Z) = single (f ≫ g) (r * s) := by
  dsimp [CategoryTheory.categoryFree]; simp

end

attribute [local simp] single_comp_single

/-- A category embeds into its `R`-linear completion.
-/
@[simps]
def embedding : C ⥤ Free R C where
  obj X := X
  map {_ _} f := Finsupp.single f 1
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/pull/10959): simp used to be able to close this goal
    rw [single_comp_single, one_mul]

variable {C} {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]

open Preadditive Linear

/-- A functor to an `R`-linear category lifts to a functor from its `R`-linear completion.
-/
@[simps]
def lift (F : C ⥤ D) : Free R C ⥤ D where
  obj X := F.obj X
  map {_ _} f := f.sum fun f' r => r • F.map f'
  map_id := by dsimp [CategoryTheory.categoryFree]; simp
  map_comp {X Y Z} f g := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ w₁ w₂ =>
      rw [add_comp]
      rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
      · simp only [w₁, w₂, add_comp]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
    | single f' r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [comp_add]
        rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
        · simp only [w₁, w₂, comp_add]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
      | single g' s =>
        rw [single_comp_single _ _ f' g' r s]
        simp [mul_comm r s, mul_smul]

theorem lift_map_single (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (r : R) :
    (lift R F).map (single f r) = r • F.map f := by simp

instance lift_additive (F : C ⥤ D) : (lift R F).Additive where
  map_add {X Y} f g := by
    dsimp
    rw [Finsupp.sum_add_index'] <;> simp [add_smul]

instance lift_linear (F : C ⥤ D) : (lift R F).Linear R where
  map_smul {X Y} f r := by
    dsimp
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]

/-- The embedding into the `R`-linear completion, followed by the lift,
is isomorphic to the original functor.
-/
def embeddingLiftIso (F : C ⥤ D) : embedding R C ⋙ lift R F ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

/-- Two `R`-linear functors out of the `R`-linear completion are isomorphic iff their
compositions with the embedding functor are isomorphic.
-/
def ext {F G : Free R C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (α : embedding R C ⋙ F ≅ embedding R C ⋙ G) : F ≅ G :=
  NatIso.ofComponents (fun X => α.app X)
    (by
      intro X Y f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [Functor.map_add, add_comp, w₁, w₂, Functor.map_add, comp_add]
      | single f' r =>
        rw [Iso.app_hom, Iso.app_hom, ← smul_single_one, F.map_smul, G.map_smul, smul_comp,
          comp_smul]
        change r • (embedding R C ⋙ F).map f' ≫ _ = r • _ ≫ (embedding R C ⋙ G).map f'
        rw [α.hom.naturality f'])

/-- `Free.lift` is unique amongst `R`-linear functors `Free R C ⥤ D`
which compose with `embedding ℤ C` to give the original functor.
-/
def liftUnique (F : C ⥤ D) (L : Free R C ⥤ D) [L.Additive] [L.Linear R]
    (α : embedding R C ⋙ L ≅ F) : L ≅ lift R F :=
  ext R (α.trans (embeddingLiftIso R F).symm)

end Free
end CategoryTheory
