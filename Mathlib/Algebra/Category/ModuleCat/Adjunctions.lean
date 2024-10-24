/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
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
  map {_ _} f := Finsupp.lmapDomain _ _ f
  map_id := by intros; exact Finsupp.lmapDomain_id _ _
  map_comp := by intros; exact Finsupp.lmapDomain_comp _ _ _ _

variable {R}

/-- Constructor for elements in the module `(free R).obj X`. -/
noncomputable def freeMk {X : Type u} (x : X) : (free R).obj X := Finsupp.single x 1

@[ext 1200]
lemma free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (free R).obj X ⟶ M}
    (h : ∀ (x : X), f (freeMk x) = g (freeMk x)) :
    f = g :=
  (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

/-- The morphism of modules `(free R).obj X ⟶ M` corresponding
to a map `f : X ⟶ M`. -/
noncomputable def freeDesc {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) :
    (free R).obj X ⟶ M :=
  Finsupp.lift M R X f

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

namespace Free

open MonoidalCategory

variable [CommRing R]

attribute [local ext] TensorProduct.ext

/-- (Implementation detail) The unitor for `Free R`. -/
def ε : 𝟙_ (ModuleCat.{u} R) ⟶ (free R).obj (𝟙_ (Type u)) :=
  Finsupp.lsingle PUnit.unit

-- This lemma has always been bad, but lean4#2644 made `simp` start noticing
@[simp, nolint simpNF]
theorem ε_apply (r : R) : ε R r = Finsupp.single PUnit.unit r :=
  rfl

/-- (Implementation detail) The tensorator for `Free R`. -/
def μ (α β : Type u) : (free R).obj α ⊗ (free R).obj β ≅ (free R).obj (α ⊗ β) :=
  (finsuppTensorFinsupp' R α β).toModuleIso

theorem μ_natural {X Y X' Y' : Type u} (f : X ⟶ Y) (g : X' ⟶ Y') :
    ((free R).map f ⊗ (free R).map g) ≫ (μ R Y Y').hom = (μ R X X').hom ≫ (free R).map (f ⊗ g) := by
  -- Porting note (#11041): broken ext
  apply TensorProduct.ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.lhom_ext'
  intro x'
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro ⟨y, y'⟩
  -- Porting note (#10934): used to be dsimp [μ]
  change (finsuppTensorFinsupp' R Y Y')
    (Finsupp.mapDomain f (Finsupp.single x 1) ⊗ₜ[R] Finsupp.mapDomain g (Finsupp.single x' 1)) _
    = (Finsupp.mapDomain (f ⊗ g) (finsuppTensorFinsupp' R X X'
    (Finsupp.single x 1 ⊗ₜ[R] Finsupp.single x' 1))) _

  -- extra `rfl` after leanprover/lean4#2466
  simp_rw [Finsupp.mapDomain_single, finsuppTensorFinsupp'_single_tmul_single, mul_one,
    Finsupp.mapDomain_single, CategoryTheory.tensor_apply]; rfl

theorem left_unitality (X : Type u) :
    (λ_ ((free R).obj X)).hom =
      (ε R ⊗ 𝟙 ((free R).obj X)) ≫ (μ R (𝟙_ (Type u)) X).hom ≫ map (free R).obj (λ_ X).hom := by
  -- Porting note (#11041): broken ext
  apply TensorProduct.ext
  apply LinearMap.ext_ring
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro x'
  -- Porting note (#10934): used to be dsimp [ε, μ]
  let q : X →₀ R := ((λ_ (of R (X →₀ R))).hom) (1 ⊗ₜ[R] Finsupp.single x 1)
  change q x' = Finsupp.mapDomain (λ_ X).hom (finsuppTensorFinsupp' R (𝟙_ (Type u)) X
    (Finsupp.single PUnit.unit 1 ⊗ₜ[R] Finsupp.single x 1)) x'
  simp_rw [q, finsuppTensorFinsupp'_single_tmul_single,
    ModuleCat.MonoidalCategory.leftUnitor_hom_apply, mul_one,
    Finsupp.mapDomain_single, CategoryTheory.leftUnitor_hom_apply, one_smul]

theorem right_unitality (X : Type u) :
    (ρ_ ((free R).obj X)).hom =
      (𝟙 ((free R).obj X) ⊗ ε R) ≫ (μ R X (𝟙_ (Type u))).hom ≫ map (free R).obj (ρ_ X).hom := by
  -- Porting note (#11041): broken ext
  apply TensorProduct.ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro x'
  -- Porting note (#10934): used to be dsimp [ε, μ]
  let q : X →₀ R := ((ρ_ (of R (X →₀ R))).hom) (Finsupp.single x 1 ⊗ₜ[R] 1)
  change q x' = Finsupp.mapDomain (ρ_ X).hom (finsuppTensorFinsupp' R X (𝟙_ (Type u))
    (Finsupp.single x 1 ⊗ₜ[R] Finsupp.single PUnit.unit 1)) x'
  simp_rw [q, finsuppTensorFinsupp'_single_tmul_single,
    ModuleCat.MonoidalCategory.rightUnitor_hom_apply, mul_one,
    Finsupp.mapDomain_single, CategoryTheory.rightUnitor_hom_apply, one_smul]

theorem associativity (X Y Z : Type u) :
    ((μ R X Y).hom ⊗ 𝟙 ((free R).obj Z)) ≫ (μ R (X ⊗ Y) Z).hom ≫ map (free R).obj (α_ X Y Z).hom =
      (α_ ((free R).obj X) ((free R).obj Y) ((free R).obj Z)).hom ≫
        (𝟙 ((free R).obj X) ⊗ (μ R Y Z).hom) ≫ (μ R X (Y ⊗ Z)).hom := by
  -- Porting note (#11041): broken ext
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  apply Finsupp.lhom_ext'
  intro y
  apply LinearMap.ext_ring
  apply Finsupp.lhom_ext'
  intro z
  apply LinearMap.ext_ring
  apply Finsupp.ext
  intro a
  -- Porting note (#10934): used to be dsimp [μ]
  change Finsupp.mapDomain (α_ X Y Z).hom (finsuppTensorFinsupp' R (X ⊗ Y) Z
    (finsuppTensorFinsupp' R X Y
    (Finsupp.single x 1 ⊗ₜ[R] Finsupp.single y 1) ⊗ₜ[R] Finsupp.single z 1)) a =
    finsuppTensorFinsupp' R X (Y ⊗ Z)
    (Finsupp.single x 1 ⊗ₜ[R]
      finsuppTensorFinsupp' R Y Z (Finsupp.single y 1 ⊗ₜ[R] Finsupp.single z 1)) a
  -- extra `rfl` after leanprover/lean4#2466
  simp_rw [finsuppTensorFinsupp'_single_tmul_single, Finsupp.mapDomain_single, mul_one,
    CategoryTheory.associator_hom_apply]; rfl

-- In fact, it's strong monoidal, but we don't yet have a typeclass for that.
/-- The free R-module functor is lax monoidal. -/
@[simps]
instance : LaxMonoidal.{u} (free R).obj := .ofTensorHom
  -- Send `R` to `PUnit →₀ R`
  (ε := ε R)
  -- Send `(α →₀ R) ⊗ (β →₀ R)` to `α × β →₀ R`
  (μ := fun X Y => (μ R X Y).hom)
  (μ_natural := fun {_} {_} {_} {_} f g ↦ μ_natural R f g)
  (left_unitality := left_unitality R)
  (right_unitality := right_unitality R)
  (associativity := associativity R)

instance : IsIso (@LaxMonoidal.ε _ _ _ _ _ _ (free R).obj _ _) := by
  refine ⟨⟨Finsupp.lapply PUnit.unit, ⟨?_, ?_⟩⟩⟩
  · -- Porting note (#11041): broken ext
    apply LinearMap.ext_ring
    -- Porting note (#10959): simp used to be able to close this goal
    dsimp
    erw [ModuleCat.comp_def, LinearMap.comp_apply, ε_apply, Finsupp.lapply_apply,
      Finsupp.single_eq_same, id_apply]
  · -- Porting note (#11041): broken ext
    apply Finsupp.lhom_ext'
    intro ⟨⟩
    apply LinearMap.ext_ring
    apply Finsupp.ext
    intro ⟨⟩
    -- Porting note (#10959): simp used to be able to close this goal
    dsimp
    erw [ModuleCat.comp_def, LinearMap.comp_apply, ε_apply, Finsupp.lapply_apply,
      Finsupp.single_eq_same]

end Free

open MonoidalCategory

variable [CommRing R]

/-- The free functor `Type u ⥤ ModuleCat R`, as a monoidal functor. -/
def monoidalFree : MonoidalFunctor (Type u) (ModuleCat.{u} R) :=
  { LaxMonoidalFunctor.of (free R).obj with
    -- Porting note (#10934): used to be dsimp
    ε_isIso := (by infer_instance : IsIso (@LaxMonoidal.ε _ _ _ _ _ _ (free R).obj _ _))
    μ_isIso := fun X Y => by dsimp; infer_instance }

example (X Y : Type u) : (free R).obj (X × Y) ≅ (free R).obj X ⊗ (free R).obj Y :=
  ((monoidalFree R).μIso X Y).symm

end ModuleCat

namespace CategoryTheory

universe v u

/-- `Free R C` is a type synonym for `C`, which, given `[CommRing R]` and `[Category C]`,
we will equip with a category structure where the morphisms are formal `R`-linear combinations
of the morphisms in `C`.
-/
-- Porting note(#5171): Removed has_nonempty_instance nolint; linter not ported yet
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
    dsimp
    -- This imitates the proof of associativity for `MonoidAlgebra`.
    simp only [sum_sum_index, sum_single_index, single_zero, single_add, eq_self_iff_true,
      forall_true_iff, forall₃_true_iff, add_mul, mul_add, Category.assoc, mul_assoc,
      zero_mul, mul_zero, sum_zero, sum_add]

namespace Free

section

-- Porting note: removed local reducible attribute for categoryFree, adjusted dsimp invocations
-- accordingly

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
    -- Porting note (#10959): simp used to be able to close this goal
    dsimp only []
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
    apply Finsupp.induction_linear f
    · simp
    · intro f₁ f₂ w₁ w₂
      rw [add_comp]
      dsimp at *
      rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
      · simp only [w₁, w₂, add_comp]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
    · intro f' r
      apply Finsupp.induction_linear g
      · simp
      · intro f₁ f₂ w₁ w₂
        rw [comp_add]
        dsimp at *
        rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
        · simp only [w₁, w₂, comp_add]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
      · intro g' s
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
      apply Finsupp.induction_linear f
      · simp
      · intro f₁ f₂ w₁ w₂
        -- Porting note: Using rw instead of simp
        rw [Functor.map_add, add_comp, w₁, w₂, Functor.map_add, comp_add]
      · intro f' r
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
