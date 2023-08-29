/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Monoidal.Linear

#align_import algebra.category.Module.monoidal.basic from "leanprover-community/mathlib"@"74403a3b2551b0970855e14ef5e8fd0d6af1bfc2"

/-!
# The monoidal category structure on R-modules

Mostly this uses existing machinery in `LinearAlgebra.TensorProduct`.
We just need to provide a few small missing pieces to build the
`MonoidalCategory` instance.
The `SymmetricCategory` instance is in `Algebra.Category.ModuleCat.Monoidal.Symmetric`
to reduce imports.

Note the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

We construct the monoidal closed structure on `Module R` in
`Algebra.Category.ModuleCat.Monoidal.Closed`.

If you're happy using the bundled `Module R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/

-- Porting note: Module
set_option linter.uppercaseLean3 false

universe v w x u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

namespace MonoidalCategory

-- The definitions inside this namespace are essentially private.
-- After we build the `MonoidalCategory (Module R)` instance,
-- you should use that API.
open TensorProduct

attribute [local ext] TensorProduct.ext

/-- (implementation) tensor product of R-modules -/
def tensorObj (M N : ModuleCat R) : ModuleCat R :=
  ModuleCat.of R (M ⊗[R] N)
#align Module.monoidal_category.tensor_obj ModuleCat.MonoidalCategory.tensorObj

/-- (implementation) tensor product of morphisms R-modules -/
def tensorHom {M N M' N' : ModuleCat R} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
  TensorProduct.map f g
#align Module.monoidal_category.tensor_hom ModuleCat.MonoidalCategory.tensorHom

/-- (implementation) left whiskering for R-modules -/
def whiskerLeft (M : ModuleCat R) {N₁ N₂ : ModuleCat R} (f : N₁ ⟶ N₂) :
    tensorObj M N₁ ⟶ tensorObj M N₂ :=
  f.lTensor M

/-- (implementation) right whiskering for R-modules -/
def whiskerRight {M₁ M₂ : ModuleCat R} (f : M₁ ⟶ M₂) (N : ModuleCat R) :
    tensorObj M₁ N ⟶ tensorObj M₂ N :=
  f.rTensor N

theorem tensor_id (M N : ModuleCat R) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (ModuleCat.of R (M ⊗ N)) := by
  -- Porting note: even with high priority ext fails to find this
  apply TensorProduct.ext
  -- ⊢ LinearMap.compr₂ (TensorProduct.mk R ↑M ↑N) (tensorHom (𝟙 M) (𝟙 N)) = Linear …
  rfl
  -- 🎉 no goals
#align Module.monoidal_category.tensor_id ModuleCat.MonoidalCategory.tensor_id

theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
  -- Porting note: even with high priority ext fails to find this
  apply TensorProduct.ext
  -- ⊢ LinearMap.compr₂ (TensorProduct.mk R ↑X₁ ↑X₂) (tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) …
  rfl
  -- 🎉 no goals
#align Module.monoidal_category.tensor_comp ModuleCat.MonoidalCategory.tensor_comp

/-- (implementation) the associator for R-modules -/
def associator (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (K : ModuleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIso
#align Module.monoidal_category.associator ModuleCat.MonoidalCategory.associator

section

/-! The `associator_naturality` and `pentagon` lemmas below are very slow to elaborate.

We give them some help by expressing the lemmas first non-categorically, then using
`convert _aux using 1` to have the elaborator work as little as possible. -/


open TensorProduct (assoc map)

private theorem associator_naturality_aux {X₁ X₂ X₃ : Type*} [AddCommMonoid X₁] [AddCommMonoid X₂]
    [AddCommMonoid X₃] [Module R X₁] [Module R X₂] [Module R X₃] {Y₁ Y₂ Y₃ : Type*}
    [AddCommMonoid Y₁] [AddCommMonoid Y₂] [AddCommMonoid Y₃] [Module R Y₁] [Module R Y₂]
    [Module R Y₃] (f₁ : X₁ →ₗ[R] Y₁) (f₂ : X₂ →ₗ[R] Y₂) (f₃ : X₃ →ₗ[R] Y₃) :
    ↑(assoc R Y₁ Y₂ Y₃) ∘ₗ map (map f₁ f₂) f₃ = map f₁ (map f₂ f₃) ∘ₗ ↑(assoc R X₁ X₂ X₃) := by
  apply TensorProduct.ext_threefold
  -- ⊢ ∀ (x : X₁) (y : X₂) (z : X₃), ↑(LinearMap.comp (↑(assoc R Y₁ Y₂ Y₃)) (map (m …
  intro x y z
  -- ⊢ ↑(LinearMap.comp (↑(assoc R Y₁ Y₂ Y₃)) (map (map f₁ f₂) f₃)) ((x ⊗ₜ[R] y) ⊗ₜ …
  rfl
  -- 🎉 no goals
-- Porting note: private so hopeful never used outside this file
-- #align Module.monoidal_category.associator_naturality_aux ModuleCat.MonoidalCategory.associator_naturality_aux

variable (R)

private theorem pentagon_aux (W X Y Z : Type*) [AddCommMonoid W] [AddCommMonoid X]
    [AddCommMonoid Y] [AddCommMonoid Z] [Module R W] [Module R X] [Module R Y] [Module R Z] :
    ((map (1 : W →ₗ[R] W) (assoc R X Y Z).toLinearMap).comp
            (assoc R W (X ⊗[R] Y) Z).toLinearMap).comp
        (map ↑(assoc R W X Y) (1 : Z →ₗ[R] Z)) =
      (assoc R W X (Y ⊗[R] Z)).toLinearMap.comp (assoc R (W ⊗[R] X) Y Z).toLinearMap := by
  apply TensorProduct.ext_fourfold
  -- ⊢ ∀ (w : W) (x : X) (y : Y) (z : Z), ↑(LinearMap.comp (LinearMap.comp (map 1 ↑ …
  intro w x y z
  -- ⊢ ↑(LinearMap.comp (LinearMap.comp (map 1 ↑(assoc R X Y Z)) ↑(assoc R W (X ⊗[R …
  rfl
  -- 🎉 no goals
-- Porting note: private so hopeful never used outside this file
-- #align Module.monoidal_category.pentagon_aux Module.monoidal_category.pentagon_aux

end

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) :=
  by convert associator_naturality_aux f₁ f₂ f₃ using 1
     -- 🎉 no goals
#align Module.monoidal_category.associator_naturality ModuleCat.MonoidalCategory.associator_naturality

-- Porting note: very slow!
set_option maxHeartbeats 1600000 in
theorem pentagon (W X Y Z : ModuleCat R) :
    tensorHom (associator W X Y).hom (𝟙 Z) ≫
        (associator W (tensorObj X Y) Z).hom ≫ tensorHom (𝟙 W) (associator X Y Z).hom =
      (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  convert pentagon_aux R W X Y Z using 1
  -- 🎉 no goals
#align Module.monoidal_category.pentagon ModuleCat.MonoidalCategory.pentagon

/-- (implementation) the left unitor for R-modules -/
def leftUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (R ⊗[R] M) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.lid R M) : of R (R ⊗ M) ≅ of R M).trans (ofSelfIso M)
#align Module.monoidal_category.left_unitor ModuleCat.MonoidalCategory.leftUnitor

theorem leftUnitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom (𝟙 (ModuleCat.of R R)) f ≫ (leftUnitor N).hom = (leftUnitor M).hom ≫ f := by
  -- Porting note: broken ext
  apply TensorProduct.ext
  -- ⊢ LinearMap.compr₂ (TensorProduct.mk R ↑(of R R) ↑M) (tensorHom (𝟙 (of R R)) f …
  apply LinearMap.ext_ring
  -- ⊢ ↑(LinearMap.compr₂ (TensorProduct.mk R ↑(of R R) ↑M) (tensorHom (𝟙 (of R R)) …
  apply LinearMap.ext; intro x
  -- ⊢ ∀ (x : ↑M), ↑(↑(LinearMap.compr₂ (TensorProduct.mk R ↑(of R R) ↑M) (tensorHo …
                       -- ⊢ ↑(↑(LinearMap.compr₂ (TensorProduct.mk R ↑(of R R) ↑M) (tensorHom (𝟙 (of R R …
  -- Porting note: used to be dsimp
  change ((leftUnitor N).hom) ((tensorHom (𝟙 (of R R)) f) ((1 : R) ⊗ₜ[R] x)) =
    f (((leftUnitor M).hom) (1 ⊗ₜ[R] x))
  erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  -- ⊢ ↑(𝟙 (of R R)) (1, x).fst • ↑f (1, x).snd = ↑f (1 • x)
  rw [LinearMap.map_smul]
  -- ⊢ ↑(𝟙 (of R R)) (1, x).fst • ↑f (1, x).snd = 1 • ↑f x
  rfl
  -- 🎉 no goals
#align Module.monoidal_category.left_unitor_naturality ModuleCat.MonoidalCategory.leftUnitor_naturality

/-- (implementation) the right unitor for R-modules -/
def rightUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (M ⊗[R] R) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.rid R M) : of R (M ⊗ R) ≅ of R M).trans (ofSelfIso M)
#align Module.monoidal_category.right_unitor ModuleCat.MonoidalCategory.rightUnitor

theorem rightUnitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom f (𝟙 (ModuleCat.of R R)) ≫ (rightUnitor N).hom = (rightUnitor M).hom ≫ f := by
  -- Porting note: broken ext
  apply TensorProduct.ext
  -- ⊢ LinearMap.compr₂ (TensorProduct.mk R ↑M ↑(of R R)) (tensorHom f (𝟙 (of R R)) …
  apply LinearMap.ext; intro x
  -- ⊢ ∀ (x : ↑M), ↑(LinearMap.compr₂ (TensorProduct.mk R ↑M ↑(of R R)) (tensorHom  …
                       -- ⊢ ↑(LinearMap.compr₂ (TensorProduct.mk R ↑M ↑(of R R)) (tensorHom f (𝟙 (of R R …
  apply LinearMap.ext_ring
  -- ⊢ ↑(↑(LinearMap.compr₂ (TensorProduct.mk R ↑M ↑(of R R)) (tensorHom f (𝟙 (of R …
  -- Porting note: used to be dsimp
  change ((rightUnitor N).hom) ((tensorHom f (𝟙 (of R R))) (x ⊗ₜ[R] (1 : R))) =
    f (((rightUnitor M).hom) (x ⊗ₜ[R] 1))
  erw [TensorProduct.rid_tmul, TensorProduct.rid_tmul]
  -- ⊢ ↑(𝟙 (of R R)) (x, 1).snd • ↑f (x, 1).fst = ↑f (1 • x)
  rw [LinearMap.map_smul]
  -- ⊢ ↑(𝟙 (of R R)) (x, 1).snd • ↑f (x, 1).fst = 1 • ↑f x
  rfl
  -- 🎉 no goals
#align Module.monoidal_category.right_unitor_naturality ModuleCat.MonoidalCategory.rightUnitor_naturality

theorem triangle (M N : ModuleCat.{u} R) :
    (associator M (ModuleCat.of R R) N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom =
      tensorHom (rightUnitor M).hom (𝟙 N) := by
  apply TensorProduct.ext_threefold
  -- ⊢ ∀ (x : ↑M) (y : ↑(of R R)) (z : ↑N), ↑((associator M (of R R) N).hom ≫ tenso …
  intro x y z
  -- ⊢ ↑((associator M (of R R) N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom) ((x ⊗ₜ …
  change R at y
  -- ⊢ ↑((associator M (of R R) N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom) ((x ⊗ₜ …
  -- Porting note: used to be dsimp [tensorHom, associator]
  change x ⊗ₜ[R] ((leftUnitor N).hom) (y ⊗ₜ[R] z) = ((rightUnitor M).hom) (x ⊗ₜ[R] y) ⊗ₜ[R] z
  -- ⊢ x ⊗ₜ[R] ↑(leftUnitor N).hom (y ⊗ₜ[R] z) = ↑(rightUnitor M).hom (x ⊗ₜ[R] y) ⊗ …
  erw [TensorProduct.lid_tmul, TensorProduct.rid_tmul]
  -- ⊢ x ⊗ₜ[R] (y • z) = (y • x) ⊗ₜ[R] z
  exact (TensorProduct.smul_tmul _ _ _).symm
  -- 🎉 no goals
#align Module.monoidal_category.triangle ModuleCat.MonoidalCategory.triangle

end MonoidalCategory

open MonoidalCategory

instance monoidalCategory : MonoidalCategory (ModuleCat.{u} R) := MonoidalCategory.ofTensorHom
  -- data
  (tensorObj := MonoidalCategory.tensorObj)
  (tensorHom := @tensorHom _ _)
  (whiskerLeft := @whiskerLeft _ _)
  (whiskerRight := @whiskerRight _ _)
  (tensorUnit' := ModuleCat.of R R)
  (associator := associator)
  (leftUnitor := leftUnitor)
  (rightUnitor := rightUnitor)
  -- properties
  (tensor_id := fun M N ↦ tensor_id M N)
  (tensor_comp := fun f g h ↦ MonoidalCategory.tensor_comp f g h)
  (associator_naturality := fun f g h ↦ MonoidalCategory.associator_naturality f g h)
  (leftUnitor_naturality := fun f ↦ MonoidalCategory.leftUnitor_naturality f)
  (rightUnitor_naturality := fun f ↦ rightUnitor_naturality f)
  (pentagon := fun M N K L ↦ pentagon M N K L)
  (triangle := fun M N ↦ triangle M N)
#align Module.monoidal_category ModuleCat.monoidalCategory

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
instance : CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u) :=
  inferInstanceAs <| CommRing R

namespace MonoidalCategory

@[simp]
theorem hom_apply {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
  rfl
#align Module.monoidal_category.hom_apply ModuleCat.MonoidalCategory.hom_apply

@[simp]
theorem leftUnitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (ModuleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r
#align Module.monoidal_category.left_unitor_hom_apply ModuleCat.MonoidalCategory.leftUnitor_hom_apply

@[simp]
theorem leftUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (ModuleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m
#align Module.monoidal_category.left_unitor_inv_apply ModuleCat.MonoidalCategory.leftUnitor_inv_apply

@[simp]
theorem rightUnitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (ModuleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r
#align Module.monoidal_category.right_unitor_hom_apply ModuleCat.MonoidalCategory.rightUnitor_hom_apply

@[simp]
theorem rightUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (ModuleCat.{u} R)) m = m ⊗ₜ[R] 1 :=
  TensorProduct.rid_symm_apply m
#align Module.monoidal_category.right_unitor_inv_apply ModuleCat.MonoidalCategory.rightUnitor_inv_apply

@[simp]
theorem associator_hom_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ N ⊗ K) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl
#align Module.monoidal_category.associator_hom_apply ModuleCat.MonoidalCategory.associator_hom_apply

@[simp]
theorem associator_inv_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl
#align Module.monoidal_category.associator_inv_apply ModuleCat.MonoidalCategory.associator_inv_apply

end MonoidalCategory

open Opposite

-- Porting note: simp wasn't firing but rw was, annoying
instance : MonoidalPreadditive (ModuleCat.{u} R) := by
  refine' ⟨_, _, _, _⟩
  · dsimp only [autoParam]; intros
    -- ⊢ ∀ {W X Y Z : ModuleCat R} (f : W ⟶ X), f ⊗ 0 = 0
                            -- ⊢ f✝ ⊗ 0 = 0
    refine' TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => _)
    -- ⊢ ↑(↑(LinearMap.compr₂ (TensorProduct.mk R ↑W✝ ↑Y✝) (f✝ ⊗ 0)) x) y = ↑(↑(Linea …
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    -- ⊢ ↑(f✝ ⊗ 0) (x ⊗ₜ[R] y) = ↑0 (x ⊗ₜ[R] y)
    rw [LinearMap.zero_apply, MonoidalCategory.hom_apply, LinearMap.zero_apply,
      TensorProduct.tmul_zero]
  · dsimp only [autoParam]; intros
    -- ⊢ ∀ {W X Y Z : ModuleCat R} (f : Y ⟶ Z), 0 ⊗ f = 0
                            -- ⊢ 0 ⊗ f✝ = 0
    refine' TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => _)
    -- ⊢ ↑(↑(LinearMap.compr₂ (TensorProduct.mk R ↑W✝ ↑Y✝) (0 ⊗ f✝)) x) y = ↑(↑(Linea …
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    -- ⊢ ↑(0 ⊗ f✝) (x ⊗ₜ[R] y) = ↑0 (x ⊗ₜ[R] y)
    rw [LinearMap.zero_apply, MonoidalCategory.hom_apply, LinearMap.zero_apply,
      TensorProduct.zero_tmul]
  · dsimp only [autoParam]; intros
    -- ⊢ ∀ {W X Y Z : ModuleCat R} (f : W ⟶ X) (g h : Y ⟶ Z), f ⊗ (g + h) = f ⊗ g + f …
                            -- ⊢ f✝ ⊗ (g✝ + h✝) = f✝ ⊗ g✝ + f✝ ⊗ h✝
    refine' TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => _)
    -- ⊢ ↑(↑(LinearMap.compr₂ (TensorProduct.mk R ↑W✝ ↑Y✝) (f✝ ⊗ (g✝ + h✝))) x) y = ↑ …
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    -- ⊢ ↑(f✝ ⊗ (g✝ + h✝)) (x ⊗ₜ[R] y) = ↑(f✝ ⊗ g✝ + f✝ ⊗ h✝) (x ⊗ₜ[R] y)
    rw [LinearMap.add_apply, MonoidalCategory.hom_apply, MonoidalCategory.hom_apply]
    -- ⊢ ↑f✝ x ⊗ₜ[R] ↑(g✝ + h✝) y = ↑f✝ x ⊗ₜ[R] ↑g✝ y + ↑(f✝ ⊗ h✝) (x ⊗ₜ[R] y)
    erw [MonoidalCategory.hom_apply]
    -- ⊢ ↑f✝ x ⊗ₜ[R] ↑(g✝ + h✝) y = ↑f✝ x ⊗ₜ[R] ↑g✝ y + ↑f✝ x ⊗ₜ[R] ↑h✝ y
    rw [LinearMap.add_apply, TensorProduct.tmul_add]
    -- 🎉 no goals
  · dsimp only [autoParam]; intros
    -- ⊢ ∀ {W X Y Z : ModuleCat R} (f g : W ⟶ X) (h : Y ⟶ Z), (f + g) ⊗ h = f ⊗ h + g …
                            -- ⊢ (f✝ + g✝) ⊗ h✝ = f✝ ⊗ h✝ + g✝ ⊗ h✝
    refine' TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => _)
    -- ⊢ ↑(↑(LinearMap.compr₂ (TensorProduct.mk R ↑W✝ ↑Y✝) ((f✝ + g✝) ⊗ h✝)) x) y = ↑ …
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    -- ⊢ ↑((f✝ + g✝) ⊗ h✝) (x ⊗ₜ[R] y) = ↑(f✝ ⊗ h✝ + g✝ ⊗ h✝) (x ⊗ₜ[R] y)
    rw [LinearMap.add_apply, MonoidalCategory.hom_apply, MonoidalCategory.hom_apply]
    -- ⊢ ↑(f✝ + g✝) x ⊗ₜ[R] ↑h✝ y = ↑f✝ x ⊗ₜ[R] ↑h✝ y + ↑(g✝ ⊗ h✝) (x ⊗ₜ[R] y)
    erw [MonoidalCategory.hom_apply]
    -- ⊢ ↑(f✝ + g✝) x ⊗ₜ[R] ↑h✝ y = ↑f✝ x ⊗ₜ[R] ↑h✝ y + ↑g✝ x ⊗ₜ[R] ↑h✝ y
    rw [LinearMap.add_apply, TensorProduct.add_tmul]
    -- 🎉 no goals

-- Porting note: simp wasn't firing but rw was, annoying
instance : MonoidalLinear R (ModuleCat.{u} R) := by
  refine' ⟨_, _⟩
  -- ⊢ ∀ {W X Y Z : ModuleCat R} (f : W ⟶ X) (r : R) (g : Y ⟶ Z), f ⊗ r • g = r • ( …
  · dsimp only [autoParam]; intros
    -- ⊢ ∀ {W X Y Z : ModuleCat R} (f : W ⟶ X) (r : R) (g : Y ⟶ Z), f ⊗ r • g = r • ( …
                            -- ⊢ f✝ ⊗ r✝ • g✝ = r✝ • (f✝ ⊗ g✝)
    refine' TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => _)
    -- ⊢ ↑(↑(LinearMap.compr₂ (TensorProduct.mk R ↑W✝ ↑Y✝) (f✝ ⊗ r✝ • g✝)) x) y = ↑(↑ …
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    -- ⊢ ↑(f✝ ⊗ r✝ • g✝) (x ⊗ₜ[R] y) = ↑(r✝ • (f✝ ⊗ g✝)) (x ⊗ₜ[R] y)
    rw [LinearMap.smul_apply, MonoidalCategory.hom_apply, MonoidalCategory.hom_apply,
      LinearMap.smul_apply, TensorProduct.tmul_smul]
  · dsimp only [autoParam]; intros
    -- ⊢ ∀ {W X Y Z : ModuleCat R} (r : R) (f : W ⟶ X) (g : Y ⟶ Z), r • f ⊗ g = r • ( …
                            -- ⊢ r✝ • f✝ ⊗ g✝ = r✝ • (f✝ ⊗ g✝)
    refine' TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => _)
    -- ⊢ ↑(↑(LinearMap.compr₂ (TensorProduct.mk R ↑W✝ ↑Y✝) (r✝ • f✝ ⊗ g✝)) x) y = ↑(↑ …
    simp only [LinearMap.compr₂_apply, TensorProduct.mk_apply]
    -- ⊢ ↑(r✝ • f✝ ⊗ g✝) (x ⊗ₜ[R] y) = ↑(r✝ • (f✝ ⊗ g✝)) (x ⊗ₜ[R] y)
    rw [LinearMap.smul_apply, MonoidalCategory.hom_apply, MonoidalCategory.hom_apply,
      LinearMap.smul_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul]

end ModuleCat
