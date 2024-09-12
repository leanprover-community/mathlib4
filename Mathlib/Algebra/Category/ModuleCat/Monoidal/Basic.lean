/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Scott Morrison, Jakob von Raumer
-/
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.CategoryTheory.Monoidal.Linear

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

We construct the monoidal closed structure on `ModuleCat R` in
`Algebra.Category.ModuleCat.Monoidal.Closed`.

If you're happy using the bundled `ModuleCat R`, it may be possible to mostly
use this as an interface and not need to interact much with the implementation details.
-/


suppress_compilation

universe v w x u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]
namespace SemigroupalCategory

-- The definitions inside this namespace are essentially private.
-- After we build the `SemigroupalCategory (Module R)` instance,
-- you should use that API.
open TensorProduct

attribute [local ext] TensorProduct.ext

/-- (implementation) tensor product of R-modules -/
def tensorObj (M N : ModuleCat R) : ModuleCat R :=
  ModuleCat.of R (M ⊗[R] N)

/-- (implementation) tensor product of morphisms R-modules -/
def tensorHom {M N M' N' : ModuleCat R} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
  TensorProduct.map f g

/-- (implementation) left whiskering for R-modules -/
def whiskerLeft (M : ModuleCat R) {N₁ N₂ : ModuleCat R} (f : N₁ ⟶ N₂) :
    tensorObj M N₁ ⟶ tensorObj M N₂ :=
  f.lTensor M

/-- (implementation) right whiskering for R-modules -/
def whiskerRight {M₁ M₂ : ModuleCat R} (f : M₁ ⟶ M₂) (N : ModuleCat R) :
    tensorObj M₁ N ⟶ tensorObj M₂ N :=
  f.rTensor N

theorem tensor_id (M N : ModuleCat R) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (ModuleCat.of R (M ⊗ N)) := by
  -- Porting note (#11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
  -- Porting note (#11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

/-- (implementation) the associator for R-modules -/
def associator (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (K : ModuleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIso

@[simps (config := .lemmasOnly)]
instance instSemigroupalCategoryStruct : SemigroupalCategoryStruct (ModuleCat R) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom f g := TensorProduct.map f g
  associator := associator

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
  intro x y z
  rfl

variable (R)

private theorem pentagon_aux (W X Y Z : Type*) [AddCommMonoid W] [AddCommMonoid X]
    [AddCommMonoid Y] [AddCommMonoid Z] [Module R W] [Module R X] [Module R Y] [Module R Z] :
    (((assoc R X Y Z).toLinearMap.lTensor W).comp
            (assoc R W (X ⊗[R] Y) Z).toLinearMap).comp
        ((assoc R W X Y).toLinearMap.rTensor Z) =
      (assoc R W X (Y ⊗[R] Z)).toLinearMap.comp (assoc R (W ⊗[R] X) Y Z).toLinearMap := by
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

end

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  convert associator_naturality_aux f₁ f₂ f₃ using 1

theorem pentagon (W X Y Z : ModuleCat R) :
    whiskerRight (associator W X Y).hom Z ≫
        (associator W (tensorObj X Y) Z).hom ≫ whiskerLeft W (associator X Y Z).hom =
      (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  convert pentagon_aux R W X Y Z using 1

end SemigroupalCategory

open SemigroupalCategory

instance semigroupalCategory : SemigroupalCategory (ModuleCat R) := SemigroupalCategory.ofTensorHom
  (tensor_id := fun M N ↦ ModuleCat.SemigroupalCategory.tensor_id M N)
  (tensor_comp := fun f g h ↦ SemigroupalCategory.tensor_comp f g h)
  (associator_naturality := fun f g h ↦ SemigroupalCategory.associator_naturality f g h)
  (pentagon := fun M N K L ↦ pentagon M N K L)

namespace SemigroupalCategory

@[simp]
theorem hom_apply {K L M N : ModuleCat R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
  rfl

@[simp]
theorem whiskerLeft_apply (L : ModuleCat R) {M N : ModuleCat R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l ⊗ₜ m) = l ⊗ₜ f m :=
  rfl

@[simp]
theorem whiskerRight_apply {L M : ModuleCat R} (f : L ⟶ M) (N : ModuleCat R)
    (l : L) (n : N) :
    (f ▷ N) (l ⊗ₜ n) = f l ⊗ₜ n :=
  rfl

@[simp]
theorem associator_hom_apply {M N K : ModuleCat R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ N ⊗ K) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl

@[simp]
theorem associator_inv_apply {M N K : ModuleCat R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl

theorem tensor_ext' {M N P : ModuleCat R} {f g : M ⊗ N ⟶ P}
    (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) : f = g :=
  TensorProduct.ext' h

def idfk_left {M : ModuleCat R} (N : ModuleCat R) (m : M) :
    N ⟶ M ⊗ N :=
  ModuleCat.ofHom <| TensorProduct.mk R M N m

def idfk_right (M : ModuleCat R) {N : ModuleCat R} (n : N) :
    M ⟶ M ⊗ N :=
  ModuleCat.ofHom <| (TensorProduct.mk R M N).flip n

@[simp]
theorem idfk_left_apply {M N : ModuleCat R} (m : M) (n : N) :
    idfk_left N m n = m ⊗ₜ n :=
  rfl

@[simp]
theorem idfk_right_apply {M N : ModuleCat R} (m : M) (n : N) :
    idfk_right M n m = m ⊗ₜ n :=
  rfl

theorem tensor_ext_left {M N P : ModuleCat R} {f g : M ⊗ N ⟶ P}
    (h : ∀ (m : M), idfk_left N m ≫ f = idfk_left N m ≫ g) : f = g := by
  apply tensor_ext'
  intro x y
  exact congr($(h x) y)

theorem tensor_ext_right {M N P : ModuleCat R} {f g : M ⊗ N ⟶ P}
    (h : ∀ (n : N), idfk_right M n ≫ f = idfk_right M n ≫ g) : f = g := by
  apply tensor_ext'
  intro x y
  exact congr($(h y) x)

theorem tensor_ext_threefold {M N P Q : ModuleCat R} {f g : (M ⊗ N) ⊗ P ⟶ Q}
    (h : ∀ m n p, f ((m ⊗ₜ[R] n) ⊗ₜ[R] p) = g ((m ⊗ₜ[R] n) ⊗ₜ[R] p)) : f = g :=
  TensorProduct.ext_threefold h

end SemigroupalCategory

open Opposite

-- Porting note: simp wasn't firing but rw was, annoying
instance : SemigroupalPreadditive (ModuleCat R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    apply tensor_ext'
    intro x y
    simp only [SemigroupalCategory.whiskerLeft_apply]
    exact TensorProduct.tmul_zero _ _
  · intros
    apply tensor_ext'
    intro x y
    simp only [SemigroupalCategory.whiskerRight_apply]
    exact TensorProduct.zero_tmul _ _
  · intros
    apply tensor_ext'
    intro x y
    simp only [whiskerLeft_apply]
    exact TensorProduct.tmul_add _ _ _
  · intros
    apply tensor_ext'
    intro x y
    simp only [whiskerRight_apply]
    exact TensorProduct.add_tmul _ _ _

-- Porting note: simp wasn't firing but rw was, annoying
instance : SemigroupalLinear R (ModuleCat R) := by
  refine ⟨?_, ?_⟩
  · intros
    apply tensor_ext'
    intro x y
    simp only [whiskerLeft_apply]
    exact TensorProduct.tmul_smul _ _ _
  · intros
    apply tensor_ext'
    intro x y
    simp only [whiskerRight_apply]
    rw [LinearMap.smul_apply, TensorProduct.smul_tmul]
    exact TensorProduct.tmul_smul _ _ _

namespace MonoidalCategory

@[simps (config := .lemmasOnly) tensorUnit leftUnitor rightUnitor]
instance (priority := high) instMonoidalCategoryStruct :
    MonoidalCategoryStruct (ModuleCat.{u} R) where
  tensorUnit := ModuleCat.of R R
  leftUnitor M := (TensorProduct.lid R M).toModuleIso.trans (ofSelfIso M)
  rightUnitor M := (TensorProduct.rid R M).toModuleIso.trans (ofSelfIso M)

open scoped MonoidalCategory

@[simp]
theorem leftUnitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (ModuleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
theorem leftUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (ModuleCat.{u} R) ⊗ M) m = (1 : R) ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

@[simp]
theorem rightUnitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (ModuleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
theorem rightUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (ModuleCat.{u} R)) m = m ⊗ₜ[R] (1 : R) :=
  TensorProduct.rid_symm_apply m

@[ext]
theorem ext_tensorUnit {M : ModuleCat.{u} R} (f g : 𝟙_ (ModuleCat R) ⟶ M)
    (h : f (1 : R) = g (1 : R)) : f = g :=
  LinearMap.ext_ring h

instance (priority := high) instMonoidalCategory : MonoidalCategory (ModuleCat.{u} R) :=
{ ModuleCat.semigroupalCategory with
  tensorUnit := 𝟙_ (ModuleCat R)
  leftUnitor := λ_
  rightUnitor := ρ_
  leftUnitor_naturality := fun _ => tensor_ext_right fun _ => by ext; simp
  rightUnitor_naturality :=fun _ => tensor_ext_left fun _ => by ext; simp
  triangle := fun _ _ => tensor_ext_threefold fun _ _ _ => by
    simp only [coe_comp, Function.comp_apply, associator_hom_apply, whiskerRight_apply,
      rightUnitor_hom_apply]
    rw [whiskerLeft_apply]
    simpa using TensorProduct.smul_tmul' _ _ _ }

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
instance : CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u) :=
  inferInstanceAs <| CommRing R

namespace Max

@[simps (config := .lemmasOnly) tensorUnit leftUnitor rightUnitor]
instance (priority := low) instMonoidalCategoryStruct :
    MonoidalCategoryStruct (ModuleCat R) where
  tensorUnit := ModuleCat.of R <| ULift R
  leftUnitor X := (ULift.moduleEquiv.rTensor X ≪≫ₗ TensorProduct.lid R X).toModuleIso
  rightUnitor X := (ULift.moduleEquiv.lTensor X ≪≫ₗ TensorProduct.rid R X).toModuleIso

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
instance : CommRing (𝟙_ (ModuleCat.{max v u} R)) :=
  inferInstanceAs <| CommRing (ULift R)

open scoped MonoidalCategory

@[simp]
theorem leftUnitor_hom_apply {M : ModuleCat.{max v u} R} (r : ULift R) (m : M) :
    (λ_ M).hom (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
theorem leftUnitor_inv_apply {M : ModuleCat.{max v u} R} (m : M) :
    (λ_ M).inv m = (1 : ULift R) ⊗ₜ[R] m :=
  rfl

@[simp]
theorem rightUnitor_hom_apply {M : ModuleCat.{max v u} R} (m : M) (r : ULift R) :
    (ρ_ M).hom (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
theorem rightUnitor_inv_apply {M : ModuleCat.{max v u} R} (m : M) :
    (ρ_ M).inv m = m ⊗ₜ[R] (1 : ULift R) :=
  rfl

@[ext]
theorem ext_tensorUnit {M : ModuleCat.{max v u} R}
    {f g : 𝟙_ (ModuleCat.{max v u} R) ⟶ M}
    (h : f (1 : ULift R) = g (1 : ULift R)) : f = g := by
  have : f ∘ₗ ULift.moduleEquiv.symm.toLinearMap = g ∘ₗ ULift.moduleEquiv.symm.toLinearMap :=
    LinearMap.ext_ring h
  ext x
  exact congr($this x.down)

instance (priority := low) instMonoidalCategory : MonoidalCategory (ModuleCat.{max v u} R) :=
{ ModuleCat.semigroupalCategory with
  tensorUnit := 𝟙_ (ModuleCat.{max v u} R)
  leftUnitor := λ_
  rightUnitor := ρ_
  leftUnitor_naturality := fun _ => tensor_ext_right fun _ => by
    apply ext_tensorUnit
    simp
  rightUnitor_naturality :=fun _ => tensor_ext_left fun _ => by
    apply ext_tensorUnit
    simp
  triangle := fun _ _ => tensor_ext_threefold fun _ _ _ => by
    simp only [coe_comp, Function.comp_apply, associator_hom_apply, whiskerRight_apply,
      rightUnitor_hom_apply]
    rw [whiskerLeft_apply]
    simpa using TensorProduct.smul_tmul' _ _ _ }

end Max

variable (R)

@[simps]
def uliftFunctor : ModuleCat.{u} R ⥤ ModuleCat.{max v u} R where
  obj M := ModuleCat.of R <| ULift M
  map {M N} f := ModuleCat.ofHom <|
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap

instance : (uliftFunctor R).Faithful where
  map_injective h := LinearMap.ext fun x => congr(ULift.down <| $h <| ULift.up x)

instance : (uliftFunctor R).Full where
  map_surjective := by
    intro M N f
    use ULift.moduleEquiv.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.symm.toLinearMap
    ext x
    rfl

@[simps]
def uliftMonoidalFunctor : MonoidalFunctor (ModuleCat R) (ModuleCat.{max v u} R) where
  toFunctor := uliftFunctor R
  μ X Y := (TensorProduct.congr ULift.moduleEquiv ULift.moduleEquiv
    ≪≫ₗ ULift.moduleEquiv.symm).toModuleIso.hom
  μ_natural_left _ _ := by apply tensor_ext'; intros; rfl
  μ_natural_right _ _ := by apply tensor_ext'; intros; rfl
  associativity _ _ _ := by apply tensor_ext_threefold; intros; rfl
  ε := 𝟙 _
  left_unitality _ := by apply tensor_ext'; intros; rfl
  right_unitality _ := by apply tensor_ext'; intros; rfl

end MonoidalCategory

end ModuleCat
