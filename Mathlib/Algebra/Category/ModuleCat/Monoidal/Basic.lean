/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
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

namespace MonoidalCategory

-- The definitions inside this namespace are essentially private.
-- After we build the `MonoidalCategory (Module R)` instance,
-- you should use that API.
open TensorProduct

attribute [local ext] TensorProduct.ext

/-- (implementation) tensor product of R-modules -/
def tensorObj (M N : ModuleCat R) : ModuleCat R :=
  ModuleCat.of R (M ⊗[R] N)

/-- (implementation) tensor product of morphisms R-modules -/
def tensorHom {M N M' N' : ModuleCat R} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
  ofHom <| TensorProduct.map f.hom g.hom

/-- (implementation) left whiskering for R-modules -/
def whiskerLeft (M : ModuleCat R) {N₁ N₂ : ModuleCat R} (f : N₁ ⟶ N₂) :
    tensorObj M N₁ ⟶ tensorObj M N₂ :=
  ofHom <| f.hom.lTensor M

/-- (implementation) right whiskering for R-modules -/
def whiskerRight {M₁ M₂ : ModuleCat R} (f : M₁ ⟶ M₂) (N : ModuleCat R) :
    tensorObj M₁ N ⟶ tensorObj M₂ N :=
  ofHom <| f.hom.rTensor N

theorem tensor_id (M N : ModuleCat R) : tensorHom (𝟙 M) (𝟙 N) = 𝟙 (ModuleCat.of R (M ⊗ N)) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/pull/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/pull/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

/-- (implementation) the associator for R-modules -/
def associator (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (K : ModuleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIso

/-- (implementation) the left unitor for R-modules -/
def leftUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (R ⊗[R] M) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.lid R M) : of R (R ⊗ M) ≅ of R M).trans (ofSelfIso M)

/-- (implementation) the right unitor for R-modules -/
def rightUnitor (M : ModuleCat.{u} R) : ModuleCat.of R (M ⊗[R] R) ≅ M :=
  (LinearEquiv.toModuleIso (TensorProduct.rid R M) : of R (M ⊗ R) ≅ of R M).trans (ofSelfIso M)

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (ModuleCat.{u} R) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom f g := ofHom <| TensorProduct.map f.hom g.hom
  tensorUnit := ModuleCat.of R R
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

open scoped MonoidalCategory

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : ModuleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

theorem pentagon (W X Y Z : ModuleCat R) :
    whiskerRight (associator W X Y).hom Z ≫
        (associator W (tensorObj X Y) Z).hom ≫ whiskerLeft W (associator X Y Z).hom =
      (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  ext : 1
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

theorem leftUnitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom (𝟙 (ModuleCat.of R R)) f ≫ (leftUnitor N).hom = (leftUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/pull/11041): broken ext
  apply TensorProduct.ext
  ext x
  dsimp
  erw [TensorProduct.lid_tmul, TensorProduct.lid_tmul]
  rw [LinearMap.map_smul]
  rfl

theorem rightUnitor_naturality {M N : ModuleCat R} (f : M ⟶ N) :
    tensorHom f (𝟙 (ModuleCat.of R R)) ≫ (rightUnitor N).hom = (rightUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/pull/11041): broken ext
  apply TensorProduct.ext
  ext x
  dsimp
  erw [TensorProduct.rid_tmul, TensorProduct.rid_tmul]
  rw [LinearMap.map_smul]
  rfl

theorem triangle (M N : ModuleCat.{u} R) :
    (associator M (ModuleCat.of R R) N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom =
      tensorHom (rightUnitor M).hom (𝟙 N) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  -- Porting note (https://github.com/leanprover-community/mathlib4/pull/10934): used to be dsimp [tensorHom, associator]
  change x ⊗ₜ[R] ((leftUnitor N).hom) (y ⊗ₜ[R] z) = ((rightUnitor M).hom) (x ⊗ₜ[R] y) ⊗ₜ[R] z
  erw [TensorProduct.lid_tmul, TensorProduct.rid_tmul]
  exact (TensorProduct.smul_tmul _ _ _).symm

end MonoidalCategory

open MonoidalCategory

instance monoidalCategory : MonoidalCategory (ModuleCat.{u} R) := MonoidalCategory.ofTensorHom
  (tensor_id := fun M N ↦ tensor_id M N)
  (tensor_comp := fun f g h ↦ MonoidalCategory.tensor_comp f g h)
  (associator_naturality := fun f g h ↦ MonoidalCategory.associator_naturality f g h)
  (leftUnitor_naturality := fun f ↦ MonoidalCategory.leftUnitor_naturality f)
  (rightUnitor_naturality := fun f ↦ rightUnitor_naturality f)
  (pentagon := fun M N K L ↦ pentagon M N K L)
  (triangle := fun M N ↦ triangle M N)

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
instance : CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u) :=
  inferInstanceAs <| CommRing R

@[simp]
theorem carrier_tensorObj {M N : ModuleCat.{u} R} :
    (M ⊗ N).carrier = TensorProduct R M.carrier N.carrier :=
  rfl

@[simp]
theorem carrier_tensorUnit : (𝟙_ _ : ModuleCat.{u} R).carrier = R :=
  rfl

@[simp]
theorem hom_tensorHom {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ g).hom = TensorProduct.map f.hom g.hom :=
  rfl

@[simp]
theorem hom_whiskerLeft (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L :=
  rfl

@[simp]
theorem hom_whiskerRight {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R) :
    (f ▷ N).hom = f.hom.rTensor N :=
  rfl

@[simp]
theorem hom_hom_leftUnitor {M : ModuleCat.{u} R} :
    (λ_ M).hom.hom = (TensorProduct.lid _ _).toLinearMap :=
  rfl

@[simp]
theorem hom_inv_leftUnitor {M : ModuleCat.{u} R} :
    (λ_ M).inv.hom = (TensorProduct.lid _ _).symm.toLinearMap :=
  rfl

@[simp]
theorem hom_hom_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).hom.hom = (TensorProduct.rid _ _).toLinearMap :=
  rfl

@[simp]
theorem hom_inv_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).inv.hom = (TensorProduct.rid _ _).symm.toLinearMap :=
  rfl

@[simp]
theorem hom_hom_associator {M N K : ModuleCat.{u} R} :
    (α_ M N K).hom.hom = (TensorProduct.assoc _ _ _ _).toLinearMap :=
  rfl

@[simp]
theorem hom_inv_associator {M N K : ModuleCat.{u} R} :
    (α_ M N K).inv.hom = (TensorProduct.assoc _ _ _ _).symm.toLinearMap :=
  rfl

namespace MonoidalCategory

@[simp]
theorem tensorHom_tmul {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ g) (k ⊗ₜ m) = f k ⊗ₜ g m := by
  rfl

@[simp]
theorem whiskerLeft_apply (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l ⊗ₜ m) = l ⊗ₜ f m :=
  rfl

@[simp]
theorem whiskerRight_apply {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R)
    (l : L) (n : N) :
    (f ▷ N) (l ⊗ₜ n) = f l ⊗ₜ n :=
  rfl

theorem leftUnitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (ModuleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

theorem leftUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (ModuleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

theorem rightUnitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (ModuleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r

theorem rightUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (ModuleCat.{u} R)) m = m ⊗ₜ[R] 1 :=
  TensorProduct.rid_symm_apply m

@[simp]
theorem associator_hom_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ N ⊗ K) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl

@[simp]
theorem associator_inv_apply {M N K : ModuleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl

variable {M₁ M₂ M₃ M₄ : ModuleCat.{u} R}

section

variable (f : M₁ → M₂ → M₃) (h₁ : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : ∀ (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : ∀ (a : R) m n, f m (a • n) = a • f m n)

/-- Construct for morphisms from the tensor product of two objects in `ModuleCat`. -/
noncomputable def tensorLift : M₁ ⊗ M₂ ⟶ M₃ :=
  ofHom <| TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]
lemma tensorLift_tmul (m : M₁) (n : M₂) :
    tensorLift f h₁ h₂ h₃ h₄ (m ⊗ₜ n) = f m n := rfl

end

lemma tensor_ext {f g : M₁ ⊗ M₂ ⟶ M₃} (h : ∀ m n, f.hom (m ⊗ₜ n) = g.hom (m ⊗ₜ n)) :
    f = g :=
  hom_ext <| TensorProduct.ext (by ext; apply h)

/-- Extensionality lemma for morphisms from a module of the form `(M₁ ⊗ M₂) ⊗ M₃`. -/
lemma tensor_ext₃' {f g : (M₁ ⊗ M₂) ⊗ M₃ ⟶ M₄}
    (h : ∀ m₁ m₂ m₃, f (m₁ ⊗ₜ m₂ ⊗ₜ m₃) = g (m₁ ⊗ₜ m₂ ⊗ₜ m₃)) :
    f = g :=
  hom_ext <| TensorProduct.ext_threefold h

/-- Extensionality lemma for morphisms from a module of the form `M₁ ⊗ (M₂ ⊗ M₃)`. -/
lemma tensor_ext₃ {f g : M₁ ⊗ (M₂ ⊗ M₃) ⟶ M₄}
    (h : ∀ m₁ m₂ m₃, f (m₁ ⊗ₜ (m₂ ⊗ₜ m₃)) = g (m₁ ⊗ₜ (m₂ ⊗ₜ m₃))) :
    f = g := by
  rw [← cancel_epi (α_ _ _ _).hom]
  exact tensor_ext₃' h

end MonoidalCategory

open Opposite

instance : MonoidalPreadditive (ModuleCat.{u} R) where
  whiskerLeft_zero {_ _ _} := by ext : 1; simp
  zero_whiskerRight {_ _ _} := by ext : 1; simp
  whiskerLeft_add _ _ := by ext : 1; simp
  add_whiskerRight _ _ := by ext : 1; simp

instance : MonoidalLinear R (ModuleCat.{u} R) where
  whiskerLeft_smul _ _ _ _ _ := by ext : 1; simp
  smul_whiskerRight _ _ _ _ _ := by ext : 1; simp

@[simp] lemma ofHom₂_compr₂ {M N P Q : ModuleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) (g : P →ₗ[R] Q):
    ofHom₂ (f.compr₂ g) = ofHom₂ f ≫ ofHom (Linear.rightComp R _ (ofHom g)) := rfl

end ModuleCat
