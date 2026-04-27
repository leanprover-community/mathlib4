/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Transport

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

@[expose] public section

universe v w x u

open CategoryTheory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

namespace MonoidalCategory

-- The definitions inside this namespace are essentially private.
-- After we build the `MonoidalCategory (Module R)` instance,
-- you should use that API.
open TensorProduct

attribute [local ext] TensorProduct.ext

/-- (implementation) tensor product of R-modules -/
def tensorObj (M N : SemimoduleCat R) : SemimoduleCat R :=
  SemimoduleCat.of R (M ⊗[R] N)

/-- (implementation) tensor product of morphisms R-modules -/
def tensorHom {M N M' N' : SemimoduleCat R} (f : M ⟶ N) (g : M' ⟶ N') :
    tensorObj M M' ⟶ tensorObj N N' :=
  ofHom <| TensorProduct.map f.hom g.hom

/-- (implementation) left whiskering for R-modules -/
def whiskerLeft (M : SemimoduleCat R) {N₁ N₂ : SemimoduleCat R} (f : N₁ ⟶ N₂) :
    tensorObj M N₁ ⟶ tensorObj M N₂ :=
  ofHom <| f.hom.lTensor M

/-- (implementation) right whiskering for R-modules -/
def whiskerRight {M₁ M₂ : SemimoduleCat R} (f : M₁ ⟶ M₂) (N : SemimoduleCat R) :
    tensorObj M₁ N ⟶ tensorObj M₂ N :=
  ofHom <| f.hom.rTensor N

theorem id_tensorHom_id (M N : SemimoduleCat R) :
    tensorHom (𝟙 M) (𝟙 N) = 𝟙 (SemimoduleCat.of R (M ⊗ N)) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

theorem tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): even with high priority `ext` fails to find this.
  apply TensorProduct.ext
  rfl

/-- (implementation) the associator for R-modules -/
def associator (M : SemimoduleCat.{v} R) (N : SemimoduleCat.{w} R) (K : SemimoduleCat.{x} R) :
    tensorObj (tensorObj M N) K ≅ tensorObj M (tensorObj N K) :=
  (TensorProduct.assoc R M N K).toModuleIsoₛ

/-- (implementation) the left unitor for R-modules -/
def leftUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (R ⊗[R] M) ≅ M :=
  (TensorProduct.lid R M).toModuleIsoₛ

/-- (implementation) the right unitor for R-modules -/
def rightUnitor (M : SemimoduleCat.{u} R) : SemimoduleCat.of R (M ⊗[R] R) ≅ M :=
  (TensorProduct.rid R M).toModuleIsoₛ

@[simps -isSimp]
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (SemimoduleCat.{u} R) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorHom := tensorHom
  tensorUnit := SemimoduleCat.of R R
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SemimoduleCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y z
  rfl

theorem pentagon (W X Y Z : SemimoduleCat R) :
    whiskerRight (associator W X Y).hom Z ≫
        (associator W (tensorObj X Y) Z).hom ≫ whiskerLeft W (associator X Y Z).hom =
      (associator (tensorObj W X) Y Z).hom ≫ (associator W X (tensorObj Y Z)).hom := by
  ext : 1
  apply TensorProduct.ext_fourfold
  intro w x y z
  rfl

theorem leftUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) :
    tensorHom (𝟙 (SemimoduleCat.of R R)) f ≫ (leftUnitor N).hom = (leftUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, leftUnitor]

theorem rightUnitor_naturality {M N : SemimoduleCat R} (f : M ⟶ N) :
    tensorHom f (𝟙 (SemimoduleCat.of R R)) ≫ (rightUnitor N).hom = (rightUnitor M).hom ≫ f := by
  ext : 1
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): broken ext
  apply TensorProduct.ext
  ext
  simp [tensorHom, tensorObj, rightUnitor]

theorem triangle (M N : SemimoduleCat.{u} R) :
    (associator M (SemimoduleCat.of R R) N).hom ≫ tensorHom (𝟙 M) (leftUnitor N).hom =
      tensorHom (rightUnitor M).hom (𝟙 N) := by
  ext : 1
  apply TensorProduct.ext_threefold
  intro x y
  exact TensorProduct.tmul_smul _ _

end MonoidalCategory

open MonoidalCategory

instance monoidalCategory : MonoidalCategory (SemimoduleCat.{u} R) := MonoidalCategory.ofTensorHom
  (id_tensorHom_id := fun M N ↦ id_tensorHom_id M N)
  (tensorHom_comp_tensorHom := fun f g h ↦ MonoidalCategory.tensorHom_comp_tensorHom f g h)
  (associator_naturality := fun f g h ↦ MonoidalCategory.associator_naturality f g h)
  (leftUnitor_naturality := fun f ↦ MonoidalCategory.leftUnitor_naturality f)
  (rightUnitor_naturality := fun f ↦ rightUnitor_naturality f)
  (pentagon := fun M N K L ↦ pentagon M N K L)
  (triangle := fun M N ↦ triangle M N)

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative semiring. -/
instance : CommSemiring ((𝟙_ (SemimoduleCat.{u} R) : SemimoduleCat.{u} R) : Type u) :=
  inferInstanceAs <| CommSemiring R

theorem hom_tensorHom {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom :=
  rfl

theorem hom_whiskerLeft (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L :=
  rfl

theorem hom_whiskerRight {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R) :
    (f ▷ N).hom = f.hom.rTensor N :=
  rfl

theorem hom_hom_leftUnitor {M : SemimoduleCat.{u} R} :
    (λ_ M).hom.hom = (TensorProduct.lid _ _).toLinearMap :=
  rfl

theorem hom_inv_leftUnitor {M : SemimoduleCat.{u} R} :
    (λ_ M).inv.hom = (TensorProduct.lid _ _).symm.toLinearMap :=
  rfl

theorem hom_hom_rightUnitor {M : SemimoduleCat.{u} R} :
    (ρ_ M).hom.hom = (TensorProduct.rid _ _).toLinearMap :=
  rfl

theorem hom_inv_rightUnitor {M : SemimoduleCat.{u} R} :
    (ρ_ M).inv.hom = (TensorProduct.rid _ _).symm.toLinearMap :=
  rfl

theorem hom_hom_associator {M N K : SemimoduleCat.{u} R} :
    (α_ M N K).hom.hom = (TensorProduct.assoc _ _ _ _).toLinearMap :=
  rfl

theorem hom_inv_associator {M N K : SemimoduleCat.{u} R} :
    (α_ M N K).inv.hom = (TensorProduct.assoc _ _ _ _).symm.toLinearMap :=
  rfl

namespace MonoidalCategory

@[simp]
theorem tensorHom_tmul {K L M N : SemimoduleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ₘ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
  rfl

@[simp]
theorem whiskerLeft_apply (L : SemimoduleCat.{u} R) {M N : SemimoduleCat.{u} R} (f : M ⟶ N)
    (l : L) (m : M) :
    (L ◁ f) (l ⊗ₜ m) = l ⊗ₜ f m :=
  rfl

@[simp]
theorem whiskerRight_apply {L M : SemimoduleCat.{u} R} (f : L ⟶ M) (N : SemimoduleCat.{u} R)
    (l : L) (n : N) :
    (f ▷ N) (l ⊗ₜ n) = f l ⊗ₜ n :=
  rfl

@[simp]
theorem leftUnitor_hom_apply {M : SemimoduleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (SemimoduleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
theorem leftUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (SemimoduleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

@[simp]
theorem rightUnitor_hom_apply {M : SemimoduleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (SemimoduleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
theorem rightUnitor_inv_apply {M : SemimoduleCat.{u} R} (m : M) :
    ((ρ_ M).inv : M ⟶ M ⊗ 𝟙_ (SemimoduleCat.{u} R)) m = m ⊗ₜ[R] 1 :=
  TensorProduct.rid_symm_apply m

@[simp]
theorem associator_hom_apply {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).hom : (M ⊗ N) ⊗ K ⟶ M ⊗ N ⊗ K) (m ⊗ₜ n ⊗ₜ k) = m ⊗ₜ (n ⊗ₜ k) :=
  rfl

@[simp]
theorem associator_inv_apply {M N K : SemimoduleCat.{u} R} (m : M) (n : N) (k : K) :
    ((α_ M N K).inv : M ⊗ N ⊗ K ⟶ (M ⊗ N) ⊗ K) (m ⊗ₜ (n ⊗ₜ k)) = m ⊗ₜ n ⊗ₜ k :=
  rfl

variable {M₁ M₂ M₃ M₄ : SemimoduleCat.{u} R}

section

variable (f : M₁ → M₂ → M₃) (h₁ : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : ∀ (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : ∀ (a : R) m n, f m (a • n) = a • f m n)

/-- Construct for morphisms from the tensor product of two objects in `SemimoduleCat`. -/
def tensorLift : M₁ ⊗ M₂ ⟶ M₃ :=
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

end SemimoduleCat

namespace ModuleCat

variable {R : Type u} [CommRing R]

@[simps -isSimp]
instance MonoidalCategory.instMonoidalCategoryStruct :
    MonoidalCategoryStruct (ModuleCat.{u} R) where
  tensorObj M N := of R (TensorProduct R M N)
  whiskerLeft M _ _ f := ofHom <| f.hom.lTensor M
  whiskerRight f M := ofHom <| f.hom.rTensor M
  tensorHom f g := ofHom <| TensorProduct.map f.hom g.hom
  tensorUnit := of R R
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M := (TensorProduct.lid R M).toModuleIso
  rightUnitor M := (TensorProduct.rid R M).toModuleIso

instance monoidalCategory : MonoidalCategory (ModuleCat.{u} R) :=
  Monoidal.induced equivalenceSemimoduleCat.functor
  { μIso _ _ := .refl _
    εIso := .refl _
    associator_eq _ _ _ := by ext1; exact TensorProduct.ext (TensorProduct.ext rfl)
    leftUnitor_eq _ := by ext1; exact TensorProduct.ext rfl
    rightUnitor_eq _ := by ext1; exact TensorProduct.ext rfl }

open MonoidalCategory

/-- Remind ourselves that the monoidal unit, being just `R`, is still a commutative ring. -/
instance : CommRing ((𝟙_ (ModuleCat.{u} R) : ModuleCat.{u} R) : Type u) :=
  inferInstanceAs <| CommRing R

theorem hom_tensorHom {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).hom = TensorProduct.map f.hom g.hom :=
  rfl

theorem hom_whiskerLeft (L : ModuleCat.{u} R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).hom = f.hom.lTensor L :=
  rfl

theorem hom_whiskerRight {L M : ModuleCat.{u} R} (f : L ⟶ M) (N : ModuleCat.{u} R) :
    (f ▷ N).hom = f.hom.rTensor N :=
  rfl

theorem hom_hom_leftUnitor {M : ModuleCat.{u} R} :
    (λ_ M).hom.hom = (TensorProduct.lid _ _).toLinearMap :=
  rfl

theorem hom_inv_leftUnitor {M : ModuleCat.{u} R} :
    (λ_ M).inv.hom = (TensorProduct.lid _ _).symm.toLinearMap :=
  rfl

theorem hom_hom_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).hom.hom = (TensorProduct.rid _ _).toLinearMap :=
  rfl

theorem hom_inv_rightUnitor {M : ModuleCat.{u} R} :
    (ρ_ M).inv.hom = (TensorProduct.rid _ _).symm.toLinearMap :=
  rfl

theorem hom_hom_associator {M N K : ModuleCat.{u} R} :
    (α_ M N K).hom.hom = (TensorProduct.assoc _ _ _ _).toLinearMap :=
  rfl

theorem hom_inv_associator {M N K : ModuleCat.{u} R} :
    (α_ M N K).inv.hom = (TensorProduct.assoc _ _ _ _).symm.toLinearMap :=
  rfl

namespace MonoidalCategory

@[deprecated (since := "2025-10-29")] alias tensorObj := tensorObj_carrier
@[deprecated (since := "2025-10-29")] alias tensorObj_def := tensorObj_carrier

@[simp]
theorem tensorHom_tmul {K L M N : ModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) (k : K) (m : M) :
    (f ⊗ₘ g) (k ⊗ₜ m) = f k ⊗ₜ g m :=
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

@[simp]
theorem leftUnitor_hom_apply {M : ModuleCat.{u} R} (r : R) (m : M) :
    ((λ_ M).hom : 𝟙_ (ModuleCat R) ⊗ M ⟶ M) (r ⊗ₜ[R] m) = r • m :=
  TensorProduct.lid_tmul m r

@[simp]
theorem leftUnitor_inv_apply {M : ModuleCat.{u} R} (m : M) :
    ((λ_ M).inv : M ⟶ 𝟙_ (ModuleCat.{u} R) ⊗ M) m = 1 ⊗ₜ[R] m :=
  TensorProduct.lid_symm_apply m

@[simp]
theorem rightUnitor_hom_apply {M : ModuleCat.{u} R} (m : M) (r : R) :
    ((ρ_ M).hom : M ⊗ 𝟙_ (ModuleCat R) ⟶ M) (m ⊗ₜ r) = r • m :=
  TensorProduct.rid_tmul m r

@[simp]
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
def tensorLift : M₁ ⊗ M₂ ⟶ M₃ :=
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

instance : MonoidalPreadditive (ModuleCat.{u} R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, hom_zero, LinearMap.zero_apply]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [MonoidalCategory.whiskerLeft_apply]
    simp
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, hom_zero, LinearMap.zero_apply, ]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [MonoidalCategory.whiskerRight_apply]
    simp
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, hom_add, LinearMap.add_apply]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [MonoidalCategory.whiskerLeft_apply, MonoidalCategory.whiskerLeft_apply]
    erw [MonoidalCategory.whiskerLeft_apply]
    simp [TensorProduct.tmul_add]
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, hom_add, LinearMap.add_apply]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [MonoidalCategory.whiskerRight_apply, MonoidalCategory.whiskerRight_apply]
    erw [MonoidalCategory.whiskerRight_apply]
    simp [TensorProduct.add_tmul]

set_option backward.isDefEq.respectTransparency false in
instance : MonoidalLinear R (ModuleCat.{u} R) := by
  refine ⟨?_, ?_⟩
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, hom_smul, LinearMap.smul_apply]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [MonoidalCategory.whiskerLeft_apply, MonoidalCategory.whiskerLeft_apply]
    simp
  · intros
    ext : 1
    refine TensorProduct.ext (LinearMap.ext fun x => LinearMap.ext fun y => ?_)
    simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, hom_smul, LinearMap.smul_apply]
    -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
    erw [MonoidalCategory.whiskerRight_apply, MonoidalCategory.whiskerRight_apply]
    simp [TensorProduct.smul_tmul, TensorProduct.tmul_smul]

@[simp] lemma ofHom₂_compr₂ {M N P Q : ModuleCat.{u} R} (f : M →ₗ[R] N →ₗ[R] P) (g : P →ₗ[R] Q) :
    ofHom₂ (f.compr₂ g) = ofHom₂ f ≫ ofHom (Linear.rightComp R _ (ofHom g)) := rfl

end ModuleCat
