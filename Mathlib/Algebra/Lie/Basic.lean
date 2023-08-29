/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Module.Equiv
import Mathlib.Data.Bracket
import Mathlib.LinearAlgebra.Basic

#align_import algebra.lie.basic from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

/-!
# Lie algebras

This file defines Lie rings and Lie algebras over a commutative ring together with their
modules, morphisms and equivalences, as well as various lemmas to make these definitions usable.

## Main definitions

  * `LieRing`
  * `LieAlgebra`
  * `LieRingModule`
  * `LieModule`
  * `LieHom`
  * `LieEquiv`
  * `LieModuleHom`
  * `LieModuleEquiv`

## Notation

Working over a fixed commutative ring `R`, we introduce the notations:
 * `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
 * `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
 * `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
 * `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

## Tagsc

lie bracket, jacobi identity, lie ring, lie algebra, lie module
-/


universe u v w w₁ w₂

open Function

/-- A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. -/
class LieRing (L : Type v) extends AddCommGroup L, Bracket L L where
  /-- A Lie ring bracket is additive in its first component. -/
  protected add_lie : ∀ x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
  /-- A Lie ring bracket is additive in its second component. -/
  protected lie_add : ∀ x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
  /-- A Lie ring bracket vanishes on the diagonal in L × L. -/
  protected lie_self : ∀ x : L, ⁅x, x⁆ = 0
  /-- A Lie ring bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : ∀ x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆
#align lie_ring LieRing

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
class LieAlgebra (R : Type u) (L : Type v) [CommRing R] [LieRing L] extends Module R L where
  /-- A Lie algebra bracket is compatible with scalar multiplication in its second argument.

  The compatibility in the first argument is not a class property, but follows since every
  Lie algebra has a natural Lie module action on itself, see `LieModule`. -/
  protected lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆
#align lie_algebra LieAlgebra

/-- A Lie ring module is an additive group, together with an additive action of a
Lie ring on this group, such that the Lie bracket acts as the commutator of endomorphisms.
(For representations of Lie *algebras* see `LieModule`.) -/
class LieRingModule (L : Type v) (M : Type w) [LieRing L] [AddCommGroup M] extends Bracket L M where
  /-- A Lie ring module bracket is additive in its first component. -/
  protected add_lie : ∀ (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
  /-- A Lie ring module bracket is additive in its second component. -/
  protected lie_add : ∀ (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
  /-- A Lie ring module bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : ∀ (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
#align lie_ring_module LieRingModule

/-- A Lie module is a module over a commutative ring, together with a linear action of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endomorphisms. -/
class LieModule (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] : Prop where
  /-- A Lie module bracket is compatible with scalar multiplication in its first argument. -/
  protected smul_lie : ∀ (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆
  /-- A Lie module bracket is compatible with scalar multiplication in its second argument. -/
  protected lie_smul : ∀ (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆
#align lie_module LieModule

section BasicProperties

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

variable (t : R) (x y z : L) (m n : M)

@[simp]
theorem add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆ :=
  LieRingModule.add_lie x y m
#align add_lie add_lie

@[simp]
theorem lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆ :=
  LieRingModule.lie_add x m n
#align lie_add lie_add

@[simp]
theorem smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆ :=
  LieModule.smul_lie t x m
#align smul_lie smul_lie

@[simp]
theorem lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆ :=
  LieModule.lie_smul t x m
#align lie_smul lie_smul

theorem leibniz_lie : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ :=
  LieRingModule.leibniz_lie x y m
#align leibniz_lie leibniz_lie

@[simp]
theorem lie_zero : ⁅x, 0⁆ = (0 : M) :=
  (AddMonoidHom.mk' _ (lie_add x)).map_zero
#align lie_zero lie_zero

@[simp]
theorem zero_lie : ⁅(0 : L), m⁆ = 0 :=
  (AddMonoidHom.mk' (fun x : L => ⁅x, m⁆) fun x y => add_lie x y m).map_zero
#align zero_lie zero_lie

@[simp]
theorem lie_self : ⁅x, x⁆ = 0 :=
  LieRing.lie_self x
#align lie_self lie_self

instance lieRingSelfModule : LieRingModule L L :=
  { (inferInstance : LieRing L) with }
#align lie_ring_self_module lieRingSelfModule

@[simp]
theorem lie_skew : -⁅y, x⁆ = ⁅x, y⁆ := by
  have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0 := by rw [← lie_add]; apply lie_self
  -- ⊢ -⁅y, x⁆ = ⁅x, y⁆
  simpa [neg_eq_iff_add_eq_zero] using h
  -- 🎉 no goals
#align lie_skew lie_skew

/-- Every Lie algebra is a module over itself. -/
instance lieAlgebraSelfModule : LieModule R L L
    where
  smul_lie t x m := by rw [← lie_skew, ← lie_skew x m, LieAlgebra.lie_smul, smul_neg]
                       -- 🎉 no goals
  lie_smul := by apply LieAlgebra.lie_smul
                 -- 🎉 no goals
#align lie_algebra_self_module lieAlgebraSelfModule

@[simp]
theorem neg_lie : ⁅-x, m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← add_lie]
  -- ⊢ ⁅-x + x, m⁆ = 0
  simp
  -- 🎉 no goals
#align neg_lie neg_lie

@[simp]
theorem lie_neg : ⁅x, -m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← lie_add]
  -- ⊢ ⁅x, -m + m⁆ = 0
  simp
  -- 🎉 no goals
#align lie_neg lie_neg

@[simp]
theorem sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by simp [sub_eq_add_neg]
                                                     -- 🎉 no goals
#align sub_lie sub_lie

@[simp]
theorem lie_sub : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by simp [sub_eq_add_neg]
                                                     -- 🎉 no goals
#align lie_sub lie_sub

@[simp]
theorem nsmul_lie (n : ℕ) : ⁅n • x, m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul ⟨⟨fun x : L => ⁅x, m⁆, zero_lie m⟩, fun _ _ => add_lie _ _ _⟩ _ _
#align nsmul_lie nsmul_lie

@[simp]
theorem lie_nsmul (n : ℕ) : ⁅x, n • m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul ⟨⟨fun m : M => ⁅x, m⁆, lie_zero x⟩, fun _ _ => lie_add _ _ _⟩ _ _
#align lie_nsmul lie_nsmul

@[simp]
theorem zsmul_lie (a : ℤ) : ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul ⟨⟨fun x : L => ⁅x, m⁆, zero_lie m⟩, fun _ _ => add_lie _ _ _⟩ _ _
#align zsmul_lie zsmul_lie

@[simp]
theorem lie_zsmul (a : ℤ) : ⁅x, a • m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul ⟨⟨fun m : M => ⁅x, m⁆, lie_zero x⟩, fun _ _ => lie_add _ _ _⟩ _ _
#align lie_zsmul lie_zsmul

@[simp]
theorem lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ := by rw [leibniz_lie, add_sub_cancel]
                                                                -- 🎉 no goals
#align lie_lie lie_lie

theorem lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  rw [← neg_neg ⁅x, y⁆, lie_neg z, lie_skew y x, ← lie_skew, lie_lie]
  -- ⊢ -(⁅y, ⁅z, x⁆⁆ - ⁅z, ⁅y, x⁆⁆) + ⁅y, ⁅z, x⁆⁆ + -⁅z, ⁅y, x⁆⁆ = 0
  abel
  -- 🎉 no goals
  -- 🎉 no goals
#align lie_jacobi lie_jacobi

instance LieRing.intLieAlgebra : LieAlgebra ℤ L where lie_smul n x y := lie_zsmul x y n
#align lie_ring.int_lie_algebra LieRing.intLieAlgebra

instance : LieRingModule L (M →ₗ[R] N) where
  bracket x f :=
    { toFun := fun m => ⁅x, f m⁆ - f ⁅x, m⁆
      map_add' := fun m n => by
        simp only [lie_add, LinearMap.map_add]
        -- ⊢ ⁅x, ↑f m⁆ + ⁅x, ↑f n⁆ - (↑f ⁅x, m⁆ + ↑f ⁅x, n⁆) = ⁅x, ↑f m⁆ - ↑f ⁅x, m⁆ + (⁅ …
        abel
        -- 🎉 no goals
        -- 🎉 no goals
      map_smul' := fun t m => by
        simp only [smul_sub, LinearMap.map_smul, lie_smul, RingHom.id_apply] }
        -- 🎉 no goals
  add_lie x y f := by
    ext n
    -- ⊢ ↑⁅x + y, f⁆ n = ↑(⁅x, f⁆ + ⁅y, f⁆) n
    simp only [add_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, LinearMap.map_add]
    -- ⊢ ⁅x, ↑f n⁆ + ⁅y, ↑f n⁆ - (↑f ⁅x, n⁆ + ↑f ⁅y, n⁆) = ⁅x, ↑f n⁆ - ↑f ⁅x, n⁆ + (⁅ …
    abel
    -- 🎉 no goals
    -- 🎉 no goals
  lie_add x f g := by
    ext n
    -- ⊢ ↑⁅x, f + g⁆ n = ↑(⁅x, f⁆ + ⁅x, g⁆) n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, lie_add, LinearMap.add_apply]
    -- ⊢ ⁅x, ↑f n⁆ + ⁅x, ↑g n⁆ - (↑f ⁅x, n⁆ + ↑g ⁅x, n⁆) = ⁅x, ↑f n⁆ - ↑f ⁅x, n⁆ + (⁅ …
    abel
    -- 🎉 no goals
    -- 🎉 no goals
  leibniz_lie x y f := by
    ext n
    -- ⊢ ↑⁅x, ⁅y, f⁆⁆ n = ↑(⁅⁅x, y⁆, f⁆ + ⁅y, ⁅x, f⁆⁆) n
    simp only [lie_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_sub, LinearMap.add_apply,
      lie_sub]
    abel
    -- 🎉 no goals
    -- 🎉 no goals

@[simp]
theorem LieHom.lie_apply (f : M →ₗ[R] N) (x : L) (m : M) : ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆ :=
  rfl
#align lie_hom.lie_apply LieHom.lie_apply

instance : LieModule R L (M →ₗ[R] N)
    where
  smul_lie t x f := by
    ext n
    -- ⊢ ↑⁅t • x, f⁆ n = ↑(t • ⁅x, f⁆) n
    simp only [smul_sub, smul_lie, LinearMap.smul_apply, LieHom.lie_apply, LinearMap.map_smul]
    -- 🎉 no goals
  lie_smul t x f := by
    ext n
    -- ⊢ ↑⁅x, t • f⁆ n = ↑(t • ⁅x, f⁆) n
    simp only [smul_sub, LinearMap.smul_apply, LieHom.lie_apply, lie_smul]
    -- 🎉 no goals

end BasicProperties

/-- A morphism of Lie algebras is a linear map respecting the bracket operations. -/
structure LieHom (R L L': Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L →ₗ[R] L' where
  /-- A morphism of Lie algebras is compatible with brackets. -/
  map_lie' : ∀ {x y : L}, toFun ⁅x, y⁆ = ⁅toFun x, toFun y⁆
#align lie_hom LieHom

@[inherit_doc]
notation:25 L " →ₗ⁅" R:25 "⁆ " L':0 => LieHom R L L'

namespace LieHom

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R]

variable [LieRing L₁] [LieAlgebra R L₁]

variable [LieRing L₂] [LieAlgebra R L₂]

variable [LieRing L₃] [LieAlgebra R L₃]

attribute [coe] LieHom.toLinearMap

instance : Coe (L₁ →ₗ⁅R⁆ L₂) (L₁ →ₗ[R] L₂) :=
  ⟨LieHom.toLinearMap⟩

instance : FunLike (L₁ →ₗ⁅R⁆ L₂) L₁ (fun _ => L₂) :=
  { coe := fun f => f.toFun,
    coe_injective' := fun x y h =>
      by cases x; cases y; simp at h; simp [h] }
         -- ⊢ { toLinearMap := toLinearMap✝, map_lie' := map_lie'✝ } = y
                  -- ⊢ { toLinearMap := toLinearMap✝¹, map_lie' := map_lie'✝¹ } = { toLinearMap :=  …
                           -- ⊢ { toLinearMap := toLinearMap✝¹, map_lie' := map_lie'✝¹ } = { toLinearMap :=  …
                                      -- 🎉 no goals

initialize_simps_projections LieHom (toFun → apply)

@[simp, norm_cast]
theorem coe_toLinearMap (f : L₁ →ₗ⁅R⁆ L₂) : ⇑(f : L₁ →ₗ[R] L₂) = f :=
  rfl
#align lie_hom.coe_to_linear_map LieHom.coe_toLinearMap

@[simp]
theorem toFun_eq_coe (f : L₁ →ₗ⁅R⁆ L₂) : f.toFun = ⇑f :=
  rfl
#align lie_hom.to_fun_eq_coe LieHom.toFun_eq_coe

@[simp]
theorem map_smul (f : L₁ →ₗ⁅R⁆ L₂) (c : R) (x : L₁) : f (c • x) = c • f x :=
  LinearMap.map_smul (f : L₁ →ₗ[R] L₂) c x
#align lie_hom.map_smul LieHom.map_smul

@[simp]
theorem map_add (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x + y) = f x + f y :=
  LinearMap.map_add (f : L₁ →ₗ[R] L₂) x y
#align lie_hom.map_add LieHom.map_add

@[simp]
theorem map_sub (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x - y) = f x - f y :=
  LinearMap.map_sub (f : L₁ →ₗ[R] L₂) x y
#align lie_hom.map_sub LieHom.map_sub

@[simp]
theorem map_neg (f : L₁ →ₗ⁅R⁆ L₂) (x : L₁) : f (-x) = -f x :=
  LinearMap.map_neg (f : L₁ →ₗ[R] L₂) x
#align lie_hom.map_neg LieHom.map_neg

@[simp]
theorem map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  LieHom.map_lie' f
#align lie_hom.map_lie LieHom.map_lie

@[simp]
theorem map_zero (f : L₁ →ₗ⁅R⁆ L₂) : f 0 = 0 :=
  (f : L₁ →ₗ[R] L₂).map_zero
#align lie_hom.map_zero LieHom.map_zero

/-- The identity map is a morphism of Lie algebras. -/
def id : L₁ →ₗ⁅R⁆ L₁ :=
  { (LinearMap.id : L₁ →ₗ[R] L₁) with map_lie' := rfl }
#align lie_hom.id LieHom.id

@[simp]
theorem coe_id : ⇑(id : L₁ →ₗ⁅R⁆ L₁) = _root_.id :=
  rfl
#align lie_hom.coe_id LieHom.coe_id

theorem id_apply (x : L₁) : (id : L₁ →ₗ⁅R⁆ L₁) x = x :=
  rfl
#align lie_hom.id_apply LieHom.id_apply

/-- The constant 0 map is a Lie algebra morphism. -/
instance : Zero (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨{ (0 : L₁ →ₗ[R] L₂) with map_lie' := by simp }⟩
                                           -- 🎉 no goals

@[norm_cast, simp]
theorem coe_zero : ((0 : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = 0 :=
  rfl
#align lie_hom.coe_zero LieHom.coe_zero

theorem zero_apply (x : L₁) : (0 : L₁ →ₗ⁅R⁆ L₂) x = 0 :=
  rfl
#align lie_hom.zero_apply LieHom.zero_apply

/-- The identity map is a Lie algebra morphism. -/
instance : One (L₁ →ₗ⁅R⁆ L₁) :=
  ⟨id⟩

@[simp]
theorem coe_one : ((1 : L₁ →ₗ⁅R⁆ L₁) : L₁ → L₁) = _root_.id :=
  rfl
#align lie_hom.coe_one LieHom.coe_one

theorem one_apply (x : L₁) : (1 : L₁ →ₗ⁅R⁆ L₁) x = x :=
  rfl
#align lie_hom.one_apply LieHom.one_apply

instance : Inhabited (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨0⟩

theorem coe_injective : @Function.Injective (L₁ →ₗ⁅R⁆ L₂) (L₁ → L₂) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h
  -- ⊢ { toLinearMap := { toAddHom := { toFun := f, map_add' := map_add'✝¹ }, map_s …
  congr
  -- 🎉 no goals
#align lie_hom.coe_injective LieHom.coe_injective

@[ext]
theorem ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
#align lie_hom.ext LieHom.ext

theorem ext_iff {f g : L₁ →ₗ⁅R⁆ L₂} : f = g ↔ ∀ x, f x = g x :=
  ⟨by
    rintro rfl x
    -- ⊢ ↑f x = ↑f x
    rfl, ext⟩
    -- 🎉 no goals
#align lie_hom.ext_iff LieHom.ext_iff

theorem congr_fun {f g : L₁ →ₗ⁅R⁆ L₂} (h : f = g) (x : L₁) : f x = g x :=
  h ▸ rfl
#align lie_hom.congr_fun LieHom.congr_fun

@[simp]
theorem mk_coe (f : L₁ →ₗ⁅R⁆ L₂) (h₁ h₂ h₃) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) = f := by
  ext
  -- ⊢ ↑{ toLinearMap := { toAddHom := { toFun := ↑f, map_add' := h₁ }, map_smul' : …
  rfl
  -- 🎉 no goals
#align lie_hom.mk_coe LieHom.mk_coe

@[simp]
theorem coe_mk (f : L₁ → L₂) (h₁ h₂ h₃) : ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f :=
  rfl
#align lie_hom.coe_mk LieHom.coe_mk

/-- The composition of morphisms is a morphism. -/
def comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      intros x y
      -- ⊢ AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : L …
      change f (g ⁅x, y⁆) = ⁅f (g x), f (g y)⁆
      -- ⊢ ↑f (↑g ⁅x, y⁆) = ⁅↑f (↑g x), ↑f (↑g y)⁆
      rw [map_lie, map_lie] }
      -- 🎉 no goals
#align lie_hom.comp LieHom.comp

theorem comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) : f.comp g x = f (g x) :=
  rfl
#align lie_hom.comp_apply LieHom.comp_apply

@[norm_cast, simp]
theorem coe_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : (f.comp g : L₁ → L₃) = f ∘ g :=
  rfl
#align lie_hom.coe_comp LieHom.coe_comp

@[norm_cast, simp]
theorem coe_linearMap_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
    (f.comp g : L₁ →ₗ[R] L₃) = (f : L₂ →ₗ[R] L₃).comp (g : L₁ →ₗ[R] L₂) :=
  rfl
#align lie_hom.coe_linear_map_comp LieHom.coe_linearMap_comp

@[simp]
theorem comp_id (f : L₁ →ₗ⁅R⁆ L₂) : f.comp (id : L₁ →ₗ⁅R⁆ L₁) = f := by
  ext
  -- ⊢ ↑(comp f id) x✝ = ↑f x✝
  rfl
  -- 🎉 no goals
#align lie_hom.comp_id LieHom.comp_id

@[simp]
theorem id_comp (f : L₁ →ₗ⁅R⁆ L₂) : (id : L₂ →ₗ⁅R⁆ L₂).comp f = f := by
  ext
  -- ⊢ ↑(comp id f) x✝ = ↑f x✝
  rfl
  -- 🎉 no goals
#align lie_hom.id_comp LieHom.id_comp

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intros x y
      -- ⊢ AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : L …
      calc
        g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ := by conv_lhs => rw [← h₂ x, ← h₂ y]
        _ = g (f ⁅g x, g y⁆) := by rw [map_lie]
        _ = ⁅g x, g y⁆ := h₁ _
         }
#align lie_hom.inverse LieHom.inverse

end LieHom

section ModulePullBack

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} (M : Type w₁)

variable [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]

variable [AddCommGroup M] [LieRingModule L₂ M]

variable (f : L₁ →ₗ⁅R⁆ L₂)

/-- A Lie ring module may be pulled back along a morphism of Lie algebras.

See note [reducible non-instances]. -/
def LieRingModule.compLieHom : LieRingModule L₁ M where
  bracket x m := ⁅f x, m⁆
  lie_add x := lie_add (f x)
  add_lie x y m := by simp only [LieHom.map_add, add_lie]
                      -- 🎉 no goals
  leibniz_lie x y m := by simp only [lie_lie, sub_add_cancel, LieHom.map_lie]
                          -- 🎉 no goals
#align lie_ring_module.comp_lie_hom LieRingModule.compLieHom

theorem LieRingModule.compLieHom_apply (x : L₁) (m : M) :
    haveI := LieRingModule.compLieHom M f
    ⁅x, m⁆ = ⁅f x, m⁆ :=
  rfl
#align lie_ring_module.comp_lie_hom_apply LieRingModule.compLieHom_apply

/-- A Lie module may be pulled back along a morphism of Lie algebras. -/
theorem LieModule.compLieHom [Module R M] [LieModule R L₂ M] :
    @LieModule R L₁ M _ _ _ _ _ (LieRingModule.compLieHom M f) :=
  { LieRingModule.compLieHom M f with
    smul_lie := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, smul_lie, LieHom.map_smul]
      -- 🎉 no goals
    lie_smul := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, lie_smul] }
      -- 🎉 no goals
#align lie_module.comp_lie_hom LieModule.compLieHom

end ModulePullBack

/-- An equivalence of Lie algebras is a morphism which is also a linear equivalence. We could
instead define an equivalence to be a morphism which is also a (plain) equivalence. However it is
more convenient to define via linear equivalence to get `.toLinearEquiv` for free. -/
structure LieEquiv (R : Type u) (L : Type v) (L' : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L →ₗ⁅R⁆ L' where
  /-- The inverse function of an equivalence of Lie algebras -/
  invFun : L' → L
  /-- The inverse function of an equivalence of Lie algebras is a left inverse of the underlying
  function. -/
  left_inv : Function.LeftInverse invFun toLieHom.toFun
  /-- The inverse function of an equivalence of Lie algebras is a right inverse of the underlying
  function. -/
  right_inv : Function.RightInverse invFun toLieHom.toFun
#align lie_equiv LieEquiv

@[inherit_doc]
notation:50 L " ≃ₗ⁅" R "⁆ " L' => LieEquiv R L L'

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}

variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]

variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

/-- Consider an equivalence of Lie algebras as a linear equivalence. -/
def toLinearEquiv (f : L₁ ≃ₗ⁅R⁆ L₂) : L₁ ≃ₗ[R] L₂ :=
  { f.toLieHom, f with }
#align lie_equiv.to_linear_equiv LieEquiv.toLinearEquiv

instance hasCoeToLieHom : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨toLieHom⟩
#align lie_equiv.has_coe_to_lie_hom LieEquiv.hasCoeToLieHom

instance hasCoeToLinearEquiv : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) :=
  ⟨toLinearEquiv⟩
#align lie_equiv.has_coe_to_linear_equiv LieEquiv.hasCoeToLinearEquiv

instance : EquivLike (L₁ ≃ₗ⁅R⁆ L₂) L₁ L₂ :=
  { coe := fun f => f.toFun,
    inv := fun f => f.invFun,
    left_inv := fun f => f.left_inv,
    right_inv := fun f => f.right_inv,
    coe_injective' := fun f g h₁ h₂ =>
      by cases f; cases g; simp at h₁ h₂; simp [*] }
         -- ⊢ { toLieHom := toLieHom✝, invFun := invFun✝, left_inv := left_inv✝, right_inv …
                  -- ⊢ { toLieHom := toLieHom✝¹, invFun := invFun✝¹, left_inv := left_inv✝¹, right_ …
                           -- ⊢ { toLieHom := toLieHom✝¹, invFun := invFun✝¹, left_inv := left_inv✝¹, right_ …
                                          -- 🎉 no goals

theorem coe_to_lieHom (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ →ₗ⁅R⁆ L₂) = e :=
  rfl
#align lie_equiv.coe_to_lie_hom LieEquiv.coe_to_lieHom

@[simp]
theorem coe_to_linearEquiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ ≃ₗ[R] L₂) = e :=
  rfl
#align lie_equiv.coe_to_linear_equiv LieEquiv.coe_to_linearEquiv

@[simp]
theorem to_linearEquiv_mk (f : L₁ →ₗ⁅R⁆ L₂) (g h₁ h₂) :
    (mk f g h₁ h₂ : L₁ ≃ₗ[R] L₂) =
      { f with
        invFun := g
        left_inv := h₁
        right_inv := h₂ } :=
  rfl
#align lie_equiv.to_linear_equiv_mk LieEquiv.to_linearEquiv_mk

theorem coe_linearEquiv_injective : Injective ((↑) : (L₁ ≃ₗ⁅R⁆ L₂) → L₁ ≃ₗ[R] L₂) := by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  -- ⊢ toLinearEquiv { toLieHom := { toLinearMap := { toAddHom := { toFun := f, map …
  intro h
  -- ⊢ { toLieHom := { toLinearMap := { toAddHom := { toFun := f, map_add' := map_a …
  simp only [to_linearEquiv_mk, LinearEquiv.mk.injEq, LinearMap.mk.injEq, AddHom.mk.injEq] at h
  -- ⊢ { toLieHom := { toLinearMap := { toAddHom := { toFun := f, map_add' := map_a …
  congr
  -- ⊢ f = g
  exacts [h.1, h.2]
  -- 🎉 no goals
#align lie_equiv.coe_linear_equiv_injective LieEquiv.coe_linearEquiv_injective

theorem coe_injective : @Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ → L₂) (↑) :=
  LinearEquiv.coe_injective.comp coe_linearEquiv_injective
#align lie_equiv.coe_injective LieEquiv.coe_injective

@[ext]
theorem ext {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
#align lie_equiv.ext LieEquiv.ext

instance : One (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨{ (1 : L₁ ≃ₗ[R] L₁) with map_lie' := rfl }⟩

@[simp]
theorem one_apply (x : L₁) : (1 : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl
#align lie_equiv.one_apply LieEquiv.one_apply

instance : Inhabited (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨1⟩

/-- Lie algebra equivalences are reflexive. -/
def refl : L₁ ≃ₗ⁅R⁆ L₁ :=
  1
#align lie_equiv.refl LieEquiv.refl

@[simp]
theorem refl_apply (x : L₁) : (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl
#align lie_equiv.refl_apply LieEquiv.refl_apply

/-- Lie algebra equivalences are symmetric. -/
@[symm]
def symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁ :=
  { LieHom.inverse e.toLieHom e.invFun e.left_inv e.right_inv, e.toLinearEquiv.symm with }
#align lie_equiv.symm LieEquiv.symm

@[simp]
theorem symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e := by
  ext
  -- ⊢ ↑(symm (symm e)) x✝ = ↑e x✝
  rfl
  -- 🎉 no goals
#align lie_equiv.symm_symm LieEquiv.symm_symm

@[simp]
theorem apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply
#align lie_equiv.apply_symm_apply LieEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply
#align lie_equiv.symm_apply_apply LieEquiv.symm_apply_apply

@[simp]
theorem refl_symm : (refl : L₁ ≃ₗ⁅R⁆ L₁).symm = refl :=
  rfl
#align lie_equiv.refl_symm LieEquiv.refl_symm

/-- Lie algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
  { LieHom.comp e₂.toLieHom e₁.toLieHom, LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }
#align lie_equiv.trans LieEquiv.trans

@[simp]
theorem self_trans_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.trans e.symm = refl :=
  ext e.symm_apply_apply
#align lie_equiv.self_trans_symm LieEquiv.self_trans_symm

@[simp]
theorem symm_trans_self (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.trans e = refl :=
  e.symm.self_trans_symm
#align lie_equiv.symm_trans_self LieEquiv.symm_trans_self

@[simp]
theorem trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl
#align lie_equiv.trans_apply LieEquiv.trans_apply

@[simp]
theorem symm_trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
#align lie_equiv.symm_trans LieEquiv.symm_trans

protected theorem bijective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Bijective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.bijective
#align lie_equiv.bijective LieEquiv.bijective

protected theorem injective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Injective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.injective
#align lie_equiv.injective LieEquiv.injective

protected theorem surjective (e : L₁ ≃ₗ⁅R⁆ L₂) :
    Function.Surjective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.surjective
#align lie_equiv.surjective LieEquiv.surjective

/-- A bijective morphism of Lie algebras yields an equivalence of Lie algebras. -/
@[simps!]
noncomputable def ofBijective (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Bijective f) : L₁ ≃ₗ⁅R⁆ L₂ :=
  { LinearEquiv.ofBijective (f : L₁ →ₗ[R] L₂)
      h with
    toFun := f
    map_lie' := by intros x y; exact f.map_lie x y }
                   -- ⊢ AddHom.toFun { toAddHom := { toFun := ↑f, map_add' := (_ : ∀ (x y : L₁), Add …
                               -- 🎉 no goals
#align lie_equiv.of_bijective LieEquiv.ofBijective

end LieEquiv

section LieModuleMorphisms

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)

variable [CommRing R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

variable [Module R M] [Module R N] [Module R P]

variable [LieRingModule L M] [LieRingModule L N] [LieRingModule L P]

variable [LieModule R L M] [LieModule R L N] [LieModule R L P]

/-- A morphism of Lie algebra modules is a linear map which commutes with the action of the Lie
algebra. -/
structure LieModuleHom extends M →ₗ[R] N where
  /-- A module of Lie algebra modules is compatible with the action of the Lie algebra on the
  modules. -/
  map_lie' : ∀ {x : L} {m : M}, toFun ⁅x, m⁆ = ⁅x, toFun m⁆
#align lie_module_hom LieModuleHom

@[inherit_doc]
notation:25 M " →ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleHom R L M N

namespace LieModuleHom

variable {R L M N P}

attribute [coe] LieModuleHom.toLinearMap

instance : CoeOut (M →ₗ⁅R,L⁆ N) (M →ₗ[R] N) :=
  ⟨LieModuleHom.toLinearMap⟩

instance : FunLike (M →ₗ⁅R, L⁆ N) M (fun _ => N) :=
  { coe := fun f => f.toFun,
    coe_injective' := fun x y h =>
      by cases x; cases y; simp at h; simp [h] }
         -- ⊢ { toLinearMap := toLinearMap✝, map_lie' := map_lie'✝ } = y
                  -- ⊢ { toLinearMap := toLinearMap✝¹, map_lie' := map_lie'✝¹ } = { toLinearMap :=  …
                           -- ⊢ { toLinearMap := toLinearMap✝¹, map_lie' := map_lie'✝¹ } = { toLinearMap :=  …
                                      -- 🎉 no goals

@[simp, norm_cast]
theorem coe_toLinearMap (f : M →ₗ⁅R,L⁆ N) : ((f : M →ₗ[R] N) : M → N) = f :=
  rfl
#align lie_module_hom.coe_to_linear_map LieModuleHom.coe_toLinearMap

@[simp]
theorem map_smul (f : M →ₗ⁅R,L⁆ N) (c : R) (x : M) : f (c • x) = c • f x :=
  LinearMap.map_smul (f : M →ₗ[R] N) c x
#align lie_module_hom.map_smul LieModuleHom.map_smul

@[simp]
theorem map_add (f : M →ₗ⁅R,L⁆ N) (x y : M) : f (x + y) = f x + f y :=
  LinearMap.map_add (f : M →ₗ[R] N) x y
#align lie_module_hom.map_add LieModuleHom.map_add

@[simp]
theorem map_sub (f : M →ₗ⁅R,L⁆ N) (x y : M) : f (x - y) = f x - f y :=
  LinearMap.map_sub (f : M →ₗ[R] N) x y
#align lie_module_hom.map_sub LieModuleHom.map_sub

@[simp]
theorem map_neg (f : M →ₗ⁅R,L⁆ N) (x : M) : f (-x) = -f x :=
  LinearMap.map_neg (f : M →ₗ[R] N) x
#align lie_module_hom.map_neg LieModuleHom.map_neg

@[simp]
theorem map_lie (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆ :=
  LieModuleHom.map_lie' f
#align lie_module_hom.map_lie LieModuleHom.map_lie

theorem map_lie₂ (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (x : L) (m : M) (n : N) :
    ⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆ := by simp only [sub_add_cancel, map_lie, LieHom.lie_apply]
                                               -- 🎉 no goals
#align lie_module_hom.map_lie₂ LieModuleHom.map_lie₂

@[simp]
theorem map_zero (f : M →ₗ⁅R,L⁆ N) : f 0 = 0 :=
  LinearMap.map_zero (f : M →ₗ[R] N)
#align lie_module_hom.map_zero LieModuleHom.map_zero

/-- The identity map is a morphism of Lie modules. -/
def id : M →ₗ⁅R,L⁆ M :=
  { (LinearMap.id : M →ₗ[R] M) with map_lie' := rfl }
#align lie_module_hom.id LieModuleHom.id

@[simp]
theorem coe_id : ((id : M →ₗ⁅R,L⁆ M) : M → M) = _root_.id :=
  rfl
#align lie_module_hom.coe_id LieModuleHom.coe_id

theorem id_apply (x : M) : (id : M →ₗ⁅R,L⁆ M) x = x :=
  rfl
#align lie_module_hom.id_apply LieModuleHom.id_apply

/-- The constant 0 map is a Lie module morphism. -/
instance : Zero (M →ₗ⁅R,L⁆ N) :=
  ⟨{ (0 : M →ₗ[R] N) with map_lie' := by simp }⟩
                                         -- 🎉 no goals

@[norm_cast, simp]
theorem coe_zero : ⇑(0 : M →ₗ⁅R,L⁆ N) = 0 :=
  rfl
#align lie_module_hom.coe_zero LieModuleHom.coe_zero

theorem zero_apply (m : M) : (0 : M →ₗ⁅R,L⁆ N) m = 0 :=
  rfl
#align lie_module_hom.zero_apply LieModuleHom.zero_apply

/-- The identity map is a Lie module morphism. -/
instance : One (M →ₗ⁅R,L⁆ M) :=
  ⟨id⟩

instance : Inhabited (M →ₗ⁅R,L⁆ N) :=
  ⟨0⟩

theorem coe_injective : @Function.Injective (M →ₗ⁅R,L⁆ N) (M → N) (↑) := by
  rintro ⟨⟨⟨f, _⟩⟩⟩ ⟨⟨⟨g, _⟩⟩⟩ h
  -- ⊢ { toLinearMap := { toAddHom := { toFun := f, map_add' := map_add'✝¹ }, map_s …
  congr
  -- 🎉 no goals
#align lie_module_hom.coe_injective LieModuleHom.coe_injective

@[ext]
theorem ext {f g : M →ₗ⁅R,L⁆ N} (h : ∀ m, f m = g m) : f = g :=
  coe_injective <| funext h
#align lie_module_hom.ext LieModuleHom.ext

theorem ext_iff {f g : M →ₗ⁅R,L⁆ N} : f = g ↔ ∀ m, f m = g m :=
  ⟨by
    rintro rfl m
    -- ⊢ ↑f m = ↑f m
    rfl, ext⟩
    -- 🎉 no goals
#align lie_module_hom.ext_iff LieModuleHom.ext_iff

theorem congr_fun {f g : M →ₗ⁅R,L⁆ N} (h : f = g) (x : M) : f x = g x :=
  h ▸ rfl
#align lie_module_hom.congr_fun LieModuleHom.congr_fun

@[simp]
theorem mk_coe (f : M →ₗ⁅R,L⁆ N) (h) : (⟨f, h⟩ : M →ₗ⁅R,L⁆ N) = f := by
  rfl
  -- 🎉 no goals
#align lie_module_hom.mk_coe LieModuleHom.mk_coe

@[simp]
theorem coe_mk (f : M →ₗ[R] N) (h) : ((⟨f, h⟩ : M →ₗ⁅R,L⁆ N) : M → N) = f := by
  rfl
  -- 🎉 no goals
#align lie_module_hom.coe_mk LieModuleHom.coe_mk

@[norm_cast]
theorem coe_linear_mk (f : M →ₗ[R] N) (h) : ((⟨f, h⟩ : M →ₗ⁅R,L⁆ N) : M →ₗ[R] N) = f := by
  rfl
  -- 🎉 no goals
#align lie_module_hom.coe_linear_mk LieModuleHom.coe_linear_mk

/-- The composition of Lie module morphisms is a morphism. -/
def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      intros x m
      -- ⊢ AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : M …
      change f (g ⁅x, m⁆) = ⁅x, f (g m)⁆
      -- ⊢ ↑f (↑g ⁅x, m⁆) = ⁅x, ↑f (↑g m)⁆
      rw [map_lie, map_lie] }
      -- 🎉 no goals
#align lie_module_hom.comp LieModuleHom.comp

theorem comp_apply (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) (m : M) : f.comp g m = f (g m) :=
  rfl
#align lie_module_hom.comp_apply LieModuleHom.comp_apply

@[norm_cast, simp]
theorem coe_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align lie_module_hom.coe_comp LieModuleHom.coe_comp

@[norm_cast, simp]
theorem coe_linearMap_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) :
    (f.comp g : M →ₗ[R] P) = (f : N →ₗ[R] P).comp (g : M →ₗ[R] N) :=
  rfl
#align lie_module_hom.coe_linear_map_comp LieModuleHom.coe_linearMap_comp

/-- The inverse of a bijective morphism of Lie modules is a morphism of Lie modules. -/
def inverse (f : M →ₗ⁅R,L⁆ N) (g : N → M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₗ⁅R,L⁆ M :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intros x n
      -- ⊢ AddHom.toFun { toAddHom := src✝.toAddHom, map_smul' := (_ : ∀ (r : R) (x : N …
      calc
        g ⁅x, n⁆ = g ⁅x, f (g n)⁆ := by rw [h₂]
        _ = g (f ⁅x, g n⁆) := by rw [map_lie]
        _ = ⁅x, g n⁆ := h₁ _
         }
#align lie_module_hom.inverse LieModuleHom.inverse

instance : Add (M →ₗ⁅R,L⁆ N)
    where add f g := { (f : M →ₗ[R] N) + (g : M →ₗ[R] N) with map_lie' := by simp }
                                                                             -- 🎉 no goals

instance : Sub (M →ₗ⁅R,L⁆ N)
    where sub f g := { (f : M →ₗ[R] N) - (g : M →ₗ[R] N) with map_lie' := by simp }
                                                                             -- 🎉 no goals

instance : Neg (M →ₗ⁅R,L⁆ N) where neg f := { -(f : M →ₗ[R] N) with map_lie' := by simp }
                                                                                   -- 🎉 no goals

@[norm_cast, simp]
theorem coe_add (f g : M →ₗ⁅R,L⁆ N) : ⇑(f + g) = f + g :=
  rfl
#align lie_module_hom.coe_add LieModuleHom.coe_add

theorem add_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m :=
  rfl
#align lie_module_hom.add_apply LieModuleHom.add_apply

@[norm_cast, simp]
theorem coe_sub (f g : M →ₗ⁅R,L⁆ N) : ⇑(f - g) = f - g :=
  rfl
#align lie_module_hom.coe_sub LieModuleHom.coe_sub

theorem sub_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f - g) m = f m - g m :=
  rfl
#align lie_module_hom.sub_apply LieModuleHom.sub_apply

@[norm_cast, simp]
theorem coe_neg (f : M →ₗ⁅R,L⁆ N) : ⇑(-f) = -f :=
  rfl
#align lie_module_hom.coe_neg LieModuleHom.coe_neg

theorem neg_apply (f : M →ₗ⁅R,L⁆ N) (m : M) : (-f) m = -f m :=
  rfl
#align lie_module_hom.neg_apply LieModuleHom.neg_apply

instance hasNsmul : SMul ℕ (M →ₗ⁅R,L⁆ N)
    where smul n f := { n • (f : M →ₗ[R] N) with map_lie' := by simp }
                                                                -- 🎉 no goals
#align lie_module_hom.has_nsmul LieModuleHom.hasNsmul

@[norm_cast, simp]
theorem coe_nsmul (n : ℕ) (f : M →ₗ⁅R,L⁆ N) : ⇑(n • f) = n • (⇑f) :=
  rfl
#align lie_module_hom.coe_nsmul LieModuleHom.coe_nsmul

theorem nsmul_apply (n : ℕ) (f : M →ₗ⁅R,L⁆ N) (m : M) : (n • f) m = n • f m :=
  rfl
#align lie_module_hom.nsmul_apply LieModuleHom.nsmul_apply

instance hasZsmul : SMul ℤ (M →ₗ⁅R,L⁆ N)
    where smul z f := { z • (f : M →ₗ[R] N) with map_lie' := by simp }
                                                                -- 🎉 no goals
#align lie_module_hom.has_zsmul LieModuleHom.hasZsmul

@[norm_cast, simp]
theorem coe_zsmul (z : ℤ) (f : M →ₗ⁅R,L⁆ N) : ⇑(z • f) = z • (⇑f) :=
  rfl
#align lie_module_hom.coe_zsmul LieModuleHom.coe_zsmul

theorem zsmul_apply (z : ℤ) (f : M →ₗ⁅R,L⁆ N) (m : M) : (z • f) m = z • f m :=
  rfl
#align lie_module_hom.zsmul_apply LieModuleHom.zsmul_apply

instance : AddCommGroup (M →ₗ⁅R,L⁆ N) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    (fun _ _ => coe_zsmul _ _)

instance : SMul R (M →ₗ⁅R,L⁆ N) where smul t f := { t • (f : M →ₗ[R] N) with map_lie' := by simp }
                                                                                            -- 🎉 no goals

@[norm_cast, simp]
theorem coe_smul (t : R) (f : M →ₗ⁅R,L⁆ N) : ⇑(t • f) = t • (⇑f) :=
  rfl
#align lie_module_hom.coe_smul LieModuleHom.coe_smul

theorem smul_apply (t : R) (f : M →ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • f m :=
  rfl
#align lie_module_hom.smul_apply LieModuleHom.smul_apply

instance : Module R (M →ₗ⁅R,L⁆ N) :=
  Function.Injective.module R ⟨⟨fun f => f.toLinearMap.toFun, rfl⟩, coe_add⟩ coe_injective coe_smul

end LieModuleHom

/-- An equivalence of Lie algebra modules is a linear equivalence which is also a morphism of
Lie algebra modules. -/
structure LieModuleEquiv extends M →ₗ⁅R,L⁆ N where
  /-- The inverse function of an equivalence of Lie modules -/
  invFun : N → M
  /-- The inverse function of an equivalence of Lie modules is a left inverse of the underlying
  function. -/
  left_inv : Function.LeftInverse invFun toFun
  /-- The inverse function of an equivalence of Lie modules is a right inverse of the underlying
  function. -/
  right_inv : Function.RightInverse invFun toFun
#align lie_module_equiv LieModuleEquiv

attribute [nolint docBlame] LieModuleEquiv.toLieModuleHom

@[inherit_doc]
notation:25 M " ≃ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleEquiv R L M N

namespace LieModuleEquiv

variable {R L M N P}

/-- View an equivalence of Lie modules as a linear equivalence. -/
def toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ₗ[R] N :=
  { e with }
#align lie_module_equiv.to_linear_equiv LieModuleEquiv.toLinearEquiv

/-- View an equivalence of Lie modules as a type level equivalence. -/
def toEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ N :=
  { e with }
#align lie_module_equiv.to_equiv LieModuleEquiv.toEquiv

instance hasCoeToEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ N) :=
  ⟨toEquiv⟩
#align lie_module_equiv.has_coe_to_equiv LieModuleEquiv.hasCoeToEquiv

instance hasCoeToLieModuleHom : Coe (M ≃ₗ⁅R,L⁆ N) (M →ₗ⁅R,L⁆ N) :=
  ⟨toLieModuleHom⟩
#align lie_module_equiv.has_coe_to_lie_module_hom LieModuleEquiv.hasCoeToLieModuleHom

instance hasCoeToLinearEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N) :=
  ⟨toLinearEquiv⟩
#align lie_module_equiv.has_coe_to_linear_equiv LieModuleEquiv.hasCoeToLinearEquiv

instance : EquivLike (M ≃ₗ⁅R,L⁆ N) M N :=
  { coe := fun f => f.toFun,
    inv := fun f => f.invFun,
    left_inv := fun f => f.left_inv,
    right_inv := fun f => f.right_inv,
    coe_injective' := fun f g h₁ h₂ =>
      by cases f; cases g; simp at h₁ h₂; simp [*] }
         -- ⊢ { toLieModuleHom := toLieModuleHom✝, invFun := invFun✝, left_inv := left_inv …
                  -- ⊢ { toLieModuleHom := toLieModuleHom✝¹, invFun := invFun✝¹, left_inv := left_i …
                           -- ⊢ { toLieModuleHom := toLieModuleHom✝¹, invFun := invFun✝¹, left_inv := left_i …
                                          -- 🎉 no goals

theorem injective (e : M ≃ₗ⁅R,L⁆ N) : Function.Injective e :=
  e.toEquiv.injective
#align lie_module_equiv.injective LieModuleEquiv.injective

@[simp]
theorem toEquiv_mk (f : M →ₗ⁅R,L⁆ N) (g : N → M) (h₁ h₂) :
  toEquiv (mk f g h₁ h₂ : M ≃ₗ⁅R,L⁆ N) = Equiv.mk f g h₁ h₂ :=
  rfl

@[simp]
theorem coe_mk (f : M →ₗ⁅R,L⁆ N) (invFun h₁ h₂) :
    ((⟨f, invFun, h₁, h₂⟩ : M ≃ₗ⁅R,L⁆ N) : M → N) = f :=
  rfl
#align lie_module_equiv.coe_mk LieModuleEquiv.coe_mk

theorem coe_to_lieModuleHom (e : M ≃ₗ⁅R,L⁆ N) : ⇑(e : M →ₗ⁅R,L⁆ N) = e :=
  rfl
#align lie_module_equiv.coe_to_lie_module_hom LieModuleEquiv.coe_to_lieModuleHom

@[simp]
theorem coe_to_linearEquiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M → N) = e :=
  rfl
#align lie_module_equiv.coe_to_linear_equiv LieModuleEquiv.coe_to_linearEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃ₗ⁅R,L⁆ N) → M ≃ N) := by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  -- ⊢ toEquiv { toLieModuleHom := { toLinearMap := { toAddHom := { toFun := f, map …
  intro h
  -- ⊢ { toLieModuleHom := { toLinearMap := { toAddHom := { toFun := f, map_add' := …
  simp only [toEquiv_mk, LieModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Equiv.mk.injEq] at h
  -- ⊢ { toLieModuleHom := { toLinearMap := { toAddHom := { toFun := f, map_add' := …
  congr
  -- ⊢ f = g
  exacts [h.1, h.2]
  -- 🎉 no goals
#align lie_module_equiv.to_equiv_injective LieModuleEquiv.toEquiv_injective

@[ext]
theorem ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : ∀ m, e₁ m = e₂ m) : e₁ = e₂ :=
  toEquiv_injective (Equiv.ext h)
#align lie_module_equiv.ext LieModuleEquiv.ext

instance : One (M ≃ₗ⁅R,L⁆ M) :=
  ⟨{ (1 : M ≃ₗ[R] M) with map_lie' := rfl }⟩

@[simp]
theorem one_apply (m : M) : (1 : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl
#align lie_module_equiv.one_apply LieModuleEquiv.one_apply

instance : Inhabited (M ≃ₗ⁅R,L⁆ M) :=
  ⟨1⟩

/-- Lie module equivalences are reflexive. -/
@[refl]
def refl : M ≃ₗ⁅R,L⁆ M :=
  1
#align lie_module_equiv.refl LieModuleEquiv.refl

@[simp]
theorem refl_apply (m : M) : (refl : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl
#align lie_module_equiv.refl_apply LieModuleEquiv.refl_apply

/-- Lie module equivalences are symmetric. -/
@[symm]
def symm (e : M ≃ₗ⁅R,L⁆ N) : N ≃ₗ⁅R,L⁆ M :=
  { LieModuleHom.inverse e.toLieModuleHom e.invFun e.left_inv e.right_inv,
    (e : M ≃ₗ[R] N).symm with }
#align lie_module_equiv.symm LieModuleEquiv.symm

@[simp]
theorem apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply
#align lie_module_equiv.apply_symm_apply LieModuleEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply
#align lie_module_equiv.symm_apply_apply LieModuleEquiv.symm_apply_apply

@[simp]
theorem symm_symm (e : M ≃ₗ⁅R,L⁆ N) : e.symm.symm = e := by
  rfl
  -- 🎉 no goals
#align lie_module_equiv.symm_symm LieModuleEquiv.symm_symm

/-- Lie module equivalences are transitive. -/
@[trans]
def trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : M ≃ₗ⁅R,L⁆ P :=
  { LieModuleHom.comp e₂.toLieModuleHom e₁.toLieModuleHom,
    LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }
#align lie_module_equiv.trans LieModuleEquiv.trans

@[simp]
theorem trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M) : (e₁.trans e₂) m = e₂ (e₁ m) :=
  rfl
#align lie_module_equiv.trans_apply LieModuleEquiv.trans_apply

@[simp]
theorem symm_trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
#align lie_module_equiv.symm_trans LieModuleEquiv.symm_trans

@[simp]
theorem self_trans_symm (e : M ≃ₗ⁅R,L⁆ N) : e.trans e.symm = refl :=
  ext _ _ e.symm_apply_apply
#align lie_module_equiv.self_trans_symm LieModuleEquiv.self_trans_symm

@[simp]
theorem symm_trans_self (e : M ≃ₗ⁅R,L⁆ N) : e.symm.trans e = refl :=
  ext _ _ e.apply_symm_apply
#align lie_module_equiv.symm_trans_self LieModuleEquiv.symm_trans_self

end LieModuleEquiv

end LieModuleMorphisms
