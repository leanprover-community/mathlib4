/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Data.Bracket
import Mathlib.Tactic.Abel

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

## Tags

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

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
@[ext] class LieAlgebra (R : Type u) (L : Type v) [CommRing R] [LieRing L] extends Module R L where
  /-- A Lie algebra bracket is compatible with scalar multiplication in its second argument.

  The compatibility in the first argument is not a class property, but follows since every
  Lie algebra has a natural Lie module action on itself, see `LieModule`. -/
  protected lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆

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

/-- A Lie module is a module over a commutative ring, together with a linear action of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endomorphisms. -/
class LieModule (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] : Prop where
  /-- A Lie module bracket is compatible with scalar multiplication in its first argument. -/
  protected smul_lie : ∀ (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆
  /-- A Lie module bracket is compatible with scalar multiplication in its second argument. -/
  protected lie_smul : ∀ (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆

/-- A tower of Lie bracket actions encapsulates the Leibniz rule for Lie bracket actions.

More precisely, it does so in a relative setting:
Let `L₁` and `L₂` be two types with Lie bracket actions on a type `M` endowed with an addition,
and additionally assume a Lie bracket action of `L₁` on `L₂`.
Then the Leibniz rule asserts for all `x : L₁`, `y : L₂`, and `m : M` that
`⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆` holds.

Common examples include the case where `L₁` is a Lie subalgebra of `L₂`
and the case where `L₂` is a Lie ideal of `L₁`. -/
class IsLieTower (L₁ L₂ M : Type*) [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M] [Add M] where
  protected leibniz_lie (x : L₁) (y : L₂) (m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

section IsLieTower

variable {L₁ L₂ M : Type*} [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M]

lemma leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) (m : M) :
    ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ := IsLieTower.leibniz_lie x y m

lemma lie_swap_lie [Bracket L₂ L₁] [AddCommGroup M] [IsLieTower L₁ L₂ M] [IsLieTower L₂ L₁ M]
    (x : L₁) (y : L₂) (m : M) : ⁅⁅x, y⁆, m⁆ = -⁅⁅y, x⁆, m⁆ := by
  have h1 := leibniz_lie x y m
  have h2 := leibniz_lie y x m
  convert congr($h1.symm - $h2) using 1 <;> simp only [add_sub_cancel_right, sub_add_cancel_right]

end IsLieTower

section BasicProperties

theorem LieAlgebra.toModule_injective (L : Type*) [LieRing L] :
    Function.Injective (@LieAlgebra.toModule _ _ _ _ : LieAlgebra ℚ L → Module ℚ L) := by
  rintro ⟨h₁⟩ ⟨h₂⟩ heq
  congr

instance (L : Type*) [LieRing L] : Subsingleton (LieAlgebra ℚ L) :=
  LieAlgebra.toModule_injective L |>.subsingleton

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable (t : R) (x y z : L) (m n : M)

@[simp]
theorem add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆ :=
  LieRingModule.add_lie x y m

@[simp]
theorem lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆ :=
  LieRingModule.lie_add x m n

@[simp]
theorem smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆ :=
  LieModule.smul_lie t x m

@[simp]
theorem lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆ :=
  LieModule.lie_smul t x m

instance : IsLieTower L L M where
  leibniz_lie x y m := LieRingModule.leibniz_lie x y m

@[simp]
theorem lie_zero : ⁅x, 0⁆ = (0 : M) :=
  (AddMonoidHom.mk' _ (lie_add x)).map_zero

@[simp]
theorem zero_lie : ⁅(0 : L), m⁆ = 0 :=
  (AddMonoidHom.mk' (fun x : L => ⁅x, m⁆) fun x y => add_lie x y m).map_zero

@[simp]
theorem lie_self : ⁅x, x⁆ = 0 :=
  LieRing.lie_self x

instance lieRingSelfModule : LieRingModule L L :=
  { (inferInstance : LieRing L) with }

@[simp]
theorem lie_skew : -⁅y, x⁆ = ⁅x, y⁆ := by
  have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0 := by rw [← lie_add]; apply lie_self
  simpa [neg_eq_iff_add_eq_zero] using h

/-- Every Lie algebra is a module over itself. -/
instance lieAlgebraSelfModule : LieModule R L L where
  smul_lie t x m := by rw [← lie_skew, ← lie_skew x m, LieAlgebra.lie_smul, smul_neg]
  lie_smul := by apply LieAlgebra.lie_smul

@[simp]
theorem neg_lie : ⁅-x, m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← add_lie]
  simp

@[simp]
theorem lie_neg : ⁅x, -m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← lie_add]
  simp

@[simp]
theorem sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by simp [sub_eq_add_neg]

@[simp]
theorem lie_sub : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by simp [sub_eq_add_neg]

@[simp]
theorem nsmul_lie (n : ℕ) : ⁅n • x, m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

@[simp]
theorem lie_nsmul (n : ℕ) : ⁅x, n • m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _}
    _ _

theorem zsmul_lie (a : ℤ) : ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

theorem lie_zsmul (a : ℤ) : ⁅x, a • m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _

@[simp]
lemma lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ := by rw [leibniz_lie, add_sub_cancel_right]

theorem lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  rw [← neg_neg ⁅x, y⁆, lie_neg z, lie_skew y x, ← lie_skew, lie_lie]
  abel

instance LieRing.instLieAlgebra : LieAlgebra ℤ L where lie_smul n x y := lie_zsmul x y n

instance : LieModule ℤ L M where
  smul_lie n x m := zsmul_lie x m n
  lie_smul n x m := lie_zsmul x m n

instance LinearMap.instLieRingModule : LieRingModule L (M →ₗ[R] N) where
  bracket x f :=
    { toFun := fun m => ⁅x, f m⁆ - f ⁅x, m⁆
      map_add' := fun m n => by
        simp only [lie_add, LinearMap.map_add]
        abel
      map_smul' := fun t m => by
        simp only [smul_sub, LinearMap.map_smul, lie_smul, RingHom.id_apply] }
  add_lie x y f := by
    ext n
    simp only [add_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, LinearMap.map_add]
    abel
  lie_add x f g := by
    ext n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, lie_add, LinearMap.add_apply]
    abel
  leibniz_lie x y f := by
    ext n
    simp only [lie_lie, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_sub, LinearMap.add_apply,
      lie_sub]
    abel

@[simp]
theorem LieHom.lie_apply (f : M →ₗ[R] N) (x : L) (m : M) : ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆ :=
  rfl

instance LinearMap.instLieModule : LieModule R L (M →ₗ[R] N) where
  smul_lie t x f := by
    ext n
    simp only [smul_sub, smul_lie, LinearMap.smul_apply, LieHom.lie_apply, LinearMap.map_smul]
  lie_smul t x f := by
    ext n
    simp only [smul_sub, LinearMap.smul_apply, LieHom.lie_apply, lie_smul]

/-- We could avoid defining this by instead defining a `LieRingModule L R` instance with a zero
bracket and relying on `LinearMap.instLieRingModule`. We do not do this because in the case that
`L = R` we would have a non-defeq diamond via `Ring.instBracket`. -/
instance Module.Dual.instLieRingModule : LieRingModule L (M →ₗ[R] R) where
  bracket := fun x f ↦
    { toFun := fun m ↦ - f ⁅x, m⁆
      map_add' := by simp [-neg_add_rev, neg_add]
      map_smul' := by simp }
  add_lie := fun x y m ↦ by ext n; simp [-neg_add_rev, neg_add]
  lie_add := fun x m n ↦ by ext p; simp [-neg_add_rev, neg_add]
  leibniz_lie := fun x m n ↦ by ext p; simp

@[simp] lemma Module.Dual.lie_apply (f : M →ₗ[R] R) : ⁅x, f⁆ m = - f ⁅x, m⁆ := rfl

instance Module.Dual.instLieModule : LieModule R L (M →ₗ[R] R) where
  smul_lie := fun t x m ↦ by ext n; simp
  lie_smul := fun t x m ↦ by ext n; simp

variable (L) in
/-- It is sometimes useful to regard a `LieRing` as a `NonUnitalNonAssocRing`. -/
def LieRing.toNonUnitalNonAssocRing : NonUnitalNonAssocRing L :=
  { mul := Bracket.bracket
    left_distrib := lie_add
    right_distrib := add_lie
    zero_mul := zero_lie
    mul_zero := lie_zero }

variable {ι κ : Type*}

theorem sum_lie (s : Finset ι) (f : ι → L) (a : L) : ⁅∑ i ∈ s, f i, a⁆ = ∑ i ∈ s, ⁅f i, a⁆ :=
  let _i := LieRing.toNonUnitalNonAssocRing L
  s.sum_mul f a

theorem lie_sum (s : Finset ι) (f : ι → L) (a : L) : ⁅a, ∑ i ∈ s, f i⁆ = ∑ i ∈ s, ⁅a, f i⁆ :=
  let _i := LieRing.toNonUnitalNonAssocRing L
  s.mul_sum f a

theorem sum_lie_sum {κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → L) (g : κ → L) :
    ⁅(∑ i ∈ s, f i), ∑ j ∈ t, g j⁆ = ∑ i ∈ s, ∑ j ∈ t, ⁅f i, g j⁆ :=
  let _i := LieRing.toNonUnitalNonAssocRing L
  s.sum_mul_sum t f g

end BasicProperties

/-- A morphism of Lie algebras (denoted as `L₁ →ₗ⁅R⁆ L₂`)
is a linear map respecting the bracket operations. -/
structure LieHom (R L L' : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L →ₗ[R] L' where
  /-- A morphism of Lie algebras is compatible with brackets. -/
  map_lie' : ∀ {x y : L}, toFun ⁅x, y⁆ = ⁅toFun x, toFun y⁆

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

instance : FunLike (L₁ →ₗ⁅R⁆ L₂) L₁ L₂ where
  coe f := f.toFun
  coe_injective' x y h := by
    cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieHom (toFun → apply)

@[simp, norm_cast]
theorem coe_toLinearMap (f : L₁ →ₗ⁅R⁆ L₂) : ⇑(f : L₁ →ₗ[R] L₂) = f :=
  rfl

@[simp]
theorem toFun_eq_coe (f : L₁ →ₗ⁅R⁆ L₂) : f.toFun = ⇑f :=
  rfl

@[simp]
theorem map_smul (f : L₁ →ₗ⁅R⁆ L₂) (c : R) (x : L₁) : f (c • x) = c • f x :=
  LinearMap.map_smul (f : L₁ →ₗ[R] L₂) c x

@[simp]
theorem map_add (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x + y) = f x + f y :=
  LinearMap.map_add (f : L₁ →ₗ[R] L₂) x y

@[simp]
theorem map_sub (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f (x - y) = f x - f y :=
  LinearMap.map_sub (f : L₁ →ₗ[R] L₂) x y

@[simp]
theorem map_neg (f : L₁ →ₗ⁅R⁆ L₂) (x : L₁) : f (-x) = -f x :=
  LinearMap.map_neg (f : L₁ →ₗ[R] L₂) x

@[simp]
theorem map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  LieHom.map_lie' f

@[simp]
theorem map_zero (f : L₁ →ₗ⁅R⁆ L₂) : f 0 = 0 :=
  (f : L₁ →ₗ[R] L₂).map_zero

/-- The identity map is a morphism of Lie algebras. -/
def id : L₁ →ₗ⁅R⁆ L₁ :=
  { (LinearMap.id : L₁ →ₗ[R] L₁) with map_lie' := rfl }

@[simp, norm_cast]
theorem coe_id : ⇑(id : L₁ →ₗ⁅R⁆ L₁) = _root_.id :=
  rfl

theorem id_apply (x : L₁) : (id : L₁ →ₗ⁅R⁆ L₁) x = x :=
  rfl

/-- The constant 0 map is a Lie algebra morphism. -/
instance : Zero (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨{ (0 : L₁ →ₗ[R] L₂) with map_lie' := by simp }⟩

@[norm_cast, simp]
theorem coe_zero : ((0 : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = 0 :=
  rfl

theorem zero_apply (x : L₁) : (0 : L₁ →ₗ⁅R⁆ L₂) x = 0 :=
  rfl

/-- The identity map is a Lie algebra morphism. -/
instance : One (L₁ →ₗ⁅R⁆ L₁) :=
  ⟨id⟩

@[simp]
theorem coe_one : ((1 : L₁ →ₗ⁅R⁆ L₁) : L₁ → L₁) = _root_.id :=
  rfl

theorem one_apply (x : L₁) : (1 : L₁ →ₗ⁅R⁆ L₁) x = x :=
  rfl

instance : Inhabited (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨0⟩

theorem coe_injective : @Function.Injective (L₁ →ₗ⁅R⁆ L₂) (L₁ → L₂) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h
  congr

@[ext]
theorem ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

theorem congr_fun {f g : L₁ →ₗ⁅R⁆ L₂} (h : f = g) (x : L₁) : f x = g x :=
  h ▸ rfl

@[simp]
theorem mk_coe (f : L₁ →ₗ⁅R⁆ L₂) (h₁ h₂ h₃) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) = f := by
  ext
  rfl

@[simp]
theorem coe_mk (f : L₁ → L₂) (h₁ h₂ h₃) : ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f :=
  rfl

/-- The composition of morphisms is a morphism. -/
def comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      intros x y
      simp }

theorem comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) : f.comp g x = f (g x) :=
  rfl

@[norm_cast, simp]
theorem coe_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : (f.comp g : L₁ → L₃) = f ∘ g :=
  rfl

@[norm_cast, simp]
theorem toLinearMap_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
    (f.comp g : L₁ →ₗ[R] L₃) = (f : L₂ →ₗ[R] L₃).comp (g : L₁ →ₗ[R] L₂) :=
  rfl

@[deprecated (since := "2024-12-30")] alias coe_linearMap_comp := toLinearMap_comp

@[simp]
theorem comp_id (f : L₁ →ₗ⁅R⁆ L₂) : f.comp (id : L₁ →ₗ⁅R⁆ L₁) = f :=
  rfl

@[simp]
theorem id_comp (f : L₁ →ₗ⁅R⁆ L₂) : (id : L₂ →ₗ⁅R⁆ L₂).comp f = f :=
  rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intros x y
      calc
        g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ := by conv_lhs => rw [← h₂ x, ← h₂ y]
        _ = g (f ⁅g x, g y⁆) := by rw [map_lie]
        _ = ⁅g x, g y⁆ := h₁ _
         }

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
  leibniz_lie x y m := by simp only [lie_lie, sub_add_cancel, LieHom.map_lie]

theorem LieRingModule.compLieHom_apply (x : L₁) (m : M) :
    haveI := LieRingModule.compLieHom M f
    ⁅x, m⁆ = ⁅f x, m⁆ :=
  rfl

/-- A Lie module may be pulled back along a morphism of Lie algebras. -/
theorem LieModule.compLieHom [Module R M] [LieModule R L₂ M] :
    @LieModule R L₁ M _ _ _ _ _ (LieRingModule.compLieHom M f) :=
  { __ := LieRingModule.compLieHom M f
    smul_lie := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, smul_lie, LieHom.map_smul]
    lie_smul := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, lie_smul] }

end ModulePullBack

/-- An equivalence of Lie algebras (denoted as `L₁ ≃ₗ⁅R⁆ L₂`) is a morphism
which is also a linear equivalence.
We could instead define an equivalence to be a morphism which is also a (plain) equivalence.
However, it is more convenient to define via linear equivalence to get `.toLinearEquiv` for free. -/
structure LieEquiv (R : Type u) (L : Type v) (L' : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L →ₗ⁅R⁆ L' where
  /-- The inverse function of an equivalence of Lie algebras -/
  invFun : L' → L
  /-- The inverse function of an equivalence of Lie algebras is a left inverse of the underlying
  function. -/
  left_inv : Function.LeftInverse invFun toLieHom.toFun := by intro; first | rfl | ext <;> rfl
  /-- The inverse function of an equivalence of Lie algebras is a right inverse of the underlying
  function. -/
  right_inv : Function.RightInverse invFun toLieHom.toFun := by intro; first | rfl | ext <;> rfl

@[inherit_doc]
notation:50 L " ≃ₗ⁅" R "⁆ " L' => LieEquiv R L L'

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]
variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

/-- Consider an equivalence of Lie algebras as a linear equivalence. -/
def toLinearEquiv (f : L₁ ≃ₗ⁅R⁆ L₂) : L₁ ≃ₗ[R] L₂ :=
  { f.toLieHom, f with }

instance hasCoeToLieHom : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨toLieHom⟩

instance hasCoeToLinearEquiv : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) :=
  ⟨toLinearEquiv⟩

instance : EquivLike (L₁ ≃ₗ⁅R⁆ L₂) L₁ L₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]

theorem coe_toLieHom (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ →ₗ⁅R⁆ L₂) = e :=
  rfl

@[deprecated (since := "2024-12-30")] alias coe_to_lieHom := coe_toLieHom

@[simp]
theorem coe_toLinearEquiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ ≃ₗ[R] L₂) = e :=
  rfl

@[simp] theorem coe_coe (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑e.toLieHom = e := rfl

@[deprecated (since := "2024-12-30")] alias coe_to_linearEquiv := coe_toLinearEquiv

@[simp]
theorem toLinearEquiv_mk (f : L₁ →ₗ⁅R⁆ L₂) (g h₁ h₂) :
    (mk f g h₁ h₂ : L₁ ≃ₗ[R] L₂) =
      { f with
        invFun := g
        left_inv := h₁
        right_inv := h₂ } :=
  rfl

@[deprecated (since := "2024-12-30")] alias to_linearEquiv_mk := toLinearEquiv_mk

theorem toLinearEquiv_injective : Injective ((↑) : (L₁ ≃ₗ⁅R⁆ L₂) → L₁ ≃ₗ[R] L₂) := by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  intro h
  simp only [toLinearEquiv_mk, LinearEquiv.mk.injEq, LinearMap.mk.injEq, AddHom.mk.injEq] at h
  congr
  exacts [h.1, h.2]

@[deprecated (since := "2024-12-30")] alias coe_linearEquiv_injective := toLinearEquiv_injective

theorem coe_injective : @Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ → L₂) (↑) :=
  LinearEquiv.coe_injective.comp toLinearEquiv_injective

@[ext]
theorem ext {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h

instance : One (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨{ (1 : L₁ ≃ₗ[R] L₁) with map_lie' := rfl }⟩

@[simp]
theorem one_apply (x : L₁) : (1 : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl

instance : Inhabited (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨1⟩

lemma map_lie (e : L₁ ≃ₗ⁅R⁆ L₂) (x y : L₁) : e ⁅x, y⁆ = ⁅e x, e y⁆ :=
  LieHom.map_lie e.toLieHom x y

/-- Lie algebra equivalences are reflexive. -/
def refl : L₁ ≃ₗ⁅R⁆ L₁ :=
  1

@[simp]
theorem refl_apply (x : L₁) : (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl

/-- Lie algebra equivalences are symmetric. -/
@[symm]
def symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁ :=
  { LieHom.inverse e.toLieHom e.invFun e.left_inv e.right_inv, e.toLinearEquiv.symm with }

@[simp]
theorem symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (LieEquiv.symm : (L₁ ≃ₗ⁅R⁆ L₂) → L₂ ≃ₗ⁅R⁆ L₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply

@[simp]
theorem refl_symm : (refl : L₁ ≃ₗ⁅R⁆ L₁).symm = refl :=
  rfl

/-- Lie algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
  { LieHom.comp e₂.toLieHom e₁.toLieHom, LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]
theorem self_trans_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.trans e.symm = refl :=
  ext e.symm_apply_apply

@[simp]
theorem symm_trans_self (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.trans e = refl :=
  e.symm.self_trans_symm

@[simp]
theorem trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
theorem symm_trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

protected theorem bijective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Bijective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.bijective

protected theorem injective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Injective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.injective

protected theorem surjective (e : L₁ ≃ₗ⁅R⁆ L₂) :
    Function.Surjective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.surjective

/-- A bijective morphism of Lie algebras yields an equivalence of Lie algebras. -/
@[simps!]
noncomputable def ofBijective (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Bijective f) : L₁ ≃ₗ⁅R⁆ L₂ :=
  { LinearEquiv.ofBijective (f : L₁ →ₗ[R] L₂)
      h with
    toFun := f
    map_lie' := by intros x y; exact f.map_lie x y }

end LieEquiv

section LieModuleMorphisms

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]
variable [LieRingModule L M] [LieRingModule L N] [LieRingModule L P]

/-- A morphism of Lie algebra modules (denoted as `M →ₗ⁅R,L⁆ N`) is a linear map
which commutes with the action of the Lie algebra. -/
structure LieModuleHom extends M →ₗ[R] N where
  /-- A module of Lie algebra modules is compatible with the action of the Lie algebra on the
  modules. -/
  map_lie' : ∀ {x : L} {m : M}, toFun ⁅x, m⁆ = ⁅x, toFun m⁆

@[inherit_doc]
notation:25 M " →ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleHom R L M N

namespace LieModuleHom

variable {R L M N P}

attribute [coe] LieModuleHom.toLinearMap

instance : CoeOut (M →ₗ⁅R,L⁆ N) (M →ₗ[R] N) :=
  ⟨LieModuleHom.toLinearMap⟩

instance : FunLike (M →ₗ⁅R, L⁆ N) M N where
  coe f := f.toFun
  coe_injective' x y h := by cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieModuleHom (toFun → apply)

@[simp, norm_cast]
theorem coe_toLinearMap (f : M →ₗ⁅R,L⁆ N) : ((f : M →ₗ[R] N) : M → N) = f :=
  rfl

@[simp]
theorem map_smul (f : M →ₗ⁅R,L⁆ N) (c : R) (x : M) : f (c • x) = c • f x :=
  LinearMap.map_smul (f : M →ₗ[R] N) c x

@[simp]
theorem map_add (f : M →ₗ⁅R,L⁆ N) (x y : M) : f (x + y) = f x + f y :=
  LinearMap.map_add (f : M →ₗ[R] N) x y

@[simp]
theorem map_sub (f : M →ₗ⁅R,L⁆ N) (x y : M) : f (x - y) = f x - f y :=
  LinearMap.map_sub (f : M →ₗ[R] N) x y

@[simp]
theorem map_neg (f : M →ₗ⁅R,L⁆ N) (x : M) : f (-x) = -f x :=
  LinearMap.map_neg (f : M →ₗ[R] N) x

@[simp]
theorem map_lie (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆ :=
  LieModuleHom.map_lie' f

variable [LieAlgebra R L] [LieModule R L N] [LieModule R L P] in
theorem map_lie₂ (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (x : L) (m : M) (n : N) :
    ⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆ := by simp only [sub_add_cancel, map_lie, LieHom.lie_apply]

@[simp]
theorem map_zero (f : M →ₗ⁅R,L⁆ N) : f 0 = 0 :=
  LinearMap.map_zero (f : M →ₗ[R] N)

/-- The identity map is a morphism of Lie modules. -/
def id : M →ₗ⁅R,L⁆ M :=
  { (LinearMap.id : M →ₗ[R] M) with map_lie' := rfl }

@[simp, norm_cast]
theorem coe_id : ((id : M →ₗ⁅R,L⁆ M) : M → M) = _root_.id :=
  rfl

theorem id_apply (x : M) : (id : M →ₗ⁅R,L⁆ M) x = x :=
  rfl

/-- The constant 0 map is a Lie module morphism. -/
instance : Zero (M →ₗ⁅R,L⁆ N) :=
  ⟨{ (0 : M →ₗ[R] N) with map_lie' := by simp }⟩

@[norm_cast, simp]
theorem coe_zero : ⇑(0 : M →ₗ⁅R,L⁆ N) = 0 :=
  rfl

theorem zero_apply (m : M) : (0 : M →ₗ⁅R,L⁆ N) m = 0 :=
  rfl

/-- The identity map is a Lie module morphism. -/
instance : One (M →ₗ⁅R,L⁆ M) :=
  ⟨id⟩

instance : Inhabited (M →ₗ⁅R,L⁆ N) :=
  ⟨0⟩

theorem coe_injective : @Function.Injective (M →ₗ⁅R,L⁆ N) (M → N) (↑) := by
  rintro ⟨⟨⟨f, _⟩⟩⟩ ⟨⟨⟨g, _⟩⟩⟩ h
  congr

@[ext]
theorem ext {f g : M →ₗ⁅R,L⁆ N} (h : ∀ m, f m = g m) : f = g :=
  coe_injective <| funext h

theorem congr_fun {f g : M →ₗ⁅R,L⁆ N} (h : f = g) (x : M) : f x = g x :=
  h ▸ rfl

@[simp]
theorem mk_coe (f : M →ₗ⁅R,L⁆ N) (h) : (⟨f, h⟩ : M →ₗ⁅R,L⁆ N) = f := by
  rfl

@[simp]
theorem coe_mk (f : M →ₗ[R] N) (h) : ((⟨f, h⟩ : M →ₗ⁅R,L⁆ N) : M → N) = f := by
  rfl

@[norm_cast]
theorem coe_linear_mk (f : M →ₗ[R] N) (h) : ((⟨f, h⟩ : M →ₗ⁅R,L⁆ N) : M →ₗ[R] N) = f := by
  rfl

/-- The composition of Lie module morphisms is a morphism. -/
def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      intros x m
      simp }

theorem comp_apply (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) (m : M) : f.comp g m = f (g m) :=
  rfl

@[norm_cast, simp]
theorem coe_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[norm_cast, simp]
theorem toLinearMap_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) :
    (f.comp g : M →ₗ[R] P) = (f : N →ₗ[R] P).comp (g : M →ₗ[R] N) :=
  rfl

@[deprecated (since := "2024-12-30")] alias coe_linearMap_comp := toLinearMap_comp

/-- The inverse of a bijective morphism of Lie modules is a morphism of Lie modules. -/
def inverse (f : M →ₗ⁅R,L⁆ N) (g : N → M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₗ⁅R,L⁆ M :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intros x n
      calc
        g ⁅x, n⁆ = g ⁅x, f (g n)⁆ := by rw [h₂]
        _ = g (f ⁅x, g n⁆) := by rw [map_lie]
        _ = ⁅x, g n⁆ := h₁ _
         }

instance : Add (M →ₗ⁅R,L⁆ N) where
  add f g := { (f : M →ₗ[R] N) + (g : M →ₗ[R] N) with map_lie' := by simp }

instance : Sub (M →ₗ⁅R,L⁆ N) where
  sub f g := { (f : M →ₗ[R] N) - (g : M →ₗ[R] N) with map_lie' := by simp }

instance : Neg (M →ₗ⁅R,L⁆ N) where neg f := { -(f : M →ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
theorem coe_add (f g : M →ₗ⁅R,L⁆ N) : ⇑(f + g) = f + g :=
  rfl

theorem add_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m :=
  rfl

@[norm_cast, simp]
theorem coe_sub (f g : M →ₗ⁅R,L⁆ N) : ⇑(f - g) = f - g :=
  rfl

theorem sub_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f - g) m = f m - g m :=
  rfl

@[norm_cast, simp]
theorem coe_neg (f : M →ₗ⁅R,L⁆ N) : ⇑(-f) = -f :=
  rfl

theorem neg_apply (f : M →ₗ⁅R,L⁆ N) (m : M) : (-f) m = -f m :=
  rfl

instance hasNSMul : SMul ℕ (M →ₗ⁅R,L⁆ N) where
  smul n f := { n • (f : M →ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
theorem coe_nsmul (n : ℕ) (f : M →ₗ⁅R,L⁆ N) : ⇑(n • f) = n • (⇑f) :=
  rfl

theorem nsmul_apply (n : ℕ) (f : M →ₗ⁅R,L⁆ N) (m : M) : (n • f) m = n • f m :=
  rfl

instance hasZSMul : SMul ℤ (M →ₗ⁅R,L⁆ N) where
  smul z f := { z • (f : M →ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
theorem coe_zsmul (z : ℤ) (f : M →ₗ⁅R,L⁆ N) : ⇑(z • f) = z • (⇑f) :=
  rfl

theorem zsmul_apply (z : ℤ) (f : M →ₗ⁅R,L⁆ N) (m : M) : (z • f) m = z • f m :=
  rfl

instance : AddCommGroup (M →ₗ⁅R,L⁆ N) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    (fun _ _ => coe_zsmul _ _)

variable [LieAlgebra R L] [LieModule R L N]

instance : SMul R (M →ₗ⁅R,L⁆ N) where
  smul t f := { t • (f : M →ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
theorem coe_smul (t : R) (f : M →ₗ⁅R,L⁆ N) : ⇑(t • f) = t • (⇑f) :=
  rfl

theorem smul_apply (t : R) (f : M →ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • f m :=
  rfl

instance : Module R (M →ₗ⁅R,L⁆ N) :=
  Function.Injective.module R
    { toFun := fun f => f.toLinearMap.toFun, map_zero' := rfl, map_add' := coe_add }
    coe_injective coe_smul

end LieModuleHom

/-- An equivalence of Lie algebra modules (denoted as `M ≃ₗ⁅R,L⁆ N`) is a linear equivalence
which is also a morphism of Lie algebra modules. -/
structure LieModuleEquiv extends M →ₗ⁅R,L⁆ N where
  /-- The inverse function of an equivalence of Lie modules -/
  invFun : N → M
  /-- The inverse function of an equivalence of Lie modules is a left inverse of the underlying
  function. -/
  left_inv : Function.LeftInverse invFun toFun
  /-- The inverse function of an equivalence of Lie modules is a right inverse of the underlying
  function. -/
  right_inv : Function.RightInverse invFun toFun

attribute [nolint docBlame] LieModuleEquiv.toLieModuleHom

@[inherit_doc]
notation:25 M " ≃ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleEquiv R L M N

namespace LieModuleEquiv

variable {R L M N P}

/-- View an equivalence of Lie modules as a linear equivalence. -/
def toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ₗ[R] N :=
  { e with }

/-- View an equivalence of Lie modules as a type level equivalence. -/
def toEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ N :=
  { e with }

instance hasCoeToEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ N) :=
  ⟨toEquiv⟩

instance hasCoeToLieModuleHom : Coe (M ≃ₗ⁅R,L⁆ N) (M →ₗ⁅R,L⁆ N) :=
  ⟨toLieModuleHom⟩

instance hasCoeToLinearEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N) :=
  ⟨toLinearEquiv⟩

instance : EquivLike (M ≃ₗ⁅R,L⁆ N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]

@[simp] lemma coe_coe (e : M ≃ₗ⁅R,L⁆ N) : ⇑(e : M →ₗ⁅R,L⁆ N) = e := rfl

theorem injective (e : M ≃ₗ⁅R,L⁆ N) : Function.Injective e :=
  e.toEquiv.injective

theorem surjective (e : M ≃ₗ⁅R,L⁆ N) : Function.Surjective e :=
  e.toEquiv.surjective

@[simp]
theorem toEquiv_mk (f : M →ₗ⁅R,L⁆ N) (g : N → M) (h₁ h₂) :
    toEquiv (mk f g h₁ h₂ : M ≃ₗ⁅R,L⁆ N) = Equiv.mk f g h₁ h₂ :=
  rfl

@[simp]
theorem coe_mk (f : M →ₗ⁅R,L⁆ N) (invFun h₁ h₂) :
    ((⟨f, invFun, h₁, h₂⟩ : M ≃ₗ⁅R,L⁆ N) : M → N) = f :=
  rfl

theorem coe_toLieModuleHom (e : M ≃ₗ⁅R,L⁆ N) : ⇑(e : M →ₗ⁅R,L⁆ N) = e :=
  rfl

@[deprecated (since := "2024-12-30")] alias coe_to_lieModuleHom := coe_toLieModuleHom

@[simp]
theorem coe_toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M → N) = e :=
  rfl

@[deprecated (since := "2024-12-30")] alias coe_to_linearEquiv := coe_toLinearEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃ₗ⁅R,L⁆ N) → M ≃ N) := by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  intro h
  simp only [toEquiv_mk, LieModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Equiv.mk.injEq] at h
  congr
  exacts [h.1, h.2]

@[ext]
theorem ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : ∀ m, e₁ m = e₂ m) : e₁ = e₂ :=
  toEquiv_injective (Equiv.ext h)

instance : One (M ≃ₗ⁅R,L⁆ M) :=
  ⟨{ (1 : M ≃ₗ[R] M) with map_lie' := rfl }⟩

@[simp]
theorem one_apply (m : M) : (1 : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl

instance : Inhabited (M ≃ₗ⁅R,L⁆ M) :=
  ⟨1⟩

/-- Lie module equivalences are reflexive. -/
@[refl]
def refl : M ≃ₗ⁅R,L⁆ M :=
  1

@[simp]
theorem refl_apply (m : M) : (refl : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl

/-- Lie module equivalences are symmetric. -/
@[symm]
def symm (e : M ≃ₗ⁅R,L⁆ N) : N ≃ₗ⁅R,L⁆ M :=
  { LieModuleHom.inverse e.toLieModuleHom e.invFun e.left_inv e.right_inv,
    (e : M ≃ₗ[R] N).symm with }

@[simp]
theorem apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply

theorem apply_eq_iff_eq_symm_apply {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) :
    e m = n ↔ m = e.symm n :=
  (e : M ≃ N).apply_eq_iff_eq_symm_apply

@[simp]
theorem symm_symm (e : M ≃ₗ⁅R,L⁆ N) : e.symm.symm = e := rfl

theorem symm_bijective :
    Function.Bijective (LieModuleEquiv.symm : (M ≃ₗ⁅R,L⁆ N) → N ≃ₗ⁅R,L⁆ M) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- Lie module equivalences are transitive. -/
@[trans]
def trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : M ≃ₗ⁅R,L⁆ P :=
  { LieModuleHom.comp e₂.toLieModuleHom e₁.toLieModuleHom,
    LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]
theorem trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M) : (e₁.trans e₂) m = e₂ (e₁ m) :=
  rfl

@[simp]
theorem symm_trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
theorem self_trans_symm (e : M ≃ₗ⁅R,L⁆ N) : e.trans e.symm = refl :=
  ext _ _ e.symm_apply_apply

@[simp]
theorem symm_trans_self (e : M ≃ₗ⁅R,L⁆ N) : e.symm.trans e = refl :=
  ext _ _ e.apply_symm_apply

end LieModuleEquiv

end LieModuleMorphisms
