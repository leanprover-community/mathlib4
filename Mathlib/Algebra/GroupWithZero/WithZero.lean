/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Algebra.GroupWithZero.Equiv
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Option.Basic
import Mathlib.Data.Option.NAry

/-!
# Adjoining a zero to a group

This file proves that one can adjoin a new zero element to a group and get a group with zero.

In valuation theory, valuations have codomain `{0} ∪ {c ^ n | n : ℤ}` for some `c > 1`, which we can
formalise as `ℤᵐ⁰ := WithZero (Multiplicative ℤ)`. It is important to be able to talk about the maps
`n ↦ c ^ n` and `c ^ n ↦ n`. We define these as `exp : ℤ → ℤᵐ⁰` and `log : ℤᵐ⁰ → ℤ` with junk value
`log 0 = 0`. Junkless versions are defined as `expEquiv : ℤ ≃ ℤᵐ⁰ˣ` and `logEquiv : ℤᵐ⁰ˣ ≃ ℤ`.

## Notation

In scope `WithZero`:
* `Mᵐ⁰` for `WithZero (Multiplicative M)`

## Main definitions

* `WithZero.map'`: the `MonoidWithZero` homomorphism `WithZero α →* WithZero β` induced by
  a monoid homomorphism `f : α →* β`.
* `WithZero.exp`: The "exponential map" `M → Mᵐ⁰`
* `WithZero.exp`: The "logarithm" `Mᵐ⁰ → M`
-/

open Function

assert_not_exists DenselyOrdered Ring

namespace WithZero
variable {α β γ : Type*}

section One
variable [One α]

instance one : One (WithZero α) where
  __ := ‹One α›

@[simp, norm_cast] lemma coe_one : ((1 : α) : WithZero α) = 1 := rfl

@[simp]
lemma recZeroCoe_one {M N : Type*} [One M] (f : M → N) (z : N) :
    recZeroCoe z f 1 = f 1 :=
  rfl

end One

section Mul
variable [Mul α]

instance instMulZeroClass : MulZeroClass (WithZero α) where
  mul := Option.map₂ (· * ·)
  zero_mul := Option.map₂_none_left (· * ·)
  mul_zero := Option.map₂_none_right (· * ·)

@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithZero α) = a * b := rfl

lemma unzero_mul {x y : WithZero α} (hxy : x * y ≠ 0) :
    unzero hxy = unzero (left_ne_zero_of_mul hxy) * unzero (right_ne_zero_of_mul hxy) := by
  simp only [← coe_inj, coe_mul, coe_unzero]

instance instNoZeroDivisors : NoZeroDivisors (WithZero α) := ⟨Option.map₂_eq_none_iff.1⟩

end Mul

instance instSemigroupWithZero [Semigroup α] : SemigroupWithZero (WithZero α) where
  mul_assoc _ _ _ := Option.map₂_assoc mul_assoc

instance instCommSemigroup [CommSemigroup α] : CommSemigroup (WithZero α) where
  mul_comm _ _ := Option.map₂_comm mul_comm

section MulOneClass
variable [MulOneClass α]

instance instMulZeroOneClass [MulOneClass α] : MulZeroOneClass (WithZero α) where
  one_mul := Option.map₂_left_identity one_mul
  mul_one := Option.map₂_right_identity mul_one

/-- Coercion as a monoid hom. -/
@[simps apply]
def coeMonoidHom : α →* WithZero α where
  toFun        := (↑)
  map_one'     := rfl
  map_mul' _ _ := rfl

section lift
variable [MulZeroOneClass β]

-- See note [partially-applied ext lemmas]
@[ext high]
theorem monoidWithZeroHom_ext ⦃f g : WithZero α →*₀ β⦄
    (h : f.toMonoidHom.comp coeMonoidHom = g.toMonoidHom.comp coeMonoidHom) :
    f = g :=
  DFunLike.ext _ _ fun
    | 0 => (map_zero f).trans (map_zero g).symm
    | (g : α) => DFunLike.congr_fun h g

/-- The (multiplicative) universal property of `WithZero`. -/
@[simps! symm_apply_apply]
nonrec def lift' : (α →* β) ≃ (WithZero α →*₀ β) where
  toFun f :=
    { toFun := recZeroCoe 0 f
      map_zero' := rfl
      map_one' := by simp
      map_mul' := fun
        | 0, _ => (zero_mul _).symm
        | (_ : α), 0 => (mul_zero _).symm
        | (_ : α), (_ : α) => map_mul f _ _ }
  invFun F := F.toMonoidHom.comp coeMonoidHom

lemma lift'_zero (f : α →* β) : lift' f (0 : WithZero α) = 0 := rfl

@[simp] lemma lift'_coe (f : α →* β) (x : α) : lift' f (x : WithZero α) = f x := rfl

lemma lift'_unique (f : WithZero α →*₀ β) : f = lift' (f.toMonoidHom.comp coeMonoidHom) :=
  (lift'.apply_symm_apply f).symm

lemma lift'_surjective {f : α →* β} (hf : Surjective f) :
    Surjective (lift' f) := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, by simp⟩

end lift

variable [MulOneClass β] [MulOneClass γ]

/-- The `MonoidWithZero` homomorphism `WithZero α →* WithZero β` induced by a monoid homomorphism
  `f : α →* β`. -/
def map' (f : α →* β) : WithZero α →*₀ WithZero β := lift' (coeMonoidHom.comp f)

lemma map'_zero (f : α →* β) : map' f 0 = 0 := rfl

@[simp] lemma map'_coe (f : α →* β) (x : α) : map' f (x : WithZero α) = f x := rfl

@[simp]
lemma map'_id : map' (MonoidHom.id β) = MonoidHom.id (WithZero β) := by
  ext x; induction x <;> rfl

lemma map'_map' (f : α →* β) (g : β →* γ) (x) : map' g (map' f x) = map' (g.comp f) x := by
  induction x <;> rfl

@[simp]
lemma map'_comp (f : α →* β) (g : β →* γ) : map' (g.comp f) = (map' g).comp (map' f) :=
  MonoidWithZeroHom.ext fun x => (map'_map' f g x).symm

lemma map'_injective_iff {f : α →* β} : Injective (map' f) ↔ Injective f := by
  simp [Injective, WithZero.forall]

alias ⟨_, map'_injective⟩ := map'_injective_iff

lemma map'_surjective_iff {f : α →* β} : Surjective (map' f) ↔ Surjective f := by
  simp only [Surjective, «forall»]
  refine ⟨fun h b ↦ ?_, fun h ↦ ⟨⟨0, by simp⟩, fun b ↦ ?_⟩⟩
  · obtain ⟨a, hab⟩ := h.2 b
    induction a using WithZero.recZeroCoe <;>
    simp at hab
    grind
  · obtain ⟨a, ha⟩ := h b
    use a
    simp [ha]

alias ⟨_, map'_surjective⟩ := map'_surjective_iff

end MulOneClass

section Pow
variable [One α] [Pow α ℕ]

instance pow : Pow (WithZero α) ℕ where
  pow
    | none, 0 => 1
    | none, _ + 1 => 0
    | some x, n => ↑(x ^ n)

@[simp, norm_cast] lemma coe_pow (a : α) (n : ℕ) : (↑(a ^ n) : WithZero α) = a ^ n := rfl

end Pow

instance instMonoidWithZero [Monoid α] : MonoidWithZero (WithZero α) where
  npow n a := a ^ n
  npow_zero
    | 0 => rfl
    | some _ => congr_arg some (pow_zero _)
  npow_succ
    | n, 0 => by simp only [mul_zero]; rfl
    | n, some _ => congr_arg some <| pow_succ _ _

instance instCommMonoidWithZero [CommMonoid α] : CommMonoidWithZero (WithZero α) :=
  { WithZero.instMonoidWithZero, WithZero.instCommSemigroup with }

section Inv
variable [Inv α]

/-- Extend the inverse operation on `α` to `WithZero α` by sending `0` to `0`. -/
instance inv : Inv (WithZero α) where inv a := Option.map (·⁻¹) a

@[simp, norm_cast] lemma coe_inv (a : α) : ((a⁻¹ : α) : WithZero α) = (↑a)⁻¹ := rfl

@[simp] protected lemma inv_zero : (0 : WithZero α)⁻¹ = 0 := rfl

end Inv

instance invOneClass [InvOneClass α] : InvOneClass (WithZero α) where
  inv_one := show ((1⁻¹ : α) : WithZero α) = 1 by simp

section Div
variable [Div α]

instance div : Div (WithZero α) where div := Option.map₂ (· / ·)

@[norm_cast] lemma coe_div (a b : α) : ↑(a / b : α) = (a / b : WithZero α) := rfl

end Div

section ZPow
variable [One α] [Pow α ℤ]

instance : Pow (WithZero α) ℤ where
  pow
    | none, Int.ofNat 0 => 1
    | none, Int.ofNat (Nat.succ _) => 0
    | none, Int.negSucc _ => 0
    | some x, n => ↑(x ^ n)

@[simp, norm_cast] lemma coe_zpow (a : α) (n : ℤ) : ↑(a ^ n) = (↑a : WithZero α) ^ n := rfl

end ZPow

instance instDivInvMonoid [DivInvMonoid α] : DivInvMonoid (WithZero α) where
  div_eq_mul_inv
    | none, _ => rfl
    | some _, none => rfl
    | some a, some b => congr_arg some (div_eq_mul_inv a b)
  zpow n a := a ^ n
  zpow_zero'
    | none => rfl
    | some _ => congr_arg some (zpow_zero _)
  zpow_succ'
    | n, none => by change 0 ^ _ = 0 ^ _ * 0; simp only [mul_zero]; rfl
    | n, some _ => congr_arg some (DivInvMonoid.zpow_succ' _ _)
  zpow_neg'
    | n, none => rfl
    | n, some _ => congr_arg some (DivInvMonoid.zpow_neg' _ _)

instance instDivInvOneMonoid [DivInvOneMonoid α] : DivInvOneMonoid (WithZero α) where

instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv (WithZero α) where
  inv_inv a := (Option.map_map _ _ _).trans <| by simp

instance instDivisionMonoid [DivisionMonoid α] : DivisionMonoid (WithZero α) where
  mul_inv_rev
    | none, none => rfl
    | none, some _ => rfl
    | some _, none => rfl
    | some _, some _ => congr_arg some (mul_inv_rev _ _)
  inv_eq_of_mul
    | none, none, _ => rfl
    | some _, some _, h =>
      congr_arg some <| inv_eq_of_mul_eq_one_right <| Option.some_injective _ h

instance instDivisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (WithZero α) where

section Group
variable [Group α]

/-- If `α` is a group then `WithZero α` is a group with zero. -/
instance instGroupWithZero : GroupWithZero (WithZero α) where
  inv_zero := WithZero.inv_zero
  mul_inv_cancel a ha := by
    lift a to α using ha
    norm_cast
    apply mul_inv_cancel

/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
@[simps]
def unitsWithZeroEquiv : (WithZero α)ˣ ≃* α where
  toFun a := unzero a.ne_zero
  invFun a := Units.mk0 a coe_ne_zero
  left_inv _ := Units.ext <| by simp only [coe_unzero, Units.mk0_val]
  map_mul' _ _ := coe_inj.mp <| by simp only [Units.val_mul, coe_unzero, coe_mul]

instance [Nontrivial α] : Nontrivial (WithZero α)ˣ :=
  unitsWithZeroEquiv.toEquiv.surjective.nontrivial

theorem coe_unitsWithZeroEquiv_eq_units_val (γ : (WithZero α)ˣ) :
    ↑(unitsWithZeroEquiv γ) = γ.val := by
  simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]

/-- Any group with zero is isomorphic to adjoining `0` to the units of itself. -/
@[simps]
def withZeroUnitsEquiv {G : Type*} [GroupWithZero G]
    [DecidablePred (fun a : G ↦ a = 0)] :
    WithZero Gˣ ≃* G where
  toFun := WithZero.recZeroCoe 0 Units.val
  invFun a := if h : a = 0 then 0 else (Units.mk0 a h : Gˣ)
  left_inv := (by induction · <;> simp)
  right_inv _ := by simp only; split <;> simp_all
  map_mul' := (by induction · <;> induction · <;> simp [← WithZero.coe_mul])

lemma withZeroUnitsEquiv_symm_apply_coe {G : Type*} [GroupWithZero G]
    [DecidablePred (fun a : G ↦ a = 0)] (a : Gˣ) :
    WithZero.withZeroUnitsEquiv.symm (a : G) = a := by
  simp

/-- A version of `Equiv.optionCongr` for `WithZero`. -/
@[simps!]
def _root_.MulEquiv.withZero [Group β] :
    (α ≃* β) ≃ (WithZero α ≃* WithZero β) where
  toFun e := ⟨⟨map' e, map' e.symm, (by induction · <;> simp), (by induction · <;> simp)⟩,
    (by induction · <;> induction · <;> simp)⟩
  invFun e := ⟨⟨
    fun x ↦ unzero (x := e x) (by simp [ne_eq, ← e.eq_symm_apply]),
    fun x ↦ unzero (x := e.symm x) (by simp [e.symm_apply_eq]),
    by intro; simp, by intro; simp⟩,
    by intro; simp [← coe_inj]⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext x; cases x <;> simp

/-- The inverse of `MulEquiv.withZero`. -/
abbrev _root_.MulEquiv.unzero [Group β] (e : WithZero α ≃* WithZero β) :
    α ≃* β :=
  _root_.MulEquiv.withZero.symm e

end Group

instance instCommGroupWithZero [CommGroup α] : CommGroupWithZero (WithZero α) where

instance instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (WithZero α) where
  natCast n := if n = 0 then 0 else (n : α)
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp

/-! ### Exponential and logarithm -/

variable {M G : Type*}

/-- `Mᵐ⁰` is notation for `WithZero (Multiplicative M)`.

This naturally shows up as the codomain of valuations in valuation theory. -/
scoped notation:1024 M:1024 "ᵐ⁰" => WithZero <| Multiplicative M

section AddMonoid

/-- The exponential map as a function `M → Mᵐ⁰`. -/
def exp (a : M) : Mᵐ⁰ := coe <| .ofAdd a

@[simp] lemma exp_ne_zero {a : M} : exp a ≠ 0 := by simp [exp]

lemma exp_injective : Injective (exp : M → Mᵐ⁰) :=
  Multiplicative.ofAdd.injective.comp WithZero.coe_injective

@[simp] lemma exp_inj {x y : M} : exp x = exp y ↔ x = y := exp_injective.eq_iff

variable [AddMonoid M]

/-- The logarithm as a function `Mᵐ⁰ → M` with junk value `log 0 = 0`. -/
def log (x : Mᵐ⁰) : M := x.recZeroCoe 0 Multiplicative.toAdd

@[simp] lemma log_exp (a : M) : log (exp a) = a := rfl
@[simp] lemma exp_log {x : Mᵐ⁰} (hx : x ≠ 0) : exp (log x) = x := by
  lift x to Multiplicative M using hx; rfl

@[simp] lemma log_zero : log 0 = (0 : M) := rfl

@[simp] lemma exp_zero : exp (0 : M) = 1 := rfl
@[simp] lemma exp_eq_one {x : M} : exp x = 1 ↔ x = 0 := by
  rw [← exp_zero, exp_inj]

@[simp] lemma log_one : log 1 = (0 : M) := rfl

@[simp] lemma exp_add (a b : M) : exp (a + b) = exp a * exp b := rfl

@[simp]
lemma log_mul {x y : Mᵐ⁰} (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y := by
  lift x to Multiplicative M using hx; lift y to Multiplicative M using hy; rfl

@[simp← ] lemma exp_nsmul (n : ℕ) (a : M) : exp (n • a) = exp a ^ n := rfl

@[simp]
lemma log_pow : ∀ (x : Mᵐ⁰) (n : ℕ), log (x ^ n) = n • log x
  | 0, 0 => by simp
  | 0, n + 1 => by simp
  | (x : Multiplicative M), n => rfl

end AddMonoid

section AddGroup
variable [AddGroup G]

/-- The exponential map as an equivalence between `G` and `(Gᵐ⁰)ˣ`. -/
def expEquiv : G ≃ (Gᵐ⁰)ˣ := Multiplicative.ofAdd.trans unitsWithZeroEquiv.symm.toEquiv

/-- The logarithm as an equivalence between `(Gᵐ⁰)ˣ` and `G`. -/
def logEquiv : (Gᵐ⁰)ˣ ≃ G := unitsWithZeroEquiv.toEquiv.trans Multiplicative.toAdd

@[simp] lemma logEquiv_symm : (logEquiv (G := G)).symm = expEquiv := rfl
@[simp] lemma expEquiv_symm : (expEquiv (G := G)).symm = logEquiv := rfl

@[simp] lemma coe_expEquiv_apply (a : G) : expEquiv a = exp a := rfl

@[simp] lemma logEquiv_apply (x : (Gᵐ⁰)ˣ) : logEquiv x = log x := by
  obtain ⟨_ | a, _ | b, hab, hba⟩ := x
  · cases hab
  · cases hab
  · cases hab
  · rfl

lemma logEquiv_unitsMk0 (x : Gᵐ⁰) (hx) : logEquiv (.mk0 x hx) = log x := logEquiv_apply _

@[simp] lemma exp_sub (a b : G) : exp (a - b) = exp a / exp b  := rfl

@[simp]
lemma log_div {x y : Gᵐ⁰} (hx : x ≠ 0) (hy : y ≠ 0) : log (x / y) = log x - log y := by
  lift x to Multiplicative G using hx; lift y to Multiplicative G using hy; rfl

@[simp] lemma exp_neg (a : G) : exp (-a) = (exp a)⁻¹  := rfl

@[simp]
lemma log_inv : ∀ x : Gᵐ⁰, log x⁻¹ = -log x
  | 0 => by simp
  | (x : Multiplicative G) => rfl

@[simp← ] lemma exp_zsmul (n : ℤ) (a : G) : exp (n • a) = exp a ^ n := rfl

@[simp]
lemma log_zpow (x : Gᵐ⁰) (n : ℤ) : log (x ^ n) = n • log x := by cases n <;> simp [log_pow, log_inv]

end AddGroup
end WithZero

namespace MonoidWithZeroHom

protected lemma map_eq_zero_iff {G₀ M₀ : Type*} [GroupWithZero G₀] [MulZeroOneClass M₀]
    [Nontrivial M₀] {f : G₀ →*₀ M₀} {x : G₀} : f x = 0 ↔ x = 0 := by
  refine ⟨?_, by simp +contextual⟩
  contrapose!
  intro hx H
  lift x to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀)
  rw [← map_one f, ← Units.mul_inv x, map_mul, H, zero_mul]

@[simp]
lemma one_apply_val_unit {M₀ N₀ : Type*} [MonoidWithZero M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] (x : M₀ˣ) :
    (1 : M₀ →*₀ N₀) x = (1 : N₀) :=
  one_apply_of_ne_zero x.ne_zero

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
lemma apply_one_apply_eq {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ ↦ x = 0]
    (f : N₀ →*₀ G₀) (x : M₀) :
    f ((1 : M₀ →*₀ N₀) x) = (1 : M₀ →*₀ G₀) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero hx, map_one]

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
lemma comp_one {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ ↦ x = 0]
    (f : N₀ →*₀ G₀) :
    f.comp (1 : M₀ →*₀ N₀) = (1 : M₀ →*₀ G₀) :=
  ext <| apply_one_apply_eq _

end MonoidWithZeroHom
