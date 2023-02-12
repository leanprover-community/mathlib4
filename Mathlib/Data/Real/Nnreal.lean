/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.real.nnreal
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Group
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Order.Nonneg.Field
import Mathbin.Algebra.Order.Field.Canonical.Basic
import Mathbin.Data.Real.Pointwise
import Mathbin.Tactic.Positivity

/-!
# Nonnegative real numbers

In this file we define `nnreal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `conditionally_complete_linear_order_bot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `linear_ordered_semiring ℝ≥0`;
  - `ordered_comm_semiring ℝ≥0`;
  - `canonically_ordered_comm_semiring ℝ≥0`;
  - `linear_ordered_comm_group_with_zero ℝ≥0`;
  - `canonically_linear_ordered_add_monoid ℝ≥0`;
  - `archimedean ℝ≥0`;
  - `conditionally_complete_linear_order_bot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`. See `algebra/order/nonneg`.

* `real.to_nnreal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(real.to_nnreal x) = x` when `0 ≤ x` and
  `↑(real.to_nnreal x) = 0` otherwise.

We also define an instance `can_lift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `nnreal`.
-/


open Classical BigOperators

-- to ensure these instances are computable
/-- Nonnegative real numbers. -/
def Nnreal :=
  { r : ℝ // 0 ≤ r }deriving StrictOrderedSemiring, CommMonoidWithZero, FloorSemiring, CommSemiring,
  Semiring, SemilatticeInf, SemilatticeSup, DistribLattice, DenselyOrdered, OrderBot,
  CanonicallyLinearOrderedSemifield, LinearOrderedCommGroupWithZero, Archimedean,
  LinearOrderedSemiring, OrderedCommSemiring, CanonicallyOrderedCommSemiring, Sub, OrderedSub, Div,
  Inhabited
#align nnreal Nnreal

-- mathport name: nnreal
scoped[Nnreal] notation "ℝ≥0" => Nnreal

namespace Nnreal

instance : Coe ℝ≥0 ℝ :=
  ⟨Subtype.val⟩

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (n : ℝ≥0) : n.val = n :=
  rfl
#align nnreal.val_eq_coe Nnreal.val_eq_coe

instance canLift : CanLift ℝ ℝ≥0 coe fun r => 0 ≤ r :=
  Subtype.canLift _
#align nnreal.can_lift Nnreal.canLift

protected theorem eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m :=
  Subtype.eq
#align nnreal.eq Nnreal.eq

protected theorem eq_iff {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) ↔ n = m :=
  Iff.intro Nnreal.eq (congr_arg coe)
#align nnreal.eq_iff Nnreal.eq_iff

theorem ne_iff {x y : ℝ≥0} : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
  not_congr <| Nnreal.eq_iff
#align nnreal.ne_iff Nnreal.ne_iff

protected theorem forall {p : ℝ≥0 → Prop} : (∀ x : ℝ≥0, p x) ↔ ∀ (x : ℝ) (hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.forall
#align nnreal.forall Nnreal.forall

protected theorem exists {p : ℝ≥0 → Prop} : (∃ x : ℝ≥0, p x) ↔ ∃ (x : ℝ)(hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.exists
#align nnreal.exists Nnreal.exists

/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
noncomputable def Real.toNnreal (r : ℝ) : ℝ≥0 :=
  ⟨max r 0, le_max_right _ _⟩
#align real.to_nnreal Real.toNnreal

theorem Real.coe_toNnreal (r : ℝ) (hr : 0 ≤ r) : (Real.toNnreal r : ℝ) = r :=
  max_eq_left hr
#align real.coe_to_nnreal Real.coe_toNnreal

theorem Real.toNnreal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r.toNnreal = ⟨r, hr⟩ := by
  simp_rw [Real.toNnreal, max_eq_left hr]
#align real.to_nnreal_of_nonneg Real.toNnreal_of_nonneg

theorem Real.le_coe_toNnreal (r : ℝ) : r ≤ Real.toNnreal r :=
  le_max_left r 0
#align real.le_coe_to_nnreal Real.le_coe_toNnreal

theorem coe_nonneg (r : ℝ≥0) : (0 : ℝ) ≤ r :=
  r.2
#align nnreal.coe_nonneg Nnreal.coe_nonneg

@[norm_cast]
theorem coe_mk (a : ℝ) (ha) : ((⟨a, ha⟩ : ℝ≥0) : ℝ) = a :=
  rfl
#align nnreal.coe_mk Nnreal.coe_mk

example : Zero ℝ≥0 := by infer_instance

example : One ℝ≥0 := by infer_instance

example : Add ℝ≥0 := by infer_instance

noncomputable example : Sub ℝ≥0 := by infer_instance

example : Mul ℝ≥0 := by infer_instance

noncomputable example : Inv ℝ≥0 := by infer_instance

noncomputable example : Div ℝ≥0 := by infer_instance

example : LE ℝ≥0 := by infer_instance

example : Bot ℝ≥0 := by infer_instance

example : Inhabited ℝ≥0 := by infer_instance

example : Nontrivial ℝ≥0 := by infer_instance

protected theorem coe_injective : Function.Injective (coe : ℝ≥0 → ℝ) :=
  Subtype.coe_injective
#align nnreal.coe_injective Nnreal.coe_injective

@[simp, norm_cast]
protected theorem coe_eq {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) = r₂ ↔ r₁ = r₂ :=
  Nnreal.coe_injective.eq_iff
#align nnreal.coe_eq Nnreal.coe_eq

protected theorem coe_zero : ((0 : ℝ≥0) : ℝ) = 0 :=
  rfl
#align nnreal.coe_zero Nnreal.coe_zero

protected theorem coe_one : ((1 : ℝ≥0) : ℝ) = 1 :=
  rfl
#align nnreal.coe_one Nnreal.coe_one

protected theorem coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ :=
  rfl
#align nnreal.coe_add Nnreal.coe_add

protected theorem coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ :=
  rfl
#align nnreal.coe_mul Nnreal.coe_mul

protected theorem coe_inv (r : ℝ≥0) : ((r⁻¹ : ℝ≥0) : ℝ) = r⁻¹ :=
  rfl
#align nnreal.coe_inv Nnreal.coe_inv

protected theorem coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = r₁ / r₂ :=
  rfl
#align nnreal.coe_div Nnreal.coe_div

@[simp, norm_cast]
protected theorem coe_bit0 (r : ℝ≥0) : ((bit0 r : ℝ≥0) : ℝ) = bit0 r :=
  rfl
#align nnreal.coe_bit0 Nnreal.coe_bit0

@[simp, norm_cast]
protected theorem coe_bit1 (r : ℝ≥0) : ((bit1 r : ℝ≥0) : ℝ) = bit1 r :=
  rfl
#align nnreal.coe_bit1 Nnreal.coe_bit1

protected theorem coe_two : ((2 : ℝ≥0) : ℝ) = 2 :=
  rfl
#align nnreal.coe_two Nnreal.coe_two

@[simp, norm_cast]
protected theorem coe_sub {r₁ r₂ : ℝ≥0} (h : r₂ ≤ r₁) : ((r₁ - r₂ : ℝ≥0) : ℝ) = r₁ - r₂ :=
  max_eq_left <| le_sub_comm.2 <| by simp [show (r₂ : ℝ) ≤ r₁ from h]
#align nnreal.coe_sub Nnreal.coe_sub

@[simp, norm_cast]
protected theorem coe_eq_zero (r : ℝ≥0) : ↑r = (0 : ℝ) ↔ r = 0 := by
  rw [← Nnreal.coe_zero, Nnreal.coe_eq]
#align nnreal.coe_eq_zero Nnreal.coe_eq_zero

@[simp, norm_cast]
protected theorem coe_eq_one (r : ℝ≥0) : ↑r = (1 : ℝ) ↔ r = 1 := by
  rw [← Nnreal.coe_one, Nnreal.coe_eq]
#align nnreal.coe_eq_one Nnreal.coe_eq_one

theorem coe_ne_zero {r : ℝ≥0} : (r : ℝ) ≠ 0 ↔ r ≠ 0 := by norm_cast
#align nnreal.coe_ne_zero Nnreal.coe_ne_zero

example : CommSemiring ℝ≥0 := by infer_instance

/-- Coercion `ℝ≥0 → ℝ` as a `ring_hom`. -/
def toRealHom : ℝ≥0 →+* ℝ :=
  ⟨coe, Nnreal.coe_one, Nnreal.coe_mul, Nnreal.coe_zero, Nnreal.coe_add⟩
#align nnreal.to_real_hom Nnreal.toRealHom

@[simp]
theorem coe_toRealHom : ⇑toRealHom = coe :=
  rfl
#align nnreal.coe_to_real_hom Nnreal.coe_toRealHom

section Actions

/-- A `mul_action` over `ℝ` restricts to a `mul_action` over `ℝ≥0`. -/
instance {M : Type _} [MulAction ℝ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M toRealHom.toMonoidHom

theorem smul_def {M : Type _} [MulAction ℝ M] (c : ℝ≥0) (x : M) : c • x = (c : ℝ) • x :=
  rfl
#align nnreal.smul_def Nnreal.smul_def

instance {M N : Type _} [MulAction ℝ M] [MulAction ℝ N] [SMul M N] [IsScalarTower ℝ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc r := (smul_assoc (r : ℝ) : _)

instance sMulCommClass_left {M N : Type _} [MulAction ℝ N] [SMul M N] [SMulCommClass ℝ M N] :
    SMulCommClass ℝ≥0 M N where smul_comm r := (smul_comm (r : ℝ) : _)
#align nnreal.smul_comm_class_left Nnreal.sMulCommClass_left

instance sMulCommClass_right {M N : Type _} [MulAction ℝ N] [SMul M N] [SMulCommClass M ℝ N] :
    SMulCommClass M ℝ≥0 N where smul_comm m r := (smul_comm m (r : ℝ) : _)
#align nnreal.smul_comm_class_right Nnreal.sMulCommClass_right

/-- A `distrib_mul_action` over `ℝ` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
instance {M : Type _} [AddMonoid M] [DistribMulAction ℝ M] : DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M toRealHom.toMonoidHom

/-- A `module` over `ℝ` restricts to a `module` over `ℝ≥0`. -/
instance {M : Type _} [AddCommMonoid M] [Module ℝ M] : Module ℝ≥0 M :=
  Module.compHom M toRealHom

/-- An `algebra` over `ℝ` restricts to an `algebra` over `ℝ≥0`. -/
instance {A : Type _} [Semiring A] [Algebra ℝ A] : Algebra ℝ≥0 A
    where
  smul := (· • ·)
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : ℝ) x, smul_def]
  toRingHom := (algebraMap ℝ A).comp (toRealHom : ℝ≥0 →+* ℝ)

-- verify that the above produces instances we might care about
example : Algebra ℝ≥0 ℝ := by infer_instance

example : DistribMulAction ℝ≥0ˣ ℝ := by infer_instance

end Actions

example : MonoidWithZero ℝ≥0 := by infer_instance

example : CommMonoidWithZero ℝ≥0 := by infer_instance

noncomputable example : CommGroupWithZero ℝ≥0 := by infer_instance

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ) = s.indicator (fun x => f x) a :=
  (toRealHom : ℝ≥0 →+ ℝ).map_indicator _ _ _
#align nnreal.coe_indicator Nnreal.coe_indicator

@[simp, norm_cast]
theorem coe_pow (r : ℝ≥0) (n : ℕ) : ((r ^ n : ℝ≥0) : ℝ) = r ^ n :=
  toRealHom.map_pow r n
#align nnreal.coe_pow Nnreal.coe_pow

@[simp, norm_cast]
theorem coe_zpow (r : ℝ≥0) (n : ℤ) : ((r ^ n : ℝ≥0) : ℝ) = r ^ n := by cases n <;> simp
#align nnreal.coe_zpow Nnreal.coe_zpow

@[norm_cast]
theorem coe_list_sum (l : List ℝ≥0) : ((l.Sum : ℝ≥0) : ℝ) = (l.map coe).Sum :=
  toRealHom.map_list_sum l
#align nnreal.coe_list_sum Nnreal.coe_list_sum

@[norm_cast]
theorem coe_list_prod (l : List ℝ≥0) : ((l.Prod : ℝ≥0) : ℝ) = (l.map coe).Prod :=
  toRealHom.map_list_prod l
#align nnreal.coe_list_prod Nnreal.coe_list_prod

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℝ≥0) : ((s.Sum : ℝ≥0) : ℝ) = (s.map coe).Sum :=
  toRealHom.map_multiset_sum s
#align nnreal.coe_multiset_sum Nnreal.coe_multiset_sum

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℝ≥0) : ((s.Prod : ℝ≥0) : ℝ) = (s.map coe).Prod :=
  toRealHom.map_multiset_prod s
#align nnreal.coe_multiset_prod Nnreal.coe_multiset_prod

@[norm_cast]
theorem coe_sum {α} {s : Finset α} {f : α → ℝ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℝ) :=
  toRealHom.map_sum _ _
#align nnreal.coe_sum Nnreal.coe_sum

theorem Real.toNnreal_sum_of_nonneg {α} {s : Finset α} {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNnreal (∑ a in s, f a) = ∑ a in s, Real.toNnreal (f a) :=
  by
  rw [← Nnreal.coe_eq, Nnreal.coe_sum, Real.coe_toNnreal _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNnreal _ (hf x hxs)]
#align real.to_nnreal_sum_of_nonneg Real.toNnreal_sum_of_nonneg

@[norm_cast]
theorem coe_prod {α} {s : Finset α} {f : α → ℝ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℝ) :=
  toRealHom.map_prod _ _
#align nnreal.coe_prod Nnreal.coe_prod

theorem Real.toNnreal_prod_of_nonneg {α} {s : Finset α} {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNnreal (∏ a in s, f a) = ∏ a in s, Real.toNnreal (f a) :=
  by
  rw [← Nnreal.coe_eq, Nnreal.coe_prod, Real.coe_toNnreal _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNnreal _ (hf x hxs)]
#align real.to_nnreal_prod_of_nonneg Real.toNnreal_prod_of_nonneg

theorem nsmul_coe (r : ℝ≥0) (n : ℕ) : ↑(n • r) = n • (r : ℝ) := by norm_cast
#align nnreal.nsmul_coe Nnreal.nsmul_coe

@[simp, norm_cast]
protected theorem coe_nat_cast (n : ℕ) : (↑(↑n : ℝ≥0) : ℝ) = n :=
  map_natCast toRealHom n
#align nnreal.coe_nat_cast Nnreal.coe_nat_cast

noncomputable example : LinearOrder ℝ≥0 := by infer_instance

@[simp, norm_cast]
protected theorem coe_le_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ :=
  Iff.rfl
#align nnreal.coe_le_coe Nnreal.coe_le_coe

@[simp, norm_cast]
protected theorem coe_lt_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ :=
  Iff.rfl
#align nnreal.coe_lt_coe Nnreal.coe_lt_coe

@[simp, norm_cast]
protected theorem coe_pos {r : ℝ≥0} : (0 : ℝ) < r ↔ 0 < r :=
  Iff.rfl
#align nnreal.coe_pos Nnreal.coe_pos

protected theorem coe_mono : Monotone (coe : ℝ≥0 → ℝ) := fun _ _ => Nnreal.coe_le_coe.2
#align nnreal.coe_mono Nnreal.coe_mono

protected theorem Real.toNnreal_mono : Monotone Real.toNnreal := fun x y h =>
  max_le_max h (le_refl 0)
#align real.to_nnreal_mono Real.toNnreal_mono

@[simp]
theorem Real.toNnreal_coe {r : ℝ≥0} : Real.toNnreal r = r :=
  Nnreal.eq <| max_eq_left r.2
#align real.to_nnreal_coe Real.toNnreal_coe

@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℝ≥0 (⟨(n : ℝ), n.cast_nonneg⟩ : ℝ≥0) n :=
  Nnreal.eq (Nnreal.coe_nat_cast n).symm
#align nnreal.mk_coe_nat Nnreal.mk_coe_nat

@[simp]
theorem toNnreal_coe_nat (n : ℕ) : Real.toNnreal n = n :=
  Nnreal.eq <| by simp [Real.coe_toNnreal]
#align nnreal.to_nnreal_coe_nat Nnreal.toNnreal_coe_nat

/-- `real.to_nnreal` and `coe : ℝ≥0 → ℝ` form a Galois insertion. -/
noncomputable def gi : GaloisInsertion Real.toNnreal coe :=
  GaloisInsertion.monotoneIntro Nnreal.coe_mono Real.toNnreal_mono Real.le_coe_toNnreal fun _ =>
    Real.toNnreal_coe
#align nnreal.gi Nnreal.gi

-- note that anything involving the (decidability of the) linear order,
-- will be noncomputable, everything else should not be.
example : OrderBot ℝ≥0 := by infer_instance

example : PartialOrder ℝ≥0 := by infer_instance

noncomputable example : CanonicallyLinearOrderedAddMonoid ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedAddCommMonoid ℝ≥0 := by infer_instance

example : DistribLattice ℝ≥0 := by infer_instance

example : SemilatticeInf ℝ≥0 := by infer_instance

example : SemilatticeSup ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedSemiring ℝ≥0 := by infer_instance

example : OrderedCommSemiring ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedCommMonoid ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedCommMonoidWithZero ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedCommGroupWithZero ℝ≥0 := by infer_instance

example : CanonicallyOrderedCommSemiring ℝ≥0 := by infer_instance

example : DenselyOrdered ℝ≥0 := by infer_instance

example : NoMaxOrder ℝ≥0 := by infer_instance

/-- If `a` is a nonnegative real number, then the closed interval `[0, a]` in `ℝ` is order
isomorphic to the interval `set.Iic a`. -/
@[simps apply_coe_coe]
def orderIsoIccZeroCoe (a : ℝ≥0) : Set.Icc (0 : ℝ) a ≃o Set.Iic a
    where
  toEquiv := Equiv.Set.sep (Set.Ici 0) fun x => x ≤ a
  map_rel_iff' x y := Iff.rfl
#align nnreal.order_iso_Icc_zero_coe Nnreal.orderIsoIccZeroCoe

@[simp]
theorem orderIsoIccZeroCoe_symm_apply_coe (a : ℝ≥0) (b : Set.Iic a) :
    ((orderIsoIccZeroCoe a).symm b : ℝ) = b :=
  rfl
#align nnreal.order_iso_Icc_zero_coe_symm_apply_coe Nnreal.orderIsoIccZeroCoe_symm_apply_coe

-- note we need the `@` to make the `has_mem.mem` have a sensible type
theorem coe_image {s : Set ℝ≥0} :
    coe '' s = { x : ℝ | ∃ h : 0 ≤ x, @Membership.Mem ℝ≥0 _ _ ⟨x, h⟩ s } :=
  Subtype.coe_image
#align nnreal.coe_image Nnreal.coe_image

theorem bddAbove_coe {s : Set ℝ≥0} : BddAbove ((coe : ℝ≥0 → ℝ) '' s) ↔ BddAbove s :=
  Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNnreal b, fun ⟨y, hy⟩ hys =>
        show y ≤ max b 0 from le_max_of_le_left <| hb <| Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun y ⟨x, hx, Eq⟩ => Eq ▸ hb hx⟩
#align nnreal.bdd_above_coe Nnreal.bddAbove_coe

theorem bddBelow_coe (s : Set ℝ≥0) : BddBelow ((coe : ℝ≥0 → ℝ) '' s) :=
  ⟨0, fun r ⟨q, _, Eq⟩ => Eq ▸ q.2⟩
#align nnreal.bdd_below_coe Nnreal.bddBelow_coe

noncomputable instance : ConditionallyCompleteLinearOrderBot ℝ≥0 :=
  Nonneg.conditionallyCompleteLinearOrderBot Real.supₛ_empty.le

@[norm_cast]
theorem coe_supₛ (s : Set ℝ≥0) : (↑(supₛ s) : ℝ) = supₛ ((coe : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <|
    @subset_supₛ_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s <|
      Real.supₛ_nonneg _ fun y ⟨x, _, hy⟩ => hy ▸ x.2
#align nnreal.coe_Sup Nnreal.coe_supₛ

@[norm_cast]
theorem coe_supᵢ {ι : Sort _} (s : ι → ℝ≥0) : (↑(⨆ i, s i) : ℝ) = ⨆ i, s i := by
  rw [supᵢ, supᵢ, coe_Sup, Set.range_comp]
#align nnreal.coe_supr Nnreal.coe_supᵢ

@[norm_cast]
theorem coe_infₛ (s : Set ℝ≥0) : (↑(infₛ s) : ℝ) = infₛ ((coe : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <|
    @subset_infₛ_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s <|
      Real.infₛ_nonneg _ fun y ⟨x, _, hy⟩ => hy ▸ x.2
#align nnreal.coe_Inf Nnreal.coe_infₛ

@[simp]
theorem infₛ_empty : infₛ (∅ : Set ℝ≥0) = 0 := by
  rw [← Nnreal.coe_eq_zero, coe_Inf, Set.image_empty, Real.infₛ_empty]
#align nnreal.Inf_empty Nnreal.infₛ_empty

@[norm_cast]
theorem coe_infᵢ {ι : Sort _} (s : ι → ℝ≥0) : (↑(⨅ i, s i) : ℝ) = ⨅ i, s i := by
  rw [infᵢ, infᵢ, coe_Inf, Set.range_comp]
#align nnreal.coe_infi Nnreal.coe_infᵢ

theorem le_infᵢ_add_infᵢ {ι ι' : Sort _} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0} {g : ι' → ℝ≥0}
    {a : ℝ≥0} (h : ∀ i j, a ≤ f i + g j) : a ≤ (⨅ i, f i) + ⨅ j, g j :=
  by
  rw [← Nnreal.coe_le_coe, Nnreal.coe_add, coe_infi, coe_infi]
  exact le_cinfᵢ_add_cinfᵢ h
#align nnreal.le_infi_add_infi Nnreal.le_infᵢ_add_infᵢ

example : Archimedean ℝ≥0 := by infer_instance

-- TODO: why are these three instances necessary? why aren't they inferred?
instance covariant_add : CovariantClass ℝ≥0 ℝ≥0 (· + ·) (· ≤ ·) :=
  OrderedAddCommMonoid.to_covariantClass_left ℝ≥0
#align nnreal.covariant_add Nnreal.covariant_add

instance contravariant_add : ContravariantClass ℝ≥0 ℝ≥0 (· + ·) (· < ·) :=
  OrderedCancelAddCommMonoid.to_contravariantClass_left ℝ≥0
#align nnreal.contravariant_add Nnreal.contravariant_add

instance covariant_mul : CovariantClass ℝ≥0 ℝ≥0 (· * ·) (· ≤ ·) :=
  OrderedCommMonoid.to_covariantClass_left ℝ≥0
#align nnreal.covariant_mul Nnreal.covariant_mul

-- Why isn't `nnreal.contravariant_add` inferred?
theorem le_of_forall_pos_le_add {a b : ℝ≥0} (h : ∀ ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
  @le_of_forall_pos_le_add _ _ _ _ _ _ Nnreal.contravariant_add _ _ h
#align nnreal.le_of_forall_pos_le_add Nnreal.le_of_forall_pos_le_add

theorem lt_iff_exists_rat_btwn (a b : ℝ≥0) :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNnreal q ∧ Real.toNnreal q < b :=
  Iff.intro
    (fun h : (↑a : ℝ) < (↑b : ℝ) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
      have : 0 ≤ (q : ℝ) := le_trans a.2 <| le_of_lt haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_toNnreal _ this, nnreal.coe_lt_coe.symm, haq, hqb]⟩)
    fun ⟨q, _, haq, hqb⟩ => lt_trans haq hqb
#align nnreal.lt_iff_exists_rat_btwn Nnreal.lt_iff_exists_rat_btwn

theorem bot_eq_zero : (⊥ : ℝ≥0) = 0 :=
  rfl
#align nnreal.bot_eq_zero Nnreal.bot_eq_zero

theorem mul_sup (a b c : ℝ≥0) : a * (b ⊔ c) = a * b ⊔ a * c :=
  mul_max_of_nonneg _ _ <| zero_le a
#align nnreal.mul_sup Nnreal.mul_sup

theorem sup_mul (a b c : ℝ≥0) : (a ⊔ b) * c = a * c ⊔ b * c :=
  max_mul_of_nonneg _ _ <| zero_le c
#align nnreal.sup_mul Nnreal.sup_mul

theorem mul_finset_sup {α} (r : ℝ≥0) (s : Finset α) (f : α → ℝ≥0) :
    r * s.sup f = s.sup fun a => r * f a :=
  Finset.comp_sup_eq_sup_comp _ (Nnreal.mul_sup r) (mul_zero r)
#align nnreal.mul_finset_sup Nnreal.mul_finset_sup

theorem finset_sup_mul {α} (s : Finset α) (f : α → ℝ≥0) (r : ℝ≥0) :
    s.sup f * r = s.sup fun a => f a * r :=
  Finset.comp_sup_eq_sup_comp (· * r) (fun x y => Nnreal.sup_mul x y r) (zero_mul r)
#align nnreal.finset_sup_mul Nnreal.finset_sup_mul

theorem finset_sup_div {α} {f : α → ℝ≥0} {s : Finset α} (r : ℝ≥0) :
    s.sup f / r = s.sup fun a => f a / r := by simp only [div_eq_inv_mul, mul_finset_sup]
#align nnreal.finset_sup_div Nnreal.finset_sup_div

@[simp, norm_cast]
theorem coe_max (x y : ℝ≥0) : ((max x y : ℝ≥0) : ℝ) = max (x : ℝ) (y : ℝ) :=
  Nnreal.coe_mono.map_max
#align nnreal.coe_max Nnreal.coe_max

@[simp, norm_cast]
theorem coe_min (x y : ℝ≥0) : ((min x y : ℝ≥0) : ℝ) = min (x : ℝ) (y : ℝ) :=
  Nnreal.coe_mono.map_min
#align nnreal.coe_min Nnreal.coe_min

@[simp]
theorem zero_le_coe {q : ℝ≥0} : 0 ≤ (q : ℝ) :=
  q.2
#align nnreal.zero_le_coe Nnreal.zero_le_coe

end Nnreal

namespace Real

section ToNnreal

@[simp]
theorem toNnreal_zero : Real.toNnreal 0 = 0 := by simp [Real.toNnreal] <;> rfl
#align real.to_nnreal_zero Real.toNnreal_zero

@[simp]
theorem toNnreal_one : Real.toNnreal 1 = 1 := by
  simp [Real.toNnreal, max_eq_left (zero_le_one : (0 : ℝ) ≤ 1)] <;> rfl
#align real.to_nnreal_one Real.toNnreal_one

@[simp]
theorem toNnreal_pos {r : ℝ} : 0 < Real.toNnreal r ↔ 0 < r := by
  simp [Real.toNnreal, nnreal.coe_lt_coe.symm, lt_irrefl]
#align real.to_nnreal_pos Real.toNnreal_pos

@[simp]
theorem toNnreal_eq_zero {r : ℝ} : Real.toNnreal r = 0 ↔ r ≤ 0 := by
  simpa [-to_nnreal_pos] using not_iff_not.2 (@to_nnreal_pos r)
#align real.to_nnreal_eq_zero Real.toNnreal_eq_zero

theorem toNnreal_of_nonpos {r : ℝ} : r ≤ 0 → Real.toNnreal r = 0 :=
  toNnreal_eq_zero.2
#align real.to_nnreal_of_nonpos Real.toNnreal_of_nonpos

@[simp]
theorem coe_to_nnreal' (r : ℝ) : (Real.toNnreal r : ℝ) = max r 0 :=
  rfl
#align real.coe_to_nnreal' Real.coe_to_nnreal'

@[simp]
theorem toNnreal_le_toNnreal_iff {r p : ℝ} (hp : 0 ≤ p) :
    Real.toNnreal r ≤ Real.toNnreal p ↔ r ≤ p := by simp [nnreal.coe_le_coe.symm, Real.toNnreal, hp]
#align real.to_nnreal_le_to_nnreal_iff Real.toNnreal_le_toNnreal_iff

@[simp]
theorem toNnreal_eq_toNnreal_iff {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNnreal r = Real.toNnreal p ↔ r = p := by simp [← Nnreal.coe_eq, coe_to_nnreal, hr, hp]
#align real.to_nnreal_eq_to_nnreal_iff Real.toNnreal_eq_toNnreal_iff

@[simp]
theorem toNnreal_lt_toNnreal_iff' {r p : ℝ} : Real.toNnreal r < Real.toNnreal p ↔ r < p ∧ 0 < p :=
  Nnreal.coe_lt_coe.symm.trans max_lt_max_left_iff
#align real.to_nnreal_lt_to_nnreal_iff' Real.toNnreal_lt_toNnreal_iff'

theorem toNnreal_lt_toNnreal_iff {r p : ℝ} (h : 0 < p) :
    Real.toNnreal r < Real.toNnreal p ↔ r < p :=
  toNnreal_lt_toNnreal_iff'.trans (and_iff_left h)
#align real.to_nnreal_lt_to_nnreal_iff Real.toNnreal_lt_toNnreal_iff

theorem toNnreal_lt_toNnreal_iff_of_nonneg {r p : ℝ} (hr : 0 ≤ r) :
    Real.toNnreal r < Real.toNnreal p ↔ r < p :=
  toNnreal_lt_toNnreal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_lt hr h⟩⟩
#align real.to_nnreal_lt_to_nnreal_iff_of_nonneg Real.toNnreal_lt_toNnreal_iff_of_nonneg

@[simp]
theorem toNnreal_add {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNnreal (r + p) = Real.toNnreal r + Real.toNnreal p :=
  Nnreal.eq <| by simp [Real.toNnreal, hr, hp, add_nonneg]
#align real.to_nnreal_add Real.toNnreal_add

theorem toNnreal_add_toNnreal {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNnreal r + Real.toNnreal p = Real.toNnreal (r + p) :=
  (Real.toNnreal_add hr hp).symm
#align real.to_nnreal_add_to_nnreal Real.toNnreal_add_toNnreal

theorem toNnreal_le_toNnreal {r p : ℝ} (h : r ≤ p) : Real.toNnreal r ≤ Real.toNnreal p :=
  Real.toNnreal_mono h
#align real.to_nnreal_le_to_nnreal Real.toNnreal_le_toNnreal

theorem toNnreal_add_le {r p : ℝ} : Real.toNnreal (r + p) ≤ Real.toNnreal r + Real.toNnreal p :=
  Nnreal.coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) Nnreal.zero_le_coe
#align real.to_nnreal_add_le Real.toNnreal_add_le

theorem toNnreal_le_iff_le_coe {r : ℝ} {p : ℝ≥0} : Real.toNnreal r ≤ p ↔ r ≤ ↑p :=
  Nnreal.gi.gc r p
#align real.to_nnreal_le_iff_le_coe Real.toNnreal_le_iff_le_coe

theorem le_toNnreal_iff_coe_le {r : ℝ≥0} {p : ℝ} (hp : 0 ≤ p) : r ≤ Real.toNnreal p ↔ ↑r ≤ p := by
  rw [← Nnreal.coe_le_coe, Real.coe_toNnreal p hp]
#align real.le_to_nnreal_iff_coe_le Real.le_toNnreal_iff_coe_le

theorem le_toNnreal_iff_coe_le' {r : ℝ≥0} {p : ℝ} (hr : 0 < r) : r ≤ Real.toNnreal p ↔ ↑r ≤ p :=
  (le_or_lt 0 p).elim le_toNnreal_iff_coe_le fun hp => by
    simp only [(hp.trans_le r.coe_nonneg).not_le, to_nnreal_eq_zero.2 hp.le, hr.not_le]
#align real.le_to_nnreal_iff_coe_le' Real.le_toNnreal_iff_coe_le'

theorem toNnreal_lt_iff_lt_coe {r : ℝ} {p : ℝ≥0} (ha : 0 ≤ r) : Real.toNnreal r < p ↔ r < ↑p := by
  rw [← Nnreal.coe_lt_coe, Real.coe_toNnreal r ha]
#align real.to_nnreal_lt_iff_lt_coe Real.toNnreal_lt_iff_lt_coe

theorem lt_toNnreal_iff_coe_lt {r : ℝ≥0} {p : ℝ} : r < Real.toNnreal p ↔ ↑r < p :=
  by
  cases le_total 0 p
  · rw [← Nnreal.coe_lt_coe, Real.coe_toNnreal p h]
  · rw [to_nnreal_eq_zero.2 h]
    constructor
    · intro
      have := not_lt_of_le (zero_le r)
      contradiction
    · intro rp
      have : ¬p ≤ 0 := not_le_of_lt (lt_of_le_of_lt (Nnreal.coe_nonneg _) rp)
      contradiction
#align real.lt_to_nnreal_iff_coe_lt Real.lt_toNnreal_iff_coe_lt

@[simp]
theorem toNnreal_bit0 (r : ℝ) : Real.toNnreal (bit0 r) = bit0 (Real.toNnreal r) :=
  by
  cases' le_total r 0 with hr hr
  · rw [to_nnreal_of_nonpos hr, to_nnreal_of_nonpos, bit0_zero]
    exact add_nonpos hr hr
  · exact to_nnreal_add hr hr
#align real.to_nnreal_bit0 Real.toNnreal_bit0

@[simp]
theorem toNnreal_bit1 {r : ℝ} (hr : 0 ≤ r) : Real.toNnreal (bit1 r) = bit1 (Real.toNnreal r) :=
  (Real.toNnreal_add (by simp [hr]) zero_le_one).trans (by simp [bit1])
#align real.to_nnreal_bit1 Real.toNnreal_bit1

theorem toNnreal_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x ^ n).toNnreal = x.toNnreal ^ n := by
  rw [← Nnreal.coe_eq, Nnreal.coe_pow, Real.coe_toNnreal _ (pow_nonneg hx _),
    Real.coe_toNnreal x hx]
#align real.to_nnreal_pow Real.toNnreal_pow

end ToNnreal

end Real

open Real

namespace Nnreal

section Mul

theorem mul_eq_mul_left {a b c : ℝ≥0} (h : a ≠ 0) : a * b = a * c ↔ b = c := by
  rw [mul_eq_mul_left_iff, or_iff_left h]
#align nnreal.mul_eq_mul_left Nnreal.mul_eq_mul_left

theorem Real.toNnreal_mul {p q : ℝ} (hp : 0 ≤ p) :
    Real.toNnreal (p * q) = Real.toNnreal p * Real.toNnreal q :=
  by
  cases' le_total 0 q with hq hq
  · apply Nnreal.eq
    simp [Real.toNnreal, hp, hq, max_eq_left, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [to_nnreal_eq_zero.2 hq, to_nnreal_eq_zero.2 hpq, mul_zero]
#align real.to_nnreal_mul Real.toNnreal_mul

end Mul

section Pow

theorem pow_antitone_exp {a : ℝ≥0} (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) : a ^ n ≤ a ^ m :=
  pow_le_pow_of_le_one (zero_le a) a1 mn
#align nnreal.pow_antitone_exp Nnreal.pow_antitone_exp

theorem exists_pow_lt_of_lt_one {a b : ℝ≥0} (ha : 0 < a) (hb : b < 1) : ∃ n : ℕ, b ^ n < a := by
  simpa only [← coe_pow, Nnreal.coe_lt_coe] using
    exists_pow_lt_of_lt_one (Nnreal.coe_pos.2 ha) (Nnreal.coe_lt_coe.2 hb)
#align nnreal.exists_pow_lt_of_lt_one Nnreal.exists_pow_lt_of_lt_one

theorem exists_mem_Ico_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ico (y ^ n) (y ^ (n + 1)) :=
  by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n ≤ x ∧ (x : ℝ) < y ^ (n + 1) :=
    exists_mem_Ico_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← Nnreal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩
#align nnreal.exists_mem_Ico_zpow Nnreal.exists_mem_Ico_zpow

theorem exists_mem_Ioc_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) :=
  by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n < x ∧ (x : ℝ) ≤ y ^ (n + 1) :=
    exists_mem_Ioc_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← Nnreal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩
#align nnreal.exists_mem_Ioc_zpow Nnreal.exists_mem_Ioc_zpow

end Pow

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas
about `has_ordered_sub` in the file `algebra.order.sub`. See also `mul_tsub` and `tsub_mul`. -/


theorem sub_def {r p : ℝ≥0} : r - p = Real.toNnreal (r - p) :=
  rfl
#align nnreal.sub_def Nnreal.sub_def

theorem coe_sub_def {r p : ℝ≥0} : ↑(r - p) = max (r - p : ℝ) 0 :=
  rfl
#align nnreal.coe_sub_def Nnreal.coe_sub_def

noncomputable example : OrderedSub ℝ≥0 := by infer_instance

theorem sub_div (a b c : ℝ≥0) : (a - b) / c = a / c - b / c :=
  tsub_div _ _ _
#align nnreal.sub_div Nnreal.sub_div

end Sub

section Inv

theorem sum_div {ι} (s : Finset ι) (f : ι → ℝ≥0) (b : ℝ≥0) :
    (∑ i in s, f i) / b = ∑ i in s, f i / b :=
  Finset.sum_div
#align nnreal.sum_div Nnreal.sum_div

@[simp]
theorem inv_pos {r : ℝ≥0} : 0 < r⁻¹ ↔ 0 < r :=
  inv_pos
#align nnreal.inv_pos Nnreal.inv_pos

theorem div_pos {r p : ℝ≥0} (hr : 0 < r) (hp : 0 < p) : 0 < r / p :=
  div_pos hr hp
#align nnreal.div_pos Nnreal.div_pos

theorem div_self_le (r : ℝ≥0) : r / r ≤ 1 :=
  div_self_le_one r
#align nnreal.div_self_le Nnreal.div_self_le

@[simp]
theorem inv_le {r p : ℝ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]
#align nnreal.inv_le Nnreal.inv_le

theorem inv_le_of_le_mul {r p : ℝ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p := by
  by_cases r = 0 <;> simp [*, inv_le]
#align nnreal.inv_le_of_le_mul Nnreal.inv_le_of_le_mul

@[simp]
theorem le_inv_iff_mul_le {r p : ℝ≥0} (h : p ≠ 0) : r ≤ p⁻¹ ↔ r * p ≤ 1 := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]
#align nnreal.le_inv_iff_mul_le Nnreal.le_inv_iff_mul_le

@[simp]
theorem lt_inv_iff_mul_lt {r p : ℝ≥0} (h : p ≠ 0) : r < p⁻¹ ↔ r * p < 1 := by
  rw [← mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]
#align nnreal.lt_inv_iff_mul_lt Nnreal.lt_inv_iff_mul_lt

theorem mul_le_iff_le_inv {a b r : ℝ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
  by
  have : 0 < r := lt_of_le_of_ne (zero_le r) hr.symm
  rw [← mul_le_mul_left (inv_pos.mpr this), ← mul_assoc, inv_mul_cancel hr, one_mul]
#align nnreal.mul_le_iff_le_inv Nnreal.mul_le_iff_le_inv

theorem le_div_iff_mul_le {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
  le_div_iff₀ hr
#align nnreal.le_div_iff_mul_le Nnreal.le_div_iff_mul_le

theorem div_le_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r :=
  div_le_iff₀ hr
#align nnreal.div_le_iff Nnreal.div_le_iff

theorem div_le_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ r * b :=
  @div_le_iff' ℝ _ a r b <| pos_iff_ne_zero.2 hr
#align nnreal.div_le_iff' Nnreal.div_le_iff'

theorem div_le_of_le_mul {a b c : ℝ≥0} (h : a ≤ b * c) : a / c ≤ b :=
  if h0 : c = 0 then by simp [h0] else (div_le_iff h0).2 h
#align nnreal.div_le_of_le_mul Nnreal.div_le_of_le_mul

theorem div_le_of_le_mul' {a b c : ℝ≥0} (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h
#align nnreal.div_le_of_le_mul' Nnreal.div_le_of_le_mul'

theorem le_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
  @le_div_iff ℝ _ a b r <| pos_iff_ne_zero.2 hr
#align nnreal.le_div_iff Nnreal.le_div_iff

theorem le_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ r * a ≤ b :=
  @le_div_iff' ℝ _ a b r <| pos_iff_ne_zero.2 hr
#align nnreal.le_div_iff' Nnreal.le_div_iff'

theorem div_lt_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < b * r :=
  lt_iff_lt_of_le_iff_le (le_div_iff hr)
#align nnreal.div_lt_iff Nnreal.div_lt_iff

theorem div_lt_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < r * b :=
  lt_iff_lt_of_le_iff_le (le_div_iff' hr)
#align nnreal.div_lt_iff' Nnreal.div_lt_iff'

theorem lt_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff hr)
#align nnreal.lt_div_iff Nnreal.lt_div_iff

theorem lt_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ r * a < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff' hr)
#align nnreal.lt_div_iff' Nnreal.lt_div_iff'

theorem mul_lt_of_lt_div {a b r : ℝ≥0} (h : a < b / r) : a * r < b :=
  by
  refine' (lt_div_iff fun hr => False.elim _).1 h
  subst r
  simpa using h
#align nnreal.mul_lt_of_lt_div Nnreal.mul_lt_of_lt_div

theorem div_le_div_left_of_le {a b c : ℝ≥0} (b0 : 0 < b) (c0 : 0 < c) (cb : c ≤ b) :
    a / b ≤ a / c := by
  by_cases a0 : a = 0
  · rw [a0, zero_div, zero_div]
  · cases' a with a ha
    replace a0 : 0 < a := lt_of_le_of_ne ha (ne_of_lt (zero_lt_iff.mpr a0))
    exact (div_le_div_left a0 b0 c0).mpr cb
#align nnreal.div_le_div_left_of_le Nnreal.div_le_div_left_of_le

theorem div_le_div_left {a b c : ℝ≥0} (a0 : 0 < a) (b0 : 0 < b) (c0 : 0 < c) :
    a / b ≤ a / c ↔ c ≤ b :=
  div_le_div_left a0 b0 c0
#align nnreal.div_le_div_left Nnreal.div_le_div_left

theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0} (h : ∀ a < 1, a * x ≤ y) : x ≤ y :=
  le_of_forall_ge_of_dense fun a ha =>
    by
    have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha)
    have hx' : x⁻¹ ≠ 0 := by rwa [(· ≠ ·), inv_eq_zero]
    have : a * x⁻¹ < 1 := by rwa [← lt_inv_iff_mul_lt hx', inv_inv]
    have : a * x⁻¹ * x ≤ y := h _ this
    rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this
#align nnreal.le_of_forall_lt_one_mul_le Nnreal.le_of_forall_lt_one_mul_le

theorem div_add_div_same (a b c : ℝ≥0) : a / c + b / c = (a + b) / c :=
  div_add_div_same _ _ _
#align nnreal.div_add_div_same Nnreal.div_add_div_same

theorem half_pos {a : ℝ≥0} (h : 0 < a) : 0 < a / 2 :=
  half_pos h
#align nnreal.half_pos Nnreal.half_pos

theorem add_halves (a : ℝ≥0) : a / 2 + a / 2 = a :=
  add_halves _
#align nnreal.add_halves Nnreal.add_halves

theorem half_le_self (a : ℝ≥0) : a / 2 ≤ a :=
  half_le_self bot_le
#align nnreal.half_le_self Nnreal.half_le_self

theorem half_lt_self {a : ℝ≥0} (h : a ≠ 0) : a / 2 < a :=
  half_lt_self h.bot_lt
#align nnreal.half_lt_self Nnreal.half_lt_self

theorem two_inv_lt_one : (2⁻¹ : ℝ≥0) < 1 :=
  two_inv_lt_one
#align nnreal.two_inv_lt_one Nnreal.two_inv_lt_one

theorem div_lt_one_of_lt {a b : ℝ≥0} (h : a < b) : a / b < 1 :=
  by
  rwa [div_lt_iff, one_mul]
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)
#align nnreal.div_lt_one_of_lt Nnreal.div_lt_one_of_lt

@[field_simps]
theorem div_add_div (a : ℝ≥0) {b : ℝ≥0} (c : ℝ≥0) {d : ℝ≥0} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d) :=
  div_add_div _ _ hb hd
#align nnreal.div_add_div Nnreal.div_add_div

@[field_simps]
theorem add_div' (a b c : ℝ≥0) (hc : c ≠ 0) : b + a / c = (b * c + a) / c :=
  add_div' _ _ _ hc
#align nnreal.add_div' Nnreal.add_div'

@[field_simps]
theorem div_add' (a b c : ℝ≥0) (hc : c ≠ 0) : a / c + b = (a + b * c) / c :=
  div_add' _ _ _ hc
#align nnreal.div_add' Nnreal.div_add'

theorem Real.toNnreal_inv {x : ℝ} : Real.toNnreal x⁻¹ = (Real.toNnreal x)⁻¹ :=
  by
  by_cases hx : 0 ≤ x
  · nth_rw 1 [← Real.coe_toNnreal x hx]
    rw [← Nnreal.coe_inv, Real.toNnreal_coe]
  · have hx' := le_of_not_ge hx
    rw [to_nnreal_eq_zero.mpr hx', inv_zero, to_nnreal_eq_zero.mpr (inv_nonpos.mpr hx')]
#align real.to_nnreal_inv Real.toNnreal_inv

theorem Real.toNnreal_div {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNnreal (x / y) = Real.toNnreal x / Real.toNnreal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.toNnreal_inv, ← Real.toNnreal_mul hx]
#align real.to_nnreal_div Real.toNnreal_div

theorem Real.toNnreal_div' {x y : ℝ} (hy : 0 ≤ y) :
    Real.toNnreal (x / y) = Real.toNnreal x / Real.toNnreal y := by
  rw [div_eq_inv_mul, div_eq_inv_mul, Real.toNnreal_mul (inv_nonneg.2 hy), Real.toNnreal_inv]
#align real.to_nnreal_div' Real.toNnreal_div'

theorem inv_lt_one_iff {x : ℝ≥0} (hx : x ≠ 0) : x⁻¹ < 1 ↔ 1 < x := by
  rwa [← one_div, div_lt_iff hx, one_mul]
#align nnreal.inv_lt_one_iff Nnreal.inv_lt_one_iff

theorem inv_lt_one {x : ℝ≥0} (hx : 1 < x) : x⁻¹ < 1 :=
  inv_lt_one hx
#align nnreal.inv_lt_one Nnreal.inv_lt_one

theorem zpow_pos {x : ℝ≥0} (hx : x ≠ 0) (n : ℤ) : 0 < x ^ n :=
  by
  cases n
  · simp [pow_pos hx.bot_lt _]
  · simp [pow_pos hx.bot_lt _]
#align nnreal.zpow_pos Nnreal.zpow_pos

theorem inv_lt_inv_iff {x y : ℝ≥0} (hx : x ≠ 0) (hy : y ≠ 0) : y⁻¹ < x⁻¹ ↔ x < y :=
  inv_lt_inv₀ hy hx
#align nnreal.inv_lt_inv_iff Nnreal.inv_lt_inv_iff

theorem inv_lt_inv {x y : ℝ≥0} (hx : x ≠ 0) (h : x < y) : y⁻¹ < x⁻¹ :=
  (inv_lt_inv_iff hx (bot_le.trans_lt h).ne').2 h
#align nnreal.inv_lt_inv Nnreal.inv_lt_inv

end Inv

@[simp]
theorem abs_eq (x : ℝ≥0) : |(x : ℝ)| = x :=
  abs_of_nonneg x.property
#align nnreal.abs_eq Nnreal.abs_eq

section Csupr

open Set

variable {ι : Sort _} {f : ι → ℝ≥0}

theorem le_toNnreal_of_coe_le {x : ℝ≥0} {y : ℝ} (h : ↑x ≤ y) : x ≤ y.toNnreal :=
  (le_toNnreal_iff_coe_le <| x.2.trans h).2 h
#align nnreal.le_to_nnreal_of_coe_le Nnreal.le_toNnreal_of_coe_le

theorem supₛ_of_not_bddAbove {s : Set ℝ≥0} (hs : ¬BddAbove s) : SupSet.supₛ s = 0 :=
  by
  rw [← bdd_above_coe] at hs
  rw [← Nnreal.coe_eq, coe_Sup]
  exact Sup_of_not_bdd_above hs
#align nnreal.Sup_of_not_bdd_above Nnreal.supₛ_of_not_bddAbove

theorem supᵢ_of_not_bddAbove (hf : ¬BddAbove (range f)) : (⨆ i, f i) = 0 :=
  supₛ_of_not_bddAbove hf
#align nnreal.supr_of_not_bdd_above Nnreal.supᵢ_of_not_bddAbove

theorem infᵢ_empty [IsEmpty ι] (f : ι → ℝ≥0) : (⨅ i, f i) = 0 :=
  by
  rw [← Nnreal.coe_eq, coe_infi]
  exact Real.cinfᵢ_empty _
#align nnreal.infi_empty Nnreal.infᵢ_empty

@[simp]
theorem infᵢ_const_zero {α : Sort _} : (⨅ i : α, (0 : ℝ≥0)) = 0 :=
  by
  rw [← Nnreal.coe_eq, coe_infi]
  exact Real.cinfᵢ_const_zero
#align nnreal.infi_const_zero Nnreal.infᵢ_const_zero

theorem infᵢ_mul (f : ι → ℝ≥0) (a : ℝ≥0) : infᵢ f * a = ⨅ i, f i * a :=
  by
  rw [← Nnreal.coe_eq, Nnreal.coe_mul, coe_infi, coe_infi]
  exact Real.infᵢ_mul_of_nonneg (Nnreal.coe_nonneg _) _
#align nnreal.infi_mul Nnreal.infᵢ_mul

theorem mul_infᵢ (f : ι → ℝ≥0) (a : ℝ≥0) : a * infᵢ f = ⨅ i, a * f i := by
  simpa only [mul_comm] using infi_mul f a
#align nnreal.mul_infi Nnreal.mul_infᵢ

theorem mul_supᵢ (f : ι → ℝ≥0) (a : ℝ≥0) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  by
  rw [← Nnreal.coe_eq, Nnreal.coe_mul, Nnreal.coe_supᵢ, Nnreal.coe_supᵢ]
  exact Real.mul_supᵢ_of_nonneg (Nnreal.coe_nonneg _) _
#align nnreal.mul_supr Nnreal.mul_supᵢ

theorem supᵢ_mul (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  by
  rw [mul_comm, mul_supr]
  simp_rw [mul_comm]
#align nnreal.supr_mul Nnreal.supᵢ_mul

theorem supᵢ_div (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, supr_mul]
#align nnreal.supr_div Nnreal.supᵢ_div

variable [Nonempty ι]

theorem le_mul_infᵢ {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, a ≤ g * h j) : a ≤ g * infᵢ h :=
  by
  rw [mul_infi]
  exact le_cinfᵢ H
#align nnreal.le_mul_infi Nnreal.le_mul_infᵢ

theorem mul_supᵢ_le {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, g * h j ≤ a) : g * supᵢ h ≤ a :=
  by
  rw [mul_supr]
  exact csupᵢ_le H
#align nnreal.mul_supr_le Nnreal.mul_supᵢ_le

theorem le_infᵢ_mul {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, a ≤ g i * h) : a ≤ infᵢ g * h :=
  by
  rw [infi_mul]
  exact le_cinfᵢ H
#align nnreal.le_infi_mul Nnreal.le_infᵢ_mul

theorem supᵢ_mul_le {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, g i * h ≤ a) : supᵢ g * h ≤ a :=
  by
  rw [supr_mul]
  exact csupᵢ_le H
#align nnreal.supr_mul_le Nnreal.supᵢ_mul_le

theorem le_infᵢ_mul_infᵢ {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, a ≤ g i * h j) :
    a ≤ infᵢ g * infᵢ h :=
  le_infᵢ_mul fun i => le_mul_infᵢ <| H i
#align nnreal.le_infi_mul_infi Nnreal.le_infᵢ_mul_infᵢ

theorem supᵢ_mul_supᵢ_le {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, g i * h j ≤ a) :
    supᵢ g * supᵢ h ≤ a :=
  supᵢ_mul_le fun i => mul_supᵢ_le <| H _
#align nnreal.supr_mul_supr_le Nnreal.supᵢ_mul_supᵢ_le

end Csupr

end Nnreal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0}

theorem preimage_coe_nnreal_real (h : s.OrdConnected) : (coe ⁻¹' s : Set ℝ≥0).OrdConnected :=
  h.preimage_mono Nnreal.coe_mono
#align set.ord_connected.preimage_coe_nnreal_real Set.OrdConnected.preimage_coe_nnreal_real

theorem image_coe_nnreal_real (h : t.OrdConnected) : (coe '' t : Set ℝ).OrdConnected :=
  ⟨ball_image_iff.2 fun x hx =>
      ball_image_iff.2 fun y hy z hz => ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩
#align set.ord_connected.image_coe_nnreal_real Set.OrdConnected.image_coe_nnreal_real

theorem image_real_toNnreal (h : s.OrdConnected) : (Real.toNnreal '' s).OrdConnected :=
  by
  refine' ⟨ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy z hz => _⟩
  cases' le_total y 0 with hy₀ hy₀
  · rw [mem_Icc, Real.toNnreal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz
    exact ⟨y, hy, (to_nnreal_of_nonpos hy₀).trans hz.2.symm⟩
  · lift y to ℝ≥0 using hy₀
    rw [to_nnreal_coe] at hz
    exact ⟨z, h.out hx hy ⟨to_nnreal_le_iff_le_coe.1 hz.1, hz.2⟩, to_nnreal_coe⟩
#align set.ord_connected.image_real_to_nnreal Set.OrdConnected.image_real_toNnreal

theorem preimage_real_toNnreal (h : t.OrdConnected) : (Real.toNnreal ⁻¹' t).OrdConnected :=
  h.preimage_mono Real.toNnreal_mono
#align set.ord_connected.preimage_real_to_nnreal Set.OrdConnected.preimage_real_toNnreal

end OrdConnected

end Set

namespace Real

/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
@[pp_nodot]
def nnabs : ℝ →*₀ ℝ≥0 where
  toFun x := ⟨|x|, abs_nonneg x⟩
  map_zero' := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp [abs_mul]
#align real.nnabs Real.nnabs

@[norm_cast, simp]
theorem coe_nnabs (x : ℝ) : (nnabs x : ℝ) = |x| :=
  rfl
#align real.coe_nnabs Real.coe_nnabs

@[simp]
theorem nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : nnabs x = toNnreal x :=
  by
  ext
  simp [coe_to_nnreal x h, abs_of_nonneg h]
#align real.nnabs_of_nonneg Real.nnabs_of_nonneg

theorem nnabs_coe (x : ℝ≥0) : nnabs x = x := by simp
#align real.nnabs_coe Real.nnabs_coe

theorem coe_toNnreal_le (x : ℝ) : (toNnreal x : ℝ) ≤ |x| :=
  max_le (le_abs_self _) (abs_nonneg _)
#align real.coe_to_nnreal_le Real.coe_toNnreal_le

theorem cast_natAbs_eq_nnabs_cast (n : ℤ) : (n.natAbs : ℝ≥0) = nnabs n :=
  by
  ext
  rw [Nnreal.coe_nat_cast, Int.cast_natAbs, Real.coe_nnabs]
#align real.cast_nat_abs_eq_nnabs_cast Real.cast_natAbs_eq_nnabs_cast

end Real

namespace Tactic

open Positivity

private theorem nnreal_coe_pos {r : ℝ≥0} : 0 < r → 0 < (r : ℝ) :=
  Nnreal.coe_pos.2
#align tactic.nnreal_coe_pos tactic.nnreal_coe_pos

/-- Extension for the `positivity` tactic: cast from `ℝ≥0` to `ℝ`. -/
@[positivity]
unsafe def positivity_coe_nnreal_real : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ <| @coeBase _ _ Nnreal.Real.hasCoe)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` nnreal_coe_pos [p]
      | _ => nonnegative <$> mk_app `` Nnreal.coe_nonneg [a]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ℝ)` for `r : ℝ≥0`"
#align tactic.positivity_coe_nnreal_real tactic.positivity_coe_nnreal_real

end Tactic

