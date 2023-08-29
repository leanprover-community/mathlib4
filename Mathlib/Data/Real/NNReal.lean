/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Field.Canonical.Basic
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.Order.Nonneg.Floor
import Mathlib.Data.Real.Pointwise
import Mathlib.Order.ConditionallyCompleteLattice.Group
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr.Core

#align_import data.real.nnreal from "leanprover-community/mathlib"@"de29c328903507bb7aff506af9135f4bdaf1849c"

/-!
# Nonnegative real numbers

In this file we define `NNReal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `ConditionallyCompleteLinearOrderBot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `LinearOrderedSemiring ℝ≥0`;
  - `OrderedCommSemiring ℝ≥0`;
  - `CanonicallyOrderedCommSemiring ℝ≥0`;
  - `LinearOrderedCommGroupWithZero ℝ≥0`;
  - `CanonicallyLinearOrderedAddMonoid ℝ≥0`;
  - `Archimedean ℝ≥0`;
  - `ConditionallyCompleteLinearOrderBot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`, see `Mathlib.Algebra.Order.Nonneg.Ring`.

* `Real.toNNReal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(Real.toNNReal x) = x` when `0 ≤ x` and
  `↑(Real.toNNReal x) = 0` otherwise.

We also define an instance `CanLift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurrences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `NNReal`.
-/

open BigOperators Function

-- to ensure these instances are computable
/-- Nonnegative real numbers. -/
def NNReal := { r : ℝ // 0 ≤ r } deriving
  Zero, One, Semiring, StrictOrderedSemiring, CommMonoidWithZero, CommSemiring,
  SemilatticeInf, SemilatticeSup, DistribLattice, OrderedCommSemiring,
  CanonicallyOrderedCommSemiring, Inhabited
#align nnreal NNReal

namespace NNReal

-- mathport name: nnreal
scoped notation "ℝ≥0" => NNReal

noncomputable instance : FloorSemiring ℝ≥0 := Nonneg.floorSemiring
instance : DenselyOrdered ℝ≥0 := Nonneg.densely_ordered
instance : OrderBot ℝ≥0 := inferInstance
instance : Archimedean ℝ≥0 := Nonneg.archimedean
noncomputable instance : Sub ℝ≥0 := Nonneg.sub
noncomputable instance : OrderedSub ℝ≥0 := Nonneg.orderedSub

noncomputable instance : CanonicallyLinearOrderedSemifield ℝ≥0 :=
  Nonneg.canonicallyLinearOrderedSemifield

/-- Coercion `ℝ≥0 → ℝ`. -/
@[coe] def toReal : ℝ≥0 → ℝ := Subtype.val

instance : Coe ℝ≥0 ℝ := ⟨toReal⟩

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (n : ℝ≥0) : n.val = n :=
  rfl
#align nnreal.val_eq_coe NNReal.val_eq_coe

instance canLift : CanLift ℝ ℝ≥0 toReal fun r => 0 ≤ r :=
  Subtype.canLift _
#align nnreal.can_lift NNReal.canLift

@[ext] protected theorem eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m :=
  Subtype.eq
#align nnreal.eq NNReal.eq

protected theorem eq_iff {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) ↔ n = m :=
  Subtype.ext_iff.symm
#align nnreal.eq_iff NNReal.eq_iff

theorem ne_iff {x y : ℝ≥0} : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
  not_congr <| NNReal.eq_iff
#align nnreal.ne_iff NNReal.ne_iff

protected theorem «forall» {p : ℝ≥0 → Prop} :
    (∀ x : ℝ≥0, p x) ↔ ∀ (x : ℝ) (hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.forall
#align nnreal.forall NNReal.forall

protected theorem «exists» {p : ℝ≥0 → Prop} :
    (∃ x : ℝ≥0, p x) ↔ ∃ (x : ℝ) (hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.exists
#align nnreal.exists NNReal.exists

/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
noncomputable def _root_.Real.toNNReal (r : ℝ) : ℝ≥0 :=
  ⟨max r 0, le_max_right _ _⟩
#align real.to_nnreal Real.toNNReal

theorem _root_.Real.coe_toNNReal (r : ℝ) (hr : 0 ≤ r) : (Real.toNNReal r : ℝ) = r :=
  max_eq_left hr
#align real.coe_to_nnreal Real.coe_toNNReal

theorem _root_.Real.toNNReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r.toNNReal = ⟨r, hr⟩ := by
  simp_rw [Real.toNNReal, max_eq_left hr]
  -- 🎉 no goals
#align real.to_nnreal_of_nonneg Real.toNNReal_of_nonneg

theorem _root_.Real.le_coe_toNNReal (r : ℝ) : r ≤ Real.toNNReal r :=
  le_max_left r 0
#align real.le_coe_to_nnreal Real.le_coe_toNNReal

theorem coe_nonneg (r : ℝ≥0) : (0 : ℝ) ≤ r := r.2
#align nnreal.coe_nonneg NNReal.coe_nonneg

@[simp, norm_cast] theorem coe_mk (a : ℝ) (ha) : toReal ⟨a, ha⟩ = a := rfl
#align nnreal.coe_mk NNReal.coe_mk

example : Zero ℝ≥0 := by infer_instance
                         -- 🎉 no goals

example : One ℝ≥0 := by infer_instance
                        -- 🎉 no goals

example : Add ℝ≥0 := by infer_instance
                        -- 🎉 no goals

noncomputable example : Sub ℝ≥0 := by infer_instance
                                      -- 🎉 no goals

example : Mul ℝ≥0 := by infer_instance
                        -- 🎉 no goals

noncomputable example : Inv ℝ≥0 := by infer_instance
                                      -- 🎉 no goals

noncomputable example : Div ℝ≥0 := by infer_instance
                                      -- 🎉 no goals

example : LE ℝ≥0 := by infer_instance
                       -- 🎉 no goals

example : Bot ℝ≥0 := by infer_instance
                        -- 🎉 no goals

example : Inhabited ℝ≥0 := by infer_instance
                              -- 🎉 no goals

example : Nontrivial ℝ≥0 := by infer_instance
                               -- 🎉 no goals

protected theorem coe_injective : Injective ((↑) : ℝ≥0 → ℝ) := Subtype.coe_injective
#align nnreal.coe_injective NNReal.coe_injective

@[simp, norm_cast]
protected theorem coe_eq {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) = r₂ ↔ r₁ = r₂ :=
  NNReal.coe_injective.eq_iff
#align nnreal.coe_eq NNReal.coe_eq

@[simp, norm_cast]
protected theorem coe_zero : ((0 : ℝ≥0) : ℝ) = 0 :=
  rfl
#align nnreal.coe_zero NNReal.coe_zero

@[simp, norm_cast]
protected theorem coe_one : ((1 : ℝ≥0) : ℝ) = 1 :=
  rfl
#align nnreal.coe_one NNReal.coe_one

@[simp, norm_cast]
protected theorem coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ :=
  rfl
#align nnreal.coe_add NNReal.coe_add

@[simp, norm_cast]
protected theorem coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ :=
  rfl
#align nnreal.coe_mul NNReal.coe_mul

@[simp, norm_cast]
protected theorem coe_inv (r : ℝ≥0) : ((r⁻¹ : ℝ≥0) : ℝ) = (r : ℝ)⁻¹ :=
  rfl
#align nnreal.coe_inv NNReal.coe_inv

@[simp, norm_cast]
protected theorem coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = (r₁ : ℝ) / r₂ :=
  rfl
#align nnreal.coe_div NNReal.coe_div

#noalign nnreal.coe_bit0
#noalign nnreal.coe_bit1

protected theorem coe_two : ((2 : ℝ≥0) : ℝ) = 2 := rfl
#align nnreal.coe_two NNReal.coe_two

@[simp, norm_cast]
protected theorem coe_sub {r₁ r₂ : ℝ≥0} (h : r₂ ≤ r₁) : ((r₁ - r₂ : ℝ≥0) : ℝ) = ↑r₁ - ↑r₂ :=
  max_eq_left <| le_sub_comm.2 <| by simp [show (r₂ : ℝ) ≤ r₁ from h]
                                     -- 🎉 no goals
#align nnreal.coe_sub NNReal.coe_sub

@[simp, norm_cast]
protected theorem coe_eq_zero (r : ℝ≥0) : ↑r = (0 : ℝ) ↔ r = 0 := by
  rw [← NNReal.coe_zero, NNReal.coe_eq]
  -- 🎉 no goals
#align nnreal.coe_eq_zero NNReal.coe_eq_zero

@[simp, norm_cast]
protected theorem coe_eq_one (r : ℝ≥0) : ↑r = (1 : ℝ) ↔ r = 1 := by
  rw [← NNReal.coe_one, NNReal.coe_eq]
  -- 🎉 no goals
#align nnreal.coe_eq_one NNReal.coe_eq_one

-- porting note: why `norm_cast` fails?
theorem coe_ne_zero {r : ℝ≥0} : (r : ℝ) ≠ 0 ↔ r ≠ 0 := r.coe_eq_zero.not
#align nnreal.coe_ne_zero NNReal.coe_ne_zero

example : CommSemiring ℝ≥0 := by infer_instance
                                 -- 🎉 no goals

/-- Coercion `ℝ≥0 → ℝ` as a `RingHom`.

Porting note: todo: what if we define `Coe ℝ≥0 ℝ` using this function? -/
def toRealHom : ℝ≥0 →+* ℝ where
  toFun := (↑)
  map_one' := NNReal.coe_one
  map_mul' := NNReal.coe_mul
  map_zero' := NNReal.coe_zero
  map_add' := NNReal.coe_add
#align nnreal.to_real_hom NNReal.toRealHom

@[simp] theorem coe_toRealHom : ⇑toRealHom = toReal := rfl
#align nnreal.coe_to_real_hom NNReal.coe_toRealHom

section Actions

/-- A `MulAction` over `ℝ` restricts to a `MulAction` over `ℝ≥0`. -/
instance {M : Type*} [MulAction ℝ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M toRealHom.toMonoidHom

theorem smul_def {M : Type*} [MulAction ℝ M] (c : ℝ≥0) (x : M) : c • x = (c : ℝ) • x :=
  rfl
#align nnreal.smul_def NNReal.smul_def

instance {M N : Type*} [MulAction ℝ M] [MulAction ℝ N] [SMul M N] [IsScalarTower ℝ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc r := (smul_assoc (r : ℝ) : _)

instance smulCommClass_left {M N : Type*} [MulAction ℝ N] [SMul M N] [SMulCommClass ℝ M N] :
    SMulCommClass ℝ≥0 M N where smul_comm r := (smul_comm (r : ℝ) : _)
#align nnreal.smul_comm_class_left NNReal.smulCommClass_left

instance smulCommClass_right {M N : Type*} [MulAction ℝ N] [SMul M N] [SMulCommClass M ℝ N] :
    SMulCommClass M ℝ≥0 N where smul_comm m r := (smul_comm m (r : ℝ) : _)
#align nnreal.smul_comm_class_right NNReal.smulCommClass_right

/-- A `DistribMulAction` over `ℝ` restricts to a `DistribMulAction` over `ℝ≥0`. -/
instance {M : Type*} [AddMonoid M] [DistribMulAction ℝ M] : DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M toRealHom.toMonoidHom

/-- A `Module` over `ℝ` restricts to a `Module` over `ℝ≥0`. -/
instance {M : Type*} [AddCommMonoid M] [Module ℝ M] : Module ℝ≥0 M :=
  Module.compHom M toRealHom

-- porting note: TODO: after this line, `↑` uses `Algebra.cast` instead of `toReal`
/-- An `Algebra` over `ℝ` restricts to an `Algebra` over `ℝ≥0`. -/
instance {A : Type*} [Semiring A] [Algebra ℝ A] : Algebra ℝ≥0 A where
  smul := (· • ·)
  commutes' r x := by simp [Algebra.commutes]
                      -- 🎉 no goals
  smul_def' r x := by simp [← Algebra.smul_def (r : ℝ) x, smul_def]
                      -- 🎉 no goals
  toRingHom := (algebraMap ℝ A).comp (toRealHom : ℝ≥0 →+* ℝ)

-- verify that the above produces instances we might care about
example : Algebra ℝ≥0 ℝ := by infer_instance
                              -- 🎉 no goals

example : DistribMulAction ℝ≥0ˣ ℝ := by infer_instance
                                        -- 🎉 no goals

end Actions

example : MonoidWithZero ℝ≥0 := by infer_instance
                                   -- 🎉 no goals

example : CommMonoidWithZero ℝ≥0 := by infer_instance
                                       -- 🎉 no goals

noncomputable example : CommGroupWithZero ℝ≥0 := by infer_instance
                                                    -- 🎉 no goals

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ) = s.indicator (fun x => ↑(f x)) a :=
  (toRealHom : ℝ≥0 →+ ℝ).map_indicator _ _ _
#align nnreal.coe_indicator NNReal.coe_indicator

@[simp, norm_cast]
theorem coe_pow (r : ℝ≥0) (n : ℕ) : ((r ^ n : ℝ≥0) : ℝ) = (r : ℝ) ^ n := rfl
#align nnreal.coe_pow NNReal.coe_pow

@[simp, norm_cast]
theorem coe_zpow (r : ℝ≥0) (n : ℤ) : ((r ^ n : ℝ≥0) : ℝ) = (r : ℝ) ^ n := rfl
#align nnreal.coe_zpow NNReal.coe_zpow

@[norm_cast]
theorem coe_list_sum (l : List ℝ≥0) : ((l.sum : ℝ≥0) : ℝ) = (l.map (↑)).sum :=
  toRealHom.map_list_sum l
#align nnreal.coe_list_sum NNReal.coe_list_sum

@[norm_cast]
theorem coe_list_prod (l : List ℝ≥0) : ((l.prod : ℝ≥0) : ℝ) = (l.map (↑)).prod :=
  toRealHom.map_list_prod l
#align nnreal.coe_list_prod NNReal.coe_list_prod

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℝ≥0) : ((s.sum : ℝ≥0) : ℝ) = (s.map (↑)).sum :=
  toRealHom.map_multiset_sum s
#align nnreal.coe_multiset_sum NNReal.coe_multiset_sum

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℝ≥0) : ((s.prod : ℝ≥0) : ℝ) = (s.map (↑)).prod :=
  toRealHom.map_multiset_prod s
#align nnreal.coe_multiset_prod NNReal.coe_multiset_prod

@[norm_cast]
theorem coe_sum {α} {s : Finset α} {f : α → ℝ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℝ) :=
  toRealHom.map_sum _ _
#align nnreal.coe_sum NNReal.coe_sum

theorem _root_.Real.toNNReal_sum_of_nonneg {α} {s : Finset α} {f : α → ℝ}
    (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNNReal (∑ a in s, f a) = ∑ a in s, Real.toNNReal (f a) := by
  rw [← NNReal.coe_eq, NNReal.coe_sum, Real.coe_toNNReal _ (Finset.sum_nonneg hf)]
  -- ⊢ ∑ i in s, f i = ∑ a in s, ↑(Real.toNNReal (f a))
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]
  -- 🎉 no goals
#align real.to_nnreal_sum_of_nonneg Real.toNNReal_sum_of_nonneg

@[norm_cast]
theorem coe_prod {α} {s : Finset α} {f : α → ℝ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℝ) :=
  toRealHom.map_prod _ _
#align nnreal.coe_prod NNReal.coe_prod

theorem _root_.Real.toNNReal_prod_of_nonneg {α} {s : Finset α} {f : α → ℝ}
    (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNNReal (∏ a in s, f a) = ∏ a in s, Real.toNNReal (f a) := by
  rw [← NNReal.coe_eq, NNReal.coe_prod, Real.coe_toNNReal _ (Finset.prod_nonneg hf)]
  -- ⊢ ∏ i in s, f i = ∏ a in s, ↑(Real.toNNReal (f a))
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]
  -- 🎉 no goals
#align real.to_nnreal_prod_of_nonneg Real.toNNReal_prod_of_nonneg

-- porting note: todo: `simp`? `norm_cast`?
theorem coe_nsmul (r : ℝ≥0) (n : ℕ) : ↑(n • r) = n • (r : ℝ) := rfl
#align nnreal.nsmul_coe NNReal.coe_nsmul

@[simp, norm_cast]
protected theorem coe_nat_cast (n : ℕ) : (↑(↑n : ℝ≥0) : ℝ) = n :=
  map_natCast toRealHom n
#align nnreal.coe_nat_cast NNReal.coe_nat_cast

@[simp, norm_cast]
protected theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n : ℝ≥0) : ℝ) = OfNat.ofNat n :=
  rfl

noncomputable example : LinearOrder ℝ≥0 := by infer_instance
                                              -- 🎉 no goals

@[simp, norm_cast]
protected theorem coe_le_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ :=
  Iff.rfl
#align nnreal.coe_le_coe NNReal.coe_le_coe

@[simp, norm_cast]
protected theorem coe_lt_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ :=
  Iff.rfl
#align nnreal.coe_lt_coe NNReal.coe_lt_coe

@[simp, norm_cast]
protected theorem coe_pos {r : ℝ≥0} : (0 : ℝ) < r ↔ 0 < r :=
  Iff.rfl
#align nnreal.coe_pos NNReal.coe_pos

protected theorem coe_mono : Monotone ((↑) : ℝ≥0 → ℝ) := fun _ _ => NNReal.coe_le_coe.2
#align nnreal.coe_mono NNReal.coe_mono

@[gcongr]
theorem _root_.NNReal.toReal_le_toReal {x y : NNReal} (h : x ≤ y) : (x : ℝ) ≤ y := NNReal.coe_mono h

protected theorem _root_.Real.toNNReal_mono : Monotone Real.toNNReal := fun _ _ h =>
  max_le_max h (le_refl 0)
#align real.to_nnreal_mono Real.toNNReal_mono

@[simp]
theorem _root_.Real.toNNReal_coe {r : ℝ≥0} : Real.toNNReal r = r :=
  NNReal.eq <| max_eq_left r.2
#align real.to_nnreal_coe Real.toNNReal_coe

@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℝ≥0 (⟨(n : ℝ), n.cast_nonneg⟩ : ℝ≥0) n :=
  NNReal.eq (NNReal.coe_nat_cast n).symm
#align nnreal.mk_coe_nat NNReal.mk_coe_nat

-- Porting note: place this in the `Real` namespace
@[simp]
theorem toNNReal_coe_nat (n : ℕ) : Real.toNNReal n = n :=
  NNReal.eq <| by simp [Real.coe_toNNReal]
                  -- 🎉 no goals
#align nnreal.to_nnreal_coe_nat NNReal.toNNReal_coe_nat

@[simp]
theorem _root_.Real.toNNReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    Real.toNNReal (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  toNNReal_coe_nat n

/-- `Real.toNNReal` and `NNReal.toReal : ℝ≥0 → ℝ` form a Galois insertion. -/
noncomputable def gi : GaloisInsertion Real.toNNReal (↑) :=
  GaloisInsertion.monotoneIntro NNReal.coe_mono Real.toNNReal_mono Real.le_coe_toNNReal fun _ =>
    Real.toNNReal_coe
#align nnreal.gi NNReal.gi

-- note that anything involving the (decidability of the) linear order,
-- will be noncomputable, everything else should not be.
example : OrderBot ℝ≥0 := by infer_instance
                             -- 🎉 no goals

example : PartialOrder ℝ≥0 := by infer_instance
                                 -- 🎉 no goals

noncomputable example : CanonicallyLinearOrderedAddMonoid ℝ≥0 := by infer_instance
                                                                    -- 🎉 no goals

noncomputable example : LinearOrderedAddCommMonoid ℝ≥0 := by infer_instance
                                                             -- 🎉 no goals

example : DistribLattice ℝ≥0 := by infer_instance
                                   -- 🎉 no goals

example : SemilatticeInf ℝ≥0 := by infer_instance
                                   -- 🎉 no goals

example : SemilatticeSup ℝ≥0 := by infer_instance
                                   -- 🎉 no goals

noncomputable example : LinearOrderedSemiring ℝ≥0 := by infer_instance
                                                        -- 🎉 no goals

example : OrderedCommSemiring ℝ≥0 := by infer_instance
                                        -- 🎉 no goals

noncomputable example : LinearOrderedCommMonoid ℝ≥0 := by infer_instance
                                                          -- 🎉 no goals

noncomputable example : LinearOrderedCommMonoidWithZero ℝ≥0 := by infer_instance
                                                                  -- 🎉 no goals

noncomputable example : LinearOrderedCommGroupWithZero ℝ≥0 := by infer_instance
                                                                 -- 🎉 no goals

example : CanonicallyOrderedCommSemiring ℝ≥0 := by infer_instance
                                                   -- 🎉 no goals

example : DenselyOrdered ℝ≥0 := by infer_instance
                                   -- 🎉 no goals

example : NoMaxOrder ℝ≥0 := by infer_instance
                               -- 🎉 no goals

/-- If `a` is a nonnegative real number, then the closed interval `[0, a]` in `ℝ` is order
isomorphic to the interval `Set.Iic a`. -/
-- porting note: todo: restore once `simps` supports `ℝ≥0` @[simps!? apply_coe_coe]
def orderIsoIccZeroCoe (a : ℝ≥0) : Set.Icc (0 : ℝ) a ≃o Set.Iic a where
  toEquiv := Equiv.Set.sep (Set.Ici 0) fun x : ℝ => x ≤ a
  map_rel_iff' := Iff.rfl
#align nnreal.order_iso_Icc_zero_coe NNReal.orderIsoIccZeroCoe

@[simp]
theorem orderIsoIccZeroCoe_apply_coe_coe (a : ℝ≥0) (b : Set.Icc (0 : ℝ) a) :
    (orderIsoIccZeroCoe a b : ℝ) = b :=
  rfl

@[simp]
theorem orderIsoIccZeroCoe_symm_apply_coe (a : ℝ≥0) (b : Set.Iic a) :
    ((orderIsoIccZeroCoe a).symm b : ℝ) = b :=
  rfl
#align nnreal.order_iso_Icc_zero_coe_symm_apply_coe NNReal.orderIsoIccZeroCoe_symm_apply_coe

-- note we need the `@` to make the `Membership.mem` have a sensible type
theorem coe_image {s : Set ℝ≥0} :
    (↑) '' s = { x : ℝ | ∃ h : 0 ≤ x, @Membership.mem ℝ≥0 _ _ ⟨x, h⟩ s } :=
  Subtype.coe_image
#align nnreal.coe_image NNReal.coe_image

theorem bddAbove_coe {s : Set ℝ≥0} : BddAbove (((↑) : ℝ≥0 → ℝ) '' s) ↔ BddAbove s :=
  Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNNReal b, fun ⟨y, _⟩ hys =>
        show y ≤ max b 0 from le_max_of_le_left <| hb <| Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun _ ⟨_, hx, eq⟩ => eq ▸ hb hx⟩
#align nnreal.bdd_above_coe NNReal.bddAbove_coe

theorem bddBelow_coe (s : Set ℝ≥0) : BddBelow (((↑) : ℝ≥0 → ℝ) '' s) :=
  ⟨0, fun _ ⟨q, _, eq⟩ => eq ▸ q.2⟩
#align nnreal.bdd_below_coe NNReal.bddBelow_coe

noncomputable instance : ConditionallyCompleteLinearOrderBot ℝ≥0 :=
  Nonneg.conditionallyCompleteLinearOrderBot Real.sSup_empty.le

@[norm_cast]
theorem coe_sSup (s : Set ℝ≥0) : (↑(sSup s) : ℝ) = sSup (((↑) : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <|
    @subset_sSup_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s <|
      Real.sSup_nonneg _ fun _y ⟨x, _, hy⟩ => hy ▸ x.2
#align nnreal.coe_Sup NNReal.coe_sSup

@[simp, norm_cast] -- porting note: add `simp`
theorem coe_iSup {ι : Sort*} (s : ι → ℝ≥0) : (↑(⨆ i, s i) : ℝ) = ⨆ i, ↑(s i) := by
  rw [iSup, iSup, coe_sSup, ← Set.range_comp]; rfl
  -- ⊢ sSup (Set.range (toReal ∘ fun i => s i)) = sSup (Set.range fun i => ↑(s i))
                                               -- 🎉 no goals
#align nnreal.coe_supr NNReal.coe_iSup

@[norm_cast]
theorem coe_sInf (s : Set ℝ≥0) : (↑(sInf s) : ℝ) = sInf (((↑) : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <|
    @subset_sInf_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s <|
      Real.sInf_nonneg _ fun _y ⟨x, _, hy⟩ => hy ▸ x.2
#align nnreal.coe_Inf NNReal.coe_sInf

@[simp]
theorem sInf_empty : sInf (∅ : Set ℝ≥0) = 0 := by
  rw [← NNReal.coe_eq_zero, coe_sInf, Set.image_empty, Real.sInf_empty]
  -- 🎉 no goals
#align nnreal.Inf_empty NNReal.sInf_empty

@[norm_cast]
theorem coe_iInf {ι : Sort*} (s : ι → ℝ≥0) : (↑(⨅ i, s i) : ℝ) = ⨅ i, ↑(s i) := by
  rw [iInf, iInf, coe_sInf, ← Set.range_comp]; rfl
  -- ⊢ sInf (Set.range (toReal ∘ fun i => s i)) = sInf (Set.range fun i => ↑(s i))
                                               -- 🎉 no goals
#align nnreal.coe_infi NNReal.coe_iInf

theorem le_iInf_add_iInf {ι ι' : Sort*} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0} {g : ι' → ℝ≥0}
    {a : ℝ≥0} (h : ∀ i j, a ≤ f i + g j) : a ≤ (⨅ i, f i) + ⨅ j, g j := by
  rw [← NNReal.coe_le_coe, NNReal.coe_add, coe_iInf, coe_iInf]
  -- ⊢ ↑a ≤ (⨅ (i : ι), ↑(f i)) + ⨅ (i : ι'), ↑(g i)
  exact le_ciInf_add_ciInf h
  -- 🎉 no goals
#align nnreal.le_infi_add_infi NNReal.le_iInf_add_iInf

example : Archimedean ℝ≥0 := by infer_instance
                                -- 🎉 no goals

-- porting note: TODO: remove?
instance covariant_add : CovariantClass ℝ≥0 ℝ≥0 (· + ·) (· ≤ ·) := inferInstance
#align nnreal.covariant_add NNReal.covariant_add

instance contravariant_add : ContravariantClass ℝ≥0 ℝ≥0 (· + ·) (· < ·) := inferInstance
#align nnreal.contravariant_add NNReal.contravariant_add

instance covariant_mul : CovariantClass ℝ≥0 ℝ≥0 (· * ·) (· ≤ ·) := inferInstance
#align nnreal.covariant_mul NNReal.covariant_mul

-- porting note: TODO: delete?
nonrec theorem le_of_forall_pos_le_add {a b : ℝ≥0} (h : ∀ ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
  le_of_forall_pos_le_add h
#align nnreal.le_of_forall_pos_le_add NNReal.le_of_forall_pos_le_add

theorem lt_iff_exists_rat_btwn (a b : ℝ≥0) :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNNReal q ∧ Real.toNNReal q < b :=
  Iff.intro
    (fun h : (↑a : ℝ) < (↑b : ℝ) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
      have : 0 ≤ (q : ℝ) := le_trans a.2 <| le_of_lt haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_toNNReal _ this, NNReal.coe_lt_coe.symm, haq, hqb]⟩)
        -- 🎉 no goals
    fun ⟨q, _, haq, hqb⟩ => lt_trans haq hqb
#align nnreal.lt_iff_exists_rat_btwn NNReal.lt_iff_exists_rat_btwn

theorem bot_eq_zero : (⊥ : ℝ≥0) = 0 := rfl
#align nnreal.bot_eq_zero NNReal.bot_eq_zero

theorem mul_sup (a b c : ℝ≥0) : a * (b ⊔ c) = a * b ⊔ a * c :=
  mul_max_of_nonneg _ _ <| zero_le a
#align nnreal.mul_sup NNReal.mul_sup

theorem sup_mul (a b c : ℝ≥0) : (a ⊔ b) * c = a * c ⊔ b * c :=
  max_mul_of_nonneg _ _ <| zero_le c
#align nnreal.sup_mul NNReal.sup_mul

theorem mul_finset_sup {α} (r : ℝ≥0) (s : Finset α) (f : α → ℝ≥0) :
    r * s.sup f = s.sup fun a => r * f a :=
  Finset.comp_sup_eq_sup_comp _ (NNReal.mul_sup r) (mul_zero r)
#align nnreal.mul_finset_sup NNReal.mul_finset_sup

theorem finset_sup_mul {α} (s : Finset α) (f : α → ℝ≥0) (r : ℝ≥0) :
    s.sup f * r = s.sup fun a => f a * r :=
  Finset.comp_sup_eq_sup_comp (· * r) (fun x y => NNReal.sup_mul x y r) (zero_mul r)
#align nnreal.finset_sup_mul NNReal.finset_sup_mul

theorem finset_sup_div {α} {f : α → ℝ≥0} {s : Finset α} (r : ℝ≥0) :
    s.sup f / r = s.sup fun a => f a / r := by simp only [div_eq_inv_mul, mul_finset_sup]
                                               -- 🎉 no goals
#align nnreal.finset_sup_div NNReal.finset_sup_div

@[simp, norm_cast]
theorem coe_max (x y : ℝ≥0) : ((max x y : ℝ≥0) : ℝ) = max (x : ℝ) (y : ℝ) :=
  NNReal.coe_mono.map_max
#align nnreal.coe_max NNReal.coe_max

@[simp, norm_cast]
theorem coe_min (x y : ℝ≥0) : ((min x y : ℝ≥0) : ℝ) = min (x : ℝ) (y : ℝ) :=
  NNReal.coe_mono.map_min
#align nnreal.coe_min NNReal.coe_min

@[simp]
theorem zero_le_coe {q : ℝ≥0} : 0 ≤ (q : ℝ) :=
  q.2
#align nnreal.zero_le_coe NNReal.zero_le_coe

end NNReal

open NNReal

namespace Real

section ToNNReal

@[simp]
theorem coe_toNNReal' (r : ℝ) : (Real.toNNReal r : ℝ) = max r 0 :=
  rfl
#align real.coe_to_nnreal' Real.coe_toNNReal'

@[simp]
theorem toNNReal_zero : Real.toNNReal 0 = 0 := NNReal.eq <| coe_toNNReal _ le_rfl
#align real.to_nnreal_zero Real.toNNReal_zero

@[simp]
theorem toNNReal_one : Real.toNNReal 1 = 1 := NNReal.eq <| coe_toNNReal _ zero_le_one
#align real.to_nnreal_one Real.toNNReal_one

@[simp]
theorem toNNReal_pos {r : ℝ} : 0 < Real.toNNReal r ↔ 0 < r := by
  simp [← NNReal.coe_lt_coe, lt_irrefl]
  -- 🎉 no goals
#align real.to_nnreal_pos Real.toNNReal_pos

@[simp]
theorem toNNReal_eq_zero {r : ℝ} : Real.toNNReal r = 0 ↔ r ≤ 0 := by
  simpa [-toNNReal_pos] using not_iff_not.2 (@toNNReal_pos r)
  -- 🎉 no goals
#align real.to_nnreal_eq_zero Real.toNNReal_eq_zero

theorem toNNReal_of_nonpos {r : ℝ} : r ≤ 0 → Real.toNNReal r = 0 :=
  toNNReal_eq_zero.2
#align real.to_nnreal_of_nonpos Real.toNNReal_of_nonpos

@[simp]
theorem toNNReal_le_toNNReal_iff {r p : ℝ} (hp : 0 ≤ p) :
    toNNReal r ≤ toNNReal p ↔ r ≤ p := by simp [← NNReal.coe_le_coe, hp]
                                          -- 🎉 no goals
#align real.to_nnreal_le_to_nnreal_iff Real.toNNReal_le_toNNReal_iff

@[simp]
theorem toNNReal_eq_toNNReal_iff {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    toNNReal r = toNNReal p ↔ r = p := by simp [← NNReal.coe_eq, coe_toNNReal, hr, hp]
                                          -- 🎉 no goals
#align real.to_nnreal_eq_to_nnreal_iff Real.toNNReal_eq_toNNReal_iff

@[simp]
theorem toNNReal_lt_toNNReal_iff' {r p : ℝ} : Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p :=
  NNReal.coe_lt_coe.symm.trans max_lt_max_left_iff
#align real.to_nnreal_lt_to_nnreal_iff' Real.toNNReal_lt_toNNReal_iff'

theorem toNNReal_lt_toNNReal_iff {r p : ℝ} (h : 0 < p) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans (and_iff_left h)
#align real.to_nnreal_lt_to_nnreal_iff Real.toNNReal_lt_toNNReal_iff

theorem toNNReal_lt_toNNReal_iff_of_nonneg {r p : ℝ} (hr : 0 ≤ r) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_lt hr h⟩⟩
#align real.to_nnreal_lt_to_nnreal_iff_of_nonneg Real.toNNReal_lt_toNNReal_iff_of_nonneg

@[simp]
theorem toNNReal_add {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal (r + p) = Real.toNNReal r + Real.toNNReal p :=
  NNReal.eq <| by simp [hr, hp, add_nonneg]
                  -- 🎉 no goals
#align real.to_nnreal_add Real.toNNReal_add

theorem toNNReal_add_toNNReal {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal r + Real.toNNReal p = Real.toNNReal (r + p) :=
  (Real.toNNReal_add hr hp).symm
#align real.to_nnreal_add_to_nnreal Real.toNNReal_add_toNNReal

theorem toNNReal_le_toNNReal {r p : ℝ} (h : r ≤ p) : Real.toNNReal r ≤ Real.toNNReal p :=
  Real.toNNReal_mono h
#align real.to_nnreal_le_to_nnreal Real.toNNReal_le_toNNReal

theorem toNNReal_add_le {r p : ℝ} : Real.toNNReal (r + p) ≤ Real.toNNReal r + Real.toNNReal p :=
  NNReal.coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) NNReal.zero_le_coe
#align real.to_nnreal_add_le Real.toNNReal_add_le

theorem toNNReal_le_iff_le_coe {r : ℝ} {p : ℝ≥0} : toNNReal r ≤ p ↔ r ≤ ↑p :=
  NNReal.gi.gc r p
#align real.to_nnreal_le_iff_le_coe Real.toNNReal_le_iff_le_coe

theorem le_toNNReal_iff_coe_le {r : ℝ≥0} {p : ℝ} (hp : 0 ≤ p) : r ≤ Real.toNNReal p ↔ ↑r ≤ p := by
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal p hp]
  -- 🎉 no goals
#align real.le_to_nnreal_iff_coe_le Real.le_toNNReal_iff_coe_le

theorem le_toNNReal_iff_coe_le' {r : ℝ≥0} {p : ℝ} (hr : 0 < r) : r ≤ Real.toNNReal p ↔ ↑r ≤ p :=
  (le_or_lt 0 p).elim le_toNNReal_iff_coe_le fun hp => by
    simp only [(hp.trans_le r.coe_nonneg).not_le, toNNReal_eq_zero.2 hp.le, hr.not_le]
    -- 🎉 no goals
#align real.le_to_nnreal_iff_coe_le' Real.le_toNNReal_iff_coe_le'

theorem toNNReal_lt_iff_lt_coe {r : ℝ} {p : ℝ≥0} (ha : 0 ≤ r) : Real.toNNReal r < p ↔ r < ↑p := by
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal r ha]
  -- 🎉 no goals
#align real.to_nnreal_lt_iff_lt_coe Real.toNNReal_lt_iff_lt_coe

theorem lt_toNNReal_iff_coe_lt {r : ℝ≥0} {p : ℝ} : r < Real.toNNReal p ↔ ↑r < p :=
  lt_iff_lt_of_le_iff_le toNNReal_le_iff_le_coe
#align real.lt_to_nnreal_iff_coe_lt Real.lt_toNNReal_iff_coe_lt

#noalign real.to_nnreal_bit0
#noalign real.to_nnreal_bit1

theorem toNNReal_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x ^ n).toNNReal = x.toNNReal ^ n := by
  rw [← NNReal.coe_eq, NNReal.coe_pow, Real.coe_toNNReal _ (pow_nonneg hx _),
    Real.coe_toNNReal x hx]
#align real.to_nnreal_pow Real.toNNReal_pow

theorem toNNReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    Real.toNNReal (p * q) = Real.toNNReal p * Real.toNNReal q :=
  NNReal.eq <| by simp [mul_max_of_nonneg, hp]
                  -- 🎉 no goals
#align real.to_nnreal_mul Real.toNNReal_mul

end ToNNReal

end Real

open Real

namespace NNReal

section Mul

theorem mul_eq_mul_left {a b c : ℝ≥0} (h : a ≠ 0) : a * b = a * c ↔ b = c := by
  rw [mul_eq_mul_left_iff, or_iff_left h]
  -- 🎉 no goals
#align nnreal.mul_eq_mul_left NNReal.mul_eq_mul_left

end Mul

section Pow

theorem pow_antitone_exp {a : ℝ≥0} (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) : a ^ n ≤ a ^ m :=
  pow_le_pow_of_le_one (zero_le a) a1 mn
#align nnreal.pow_antitone_exp NNReal.pow_antitone_exp

nonrec theorem exists_pow_lt_of_lt_one {a b : ℝ≥0} (ha : 0 < a) (hb : b < 1) :
    ∃ n : ℕ, b ^ n < a := by
  simpa only [← coe_pow, NNReal.coe_lt_coe] using
    exists_pow_lt_of_lt_one (NNReal.coe_pos.2 ha) (NNReal.coe_lt_coe.2 hb)
#align nnreal.exists_pow_lt_of_lt_one NNReal.exists_pow_lt_of_lt_one

nonrec theorem exists_mem_Ico_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ico (y ^ n) (y ^ (n + 1)) :=
  exists_mem_Ico_zpow (α := ℝ) hx.bot_lt hy
#align nnreal.exists_mem_Ico_zpow NNReal.exists_mem_Ico_zpow

nonrec theorem exists_mem_Ioc_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) :=
  exists_mem_Ioc_zpow (α := ℝ) hx.bot_lt hy
#align nnreal.exists_mem_Ioc_zpow NNReal.exists_mem_Ioc_zpow

end Pow

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas about `OrderedSub` in the file
`Mathlib.Algebra.Order.Sub.Basic`. See also `mul_tsub` and `tsub_mul`.
-/

theorem sub_def {r p : ℝ≥0} : r - p = Real.toNNReal (r - p) :=
  rfl
#align nnreal.sub_def NNReal.sub_def

theorem coe_sub_def {r p : ℝ≥0} : ↑(r - p) = max (r - p : ℝ) 0 :=
  rfl
#align nnreal.coe_sub_def NNReal.coe_sub_def

example : OrderedSub ℝ≥0 := by infer_instance
                               -- 🎉 no goals

theorem sub_div (a b c : ℝ≥0) : (a - b) / c = a / c - b / c :=
  tsub_div _ _ _
#align nnreal.sub_div NNReal.sub_div

end Sub

section Inv

theorem sum_div {ι} (s : Finset ι) (f : ι → ℝ≥0) (b : ℝ≥0) :
    (∑ i in s, f i) / b = ∑ i in s, f i / b :=
  Finset.sum_div
#align nnreal.sum_div NNReal.sum_div

@[simp]
theorem inv_le {r p : ℝ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]
  -- 🎉 no goals
#align nnreal.inv_le NNReal.inv_le

theorem inv_le_of_le_mul {r p : ℝ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p := by
  by_cases r = 0 <;> simp [*, inv_le]
  -- ⊢ r⁻¹ ≤ p
  -- ⊢ r⁻¹ ≤ p
                     -- 🎉 no goals
                     -- 🎉 no goals
#align nnreal.inv_le_of_le_mul NNReal.inv_le_of_le_mul

@[simp]
theorem le_inv_iff_mul_le {r p : ℝ≥0} (h : p ≠ 0) : r ≤ p⁻¹ ↔ r * p ≤ 1 := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]
  -- 🎉 no goals
#align nnreal.le_inv_iff_mul_le NNReal.le_inv_iff_mul_le

@[simp]
theorem lt_inv_iff_mul_lt {r p : ℝ≥0} (h : p ≠ 0) : r < p⁻¹ ↔ r * p < 1 := by
  rw [← mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]
  -- 🎉 no goals
#align nnreal.lt_inv_iff_mul_lt NNReal.lt_inv_iff_mul_lt

theorem mul_le_iff_le_inv {a b r : ℝ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  have : 0 < r := lt_of_le_of_ne (zero_le r) hr.symm
  -- ⊢ r * a ≤ b ↔ a ≤ r⁻¹ * b
  rw [← mul_le_mul_left (inv_pos.mpr this), ← mul_assoc, inv_mul_cancel hr, one_mul]
  -- 🎉 no goals
#align nnreal.mul_le_iff_le_inv NNReal.mul_le_iff_le_inv

theorem le_div_iff_mul_le {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
  le_div_iff₀ hr
#align nnreal.le_div_iff_mul_le NNReal.le_div_iff_mul_le

theorem div_le_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r :=
  div_le_iff₀ hr
#align nnreal.div_le_iff NNReal.div_le_iff

nonrec theorem div_le_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ r * b :=
  @div_le_iff' ℝ _ a r b <| pos_iff_ne_zero.2 hr
#align nnreal.div_le_iff' NNReal.div_le_iff'

theorem div_le_of_le_mul {a b c : ℝ≥0} (h : a ≤ b * c) : a / c ≤ b :=
  if h0 : c = 0 then by simp [h0] else (div_le_iff h0).2 h
                        -- 🎉 no goals
#align nnreal.div_le_of_le_mul NNReal.div_le_of_le_mul

theorem div_le_of_le_mul' {a b c : ℝ≥0} (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h
#align nnreal.div_le_of_le_mul' NNReal.div_le_of_le_mul'

nonrec theorem le_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
  @le_div_iff ℝ _ a b r <| pos_iff_ne_zero.2 hr
#align nnreal.le_div_iff NNReal.le_div_iff

nonrec theorem le_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ r * a ≤ b :=
  @le_div_iff' ℝ _ a b r <| pos_iff_ne_zero.2 hr
#align nnreal.le_div_iff' NNReal.le_div_iff'

theorem div_lt_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < b * r :=
  lt_iff_lt_of_le_iff_le (le_div_iff hr)
#align nnreal.div_lt_iff NNReal.div_lt_iff

theorem div_lt_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < r * b :=
  lt_iff_lt_of_le_iff_le (le_div_iff' hr)
#align nnreal.div_lt_iff' NNReal.div_lt_iff'

theorem lt_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff hr)
#align nnreal.lt_div_iff NNReal.lt_div_iff

theorem lt_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ r * a < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff' hr)
#align nnreal.lt_div_iff' NNReal.lt_div_iff'

theorem mul_lt_of_lt_div {a b r : ℝ≥0} (h : a < b / r) : a * r < b :=
  (lt_div_iff fun hr => False.elim <| by simp [hr] at h).1 h
                                         -- 🎉 no goals
#align nnreal.mul_lt_of_lt_div NNReal.mul_lt_of_lt_div

-- porting note: drop an unneeded assumption, assume `≠ 0`
theorem div_le_div_left_of_le {a b c : ℝ≥0} (c0 : c ≠ 0) (cb : c ≤ b) :
    a / b ≤ a / c :=
  div_le_div_of_le_left (zero_le _) c0.bot_lt cb
#align nnreal.div_le_div_left_of_le NNReal.div_le_div_left_of_leₓ

nonrec theorem div_le_div_left {a b c : ℝ≥0} (a0 : 0 < a) (b0 : 0 < b) (c0 : 0 < c) :
    a / b ≤ a / c ↔ c ≤ b :=
  div_le_div_left a0 b0 c0
#align nnreal.div_le_div_left NNReal.div_le_div_left

theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0} (h : ∀ a < 1, a * x ≤ y) : x ≤ y :=
  le_of_forall_ge_of_dense fun a ha => by
    have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha)
    -- ⊢ a ≤ y
    have hx' : x⁻¹ ≠ 0 := by rwa [Ne.def, inv_eq_zero]
    -- ⊢ a ≤ y
    have : a * x⁻¹ < 1 := by rwa [← lt_inv_iff_mul_lt hx', inv_inv]
    -- ⊢ a ≤ y
    have : a * x⁻¹ * x ≤ y := h _ this
    -- ⊢ a ≤ y
    rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this
    -- 🎉 no goals
#align nnreal.le_of_forall_lt_one_mul_le NNReal.le_of_forall_lt_one_mul_le

nonrec theorem half_le_self (a : ℝ≥0) : a / 2 ≤ a :=
  half_le_self bot_le
#align nnreal.half_le_self NNReal.half_le_self

nonrec theorem half_lt_self {a : ℝ≥0} (h : a ≠ 0) : a / 2 < a :=
  half_lt_self h.bot_lt
#align nnreal.half_lt_self NNReal.half_lt_self

theorem div_lt_one_of_lt {a b : ℝ≥0} (h : a < b) : a / b < 1 := by
  rwa [div_lt_iff, one_mul]
  -- ⊢ b ≠ 0
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)
  -- 🎉 no goals
#align nnreal.div_lt_one_of_lt NNReal.div_lt_one_of_lt

theorem _root_.Real.toNNReal_inv {x : ℝ} : Real.toNNReal x⁻¹ = (Real.toNNReal x)⁻¹ := by
  cases' le_total 0 x with hx hx
  -- ⊢ toNNReal x⁻¹ = (toNNReal x)⁻¹
  · nth_rw 1 [← Real.coe_toNNReal x hx]
    -- ⊢ toNNReal (↑(toNNReal x))⁻¹ = (toNNReal x)⁻¹
    rw [← NNReal.coe_inv, Real.toNNReal_coe]
    -- 🎉 no goals
  · rw [toNNReal_eq_zero.mpr hx, inv_zero, toNNReal_eq_zero.mpr (inv_nonpos.mpr hx)]
    -- 🎉 no goals
#align real.to_nnreal_inv Real.toNNReal_inv

theorem _root_.Real.toNNReal_div {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.toNNReal_inv, ← Real.toNNReal_mul hx]
  -- 🎉 no goals
#align real.to_nnreal_div Real.toNNReal_div

theorem _root_.Real.toNNReal_div' {x y : ℝ} (hy : 0 ≤ y) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_inv_mul, div_eq_inv_mul, Real.toNNReal_mul (inv_nonneg.2 hy), Real.toNNReal_inv]
  -- 🎉 no goals
#align real.to_nnreal_div' Real.toNNReal_div'

theorem inv_lt_one_iff {x : ℝ≥0} (hx : x ≠ 0) : x⁻¹ < 1 ↔ 1 < x := by
  rw [← one_div, div_lt_iff hx, one_mul]
  -- 🎉 no goals
#align nnreal.inv_lt_one_iff NNReal.inv_lt_one_iff

theorem zpow_pos {x : ℝ≥0} (hx : x ≠ 0) (n : ℤ) : 0 < x ^ n :=
  zpow_pos_of_pos hx.bot_lt _
#align nnreal.zpow_pos NNReal.zpow_pos

theorem inv_lt_inv {x y : ℝ≥0} (hx : x ≠ 0) (h : x < y) : y⁻¹ < x⁻¹ :=
  inv_lt_inv_of_lt hx.bot_lt h
#align nnreal.inv_lt_inv NNReal.inv_lt_inv

end Inv

@[simp]
theorem abs_eq (x : ℝ≥0) : |(x : ℝ)| = x :=
  abs_of_nonneg x.property
#align nnreal.abs_eq NNReal.abs_eq

section Csupr

open Set

variable {ι : Sort*} {f : ι → ℝ≥0}

theorem le_toNNReal_of_coe_le {x : ℝ≥0} {y : ℝ} (h : ↑x ≤ y) : x ≤ y.toNNReal :=
  (le_toNNReal_iff_coe_le <| x.2.trans h).2 h
#align nnreal.le_to_nnreal_of_coe_le NNReal.le_toNNReal_of_coe_le

nonrec theorem sSup_of_not_bddAbove {s : Set ℝ≥0} (hs : ¬BddAbove s) : SupSet.sSup s = 0 := by
  rw [← bddAbove_coe] at hs
  -- ⊢ sSup s = 0
  rw [← NNReal.coe_eq, coe_sSup, NNReal.coe_zero]
  -- ⊢ sSup (toReal '' s) = 0
  exact sSup_of_not_bddAbove hs
  -- 🎉 no goals
#align nnreal.Sup_of_not_bdd_above NNReal.sSup_of_not_bddAbove

theorem iSup_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = 0 :=
  sSup_of_not_bddAbove hf
#align nnreal.supr_of_not_bdd_above NNReal.iSup_of_not_bddAbove

theorem iSup_empty [IsEmpty ι] (f : ι → ℝ≥0) : ⨆ i, f i = 0 := ciSup_of_empty f

theorem iInf_empty [IsEmpty ι] (f : ι → ℝ≥0) : ⨅ i, f i = 0 := by
  rw [iInf_of_empty', sInf_empty]
  -- 🎉 no goals
#align nnreal.infi_empty NNReal.iInf_empty

@[simp]
theorem iInf_const_zero {α : Sort*} : ⨅ _ : α, (0 : ℝ≥0) = 0 := by
  rw [← NNReal.coe_eq, coe_iInf]
  -- ⊢ ⨅ (i : α), ↑0 = ↑0
  exact Real.ciInf_const_zero
  -- 🎉 no goals
#align nnreal.infi_const_zero NNReal.iInf_const_zero

theorem iInf_mul (f : ι → ℝ≥0) (a : ℝ≥0) : iInf f * a = ⨅ i, f i * a := by
  rw [← NNReal.coe_eq, NNReal.coe_mul, coe_iInf, coe_iInf]
  -- ⊢ (⨅ (i : ι), ↑(f i)) * ↑a = ⨅ (i : ι), ↑(f i * a)
  exact Real.iInf_mul_of_nonneg (NNReal.coe_nonneg _) _
  -- 🎉 no goals
#align nnreal.infi_mul NNReal.iInf_mul

theorem mul_iInf (f : ι → ℝ≥0) (a : ℝ≥0) : a * iInf f = ⨅ i, a * f i := by
  simpa only [mul_comm] using iInf_mul f a
  -- 🎉 no goals
#align nnreal.mul_infi NNReal.mul_iInf

theorem mul_iSup (f : ι → ℝ≥0) (a : ℝ≥0) : (a * ⨆ i, f i) = ⨆ i, a * f i := by
  rw [← NNReal.coe_eq, NNReal.coe_mul, NNReal.coe_iSup, NNReal.coe_iSup]
  -- ⊢ ↑a * ⨆ (i : ι), ↑(f i) = ⨆ (i : ι), ↑(a * f i)
  exact Real.mul_iSup_of_nonneg (NNReal.coe_nonneg _) _
  -- 🎉 no goals
#align nnreal.mul_supr NNReal.mul_iSup

theorem iSup_mul (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  rw [mul_comm, mul_iSup]
  -- ⊢ ⨆ (i : ι), a * f i = ⨆ (i : ι), f i * a
  simp_rw [mul_comm]
  -- 🎉 no goals
#align nnreal.supr_mul NNReal.iSup_mul

theorem iSup_div (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, iSup_mul]
  -- 🎉 no goals
#align nnreal.supr_div NNReal.iSup_div

-- porting note: generalized to allow empty `ι`
theorem mul_iSup_le {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, g * h j ≤ a) : g * iSup h ≤ a := by
  rw [mul_iSup]
  -- ⊢ ⨆ (i : ι), g * h i ≤ a
  exact ciSup_le' H
  -- 🎉 no goals
#align nnreal.mul_supr_le NNReal.mul_iSup_le

-- porting note: generalized to allow empty `ι`
theorem iSup_mul_le {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, g i * h ≤ a) : iSup g * h ≤ a := by
  rw [iSup_mul]
  -- ⊢ ⨆ (i : ι), g i * h ≤ a
  exact ciSup_le' H
  -- 🎉 no goals
#align nnreal.supr_mul_le NNReal.iSup_mul_le

-- porting note: generalized to allow empty `ι`
theorem iSup_mul_iSup_le {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, g i * h j ≤ a) :
    iSup g * iSup h ≤ a :=
  iSup_mul_le fun _ => mul_iSup_le <| H _
#align nnreal.supr_mul_supr_le NNReal.iSup_mul_iSup_le

variable [Nonempty ι]

theorem le_mul_iInf {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, a ≤ g * h j) : a ≤ g * iInf h := by
  rw [mul_iInf]
  -- ⊢ a ≤ ⨅ (i : ι), g * h i
  exact le_ciInf H
  -- 🎉 no goals
#align nnreal.le_mul_infi NNReal.le_mul_iInf

theorem le_iInf_mul {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, a ≤ g i * h) : a ≤ iInf g * h := by
  rw [iInf_mul]
  -- ⊢ a ≤ ⨅ (i : ι), g i * h
  exact le_ciInf H
  -- 🎉 no goals
#align nnreal.le_infi_mul NNReal.le_iInf_mul

theorem le_iInf_mul_iInf {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, a ≤ g i * h j) :
    a ≤ iInf g * iInf h :=
  le_iInf_mul fun i => le_mul_iInf <| H i
#align nnreal.le_infi_mul_infi NNReal.le_iInf_mul_iInf

end Csupr

end NNReal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0}

theorem preimage_coe_nnreal_real (h : s.OrdConnected) : ((↑) ⁻¹' s : Set ℝ≥0).OrdConnected :=
  h.preimage_mono NNReal.coe_mono
#align set.ord_connected.preimage_coe_nnreal_real Set.OrdConnected.preimage_coe_nnreal_real

theorem image_coe_nnreal_real (h : t.OrdConnected) : ((↑) '' t : Set ℝ).OrdConnected :=
  ⟨ball_image_iff.2 fun x hx =>
      ball_image_iff.2 fun _y hy z hz => ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩
#align set.ord_connected.image_coe_nnreal_real Set.OrdConnected.image_coe_nnreal_real

-- porting note: todo: does it generalize to a `GaloisInsertion`?
theorem image_real_toNNReal (h : s.OrdConnected) : (Real.toNNReal '' s).OrdConnected := by
  refine' ⟨ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy z hz => _⟩
  -- ⊢ z ∈ toNNReal '' s
  cases' le_total y 0 with hy₀ hy₀
  -- ⊢ z ∈ toNNReal '' s
  · rw [mem_Icc, Real.toNNReal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz
    -- ⊢ z ∈ toNNReal '' s
    exact ⟨y, hy, (toNNReal_of_nonpos hy₀).trans hz.2.symm⟩
    -- 🎉 no goals
  · lift y to ℝ≥0 using hy₀
    -- ⊢ z ∈ toNNReal '' s
    rw [toNNReal_coe] at hz
    -- ⊢ z ∈ toNNReal '' s
    exact ⟨z, h.out hx hy ⟨toNNReal_le_iff_le_coe.1 hz.1, hz.2⟩, toNNReal_coe⟩
    -- 🎉 no goals
#align set.ord_connected.image_real_to_nnreal Set.OrdConnected.image_real_toNNReal

theorem preimage_real_toNNReal (h : t.OrdConnected) : (Real.toNNReal ⁻¹' t).OrdConnected :=
  h.preimage_mono Real.toNNReal_mono
#align set.ord_connected.preimage_real_to_nnreal Set.OrdConnected.preimage_real_toNNReal

end OrdConnected

end Set

namespace Real

/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
-- porting note: removed @[pp_nodot]
def nnabs : ℝ →*₀ ℝ≥0 where
  toFun x := ⟨|x|, abs_nonneg x⟩
  map_zero' := by ext; simp
                  -- ⊢ ↑((fun x => { val := |x|, property := (_ : 0 ≤ |x|) }) 0) = ↑0
                       -- 🎉 no goals
  map_one' := by ext; simp
                 -- ⊢ ↑(ZeroHom.toFun { toFun := fun x => { val := |x|, property := (_ : 0 ≤ |x|)  …
                      -- 🎉 no goals
  map_mul' x y := by ext; simp [abs_mul]
                     -- ⊢ ↑(ZeroHom.toFun { toFun := fun x => { val := |x|, property := (_ : 0 ≤ |x|)  …
                          -- 🎉 no goals
#align real.nnabs Real.nnabs

@[norm_cast, simp]
theorem coe_nnabs (x : ℝ) : (nnabs x : ℝ) = |x| :=
  rfl
#align real.coe_nnabs Real.coe_nnabs

@[simp]
theorem nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : nnabs x = toNNReal x := by
  ext
  -- ⊢ ↑(↑nnabs x) = ↑(toNNReal x)
  rw [coe_toNNReal x h, coe_nnabs, abs_of_nonneg h]
  -- 🎉 no goals
#align real.nnabs_of_nonneg Real.nnabs_of_nonneg

theorem nnabs_coe (x : ℝ≥0) : nnabs x = x := by simp
                                                -- 🎉 no goals
#align real.nnabs_coe Real.nnabs_coe

theorem coe_toNNReal_le (x : ℝ) : (toNNReal x : ℝ) ≤ |x| :=
  max_le (le_abs_self _) (abs_nonneg _)
#align real.coe_to_nnreal_le Real.coe_toNNReal_le

theorem cast_natAbs_eq_nnabs_cast (n : ℤ) : (n.natAbs : ℝ≥0) = nnabs n := by
  ext
  -- ⊢ ↑↑(Int.natAbs n) = ↑(↑nnabs ↑n)
  rw [NNReal.coe_nat_cast, Int.cast_natAbs, Real.coe_nnabs, Int.cast_abs]
  -- 🎉 no goals
#align real.cast_nat_abs_eq_nnabs_cast Real.cast_natAbs_eq_nnabs_cast

end Real

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

private theorem nnreal_coe_pos {r : ℝ≥0} : 0 < r → 0 < (r : ℝ) :=
  NNReal.coe_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ≥0` to `ℝ`. -/
@[positivity NNReal.toReal _]
def evalNNRealtoReal : PositivityExt where eval {_ _} _zα _pα e := do
  let (.app _ (a : Q(NNReal))) ← whnfR e | throwError "not NNReal.toReal"
  let zα' ← synthInstanceQ (q(Zero NNReal) : Q(Type))
  let pα' ← synthInstanceQ (q(PartialOrder NNReal) : Q(Type))
  let ra ← core zα' pα' a
  assertInstancesCommute
  match ra with
  | .positive pa => pure (.positive (q(nnreal_coe_pos $pa) : Expr))
  | _ => pure (.nonnegative (q(NNReal.coe_nonneg $a) : Expr))

end Mathlib.Meta.Positivity
