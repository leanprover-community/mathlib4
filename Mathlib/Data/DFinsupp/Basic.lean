/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.GroupAction.BigOperators

#align_import data.dfinsupp.basic from "leanprover-community/mathlib"@"6623e6af705e97002a9054c1c05a980180276fc1"

/-!
# Dependent functions with finite support

For a non-dependent version see `data/finsupp.lean`.

## Notation

This file introduces the notation `Π₀ a, β a` as notation for `DFinsupp β`, mirroring the `α →₀ β`
notation used for `Finsupp`. This works for nested binders too, with `Π₀ a b, γ a b` as notation
for `DFinsupp (fun a ↦ DFinsupp (γ a))`.

## Implementation notes

The support is internally represented (in the primed `DFinsupp.support'`) as a `Multiset` that
represents a superset of the true support of the function, quotiented by the always-true relation so
that this does not impact equality. This approach has computational benefits over storing a
`Finset`; it allows us to add together two finitely-supported functions without
having to evaluate the resulting function to recompute its support (which would required
decidability of `b = 0` for `b : β i`).

The true support of the function can still be recovered with `DFinsupp.support`; but these
decidability obligations are now postponed to when the support is actually needed. As a consequence,
there are two ways to sum a `DFinsupp`: with `DFinsupp.sum` which works over an arbitrary function
but requires recomputation of the support and therefore a `Decidable` argument; and with
`DFinsupp.sumAddHom` which requires an additive morphism, using its properties to show that
summing over a superset of the support is sufficient.

`Finsupp` takes an altogether different approach here; it uses `Classical.Decidable` and declares
the `Add` instance as noncomputable. This design difference is independent of the fact that
`DFinsupp` is dependently-typed and `Finsupp` is not; in future, we may want to align these two
definitions, or introduce two more definitions for the other combinations of decisions.
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variable (β)

/-- A dependent function `Π i, β i` with finite support, with notation `Π₀ i, β i`.

Note that `DFinsupp.support` is the preferred API for accessing the support of the function,
`DFinsupp.support'` is an implementation detail that aids computability; see the implementation
notes in this file for more information. -/
structure DFinsupp [∀ i, Zero (β i)] : Type max u v where mk' ::
  /-- The underlying function of a dependent function with finite support (aka `DFinsupp`). -/
  toFun : ∀ i, β i
  /-- The support of a dependent function with finite support (aka `DFinsupp`). -/
  support' : Trunc { s : Multiset ι // ∀ i, i ∈ s ∨ toFun i = 0 }
#align dfinsupp DFinsupp

variable {β}

/-- `Π₀ i, β i` denotes the type of dependent functions with finite support `DFinsupp β`. -/
notation3 "Π₀ "(...)", "r:(scoped f => DFinsupp f) => r

namespace DFinsupp

section Basic

variable [∀ i, Zero (β i)] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

instance instDFunLike : DFunLike (Π₀ i, β i) ι β :=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ ↦ fun (h : f₁ = f₂) ↦ by
    subst h
    congr
    apply Subsingleton.elim ⟩
#align dfinsupp.fun_like DFinsupp.instDFunLike

/-- Helper instance for when there are too many metavariables to apply `DFunLike.coeFunForall`
directly. -/
instance : CoeFun (Π₀ i, β i) fun _ => ∀ i, β i :=
  inferInstance

@[simp]
theorem toFun_eq_coe (f : Π₀ i, β i) : f.toFun = f :=
  rfl
#align dfinsupp.to_fun_eq_coe DFinsupp.toFun_eq_coe

@[ext]
theorem ext {f g : Π₀ i, β i} (h : ∀ i, f i = g i) : f = g :=
  DFunLike.ext _ _ h
#align dfinsupp.ext DFinsupp.ext

#align dfinsupp.ext_iff DFunLike.ext_iff
#align dfinsupp.coe_fn_injective DFunLike.coe_injective

lemma ne_iff {f g : Π₀ i, β i} : f ≠ g ↔ ∃ i, f i ≠ g i := DFunLike.ne_iff

instance : Zero (Π₀ i, β i) :=
  ⟨⟨0, Trunc.mk <| ⟨∅, fun _ => Or.inr rfl⟩⟩⟩

instance : Inhabited (Π₀ i, β i) :=
  ⟨0⟩

@[simp, norm_cast] lemma coe_mk' (f : ∀ i, β i) (s) : ⇑(⟨f, s⟩ : Π₀ i, β i) = f := rfl
#align dfinsupp.coe_mk' DFinsupp.coe_mk'

@[simp, norm_cast] lemma coe_zero : ⇑(0 : Π₀ i, β i) = 0 := rfl
#align dfinsupp.coe_zero DFinsupp.coe_zero

theorem zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0 :=
  rfl
#align dfinsupp.zero_apply DFinsupp.zero_apply

/-- The composition of `f : β₁ → β₂` and `g : Π₀ i, β₁ i` is
  `mapRange f hf g : Π₀ i, β₂ i`, well defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled:

* `DFinsupp.mapRange.addMonoidHom`
* `DFinsupp.mapRange.addEquiv`
* `dfinsupp.mapRange.linearMap`
* `dfinsupp.mapRange.linearEquiv`
-/
def mapRange (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (x : Π₀ i, β₁ i) : Π₀ i, β₂ i :=
  ⟨fun i => f i (x i),
    x.support'.map fun s => ⟨s.1, fun i => (s.2 i).imp_right fun h : x i = 0 => by
      rw [← hf i, ← h]⟩⟩
#align dfinsupp.map_range DFinsupp.mapRange

@[simp]
theorem mapRange_apply (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι) :
    mapRange f hf g i = f i (g i) :=
  rfl
#align dfinsupp.map_range_apply DFinsupp.mapRange_apply

@[simp]
theorem mapRange_id (h : ∀ i, id (0 : β₁ i) = 0 := fun i => rfl) (g : Π₀ i : ι, β₁ i) :
    mapRange (fun i => (id : β₁ i → β₁ i)) h g = g := by
  ext
  rfl
#align dfinsupp.map_range_id DFinsupp.mapRange_id

theorem mapRange_comp (f : ∀ i, β₁ i → β₂ i) (f₂ : ∀ i, β i → β₁ i) (hf : ∀ i, f i 0 = 0)
    (hf₂ : ∀ i, f₂ i 0 = 0) (h : ∀ i, (f i ∘ f₂ i) 0 = 0) (g : Π₀ i : ι, β i) :
    mapRange (fun i => f i ∘ f₂ i) h g = mapRange f hf (mapRange f₂ hf₂ g) := by
  ext
  simp only [mapRange_apply]; rfl
#align dfinsupp.map_range_comp DFinsupp.mapRange_comp

@[simp]
theorem mapRange_zero (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) :
    mapRange f hf (0 : Π₀ i, β₁ i) = 0 := by
  ext
  simp only [mapRange_apply, coe_zero, Pi.zero_apply, hf]
#align dfinsupp.map_range_zero DFinsupp.mapRange_zero

/-- Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i 0 0 = 0`.
Then `zipWith f hf` is a binary operation `Π₀ i, β₁ i → Π₀ i, β₂ i → Π₀ i, β i`. -/
def zipWith (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (x : Π₀ i, β₁ i) (y : Π₀ i, β₂ i) :
    Π₀ i, β i :=
  ⟨fun i => f i (x i) (y i), by
    refine x.support'.bind fun xs => ?_
    refine y.support'.map fun ys => ?_
    refine ⟨xs + ys, fun i => ?_⟩
    obtain h1 | (h1 : x i = 0) := xs.prop i
    · left
      rw [Multiset.mem_add]
      left
      exact h1
    obtain h2 | (h2 : y i = 0) := ys.prop i
    · left
      rw [Multiset.mem_add]
      right
      exact h2
    right; rw [← hf, ← h1, ← h2]⟩
#align dfinsupp.zip_with DFinsupp.zipWith

@[simp]
theorem zipWith_apply (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i)
    (g₂ : Π₀ i, β₂ i) (i : ι) : zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
  rfl
#align dfinsupp.zip_with_apply DFinsupp.zipWith_apply

section Piecewise

variable (x y : Π₀ i, β i) (s : Set ι) [∀ i, Decidable (i ∈ s)]

/-- `x.piecewise y s` is the finitely supported function equal to `x` on the set `s`,
  and to `y` on its complement. -/
def piecewise : Π₀ i, β i :=
  zipWith (fun i x y => if i ∈ s then x else y) (fun _ => ite_self 0) x y
#align dfinsupp.piecewise DFinsupp.piecewise

theorem piecewise_apply (i : ι) : x.piecewise y s i = if i ∈ s then x i else y i :=
  zipWith_apply _ _ x y i
#align dfinsupp.piecewise_apply DFinsupp.piecewise_apply

@[simp, norm_cast]
theorem coe_piecewise : ⇑(x.piecewise y s) = s.piecewise x y := by
  ext
  apply piecewise_apply
#align dfinsupp.coe_piecewise DFinsupp.coe_piecewise

end Piecewise

end Basic

section Algebra

instance [∀ i, AddZeroClass (β i)] : Add (Π₀ i, β i) :=
  ⟨zipWith (fun _ => (· + ·)) fun _ => add_zero 0⟩

theorem add_apply [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
    (g₁ + g₂) i = g₁ i + g₂ i :=
  rfl
#align dfinsupp.add_apply DFinsupp.add_apply

@[simp, norm_cast]
theorem coe_add [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ + g₂) = g₁ + g₂ :=
  rfl
#align dfinsupp.coe_add DFinsupp.coe_add

instance addZeroClass [∀ i, AddZeroClass (β i)] : AddZeroClass (Π₀ i, β i) :=
  DFunLike.coe_injective.addZeroClass _ coe_zero coe_add

instance instIsLeftCancelAdd [∀ i, AddZeroClass (β i)] [∀ i, IsLeftCancelAdd (β i)] :
    IsLeftCancelAdd (Π₀ i, β i) where
  add_left_cancel _ _ _ h := ext fun x => add_left_cancel <| DFunLike.congr_fun h x

instance instIsRightCancelAdd [∀ i, AddZeroClass (β i)] [∀ i, IsRightCancelAdd (β i)] :
    IsRightCancelAdd (Π₀ i, β i) where
  add_right_cancel _ _ _ h := ext fun x => add_right_cancel <| DFunLike.congr_fun h x

instance instIsCancelAdd [∀ i, AddZeroClass (β i)] [∀ i, IsCancelAdd (β i)] :
    IsCancelAdd (Π₀ i, β i) where

/-- Note the general `SMul` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasNatScalar [∀ i, AddMonoid (β i)] : SMul ℕ (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => nsmul_zero _⟩
#align dfinsupp.has_nat_scalar DFinsupp.hasNatScalar

theorem nsmul_apply [∀ i, AddMonoid (β i)] (b : ℕ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl
#align dfinsupp.nsmul_apply DFinsupp.nsmul_apply

@[simp, norm_cast]
theorem coe_nsmul [∀ i, AddMonoid (β i)] (b : ℕ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl
#align dfinsupp.coe_nsmul DFinsupp.coe_nsmul

instance [∀ i, AddMonoid (β i)] : AddMonoid (Π₀ i, β i) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

/-- Coercion from a `DFinsupp` to a pi type is an `AddMonoidHom`. -/
def coeFnAddMonoidHom [∀ i, AddZeroClass (β i)] : (Π₀ i, β i) →+ ∀ i, β i where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align dfinsupp.coe_fn_add_monoid_hom DFinsupp.coeFnAddMonoidHom

/-- Evaluation at a point is an `AddMonoidHom`. This is the finitely-supported version of
`Pi.evalAddMonoidHom`. -/
def evalAddMonoidHom [∀ i, AddZeroClass (β i)] (i : ι) : (Π₀ i, β i) →+ β i :=
  (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom
#align dfinsupp.eval_add_monoid_hom DFinsupp.evalAddMonoidHom

instance addCommMonoid [∀ i, AddCommMonoid (β i)] : AddCommMonoid (Π₀ i, β i) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

@[simp, norm_cast]
theorem coe_finset_sum {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) :
    ⇑(∑ a ∈ s, g a) = ∑ a ∈ s, ⇑(g a) :=
  map_sum coeFnAddMonoidHom g s
#align dfinsupp.coe_finset_sum DFinsupp.coe_finset_sum

@[simp]
theorem finset_sum_apply {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) (i : ι) :
    (∑ a ∈ s, g a) i = ∑ a ∈ s, g a i :=
  map_sum (evalAddMonoidHom i) g s
#align dfinsupp.finset_sum_apply DFinsupp.finset_sum_apply

instance [∀ i, AddGroup (β i)] : Neg (Π₀ i, β i) :=
  ⟨fun f => f.mapRange (fun _ => Neg.neg) fun _ => neg_zero⟩

theorem neg_apply [∀ i, AddGroup (β i)] (g : Π₀ i, β i) (i : ι) : (-g) i = -g i :=
  rfl
#align dfinsupp.neg_apply DFinsupp.neg_apply

@[simp, norm_cast] lemma coe_neg [∀ i, AddGroup (β i)] (g : Π₀ i, β i) : ⇑(-g) = -g := rfl
#align dfinsupp.coe_neg DFinsupp.coe_neg

instance [∀ i, AddGroup (β i)] : Sub (Π₀ i, β i) :=
  ⟨zipWith (fun _ => Sub.sub) fun _ => sub_zero 0⟩

theorem sub_apply [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  rfl
#align dfinsupp.sub_apply DFinsupp.sub_apply

@[simp, norm_cast]
theorem coe_sub [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  rfl
#align dfinsupp.coe_sub DFinsupp.coe_sub

/-- Note the general `SMul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasIntScalar [∀ i, AddGroup (β i)] : SMul ℤ (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => zsmul_zero _⟩
#align dfinsupp.has_int_scalar DFinsupp.hasIntScalar

theorem zsmul_apply [∀ i, AddGroup (β i)] (b : ℤ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl
#align dfinsupp.zsmul_apply DFinsupp.zsmul_apply

@[simp, norm_cast]
theorem coe_zsmul [∀ i, AddGroup (β i)] (b : ℤ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl
#align dfinsupp.coe_zsmul DFinsupp.coe_zsmul

instance [∀ i, AddGroup (β i)] : AddGroup (Π₀ i, β i) :=
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

instance addCommGroup [∀ i, AddCommGroup (β i)] : AddCommGroup (Π₀ i, β i) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

/-- Dependent functions with finite support inherit a semiring action from an action on each
coordinate. -/
instance [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] : SMul γ (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => smul_zero _⟩

theorem smul_apply [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] (b : γ)
    (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl
#align dfinsupp.smul_apply DFinsupp.smul_apply

@[simp, norm_cast]
theorem coe_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] (b : γ)
    (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl
#align dfinsupp.coe_smul DFinsupp.coe_smul

instance smulCommClass {δ : Type*} [Monoid γ] [Monoid δ] [∀ i, AddMonoid (β i)]
    [∀ i, DistribMulAction γ (β i)] [∀ i, DistribMulAction δ (β i)] [∀ i, SMulCommClass γ δ (β i)] :
    SMulCommClass γ δ (Π₀ i, β i) where
  smul_comm r s m := ext fun i => by simp only [smul_apply, smul_comm r s (m i)]

instance isScalarTower {δ : Type*} [Monoid γ] [Monoid δ] [∀ i, AddMonoid (β i)]
    [∀ i, DistribMulAction γ (β i)] [∀ i, DistribMulAction δ (β i)] [SMul γ δ]
    [∀ i, IsScalarTower γ δ (β i)] : IsScalarTower γ δ (Π₀ i, β i) where
  smul_assoc r s m := ext fun i => by simp only [smul_apply, smul_assoc r s (m i)]

instance isCentralScalar [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    [∀ i, DistribMulAction γᵐᵒᵖ (β i)] [∀ i, IsCentralScalar γ (β i)] :
    IsCentralScalar γ (Π₀ i, β i) where
  op_smul_eq_smul r m := ext fun i => by simp only [smul_apply, op_smul_eq_smul r (m i)]

/-- Dependent functions with finite support inherit a `DistribMulAction` structure from such a
structure on each coordinate. -/
instance distribMulAction [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] :
    DistribMulAction γ (Π₀ i, β i) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom DFunLike.coe_injective coe_smul

/-- Dependent functions with finite support inherit a module structure from such a structure on
each coordinate. -/
instance module [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] :
    Module γ (Π₀ i, β i) :=
  { inferInstanceAs (DistribMulAction γ (Π₀ i, β i)) with
    zero_smul := fun c => ext fun i => by simp only [smul_apply, zero_smul, zero_apply]
    add_smul := fun c x y => ext fun i => by simp only [add_apply, smul_apply, add_smul] }
#align dfinsupp.module DFinsupp.module


end Algebra

section FilterAndSubtypeDomain

/-- `Filter p f` is the function which is `f i` if `p i` is true and 0 otherwise. -/
def filter [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (x : Π₀ i, β i) : Π₀ i, β i :=
  ⟨fun i => if p i then x i else 0,
    x.support'.map fun xs =>
      ⟨xs.1, fun i => (xs.prop i).imp_right fun H : x i = 0 => by simp only [H, ite_self]⟩⟩
#align dfinsupp.filter DFinsupp.filter

@[simp]
theorem filter_apply [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (i : ι) (f : Π₀ i, β i) :
    f.filter p i = if p i then f i else 0 :=
  rfl
#align dfinsupp.filter_apply DFinsupp.filter_apply

theorem filter_apply_pos [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : p i) : f.filter p i = f i := by simp only [filter_apply, if_pos h]
#align dfinsupp.filter_apply_pos DFinsupp.filter_apply_pos

theorem filter_apply_neg [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : ¬p i) : f.filter p i = 0 := by simp only [filter_apply, if_neg h]
#align dfinsupp.filter_apply_neg DFinsupp.filter_apply_neg

theorem filter_pos_add_filter_neg [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i) (p : ι → Prop)
    [DecidablePred p] : (f.filter p + f.filter fun i => ¬p i) = f :=
  ext fun i => by
    simp only [add_apply, filter_apply]; split_ifs <;> simp only [add_zero, zero_add]
#align dfinsupp.filter_pos_add_filter_neg DFinsupp.filter_pos_add_filter_neg

@[simp]
theorem filter_zero [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] :
    (0 : Π₀ i, β i).filter p = 0 := by
  ext
  simp
#align dfinsupp.filter_zero DFinsupp.filter_zero

@[simp]
theorem filter_add [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f + g).filter p = f.filter p + g.filter p := by
  ext
  simp [ite_add_zero]
#align dfinsupp.filter_add DFinsupp.filter_add

@[simp]
theorem filter_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] (p : ι → Prop)
    [DecidablePred p] (r : γ) (f : Π₀ i, β i) : (r • f).filter p = r • f.filter p := by
  ext
  simp [smul_apply, smul_ite]
#align dfinsupp.filter_smul DFinsupp.filter_smul

variable (γ β)

/-- `DFinsupp.filter` as an `AddMonoidHom`. -/
@[simps]
def filterAddMonoidHom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i, β i) →+ Π₀ i, β i where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' := filter_add p
#align dfinsupp.filter_add_monoid_hom DFinsupp.filterAddMonoidHom
#align dfinsupp.filter_add_monoid_hom_apply DFinsupp.filterAddMonoidHom_apply

/-- `DFinsupp.filter` as a `LinearMap`. -/
@[simps]
def filterLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] (p : ι → Prop)
    [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i, β i where
  toFun := filter p
  map_add' := filter_add p
  map_smul' := filter_smul p
#align dfinsupp.filter_linear_map DFinsupp.filterLinearMap
#align dfinsupp.filter_linear_map_apply DFinsupp.filterLinearMap_apply

variable {γ β}

@[simp]
theorem filter_neg [∀ i, AddGroup (β i)] (p : ι → Prop) [DecidablePred p] (f : Π₀ i, β i) :
    (-f).filter p = -f.filter p :=
  (filterAddMonoidHom β p).map_neg f
#align dfinsupp.filter_neg DFinsupp.filter_neg

@[simp]
theorem filter_sub [∀ i, AddGroup (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f - g).filter p = f.filter p - g.filter p :=
  (filterAddMonoidHom β p).map_sub f g
#align dfinsupp.filter_sub DFinsupp.filter_sub

/-- `subtypeDomain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtypeDomain [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (x : Π₀ i, β i) :
    Π₀ i : Subtype p, β i :=
  ⟨fun i => x (i : ι),
    x.support'.map fun xs =>
      ⟨(Multiset.filter p xs.1).attach.map fun j => ⟨j.1, (Multiset.mem_filter.1 j.2).2⟩, fun i =>
        (xs.prop i).imp_left fun H =>
          Multiset.mem_map.2
            ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩⟩
#align dfinsupp.subtype_domain DFinsupp.subtypeDomain

@[simp]
theorem subtypeDomain_zero [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] :
    subtypeDomain p (0 : Π₀ i, β i) = 0 :=
  rfl
#align dfinsupp.subtype_domain_zero DFinsupp.subtypeDomain_zero

@[simp]
theorem subtypeDomain_apply [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] {i : Subtype p}
    {v : Π₀ i, β i} : (subtypeDomain p v) i = v i :=
  rfl
#align dfinsupp.subtype_domain_apply DFinsupp.subtypeDomain_apply

@[simp]
theorem subtypeDomain_add [∀ i, AddZeroClass (β i)] {p : ι → Prop} [DecidablePred p]
    (v v' : Π₀ i, β i) : (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  DFunLike.coe_injective rfl
#align dfinsupp.subtype_domain_add DFinsupp.subtypeDomain_add

@[simp]
theorem subtypeDomain_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    {p : ι → Prop} [DecidablePred p] (r : γ) (f : Π₀ i, β i) :
    (r • f).subtypeDomain p = r • f.subtypeDomain p :=
  DFunLike.coe_injective rfl
#align dfinsupp.subtype_domain_smul DFinsupp.subtypeDomain_smul

variable (γ β)

/-- `subtypeDomain` but as an `AddMonoidHom`. -/
@[simps]
def subtypeDomainAddMonoidHom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i : ι, β i) →+ Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' := subtypeDomain_add
#align dfinsupp.subtype_domain_add_monoid_hom DFinsupp.subtypeDomainAddMonoidHom
#align dfinsupp.subtype_domain_add_monoid_hom_apply DFinsupp.subtypeDomainAddMonoidHom_apply

/-- `DFinsupp.subtypeDomain` as a `LinearMap`. -/
@[simps]
def subtypeDomainLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    (p : ι → Prop) [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_add' := subtypeDomain_add
  map_smul' := subtypeDomain_smul
#align dfinsupp.subtype_domain_linear_map DFinsupp.subtypeDomainLinearMap
#align dfinsupp.subtype_domain_linear_map_apply DFinsupp.subtypeDomainLinearMap_apply

variable {γ β}

@[simp]
theorem subtypeDomain_neg [∀ i, AddGroup (β i)] {p : ι → Prop} [DecidablePred p] {v : Π₀ i, β i} :
    (-v).subtypeDomain p = -v.subtypeDomain p :=
  DFunLike.coe_injective rfl
#align dfinsupp.subtype_domain_neg DFinsupp.subtypeDomain_neg

@[simp]
theorem subtypeDomain_sub [∀ i, AddGroup (β i)] {p : ι → Prop} [DecidablePred p]
    {v v' : Π₀ i, β i} : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  DFunLike.coe_injective rfl
#align dfinsupp.subtype_domain_sub DFinsupp.subtypeDomain_sub

end FilterAndSubtypeDomain

variable [DecidableEq ι]

section Basic

variable [∀ i, Zero (β i)]

theorem finite_support (f : Π₀ i, β i) : Set.Finite { i | f i ≠ 0 } :=
  Trunc.induction_on f.support' fun xs ↦
    xs.1.finite_toSet.subset fun i H ↦ ((xs.prop i).resolve_right H)
#align dfinsupp.finite_support DFinsupp.finite_support

/-- Create an element of `Π₀ i, β i` from a finset `s` and a function `x`
defined on this `Finset`. -/
def mk (s : Finset ι) (x : ∀ i : (↑s : Set ι), β (i : ι)) : Π₀ i, β i :=
  ⟨fun i => if H : i ∈ s then x ⟨i, H⟩ else 0,
    Trunc.mk ⟨s.1, fun i => if H : i ∈ s then Or.inl H else Or.inr <| dif_neg H⟩⟩
#align dfinsupp.mk DFinsupp.mk

variable {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i} {i : ι}

@[simp]
theorem mk_apply : (mk s x : ∀ i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else 0 :=
  rfl
#align dfinsupp.mk_apply DFinsupp.mk_apply

theorem mk_of_mem (hi : i ∈ s) : (mk s x : ∀ i, β i) i = x ⟨i, hi⟩ :=
  dif_pos hi
#align dfinsupp.mk_of_mem DFinsupp.mk_of_mem

theorem mk_of_not_mem (hi : i ∉ s) : (mk s x : ∀ i, β i) i = 0 :=
  dif_neg hi
#align dfinsupp.mk_of_not_mem DFinsupp.mk_of_not_mem

theorem mk_injective (s : Finset ι) : Function.Injective (@mk ι β _ _ s) := by
  intro x y H
  ext i
  have h1 : (mk s x : ∀ i, β i) i = (mk s y : ∀ i, β i) i := by rw [H]
  obtain ⟨i, hi : i ∈ s⟩ := i
  dsimp only [mk_apply, Subtype.coe_mk] at h1
  simpa only [dif_pos hi] using h1
#align dfinsupp.mk_injective DFinsupp.mk_injective

instance unique [∀ i, Subsingleton (β i)] : Unique (Π₀ i, β i) :=
  DFunLike.coe_injective.unique
#align dfinsupp.unique DFinsupp.unique

instance uniqueOfIsEmpty [IsEmpty ι] : Unique (Π₀ i, β i) :=
  DFunLike.coe_injective.unique
#align dfinsupp.unique_of_is_empty DFinsupp.uniqueOfIsEmpty

/-- Given `Fintype ι`, `equivFunOnFintype` is the `Equiv` between `Π₀ i, β i` and `Π i, β i`.
  (All dependent functions on a finite type are finitely supported.) -/
@[simps apply]
def equivFunOnFintype [Fintype ι] : (Π₀ i, β i) ≃ ∀ i, β i where
  toFun := (⇑)
  invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl <| Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl
  right_inv _ := rfl
#align dfinsupp.equiv_fun_on_fintype DFinsupp.equivFunOnFintype
#align dfinsupp.equiv_fun_on_fintype_apply DFinsupp.equivFunOnFintype_apply

@[simp]
theorem equivFunOnFintype_symm_coe [Fintype ι] (f : Π₀ i, β i) : equivFunOnFintype.symm f = f :=
  Equiv.symm_apply_apply _ _
#align dfinsupp.equiv_fun_on_fintype_symm_coe DFinsupp.equivFunOnFintype_symm_coe

/-- The function `single i b : Π₀ i, β i` sends `i` to `b`
and all other points to `0`. -/
def single (i : ι) (b : β i) : Π₀ i, β i :=
  ⟨Pi.single i b,
    Trunc.mk ⟨{i}, fun j => (Decidable.eq_or_ne j i).imp (by simp) fun h => Pi.single_eq_of_ne h _⟩⟩
#align dfinsupp.single DFinsupp.single

theorem single_eq_pi_single {i b} : ⇑(single i b : Π₀ i, β i) = Pi.single i b :=
  rfl
#align dfinsupp.single_eq_pi_single DFinsupp.single_eq_pi_single

@[simp]
theorem single_apply {i i' b} :
    (single i b : Π₀ i, β i) i' = if h : i = i' then Eq.recOn h b else 0 := by
  rw [single_eq_pi_single, Pi.single, Function.update]
  simp [@eq_comm _ i i']
#align dfinsupp.single_apply DFinsupp.single_apply

@[simp]
theorem single_zero (i) : (single i 0 : Π₀ i, β i) = 0 :=
  DFunLike.coe_injective <| Pi.single_zero _
#align dfinsupp.single_zero DFinsupp.single_zero

-- @[simp] -- Porting note (#10618): simp can prove this
theorem single_eq_same {i b} : (single i b : Π₀ i, β i) i = b := by
  simp only [single_apply, dite_eq_ite, ite_true]
#align dfinsupp.single_eq_same DFinsupp.single_eq_same

theorem single_eq_of_ne {i i' b} (h : i ≠ i') : (single i b : Π₀ i, β i) i' = 0 := by
  simp only [single_apply, dif_neg h]
#align dfinsupp.single_eq_of_ne DFinsupp.single_eq_of_ne

theorem single_injective {i} : Function.Injective (single i : β i → Π₀ i, β i) := fun _ _ H =>
  Pi.single_injective β i <| DFunLike.coe_injective.eq_iff.mpr H
#align dfinsupp.single_injective DFinsupp.single_injective

/-- Like `Finsupp.single_eq_single_iff`, but with a `HEq` due to dependent types -/
theorem single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) :
    DFinsupp.single i xi = DFinsupp.single j xj ↔ i = j ∧ HEq xi xj ∨ xi = 0 ∧ xj = 0 := by
  constructor
  · intro h
    by_cases hij : i = j
    · subst hij
      exact Or.inl ⟨rfl, heq_of_eq (DFinsupp.single_injective h)⟩
    · have h_coe : ⇑(DFinsupp.single i xi) = DFinsupp.single j xj := congr_arg (⇑) h
      have hci := congr_fun h_coe i
      have hcj := congr_fun h_coe j
      rw [DFinsupp.single_eq_same] at hci hcj
      rw [DFinsupp.single_eq_of_ne (Ne.symm hij)] at hci
      rw [DFinsupp.single_eq_of_ne hij] at hcj
      exact Or.inr ⟨hci, hcj.symm⟩
  · rintro (⟨rfl, hxi⟩ | ⟨hi, hj⟩)
    · rw [eq_of_heq hxi]
    · rw [hi, hj, DFinsupp.single_zero, DFinsupp.single_zero]
#align dfinsupp.single_eq_single_iff DFinsupp.single_eq_single_iff

/-- `DFinsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`DFinsupp.single_injective` -/
theorem single_left_injective {b : ∀ i : ι, β i} (h : ∀ i, b i ≠ 0) :
    Function.Injective (fun i => single i (b i) : ι → Π₀ i, β i) := fun _ _ H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h _ hb.1).left
#align dfinsupp.single_left_injective DFinsupp.single_left_injective

@[simp]
theorem single_eq_zero {i : ι} {xi : β i} : single i xi = 0 ↔ xi = 0 := by
  rw [← single_zero i, single_eq_single_iff]
  simp
#align dfinsupp.single_eq_zero DFinsupp.single_eq_zero

theorem filter_single (p : ι → Prop) [DecidablePred p] (i : ι) (x : β i) :
    (single i x).filter p = if p i then single i x else 0 := by
  ext j
  have := apply_ite (fun x : Π₀ i, β i => x j) (p i) (single i x) 0
  dsimp at this
  rw [filter_apply, this]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · rw [single_eq_of_ne hij, ite_self, Pi.zero_apply, ite_self]
#align dfinsupp.filter_single DFinsupp.filter_single

@[simp]
theorem filter_single_pos {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i) :
    (single i x).filter p = single i x := by rw [filter_single, if_pos h]
#align dfinsupp.filter_single_pos DFinsupp.filter_single_pos

@[simp]
theorem filter_single_neg {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i) :
    (single i x).filter p = 0 := by rw [filter_single, if_neg h]
#align dfinsupp.filter_single_neg DFinsupp.filter_single_neg

/-- Equality of sigma types is sufficient (but not necessary) to show equality of `DFinsupp`s. -/
theorem single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) :
    DFinsupp.single i xi = DFinsupp.single j xj := by
  cases h
  rfl
#align dfinsupp.single_eq_of_sigma_eq DFinsupp.single_eq_of_sigma_eq

@[simp]
theorem equivFunOnFintype_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp.equivFunOnFintype ι β _ _) (DFinsupp.single i m) = Pi.single i m := by
  ext x
  dsimp [Pi.single, Function.update]
  simp [DFinsupp.single_eq_pi_single, @eq_comm _ i]
#align dfinsupp.equiv_fun_on_fintype_single DFinsupp.equivFunOnFintype_single

@[simp]
theorem equivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp.equivFunOnFintype ι β _ _).symm (Pi.single i m) = DFinsupp.single i m := by
  ext i'
  simp only [← single_eq_pi_single, equivFunOnFintype_symm_coe]
#align dfinsupp.equiv_fun_on_fintype_symm_single DFinsupp.equivFunOnFintype_symm_single

section SingleAndZipWith

variable [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]
@[simp]
theorem zipWith_single_single (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0)
    {i} (b₁ : β₁ i) (b₂ : β₂ i) :
    zipWith f hf (single i b₁) (single i b₂) = single i (f i b₁ b₂) := by
  ext j
  rw [zipWith_apply]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rw [single_eq_same, single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hij, single_eq_of_ne hij, single_eq_of_ne hij, hf]

end SingleAndZipWith

/-- Redefine `f i` to be `0`. -/
def erase (i : ι) (x : Π₀ i, β i) : Π₀ i, β i :=
  ⟨fun j ↦ if j = i then 0 else x.1 j,
    x.support'.map fun xs ↦ ⟨xs.1, fun j ↦ (xs.prop j).imp_right (by simp only [·, ite_self])⟩⟩
#align dfinsupp.erase DFinsupp.erase

@[simp]
theorem erase_apply {i j : ι} {f : Π₀ i, β i} : (f.erase i) j = if j = i then 0 else f j :=
  rfl
#align dfinsupp.erase_apply DFinsupp.erase_apply

-- @[simp] -- Porting note (#10618): simp can prove this
theorem erase_same {i : ι} {f : Π₀ i, β i} : (f.erase i) i = 0 := by simp
#align dfinsupp.erase_same DFinsupp.erase_same

theorem erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' ≠ i) : (f.erase i) i' = f i' := by simp [h]
#align dfinsupp.erase_ne DFinsupp.erase_ne

theorem piecewise_single_erase (x : Π₀ i, β i) (i : ι)
    [∀ i' : ι, Decidable <| (i' ∈ ({i} : Set ι))] : -- Porting note: added Decidable hypothesis
    (single i (x i)).piecewise (x.erase i) {i} = x := by
  ext j; rw [piecewise_apply]; split_ifs with h
  · rw [(id h : j = i), single_eq_same]
  · exact erase_ne h
#align dfinsupp.piecewise_single_erase DFinsupp.piecewise_single_erase

theorem erase_eq_sub_single {β : ι → Type*} [∀ i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι) :
    f.erase i = f - single i (f i) := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [erase_ne h.symm, single_eq_of_ne h, @eq_comm _ j, h]
#align dfinsupp.erase_eq_sub_single DFinsupp.erase_eq_sub_single

@[simp]
theorem erase_zero (i : ι) : erase i (0 : Π₀ i, β i) = 0 :=
  ext fun _ => ite_self _
#align dfinsupp.erase_zero DFinsupp.erase_zero

@[simp]
theorem filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) : f.filter (· ≠ i) = f.erase i := by
  ext1 j
  simp only [DFinsupp.filter_apply, DFinsupp.erase_apply, ite_not]
#align dfinsupp.filter_ne_eq_erase DFinsupp.filter_ne_eq_erase

@[simp]
theorem filter_ne_eq_erase' (f : Π₀ i, β i) (i : ι) : f.filter (i ≠ ·) = f.erase i := by
  rw [← filter_ne_eq_erase f i]
  congr with j
  exact ne_comm
#align dfinsupp.filter_ne_eq_erase' DFinsupp.filter_ne_eq_erase'

theorem erase_single (j : ι) (i : ι) (x : β i) :
    (single i x).erase j = if i = j then 0 else single i x := by
  rw [← filter_ne_eq_erase, filter_single, ite_not]
#align dfinsupp.erase_single DFinsupp.erase_single

@[simp]
theorem erase_single_same (i : ι) (x : β i) : (single i x).erase i = 0 := by
  rw [erase_single, if_pos rfl]
#align dfinsupp.erase_single_same DFinsupp.erase_single_same

@[simp]
theorem erase_single_ne {i j : ι} (x : β i) (h : i ≠ j) : (single i x).erase j = single i x := by
  rw [erase_single, if_neg h]
#align dfinsupp.erase_single_ne DFinsupp.erase_single_ne

section Update

variable (f : Π₀ i, β i) (i) (b : β i)

/-- Replace the value of a `Π₀ i, β i` at a given point `i : ι` by a given value `b : β i`.
If `b = 0`, this amounts to removing `i` from the support.
Otherwise, `i` is added to it.

This is the (dependent) finitely-supported version of `Function.update`. -/
def update : Π₀ i, β i :=
  ⟨Function.update f i b,
    f.support'.map fun s =>
      ⟨i ::ₘ s.1, fun j => by
        rcases eq_or_ne i j with (rfl | hi)
        · simp
        · obtain hj | (hj : f j = 0) := s.prop j
          · exact Or.inl (Multiset.mem_cons_of_mem hj)
          · exact Or.inr ((Function.update_noteq hi.symm b _).trans hj)⟩⟩
#align dfinsupp.update DFinsupp.update

variable (j : ι)

@[simp, norm_cast] lemma coe_update : (f.update i b : ∀ i : ι, β i) = Function.update f i b := rfl
#align dfinsupp.coe_update DFinsupp.coe_update

@[simp]
theorem update_self : f.update i (f i) = f := by
  ext
  simp
#align dfinsupp.update_self DFinsupp.update_self

@[simp]
theorem update_eq_erase : f.update i 0 = f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
  · simp [hi.symm]
#align dfinsupp.update_eq_erase DFinsupp.update_eq_erase

theorem update_eq_single_add_erase {β : ι → Type*} [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = single i b + f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [Function.update_noteq h.symm, h, erase_ne, h.symm]
#align dfinsupp.update_eq_single_add_erase DFinsupp.update_eq_single_add_erase

theorem update_eq_erase_add_single {β : ι → Type*} [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = f.erase i + single i b := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [Function.update_noteq h.symm, h, erase_ne, h.symm]
#align dfinsupp.update_eq_erase_add_single DFinsupp.update_eq_erase_add_single

theorem update_eq_sub_add_single {β : ι → Type*} [∀ i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι)
    (b : β i) : f.update i b = f - single i (f i) + single i b := by
  rw [update_eq_erase_add_single f i b, erase_eq_sub_single f i]
#align dfinsupp.update_eq_sub_add_single DFinsupp.update_eq_sub_add_single

end Update

end Basic

section AddMonoid

variable [∀ i, AddZeroClass (β i)]

@[simp]
theorem single_add (i : ι) (b₁ b₂ : β i) : single i (b₁ + b₂) = single i b₁ + single i b₂ :=
  (zipWith_single_single (fun _ => (· + ·)) _ b₁ b₂).symm
#align dfinsupp.single_add DFinsupp.single_add

@[simp]
theorem erase_add (i : ι) (f₁ f₂ : Π₀ i, β i) : erase i (f₁ + f₂) = erase i f₁ + erase i f₂ :=
  ext fun _ => by simp [ite_zero_add]
#align dfinsupp.erase_add DFinsupp.erase_add

variable (β)

/-- `DFinsupp.single` as an `AddMonoidHom`. -/
@[simps]
def singleAddHom (i : ι) : β i →+ Π₀ i, β i where
  toFun := single i
  map_zero' := single_zero i
  map_add' := single_add i
#align dfinsupp.single_add_hom DFinsupp.singleAddHom
#align dfinsupp.single_add_hom_apply DFinsupp.singleAddHom_apply

/-- `DFinsupp.erase` as an `AddMonoidHom`. -/
@[simps]
def eraseAddHom (i : ι) : (Π₀ i, β i) →+ Π₀ i, β i where
  toFun := erase i
  map_zero' := erase_zero i
  map_add' := erase_add i
#align dfinsupp.erase_add_hom DFinsupp.eraseAddHom
#align dfinsupp.erase_add_hom_apply DFinsupp.eraseAddHom_apply

variable {β}

@[simp]
theorem single_neg {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (x : β i) :
    single i (-x) = -single i x :=
  (singleAddHom β i).map_neg x
#align dfinsupp.single_neg DFinsupp.single_neg

@[simp]
theorem single_sub {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (x y : β i) :
    single i (x - y) = single i x - single i y :=
  (singleAddHom β i).map_sub x y
#align dfinsupp.single_sub DFinsupp.single_sub

@[simp]
theorem erase_neg {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (f : Π₀ i, β i) :
    (-f).erase i = -f.erase i :=
  (eraseAddHom β i).map_neg f
#align dfinsupp.erase_neg DFinsupp.erase_neg

@[simp]
theorem erase_sub {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (f g : Π₀ i, β i) :
    (f - g).erase i = f.erase i - g.erase i :=
  (eraseAddHom β i).map_sub f g
#align dfinsupp.erase_sub DFinsupp.erase_sub

theorem single_add_erase (i : ι) (f : Π₀ i, β i) : single i (f i) + f.erase i = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, add_zero, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), zero_add]
#align dfinsupp.single_add_erase DFinsupp.single_add_erase

theorem erase_add_single (i : ι) (f : Π₀ i, β i) : f.erase i + single i (f i) = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, zero_add, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), add_zero]
#align dfinsupp.erase_add_single DFinsupp.erase_add_single

protected theorem induction {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (single i b + f)) : p f := by
  cases' f with f s
  induction' s using Trunc.induction_on with s
  cases' s with s H
  induction' s using Multiset.induction_on with i s ih generalizing f
  · have : f = 0 := funext fun i => (H i).resolve_left (Multiset.not_mem_zero _)
    subst this
    exact h0
  have H2 : p (erase i ⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩) := by
    dsimp only [erase, Trunc.map, Trunc.bind, Trunc.liftOn, Trunc.lift_mk,
      Function.comp, Subtype.coe_mk]
    have H2 : ∀ j, j ∈ s ∨ ite (j = i) 0 (f j) = 0 := by
      intro j
      cases' H j with H2 H2
      · cases' Multiset.mem_cons.1 H2 with H3 H3
        · right; exact if_pos H3
        · left; exact H3
      right
      split_ifs <;> [rfl; exact H2]
    have H3 : ∀ aux, (⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨i ::ₘ s, aux⟩⟩ : Π₀ i, β i) =
        ⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨s, H2⟩⟩ :=
      fun _ ↦ ext fun _ => rfl
    rw [H3]
    apply ih
  have H3 : single i _ + _ = (⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩ : Π₀ i, β i) := single_add_erase _ _
  rw [← H3]
  change p (single i (f i) + _)
  cases' Classical.em (f i = 0) with h h
  · rw [h, single_zero, zero_add]
    exact H2
  refine ha _ _ _ ?_ h H2
  rw [erase_same]
#align dfinsupp.induction DFinsupp.induction

theorem induction₂ {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (f + single i b)) : p f :=
  DFinsupp.induction f h0 fun i b f h1 h2 h3 =>
    have h4 : f + single i b = single i b + f := by
      ext j; by_cases H : i = j
      · subst H
        simp [h1]
      · simp [H]
    Eq.recOn h4 <| ha i b f h1 h2 h3
#align dfinsupp.induction₂ DFinsupp.induction₂

@[simp]
theorem add_closure_iUnion_range_single :
    AddSubmonoid.closure (⋃ i : ι, Set.range (single i : β i → Π₀ i, β i)) = ⊤ :=
  top_unique fun x _ => by
    apply DFinsupp.induction x
    · exact AddSubmonoid.zero_mem _
    exact fun a b f _ _ hf =>
      AddSubmonoid.add_mem _
        (AddSubmonoid.subset_closure <| Set.mem_iUnion.2 ⟨a, Set.mem_range_self _⟩) hf
#align dfinsupp.add_closure_Union_range_single DFinsupp.add_closure_iUnion_range_single

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal. -/
theorem addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (single i y) = g (single i y)) : f = g := by
  refine AddMonoidHom.eq_of_eqOn_denseM add_closure_iUnion_range_single fun f hf => ?_
  simp only [Set.mem_iUnion, Set.mem_range] at hf
  rcases hf with ⟨x, y, rfl⟩
  apply H
#align dfinsupp.add_hom_ext DFinsupp.addHom_ext

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem addHom_ext' {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ x, f.comp (singleAddHom β x) = g.comp (singleAddHom β x)) : f = g :=
  addHom_ext fun x => DFunLike.congr_fun (H x)
#align dfinsupp.add_hom_ext' DFinsupp.addHom_ext'

end AddMonoid

@[simp]
theorem mk_add [∀ i, AddZeroClass (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i} :
    mk s (x + y) = mk s x + mk s y :=
  ext fun i => by simp only [add_apply, mk_apply]; split_ifs <;> [rfl; rw [zero_add]]
#align dfinsupp.mk_add DFinsupp.mk_add

@[simp]
theorem mk_zero [∀ i, Zero (β i)] {s : Finset ι} : mk s (0 : ∀ i : (↑s : Set ι), β i.1) = 0 :=
  ext fun i => by simp only [mk_apply]; split_ifs <;> rfl
#align dfinsupp.mk_zero DFinsupp.mk_zero

@[simp]
theorem mk_neg [∀ i, AddGroup (β i)] {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} :
    mk s (-x) = -mk s x :=
  ext fun i => by simp only [neg_apply, mk_apply]; split_ifs <;> [rfl; rw [neg_zero]]
#align dfinsupp.mk_neg DFinsupp.mk_neg

@[simp]
theorem mk_sub [∀ i, AddGroup (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i.1} :
    mk s (x - y) = mk s x - mk s y :=
  ext fun i => by simp only [sub_apply, mk_apply]; split_ifs <;> [rfl; rw [sub_zero]]
#align dfinsupp.mk_sub DFinsupp.mk_sub

/-- If `s` is a subset of `ι` then `mk_addGroupHom s` is the canonical additive
group homomorphism from $\prod_{i\in s}\beta_i$ to $\prod_{\mathtt{i : \iota}}\beta_i.$-/
def mkAddGroupHom [∀ i, AddGroup (β i)] (s : Finset ι) :
    (∀ i : (s : Set ι), β ↑i) →+ Π₀ i : ι, β i where
  toFun := mk s
  map_zero' := mk_zero
  map_add' _ _ := mk_add
#align dfinsupp.mk_add_group_hom DFinsupp.mkAddGroupHom

section

variable [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]

@[simp]
theorem mk_smul {s : Finset ι} (c : γ) (x : ∀ i : (↑s : Set ι), β (i : ι)) :
    mk s (c • x) = c • mk s x :=
  ext fun i => by simp only [smul_apply, mk_apply]; split_ifs <;> [rfl; rw [smul_zero]]
#align dfinsupp.mk_smul DFinsupp.mk_smul

@[simp]
theorem single_smul {i : ι} (c : γ) (x : β i) : single i (c • x) = c • single i x :=
  ext fun i => by
    simp only [smul_apply, single_apply]
    split_ifs with h
    · cases h; rfl
    · rw [smul_zero]
#align dfinsupp.single_smul DFinsupp.single_smul

end

section SupportBasic

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

/-- Set `{i | f x ≠ 0}` as a `Finset`. -/
def support (f : Π₀ i, β i) : Finset ι :=
  (f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun i => f i ≠ 0) <| by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hx i).resolve_right h, h⟩
#align dfinsupp.support DFinsupp.support

@[simp]
theorem support_mk_subset {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} : (mk s x).support ⊆ s :=
  fun _ H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1
#align dfinsupp.support_mk_subset DFinsupp.support_mk_subset

@[simp]
theorem support_mk'_subset {f : ∀ i, β i} {s : Multiset ι} {h} :
    (mk' f <| Trunc.mk ⟨s, h⟩).support ⊆ s.toFinset := fun i H =>
  Multiset.mem_toFinset.1 <| by simpa using (Finset.mem_filter.1 H).1
#align dfinsupp.support_mk'_subset DFinsupp.support_mk'_subset

@[simp]
theorem mem_support_toFun (f : Π₀ i, β i) (i) : i ∈ f.support ↔ f i ≠ 0 := by
  cases' f with f s
  induction' s using Trunc.induction_on with s
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter, Multiset.mem_toFinset, coe_mk']
  exact and_iff_right_of_imp (s.prop i).resolve_right
#align dfinsupp.mem_support_to_fun DFinsupp.mem_support_toFun

theorem eq_mk_support (f : Π₀ i, β i) : f = mk f.support fun i => f i := by aesop
#align dfinsupp.eq_mk_support DFinsupp.eq_mk_support

/-- Equivalence between dependent functions with finite support `s : Finset ι` and functions
`∀ i, {x : β i // x ≠ 0}`. -/
@[simps]
def subtypeSupportEqEquiv (s : Finset ι) :
    {f : Π₀ i, β i // f.support = s} ≃ ∀ i : s, {x : β i // x ≠ 0} where
  toFun | ⟨f, hf⟩ => fun ⟨i, hi⟩ ↦ ⟨f i, (f.mem_support_toFun i).1 <| hf.symm ▸ hi⟩
  invFun f := ⟨mk s fun i ↦ (f i).1, Finset.ext fun i ↦ by
    -- TODO: `simp` fails to use `(f _).2` inside `∃ _, _`
    calc
      i ∈ support (mk s fun i ↦ (f i).1) ↔ ∃ h : i ∈ s, (f ⟨i, h⟩).1 ≠ 0 := by simp
      _ ↔ ∃ _ : i ∈ s, True := exists_congr fun h ↦ (iff_true _).mpr (f _).2
      _ ↔ i ∈ s := by simp⟩
  left_inv := by
    rintro ⟨f, rfl⟩
    ext i
    simpa using Eq.symm
  right_inv f := by
    ext1
    simp [Subtype.eta]; rfl

/-- Equivalence between all dependent finitely supported functions `f : Π₀ i, β i` and type
of pairs `⟨s : Finset ι, f : ∀ i : s, {x : β i // x ≠ 0}⟩`. -/
@[simps! apply_fst apply_snd_coe]
def sigmaFinsetFunEquiv : (Π₀ i, β i) ≃ Σ s : Finset ι, ∀ i : s, {x : β i // x ≠ 0} :=
  (Equiv.sigmaFiberEquiv DFinsupp.support).symm.trans (.sigmaCongrRight subtypeSupportEqEquiv)

@[simp]
theorem support_zero : (0 : Π₀ i, β i).support = ∅ :=
  rfl
#align dfinsupp.support_zero DFinsupp.support_zero

theorem mem_support_iff {f : Π₀ i, β i} {i : ι} : i ∈ f.support ↔ f i ≠ 0 :=
  f.mem_support_toFun _
#align dfinsupp.mem_support_iff DFinsupp.mem_support_iff

theorem not_mem_support_iff {f : Π₀ i, β i} {i : ι} : i ∉ f.support ↔ f i = 0 :=
  not_iff_comm.1 mem_support_iff.symm
#align dfinsupp.not_mem_support_iff DFinsupp.not_mem_support_iff

@[simp]
theorem support_eq_empty {f : Π₀ i, β i} : f.support = ∅ ↔ f = 0 :=
  ⟨fun H => ext <| by simpa [Finset.ext_iff] using H, by simp (config := { contextual := true })⟩
#align dfinsupp.support_eq_empty DFinsupp.support_eq_empty

instance decidableZero : DecidablePred (Eq (0 : Π₀ i, β i)) := fun _ =>
  decidable_of_iff _ <| support_eq_empty.trans eq_comm
#align dfinsupp.decidable_zero DFinsupp.decidableZero

theorem support_subset_iff {s : Set ι} {f : Π₀ i, β i} : ↑f.support ⊆ s ↔ ∀ i ∉ s, f i = 0 := by
  simp [Set.subset_def]; exact forall_congr' fun i => not_imp_comm
#align dfinsupp.support_subset_iff DFinsupp.support_subset_iff

theorem support_single_ne_zero {i : ι} {b : β i} (hb : b ≠ 0) : (single i b).support = {i} := by
  ext j; by_cases h : i = j
  · subst h
    simp [hb]
  simp [Ne.symm h, h]
#align dfinsupp.support_single_ne_zero DFinsupp.support_single_ne_zero

theorem support_single_subset {i : ι} {b : β i} : (single i b).support ⊆ {i} :=
  support_mk'_subset
#align dfinsupp.support_single_subset DFinsupp.support_single_subset

section MapRangeAndZipWith

variable [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

theorem mapRange_def [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] {f : ∀ i, β₁ i → β₂ i}
    {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    mapRange f hf g = mk g.support fun i => f i.1 (g i.1) := by
  ext i
  by_cases h : g i ≠ 0 <;> simp at h <;> simp [h, hf]
#align dfinsupp.map_range_def DFinsupp.mapRange_def

@[simp]
theorem mapRange_single {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {i : ι} {b : β₁ i} :
    mapRange f hf (single i b) = single i (f i b) :=
  DFinsupp.ext fun i' => by
    by_cases h : i = i'
    · subst i'
      simp
    · simp [h, hf]
#align dfinsupp.map_range_single DFinsupp.mapRange_single

variable [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]

theorem support_mapRange {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    (mapRange f hf g).support ⊆ g.support := by simp [mapRange_def]
#align dfinsupp.support_map_range DFinsupp.support_mapRange

theorem zipWith_def {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
    [dec : DecidableEq ι] [∀ i : ι, Zero (β i)] [∀ i : ι, Zero (β₁ i)] [∀ i : ι, Zero (β₂ i)]
    [∀ (i : ι) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i : ι) (x : β₂ i), Decidable (x ≠ 0)]
    {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
    zipWith f hf g₁ g₂ = mk (g₁.support ∪ g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1) := by
  ext i
  by_cases h1 : g₁ i ≠ 0 <;> by_cases h2 : g₂ i ≠ 0 <;> simp only [not_not, Ne] at h1 h2 <;>
    simp [h1, h2, hf]
#align dfinsupp.zip_with_def DFinsupp.zipWith_def

theorem support_zipWith {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i}
    {g₂ : Π₀ i, β₂ i} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  simp [zipWith_def]
#align dfinsupp.support_zip_with DFinsupp.support_zipWith

end MapRangeAndZipWith

theorem erase_def (i : ι) (f : Π₀ i, β i) : f.erase i = mk (f.support.erase i) fun j => f j.1 := by
  ext j
  by_cases h1 : j = i <;> by_cases h2 : f j ≠ 0 <;> simp at h2 <;> simp [h1, h2]
#align dfinsupp.erase_def DFinsupp.erase_def

@[simp]
theorem support_erase (i : ι) (f : Π₀ i, β i) : (f.erase i).support = f.support.erase i := by
  ext j
  by_cases h1 : j = i
  · simp only [h1, mem_support_toFun, erase_apply, ite_true, ne_eq, not_true, not_not,
      Finset.mem_erase, false_and]
  by_cases h2 : f j ≠ 0 <;> simp at h2 <;> simp [h1, h2]
#align dfinsupp.support_erase DFinsupp.support_erase

theorem support_update_ne_zero (f : Π₀ i, β i) (i : ι) {b : β i} (h : b ≠ 0) :
    support (f.update i b) = insert i f.support := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [h]
  · simp [hi.symm]
#align dfinsupp.support_update_ne_zero DFinsupp.support_update_ne_zero

theorem support_update (f : Π₀ i, β i) (i : ι) (b : β i) [Decidable (b = 0)] :
    support (f.update i b) = if b = 0 then support (f.erase i) else insert i f.support := by
  ext j
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne_zero f _ hb]
#align dfinsupp.support_update DFinsupp.support_update

section FilterAndSubtypeDomain

variable {p : ι → Prop} [DecidablePred p]

theorem filter_def (f : Π₀ i, β i) : f.filter p = mk (f.support.filter p) fun i => f i.1 := by
  ext i; by_cases h1 : p i <;> by_cases h2 : f i ≠ 0 <;> simp at h2 <;> simp [h1, h2]
#align dfinsupp.filter_def DFinsupp.filter_def

@[simp]
theorem support_filter (f : Π₀ i, β i) : (f.filter p).support = f.support.filter p := by
  ext i; by_cases h : p i <;> simp [h]
#align dfinsupp.support_filter DFinsupp.support_filter

theorem subtypeDomain_def (f : Π₀ i, β i) :
    f.subtypeDomain p = mk (f.support.subtype p) fun i => f i := by
  ext i; by_cases h2 : f i ≠ 0 <;> try simp at h2; dsimp; simp [h2]
#align dfinsupp.subtype_domain_def DFinsupp.subtypeDomain_def

@[simp, nolint simpNF] -- Porting note: simpNF claims that LHS does not simplify, but it does
theorem support_subtypeDomain {f : Π₀ i, β i} :
    (subtypeDomain p f).support = f.support.subtype p := by
  ext i
  simp
#align dfinsupp.support_subtype_domain DFinsupp.support_subtypeDomain

end FilterAndSubtypeDomain

end SupportBasic

theorem support_add [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    {g₁ g₂ : Π₀ i, β i} : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
  support_zipWith
#align dfinsupp.support_add DFinsupp.support_add

@[simp]
theorem support_neg [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    support (-f) = support f := by ext i; simp
#align dfinsupp.support_neg DFinsupp.support_neg

theorem support_smul {γ : Type w} [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (b : γ) (v : Π₀ i, β i) :
    (b • v).support ⊆ v.support :=
  support_mapRange
#align dfinsupp.support_smul DFinsupp.support_smul

instance [∀ i, Zero (β i)] [∀ i, DecidableEq (β i)] : DecidableEq (Π₀ i, β i) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ i ∈ f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ => ext fun i => if h : i ∈ f.support then h₂ i h else by
      have hf : f i = 0 := by rwa [mem_support_iff, not_not] at h
      have hg : g i = 0 := by rwa [h₁, mem_support_iff, not_not] at h
      rw [hf, hg],
     by rintro rfl; simp⟩

section Equiv

open Finset

variable {κ : Type*}

/-- Reindexing (and possibly removing) terms of a dfinsupp. -/
noncomputable def comapDomain [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨((Multiset.toFinset s.1).preimage h hh.injOn).val, fun x =>
        (s.prop (h x)).imp_left fun hx => mem_preimage.mpr <| Multiset.mem_toFinset.mpr hx⟩
#align dfinsupp.comap_domain DFinsupp.comapDomain

@[simp]
theorem comapDomain_apply [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) (f : Π₀ i, β i)
    (k : κ) : comapDomain h hh f k = f (h k) :=
  rfl
#align dfinsupp.comap_domain_apply DFinsupp.comapDomain_apply

@[simp]
theorem comapDomain_zero [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) :
    comapDomain h hh (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply, comapDomain_apply, zero_apply]
#align dfinsupp.comap_domain_zero DFinsupp.comapDomain_zero

@[simp]
theorem comapDomain_add [∀ i, AddZeroClass (β i)] (h : κ → ι) (hh : Function.Injective h)
    (f g : Π₀ i, β i) : comapDomain h hh (f + g) = comapDomain h hh f + comapDomain h hh g := by
  ext
  rw [add_apply, comapDomain_apply, comapDomain_apply, comapDomain_apply, add_apply]
#align dfinsupp.comap_domain_add DFinsupp.comapDomain_add

@[simp]
theorem comapDomain_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    (h : κ → ι) (hh : Function.Injective h) (r : γ) (f : Π₀ i, β i) :
    comapDomain h hh (r • f) = r • comapDomain h hh f := by
  ext
  rw [smul_apply, comapDomain_apply, smul_apply, comapDomain_apply]
#align dfinsupp.comap_domain_smul DFinsupp.comapDomain_smul

@[simp]
theorem comapDomain_single [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h)
    (k : κ) (x : β (h k)) : comapDomain h hh (single (h k) x) = single k x := by
  ext i
  rw [comapDomain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh.ne hik.symm)]
#align dfinsupp.comap_domain_single DFinsupp.comapDomain_single

/-- A computable version of comap_domain when an explicit left inverse is provided. -/
def comapDomain' [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.map h' s.1, fun x =>
        (s.prop (h x)).imp_left fun hx => Multiset.mem_map.mpr ⟨_, hx, hh' _⟩⟩
#align dfinsupp.comap_domain' DFinsupp.comapDomain'

@[simp]
theorem comapDomain'_apply [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (f : Π₀ i, β i) (k : κ) : comapDomain' h hh' f k = f (h k) :=
  rfl
#align dfinsupp.comap_domain'_apply DFinsupp.comapDomain'_apply

@[simp]
theorem comapDomain'_zero [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) : comapDomain' h hh' (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply, comapDomain'_apply, zero_apply]
#align dfinsupp.comap_domain'_zero DFinsupp.comapDomain'_zero

@[simp]
theorem comapDomain'_add [∀ i, AddZeroClass (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (f g : Π₀ i, β i) :
    comapDomain' h hh' (f + g) = comapDomain' h hh' f + comapDomain' h hh' g := by
  ext
  rw [add_apply, comapDomain'_apply, comapDomain'_apply, comapDomain'_apply, add_apply]
#align dfinsupp.comap_domain'_add DFinsupp.comapDomain'_add

@[simp]
theorem comapDomain'_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h) (r : γ) (f : Π₀ i, β i) :
    comapDomain' h hh' (r • f) = r • comapDomain' h hh' f := by
  ext
  rw [smul_apply, comapDomain'_apply, smul_apply, comapDomain'_apply]
#align dfinsupp.comap_domain'_smul DFinsupp.comapDomain'_smul

@[simp]
theorem comapDomain'_single [DecidableEq ι] [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι)
    {h' : ι → κ} (hh' : Function.LeftInverse h' h) (k : κ) (x : β (h k)) :
    comapDomain' h hh' (single (h k) x) = single k x := by
  ext i
  rw [comapDomain'_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh'.injective.ne hik.symm)]
#align dfinsupp.comap_domain'_single DFinsupp.comapDomain'_single

/-- Reindexing terms of a dfinsupp.

This is the dfinsupp version of `Equiv.piCongrLeft'`. -/
@[simps apply]
def equivCongrLeft [∀ i, Zero (β i)] (h : ι ≃ κ) : (Π₀ i, β i) ≃ Π₀ k, β (h.symm k) where
  toFun := comapDomain' h.symm h.right_inv
  invFun f :=
    mapRange (fun i => Equiv.cast <| congr_arg β <| h.symm_apply_apply i)
      (fun i => (Equiv.cast_eq_iff_heq _).mpr <| by rw [Equiv.symm_apply_apply])
      (@comapDomain' _ _ _ _ h _ h.left_inv f)
  left_inv f := by
    ext i
    rw [mapRange_apply, comapDomain'_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.symm_apply_apply]
  right_inv f := by
    ext k
    rw [comapDomain'_apply, mapRange_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.apply_symm_apply]
#align dfinsupp.equiv_congr_left DFinsupp.equivCongrLeft
#align dfinsupp.equiv_congr_left_apply DFinsupp.equivCongrLeft_apply

section SigmaCurry

variable {α : ι → Type*} {δ : ∀ i, α i → Type v}

-- lean can't find these instances -- Porting note: but Lean 4 can!!!
instance hasAdd₂ [∀ i j, AddZeroClass (δ i j)] : Add (Π₀ (i : ι) (j : α i), δ i j) :=
  inferInstance
  -- @DFinsupp.hasAdd ι (fun i => Π₀ j, δ i j) _
#align dfinsupp.has_add₂ DFinsupp.hasAdd₂

instance addZeroClass₂ [∀ i j, AddZeroClass (δ i j)] : AddZeroClass (Π₀ (i : ι) (j : α i), δ i j) :=
  inferInstance
  -- @DFinsupp.addZeroClass ι (fun i => Π₀ j, δ i j) _
#align dfinsupp.add_zero_class₂ DFinsupp.addZeroClass₂

instance addMonoid₂ [∀ i j, AddMonoid (δ i j)] : AddMonoid (Π₀ (i : ι) (j : α i), δ i j) :=
  inferInstance
  -- @DFinsupp.addMonoid ι (fun i => Π₀ j, δ i j) _
#align dfinsupp.add_monoid₂ DFinsupp.addMonoid₂

instance distribMulAction₂ [Monoid γ] [∀ i j, AddMonoid (δ i j)]
    [∀ i j, DistribMulAction γ (δ i j)] : DistribMulAction γ (Π₀ (i : ι) (j : α i), δ i j) :=
  @DFinsupp.distribMulAction ι _ (fun i => Π₀ j, δ i j) _ _ _
#align dfinsupp.distrib_mul_action₂ DFinsupp.distribMulAction₂

/-- The natural map between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`.  -/
def sigmaCurry [∀ i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    Π₀ (i) (j), δ i j where
  toFun := fun i ↦
  { toFun := fun j ↦ f ⟨i, j⟩,
    support' := f.support'.map (fun ⟨m, hm⟩ ↦
      ⟨m.filterMap (fun ⟨i', j'⟩ ↦ if h : i' = i then some <| h.rec j' else none),
        fun j ↦ (hm ⟨i, j⟩).imp_left (fun h ↦ (m.mem_filterMap _).mpr ⟨⟨i, j⟩, h, dif_pos rfl⟩)⟩) }
  support' := f.support'.map (fun ⟨m, hm⟩ ↦
    ⟨m.map Sigma.fst, fun i ↦ Decidable.or_iff_not_imp_left.mpr (fun h ↦ DFinsupp.ext
      (fun j ↦ (hm ⟨i, j⟩).resolve_left (fun H ↦ (Multiset.mem_map.not.mp h) ⟨⟨i, j⟩, H, rfl⟩)))⟩)

@[simp]
theorem sigmaCurry_apply [∀ i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  rfl
#align dfinsupp.sigma_curry_apply DFinsupp.sigmaCurry_apply

@[simp]
theorem sigmaCurry_zero [∀ i j, Zero (δ i j)] :
    sigmaCurry (0 : Π₀ (i : Σ _, _), δ i.1 i.2) = 0 :=
  rfl
#align dfinsupp.sigma_curry_zero DFinsupp.sigmaCurry_zero

@[simp]
theorem sigmaCurry_add [∀ i j, AddZeroClass (δ i j)] (f g : Π₀ (i : Σ _, _), δ i.1 i.2) :
    sigmaCurry (f + g) = sigmaCurry f + sigmaCurry g := by
  ext (i j)
  rfl
#align dfinsupp.sigma_curry_add DFinsupp.sigmaCurry_add

@[simp]
theorem sigmaCurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)] [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    sigmaCurry (r • f) = r • sigmaCurry f := by
  ext (i j)
  rfl
#align dfinsupp.sigma_curry_smul DFinsupp.sigmaCurry_smul

@[simp]
theorem sigmaCurry_single [∀ i, DecidableEq (α i)] [∀ i j, Zero (δ i j)]
    (ij : Σ i, α i) (x : δ ij.1 ij.2) :
    sigmaCurry (single ij x) = single ij.1 (single ij.2 x : Π₀ j, δ ij.1 j) := by
  obtain ⟨i, j⟩ := ij
  ext i' j'
  dsimp only
  rw [sigmaCurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j j'
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne, single_eq_of_ne hj]
      simpa using hj
  · rw [single_eq_of_ne, single_eq_of_ne hi, zero_apply]
    simp [hi]
#align dfinsupp.sigma_curry_single DFinsupp.sigmaCurry_single

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The natural map between `Π₀ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`. -/
def sigmaUncurry [∀ i j, Zero (δ i j)]
    [∀ i, DecidableEq (α i)] [∀ i j (x : δ i j), Decidable (x ≠ 0)]
    (f : Π₀ (i) (j), δ i j) :
    Π₀ i : Σi, _, δ i.1 i.2 where
  toFun i := f i.1 i.2
  support' := f.support'.map fun s => ⟨Multiset.bind s.1 fun i =>
    ((f i).support.map ⟨Sigma.mk i, sigma_mk_injective⟩).val, fun i => by
      simp_rw [Multiset.mem_bind, map_val, Multiset.mem_map, Function.Embedding.coeFn_mk, ←
        Finset.mem_def, mem_support_toFun]
      obtain hi | (hi : f i.1 = 0) := s.prop i.1
      · by_cases hi' : f i.1 i.2 = 0
        · exact Or.inr hi'
        · exact Or.inl ⟨_, hi, i.2, hi', Sigma.eta _⟩
      · right
        rw [hi, zero_apply]⟩
#align dfinsupp.sigma_uncurry DFinsupp.sigmaUncurry

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_apply [∀ i j, Zero (δ i j)]
    [∀ i, DecidableEq (α i)] [∀ i j (x : δ i j), Decidable (x ≠ 0)]
    (f : Π₀ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j :=
  rfl
#align dfinsupp.sigma_uncurry_apply DFinsupp.sigmaUncurry_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_zero [∀ i j, Zero (δ i j)]
    [∀ i, DecidableEq (α i)] [∀ i j (x : δ i j), Decidable (x ≠ 0)] :
    sigmaUncurry (0 : Π₀ (i) (j), δ i j) = 0 :=
  rfl
#align dfinsupp.sigma_uncurry_zero DFinsupp.sigmaUncurry_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_add [∀ i j, AddZeroClass (δ i j)]
    [∀ i, DecidableEq (α i)] [∀ i j (x : δ i j), Decidable (x ≠ 0)]
    (f g : Π₀ (i) (j), δ i j) :
    sigmaUncurry (f + g) = sigmaUncurry f + sigmaUncurry g :=
  DFunLike.coe_injective rfl
#align dfinsupp.sigma_uncurry_add DFinsupp.sigmaUncurry_add

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)]
    [∀ i, DecidableEq (α i)] [∀ i j (x : δ i j), Decidable (x ≠ 0)]
    [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i) (j), δ i j) : sigmaUncurry (r • f) = r • sigmaUncurry f :=
  DFunLike.coe_injective rfl
#align dfinsupp.sigma_uncurry_smul DFinsupp.sigmaUncurry_smul

@[simp]
theorem sigmaUncurry_single [∀ i j, Zero (δ i j)]
    [∀ i, DecidableEq (α i)] [∀ i j (x : δ i j), Decidable (x ≠ 0)]
    (i) (j : α i) (x : δ i j) :
    sigmaUncurry (single i (single j x : Π₀ j : α i, δ i j)) = single ⟨i, j⟩ (by exact x) := by
  ext ⟨i', j'⟩
  dsimp only
  rw [sigmaUncurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j j'
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hj, single_eq_of_ne]
      simpa using hj
  · rw [single_eq_of_ne hi, single_eq_of_ne, zero_apply]
    simp [hi]
#align dfinsupp.sigma_uncurry_single DFinsupp.sigmaUncurry_single

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The natural bijection between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`.

This is the dfinsupp version of `Equiv.piCurry`. -/
def sigmaCurryEquiv [∀ i j, Zero (δ i j)]
    [∀ i, DecidableEq (α i)] [∀ i j (x : δ i j), Decidable (x ≠ 0)] :
    (Π₀ i : Σi, _, δ i.1 i.2) ≃ Π₀ (i) (j), δ i j where
  toFun := sigmaCurry
  invFun := sigmaUncurry
  left_inv f := by
    ext ⟨i, j⟩
    rw [sigmaUncurry_apply, sigmaCurry_apply]
  right_inv f := by
    ext i j
    rw [sigmaCurry_apply, sigmaUncurry_apply]
#align dfinsupp.sigma_curry_equiv DFinsupp.sigmaCurryEquiv

end SigmaCurry

variable {α : Option ι → Type v}

/-- Adds a term to a dfinsupp, making a dfinsupp indexed by an `Option`.

This is the dfinsupp version of `Option.rec`. -/
def extendWith [∀ i, Zero (α i)] (a : α none) (f : Π₀ i, α (some i)) : Π₀ i, α i where
  toFun := fun i ↦ match i with | none => a | some _ => f _
  support' :=
    f.support'.map fun s =>
      ⟨none ::ₘ Multiset.map some s.1, fun i =>
        Option.rec (Or.inl <| Multiset.mem_cons_self _ _)
          (fun i =>
            (s.prop i).imp_left fun h => Multiset.mem_cons_of_mem <| Multiset.mem_map_of_mem _ h)
          i⟩
#align dfinsupp.extend_with DFinsupp.extendWith

@[simp]
theorem extendWith_none [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) :
    f.extendWith a none = a :=
  rfl
#align dfinsupp.extend_with_none DFinsupp.extendWith_none

@[simp]
theorem extendWith_some [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) (i : ι) :
    f.extendWith a (some i) = f i :=
  rfl
#align dfinsupp.extend_with_some DFinsupp.extendWith_some

@[simp]
theorem extendWith_single_zero [DecidableEq ι] [∀ i, Zero (α i)] (i : ι) (x : α (some i)) :
    (single i x).extendWith 0 = single (some i) x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_of_ne (Option.some_ne_none _)]
  · rw [extendWith_some]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).ne hij)]
#align dfinsupp.extend_with_single_zero DFinsupp.extendWith_single_zero

@[simp]
theorem extendWith_zero [DecidableEq ι] [∀ i, Zero (α i)] (x : α none) :
    (0 : Π₀ i, α (some i)).extendWith x = single none x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_same]
  · rw [extendWith_some, single_eq_of_ne (Option.some_ne_none _).symm, zero_apply]
#align dfinsupp.extend_with_zero DFinsupp.extendWith_zero

/-- Bijection obtained by separating the term of index `none` of a dfinsupp over `Option ι`.

This is the dfinsupp version of `Equiv.piOptionEquivProd`. -/
@[simps]
noncomputable def equivProdDFinsupp [∀ i, Zero (α i)] :
    (Π₀ i, α i) ≃ α none × Π₀ i, α (some i) where
  toFun f := (f none, comapDomain some (Option.some_injective _) f)
  invFun f := f.2.extendWith f.1
  left_inv f := by
    ext i; cases' i with i
    · rw [extendWith_none]
    · rw [extendWith_some, comapDomain_apply]
  right_inv x := by
    dsimp only
    ext
    · exact extendWith_none x.snd _
    · rw [comapDomain_apply, extendWith_some]
#align dfinsupp.equiv_prod_dfinsupp DFinsupp.equivProdDFinsupp
#align dfinsupp.equiv_prod_dfinsupp_apply DFinsupp.equivProdDFinsupp_apply
#align dfinsupp.equiv_prod_dfinsupp_symm_apply DFinsupp.equivProdDFinsupp_symm_apply

theorem equivProdDFinsupp_add [∀ i, AddZeroClass (α i)] (f g : Π₀ i, α i) :
    equivProdDFinsupp (f + g) = equivProdDFinsupp f + equivProdDFinsupp g :=
  Prod.ext (add_apply _ _ _) (comapDomain_add _ (Option.some_injective _) _ _)
#align dfinsupp.equiv_prod_dfinsupp_add DFinsupp.equivProdDFinsupp_add

theorem equivProdDFinsupp_smul [Monoid γ] [∀ i, AddMonoid (α i)] [∀ i, DistribMulAction γ (α i)]
    (r : γ) (f : Π₀ i, α i) : equivProdDFinsupp (r • f) = r • equivProdDFinsupp f :=
  Prod.ext (smul_apply _ _ _) (comapDomain_smul _ (Option.some_injective _) _ _)
#align dfinsupp.equiv_prod_dfinsupp_smul DFinsupp.equivProdDFinsupp_smul

end Equiv

section ProdAndSum

/-- `DFinsupp.prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g i (f i)` over the support of `f`."]
def prod [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] (f : Π₀ i, β i)
    (g : ∀ i, β i → γ) : γ :=
  ∏ i ∈ f.support, g i (f i)
#align dfinsupp.prod DFinsupp.prod
#align dfinsupp.sum DFinsupp.sum

@[to_additive (attr := simp)]
theorem _root_.map_dfinsupp_prod
    {R S H : Type*} [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid R] [CommMonoid S] [FunLike H R S] [MonoidHomClass H R S] (h : H) (f : Π₀ i, β i)
    (g : ∀ i, β i → R) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod _ _ _

@[to_additive]
theorem prod_mapRange_index {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [∀ i, Zero (β₁ i)]
    [∀ i, Zero (β₂ i)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]
    [CommMonoid γ] {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : ∀ i, β₂ i → γ}
    (h0 : ∀ i, h i 0 = 1) : (mapRange f hf g).prod h = g.prod fun i b => h i (f i b) := by
  rw [mapRange_def]
  refine (Finset.prod_subset support_mk_subset ?_).trans ?_
  · intro i h1 h2
    simp only [mem_support_toFun, ne_eq] at h1
    simp only [Finset.coe_sort_coe, mem_support_toFun, mk_apply, ne_eq, h1, not_false_iff,
      dite_eq_ite, ite_true, not_not] at h2
    simp [h2, h0]
  · refine Finset.prod_congr rfl ?_
    intro i h1
    simp only [mem_support_toFun, ne_eq] at h1
    simp [h1]
#align dfinsupp.prod_map_range_index DFinsupp.prod_mapRange_index
#align dfinsupp.sum_map_range_index DFinsupp.sum_mapRange_index

@[to_additive]
theorem prod_zero_index [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {h : ∀ i, β i → γ} : (0 : Π₀ i, β i).prod h = 1 :=
  rfl
#align dfinsupp.prod_zero_index DFinsupp.prod_zero_index
#align dfinsupp.sum_zero_index DFinsupp.sum_zero_index

@[to_additive]
theorem prod_single_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {i : ι} {b : β i} {h : ∀ i, β i → γ} (h_zero : h i 0 = 1) : (single i b).prod h = h i b := by
  by_cases h : b ≠ 0
  · simp [DFinsupp.prod, support_single_ne_zero h]
  · rw [not_not] at h
    simp [h, prod_zero_index, h_zero]
    rfl
#align dfinsupp.prod_single_index DFinsupp.prod_single_index
#align dfinsupp.sum_single_index DFinsupp.sum_single_index

@[to_additive]
theorem prod_neg_index [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {g : Π₀ i, β i} {h : ∀ i, β i → γ} (h0 : ∀ i, h i 0 = 1) :
    (-g).prod h = g.prod fun i b => h i (-b) :=
  prod_mapRange_index h0
#align dfinsupp.prod_neg_index DFinsupp.prod_neg_index
#align dfinsupp.sum_neg_index DFinsupp.sum_neg_index

@[to_additive]
theorem prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} [DecidableEq ι₁]
    [DecidableEq ι₂] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)]
    [∀ (i) (x : β₂ i), Decidable (x ≠ 0)] [CommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i)
    (h : ∀ i, β₁ i → ∀ i, β₂ i → γ) :
    (f₁.prod fun i₁ x₁ => f₂.prod fun i₂ x₂ => h i₁ x₁ i₂ x₂) =
      f₂.prod fun i₂ x₂ => f₁.prod fun i₁ x₁ => h i₁ x₁ i₂ x₂ :=
  Finset.prod_comm
#align dfinsupp.prod_comm DFinsupp.prod_comm
#align dfinsupp.sum_comm DFinsupp.sum_comm

@[simp]
theorem sum_apply {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)] {f : Π₀ i₁, β₁ i₁}
    {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} {i₂ : ι} : (f.sum g) i₂ = f.sum fun i₁ b => g i₁ b i₂ :=
  map_sum (evalAddMonoidHom i₂) _ f.support
#align dfinsupp.sum_apply DFinsupp.sum_apply

theorem support_sum {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} :
    (f.sum g).support ⊆ f.support.biUnion fun i => (g i (f i)).support := by
  have :
    ∀ i₁ : ι,
      (f.sum fun (i : ι₁) (b : β₁ i) => (g i b) i₁) ≠ 0 → ∃ i : ι₁, f i ≠ 0 ∧ ¬(g i (f i)) i₁ = 0 :=
    fun i₁ h =>
    let ⟨i, hi, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨i, mem_support_iff.1 hi, Ne⟩
  simpa [Finset.subset_iff, mem_support_iff, Finset.mem_biUnion, sum_apply] using this
#align dfinsupp.support_sum DFinsupp.support_sum

@[to_additive (attr := simp)]
theorem prod_one [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} : (f.prod fun _ _ => (1 : γ)) = 1 :=
  Finset.prod_const_one
#align dfinsupp.prod_one DFinsupp.prod_one
#align dfinsupp.sum_zero DFinsupp.sum_zero

@[to_additive (attr := simp)]
theorem prod_mul [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h₁ h₂ : ∀ i, β i → γ} :
    (f.prod fun i b => h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib
#align dfinsupp.prod_mul DFinsupp.prod_mul
#align dfinsupp.sum_add DFinsupp.sum_add

@[to_additive (attr := simp)]
theorem prod_inv [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommGroup γ]
    {f : Π₀ i, β i} {h : ∀ i, β i → γ} : (f.prod fun i b => (h i b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (invMonoidHom : γ →* γ) _ f.support).symm
#align dfinsupp.prod_inv DFinsupp.prod_inv
#align dfinsupp.sum_neg DFinsupp.sum_neg

@[to_additive]
theorem prod_eq_one [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h : ∀ i, β i → γ} (hyp : ∀ i, h i (f i) = 1) : f.prod h = 1 :=
  Finset.prod_eq_one fun i _ => hyp i
#align dfinsupp.prod_eq_one DFinsupp.prod_eq_one
#align dfinsupp.sum_eq_zero DFinsupp.sum_eq_zero

theorem smul_sum {α : Type*} [Monoid α] [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] [DistribMulAction α γ] {f : Π₀ i, β i} {h : ∀ i, β i → γ} {c : α} :
    c • f.sum h = f.sum fun a b => c • h a b :=
  Finset.smul_sum
#align dfinsupp.smul_sum DFinsupp.smul_sum

@[to_additive]
theorem prod_add_index [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {f g : Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) : (f + g).prod h = f.prod h * g.prod h :=
  have f_eq : (∏ i ∈ f.support ∪ g.support, h i (f i)) = f.prod h :=
    (Finset.prod_subset Finset.subset_union_left <| by
        simp (config := { contextual := true }) [mem_support_iff, h_zero]).symm
  have g_eq : (∏ i ∈ f.support ∪ g.support, h i (g i)) = g.prod h :=
    (Finset.prod_subset Finset.subset_union_right <| by
        simp (config := { contextual := true }) [mem_support_iff, h_zero]).symm
  calc
    (∏ i ∈ (f + g).support, h i ((f + g) i)) = ∏ i ∈ f.support ∪ g.support, h i ((f + g) i) :=
      Finset.prod_subset support_add <| by
        simp (config := { contextual := true }) [mem_support_iff, h_zero]
    _ = (∏ i ∈ f.support ∪ g.support, h i (f i)) * ∏ i ∈ f.support ∪ g.support, h i (g i) := by
      { simp [h_add, Finset.prod_mul_distrib] }
    _ = _ := by rw [f_eq, g_eq]
#align dfinsupp.prod_add_index DFinsupp.prod_add_index
#align dfinsupp.sum_add_index DFinsupp.sum_add_index

@[to_additive]
theorem _root_.dfinsupp_prod_mem [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {S : Type*} [SetLike S γ] [SubmonoidClass S γ]
    (s : S) (f : Π₀ i, β i) (g : ∀ i, β i → γ)
    (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.prod g ∈ s :=
  prod_mem fun _ hi => h _ <| mem_support_iff.1 hi
#align dfinsupp_prod_mem dfinsupp_prod_mem
#align dfinsupp_sum_mem dfinsupp_sum_mem

@[to_additive (attr := simp)]
theorem prod_eq_prod_fintype [Fintype ι] [∀ i, Zero (β i)] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    -- Porting note: `f` was a typeclass argument
    [CommMonoid γ] (v : Π₀ i, β i) {f : ∀ i, β i → γ} (hf : ∀ i, f i 0 = 1) :
    v.prod f = ∏ i, f i (DFinsupp.equivFunOnFintype v i) := by
  suffices (∏ i ∈ v.support, f i (v i)) = ∏ i, f i (v i) by simp [DFinsupp.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i _ hi
  rw [mem_support_iff, not_not] at hi
  rw [hi, hf]
#align dfinsupp.prod_eq_prod_fintype DFinsupp.prod_eq_prod_fintype
#align dfinsupp.sum_eq_sum_fintype DFinsupp.sum_eq_sum_fintype

section CommMonoidWithZero
variable [Π i, Zero (β i)] [CommMonoidWithZero γ] [Nontrivial γ] [NoZeroDivisors γ]
  [Π i, DecidableEq (β i)] {f : Π₀ i, β i} {g : Π i, β i → γ}

@[simp]
lemma prod_eq_zero_iff : f.prod g = 0 ↔ ∃ i ∈ f.support, g i (f i) = 0 := Finset.prod_eq_zero_iff
lemma prod_ne_zero_iff : f.prod g ≠ 0 ↔ ∀ i ∈ f.support, g i (f i) ≠ 0 := Finset.prod_ne_zero_iff

end CommMonoidWithZero

/--
When summing over an `AddMonoidHom`, the decidability assumption is not needed, and the result is
also an `AddMonoidHom`.
-/
def sumAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) :
    (Π₀ i, β i) →+ γ where
  toFun f :=
    (f.support'.lift fun s => ∑ i ∈ Multiset.toFinset s.1, φ i (f i)) <| by
      rintro ⟨sx, hx⟩ ⟨sy, hy⟩
      dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
      have H1 : sx.toFinset ∩ sy.toFinset ⊆ sx.toFinset := Finset.inter_subset_left
      have H2 : sx.toFinset ∩ sy.toFinset ⊆ sy.toFinset := Finset.inter_subset_right
      refine
        (Finset.sum_subset H1 ?_).symm.trans
          ((Finset.sum_congr rfl ?_).trans (Finset.sum_subset H2 ?_))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert AddMonoidHom.map_zero (φ i)
        exact (hy i).resolve_left (mt (And.intro H1) H2)
      · intro i _
        rfl
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        convert AddMonoidHom.map_zero (φ i)
        exact (hx i).resolve_left (mt (fun H3 => And.intro H3 H1) H2)
  map_add' := by
    rintro ⟨f, sf, hf⟩ ⟨g, sg, hg⟩
    change (∑ i ∈ _, _) = (∑ i ∈ _, _) + ∑ i ∈ _, _
    simp only [coe_add, coe_mk', Subtype.coe_mk, Pi.add_apply, map_add, Finset.sum_add_distrib]
    congr 1
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inl
      · intro i _ H2
        simp only [Multiset.mem_toFinset, Multiset.mem_add] at H2
        rw [(hf i).resolve_left H2, AddMonoidHom.map_zero]
    · refine (Finset.sum_subset ?_ ?_).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inr
      · intro i _ H2
        simp only [Multiset.mem_toFinset, Multiset.mem_add] at H2
        rw [(hg i).resolve_left H2, AddMonoidHom.map_zero]
  map_zero' := by
    simp only [toFun_eq_coe, coe_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero]; rfl
#align dfinsupp.sum_add_hom DFinsupp.sumAddHom

@[simp]
theorem sumAddHom_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) (i)
    (x : β i) : sumAddHom φ (single i x) = φ i x := by
  dsimp [sumAddHom, single, Trunc.lift_mk]
  rw [Multiset.toFinset_singleton, Finset.sum_singleton, Pi.single_eq_same]
#align dfinsupp.sum_add_hom_single DFinsupp.sumAddHom_single

@[simp]
theorem sumAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (sumAddHom f).comp (singleAddHom β i) = f i :=
  AddMonoidHom.ext fun x => sumAddHom_single f i x
#align dfinsupp.sum_add_hom_comp_single DFinsupp.sumAddHom_comp_single

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
theorem sumAddHom_apply [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) (f : Π₀ i, β i) : sumAddHom φ f = f.sum fun x => φ x := by
  rcases f with ⟨f, s, hf⟩
  change (∑ i ∈ _, _) = ∑ i ∈ Finset.filter _ _, _
  rw [Finset.sum_filter, Finset.sum_congr rfl]
  intro i _
  dsimp only [coe_mk', Subtype.coe_mk] at *
  split_ifs with h
  · rfl
  · rw [not_not.mp h, AddMonoidHom.map_zero]
#align dfinsupp.sum_add_hom_apply DFinsupp.sumAddHom_apply

theorem _root_.dfinsupp_sumAddHom_mem [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] {S : Type*}
    [SetLike S γ] [AddSubmonoidClass S γ] (s : S) (f : Π₀ i, β i) (g : ∀ i, β i →+ γ)
    (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : DFinsupp.sumAddHom g f ∈ s := by
  classical
    rw [DFinsupp.sumAddHom_apply]
    exact dfinsupp_sum_mem s f (g ·) h
#align dfinsupp_sum_add_hom_mem dfinsupp_sumAddHom_mem

/-- The supremum of a family of commutative additive submonoids is equal to the range of
`DFinsupp.sumAddHom`; that is, every element in the `iSup` can be produced from taking a finite
number of non-zero elements of `S i`, coercing them to `γ`, and summing them. -/
theorem _root_.AddSubmonoid.iSup_eq_mrange_dfinsupp_sumAddHom
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) :
    iSup S = AddMonoidHom.mrange (DFinsupp.sumAddHom fun i => (S i).subtype) := by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsupp_sumAddHom_mem _ v _ fun i _ => (le_iSup S i : S i ≤ _) (v i).prop
#align add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom AddSubmonoid.iSup_eq_mrange_dfinsupp_sumAddHom

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`DFinsupp.sumAddHom` composed with `DFinsupp.filterAddMonoidHom`; that is, every element in the
bounded `iSup` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
theorem _root_.AddSubmonoid.bsupr_eq_mrange_dfinsupp_sumAddHom (p : ι → Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) :
    ⨆ (i) (_ : p i), S i =
      AddMonoidHom.mrange ((sumAddHom fun i => (S i).subtype).comp (filterAddMonoidHom _ p)) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [AddMonoidHom.comp_apply, filterAddMonoidHom_apply, filter_single_pos _ _ hi]
    exact sumAddHom_single _ _ _
  · rintro x ⟨v, rfl⟩
    refine dfinsupp_sumAddHom_mem _ _ _ fun i _ => ?_
    refine AddSubmonoid.mem_iSup_of_mem i ?_
    by_cases hp : p i
    · simp [hp]
    · simp [hp]
#align add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom AddSubmonoid.bsupr_eq_mrange_dfinsupp_sumAddHom

theorem _root_.AddSubmonoid.mem_iSup_iff_exists_dfinsupp [AddCommMonoid γ] (S : ι → AddSubmonoid γ)
    (x : γ) : x ∈ iSup S ↔ ∃ f : Π₀ i, S i, DFinsupp.sumAddHom (fun i => (S i).subtype) f = x :=
  SetLike.ext_iff.mp (AddSubmonoid.iSup_eq_mrange_dfinsupp_sumAddHom S) x
#align add_submonoid.mem_supr_iff_exists_dfinsupp AddSubmonoid.mem_iSup_iff_exists_dfinsupp

/-- A variant of `AddSubmonoid.mem_iSup_iff_exists_dfinsupp` with the RHS fully unfolded. -/
theorem _root_.AddSubmonoid.mem_iSup_iff_exists_dfinsupp' [AddCommMonoid γ] (S : ι → AddSubmonoid γ)
    [∀ (i) (x : S i), Decidable (x ≠ 0)] (x : γ) :
    x ∈ iSup S ↔ ∃ f : Π₀ i, S i, (f.sum fun i xi => ↑xi) = x := by
  rw [AddSubmonoid.mem_iSup_iff_exists_dfinsupp]
  simp_rw [sumAddHom_apply]
  rfl
#align add_submonoid.mem_supr_iff_exists_dfinsupp' AddSubmonoid.mem_iSup_iff_exists_dfinsupp'

theorem _root_.AddSubmonoid.mem_bsupr_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) (x : γ) :
    (x ∈ ⨆ (i) (_ : p i), S i) ↔
      ∃ f : Π₀ i, S i, DFinsupp.sumAddHom (fun i => (S i).subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (AddSubmonoid.bsupr_eq_mrange_dfinsupp_sumAddHom p S) x
#align add_submonoid.mem_bsupr_iff_exists_dfinsupp AddSubmonoid.mem_bsupr_iff_exists_dfinsupp

theorem sumAddHom_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} {γ : Type*}
    [DecidableEq ι₁] [DecidableEq ι₂] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)]
    [AddCommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : ∀ i j, β₁ i →+ β₂ j →+ γ) :
    sumAddHom (fun i₂ => sumAddHom (fun i₁ => h i₁ i₂) f₁) f₂ =
      sumAddHom (fun i₁ => sumAddHom (fun i₂ => (h i₁ i₂).flip) f₂) f₁ := by
  obtain ⟨⟨f₁, s₁, h₁⟩, ⟨f₂, s₂, h₂⟩⟩ := f₁, f₂
  simp only [sumAddHom, AddMonoidHom.finset_sum_apply, Quotient.liftOn_mk, AddMonoidHom.coe_mk,
    AddMonoidHom.flip_apply, Trunc.lift, toFun_eq_coe, ZeroHom.coe_mk, coe_mk']
  exact Finset.sum_comm
#align dfinsupp.sum_add_hom_comm DFinsupp.sumAddHom_comm

/-- The `DFinsupp` version of `Finsupp.liftAddHom`,-/
@[simps apply symm_apply]
def liftAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (∀ i, β i →+ γ) ≃+ ((Π₀ i, β i) →+ γ) where
  toFun := sumAddHom
  invFun F i := F.comp (singleAddHom β i)
  left_inv x := by ext; simp
  right_inv ψ := by ext; simp
  map_add' F G := by ext; simp
#align dfinsupp.lift_add_hom DFinsupp.liftAddHom
#align dfinsupp.lift_add_hom_apply DFinsupp.liftAddHom_apply
#align dfinsupp.lift_add_hom_symm_apply DFinsupp.liftAddHom_symm_apply

-- Porting note: The elaborator is struggling with `liftAddHom`. Passing it `β` explicitly helps.
-- This applies to roughly the remainder of the file.

/-- The `DFinsupp` version of `Finsupp.liftAddHom_singleAddHom`,-/
@[simp, nolint simpNF] -- Porting note: linter claims that simp can prove this, but it can not
theorem liftAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    liftAddHom (β := β) (singleAddHom β) = AddMonoidHom.id (Π₀ i, β i) :=
  (liftAddHom (β := β)).toEquiv.apply_eq_iff_eq_symm_apply.2 rfl
#align dfinsupp.lift_add_hom_single_add_hom DFinsupp.liftAddHom_singleAddHom

/-- The `DFinsupp` version of `Finsupp.liftAddHom_apply_single`,-/
theorem liftAddHom_apply_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) (x : β i) : liftAddHom (β := β) f (single i x) = f i x := by simp
#align dfinsupp.lift_add_hom_apply_single DFinsupp.liftAddHom_apply_single

/-- The `DFinsupp` version of `Finsupp.liftAddHom_comp_single`,-/
theorem liftAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (liftAddHom (β := β) f).comp (singleAddHom β i) = f i := by simp
#align dfinsupp.lift_add_hom_comp_single DFinsupp.liftAddHom_comp_single

/-- The `DFinsupp` version of `Finsupp.comp_liftAddHom`,-/
theorem comp_liftAddHom {δ : Type*} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) :
    g.comp (liftAddHom (β := β) f) = liftAddHom (β := β) fun a => g.comp (f a) :=
  (liftAddHom (β := β)).symm_apply_eq.1 <|
    funext fun a => by
      rw [liftAddHom_symm_apply, AddMonoidHom.comp_assoc, liftAddHom_comp_single]
#align dfinsupp.comp_lift_add_hom DFinsupp.comp_liftAddHom

@[simp]
theorem sumAddHom_zero [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (sumAddHom fun i => (0 : β i →+ γ)) = 0 :=
  (liftAddHom (β := β) : (∀ i, β i →+ γ) ≃+ _).map_zero
#align dfinsupp.sum_add_hom_zero DFinsupp.sumAddHom_zero

@[simp]
theorem sumAddHom_add [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (g : ∀ i, β i →+ γ)
    (h : ∀ i, β i →+ γ) : (sumAddHom fun i => g i + h i) = sumAddHom g + sumAddHom h :=
  (liftAddHom (β := β)).map_add _ _
#align dfinsupp.sum_add_hom_add DFinsupp.sumAddHom_add

@[simp]
theorem sumAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    sumAddHom (singleAddHom β) = AddMonoidHom.id _ :=
  liftAddHom_singleAddHom
#align dfinsupp.sum_add_hom_single_add_hom DFinsupp.sumAddHom_singleAddHom

theorem comp_sumAddHom {δ : Type*} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) : g.comp (sumAddHom f) = sumAddHom fun a => g.comp (f a) :=
  comp_liftAddHom _ _
#align dfinsupp.comp_sum_add_hom DFinsupp.comp_sumAddHom

theorem sum_sub_index [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [AddCommGroup γ]
    {f g : Π₀ i, β i} {h : ∀ i, β i → γ} (h_sub : ∀ i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) :
    (f - g).sum h = f.sum h - g.sum h := by
  have := (liftAddHom (β := β) fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g
  rw [liftAddHom_apply, sumAddHom_apply, sumAddHom_apply, sumAddHom_apply] at this
  exact this
#align dfinsupp.sum_sub_index DFinsupp.sum_sub_index

@[to_additive]
theorem prod_finset_sum_index {γ : Type w} {α : Type x} [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] {s : Finset α} {g : α → Π₀ i, β i}
    {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (∏ i ∈ s, (g i).prod h) = (∑ i ∈ s, g i).prod h := by
  classical
  exact Finset.induction_on s (by simp [prod_zero_index])
        (by simp (config := { contextual := true }) [prod_add_index, h_zero, h_add])
#align dfinsupp.prod_finset_sum_index DFinsupp.prod_finset_sum_index
#align dfinsupp.sum_finset_sum_index DFinsupp.sum_finset_sum_index

@[to_additive]
theorem prod_sum_index {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] {f : Π₀ i₁, β₁ i₁}
    {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (f.sum g).prod h = f.prod fun i b => (g i b).prod h :=
  (prod_finset_sum_index h_zero h_add).symm
#align dfinsupp.prod_sum_index DFinsupp.prod_sum_index
#align dfinsupp.sum_sum_index DFinsupp.sum_sum_index

@[simp]
theorem sum_single [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    f.sum single = f := by
  have := DFunLike.congr_fun (liftAddHom_singleAddHom (β := β)) f
  rw [liftAddHom_apply, sumAddHom_apply] at this
  exact this
#align dfinsupp.sum_single DFinsupp.sum_single

@[to_additive]
theorem prod_subtypeDomain_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {v : Π₀ i, β i} {p : ι → Prop} [DecidablePred p] {h : ∀ i, β i → γ}
    (hp : ∀ x ∈ v.support, p x) : (v.subtypeDomain p).prod (fun i b => h i b) = v.prod h := by
  refine Finset.prod_bij (fun p _ ↦ p) ?_ ?_ ?_ ?_ <;> aesop
#align dfinsupp.prod_subtype_domain_index DFinsupp.prod_subtypeDomain_index
#align dfinsupp.sum_subtype_domain_index DFinsupp.sum_subtypeDomain_index

theorem subtypeDomain_sum [∀ i, AddCommMonoid (β i)] {s : Finset γ} {h : γ → Π₀ i, β i}
    {p : ι → Prop} [DecidablePred p] :
    (∑ c ∈ s, h c).subtypeDomain p = ∑ c ∈ s, (h c).subtypeDomain p :=
  map_sum (subtypeDomainAddMonoidHom β p) _ s
#align dfinsupp.subtype_domain_sum DFinsupp.subtypeDomain_sum

theorem subtypeDomain_finsupp_sum {δ : γ → Type x} [DecidableEq γ] [∀ c, Zero (δ c)]
    [∀ (c) (x : δ c), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)] {p : ι → Prop} [DecidablePred p]
    {s : Π₀ c, δ c} {h : ∀ c, δ c → Π₀ i, β i} :
    (s.sum h).subtypeDomain p = s.sum fun c d => (h c d).subtypeDomain p :=
  subtypeDomain_sum
#align dfinsupp.subtype_domain_finsupp_sum DFinsupp.subtypeDomain_finsupp_sum

end ProdAndSum

/-! ### Bundled versions of `DFinsupp.mapRange`

The names should match the equivalent bundled `Finsupp.mapRange` definitions.
-/


section MapRange

variable [∀ i, AddZeroClass (β i)] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)]

theorem mapRange_add (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0)
    (hf' : ∀ i x y, f i (x + y) = f i x + f i y) (g₁ g₂ : Π₀ i, β₁ i) :
    mapRange f hf (g₁ + g₂) = mapRange f hf g₁ + mapRange f hf g₂ := by
  ext
  simp only [mapRange_apply f, coe_add, Pi.add_apply, hf']
#align dfinsupp.map_range_add DFinsupp.mapRange_add

/-- `DFinsupp.mapRange` as an `AddMonoidHom`. -/
@[simps apply]
def mapRange.addMonoidHom (f : ∀ i, β₁ i →+ β₂ i) : (Π₀ i, β₁ i) →+ Π₀ i, β₂ i where
  toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
  map_zero' := mapRange_zero _ _
  map_add' := mapRange_add _ (fun i => (f i).map_zero) fun i => (f i).map_add
#align dfinsupp.map_range.add_monoid_hom DFinsupp.mapRange.addMonoidHom
#align dfinsupp.map_range.add_monoid_hom_apply DFinsupp.mapRange.addMonoidHom_apply

@[simp]
theorem mapRange.addMonoidHom_id :
    (mapRange.addMonoidHom fun i => AddMonoidHom.id (β₂ i)) = AddMonoidHom.id _ :=
  AddMonoidHom.ext mapRange_id
#align dfinsupp.map_range.add_monoid_hom_id DFinsupp.mapRange.addMonoidHom_id

theorem mapRange.addMonoidHom_comp (f : ∀ i, β₁ i →+ β₂ i) (f₂ : ∀ i, β i →+ β₁ i) :
    (mapRange.addMonoidHom fun i => (f i).comp (f₂ i)) =
      (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) := by
  refine AddMonoidHom.ext <| mapRange_comp (fun i x => f i x) (fun i x => f₂ i x) ?_ ?_ ?_
  · intros; apply map_zero
  · intros; apply map_zero
  · intros; dsimp; simp only [map_zero]
#align dfinsupp.map_range.add_monoid_hom_comp DFinsupp.mapRange.addMonoidHom_comp

/-- `DFinsupp.mapRange.addMonoidHom` as an `AddEquiv`. -/
@[simps apply]
def mapRange.addEquiv (e : ∀ i, β₁ i ≃+ β₂ i) : (Π₀ i, β₁ i) ≃+ Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i =>
      (e i).toAddMonoidHom with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero
    left_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.symm_comp_self]
          simp
    right_inv := fun x => by
      rw [← mapRange_comp] <;>
        · simp_rw [AddEquiv.self_comp_symm]
          simp }
#align dfinsupp.map_range.add_equiv DFinsupp.mapRange.addEquiv
#align dfinsupp.map_range.add_equiv_apply DFinsupp.mapRange.addEquiv_apply

@[simp]
theorem mapRange.addEquiv_refl :
    (mapRange.addEquiv fun i => AddEquiv.refl (β₁ i)) = AddEquiv.refl _ :=
  AddEquiv.ext mapRange_id
#align dfinsupp.map_range.add_equiv_refl DFinsupp.mapRange.addEquiv_refl

theorem mapRange.addEquiv_trans (f : ∀ i, β i ≃+ β₁ i) (f₂ : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) := by
  refine AddEquiv.ext <| mapRange_comp (fun i x => f₂ i x) (fun i x => f i x) ?_ ?_ ?_
  · intros; apply map_zero
  · intros; apply map_zero
  · intros; dsimp; simp only [map_zero]
#align dfinsupp.map_range.add_equiv_trans DFinsupp.mapRange.addEquiv_trans

@[simp]
theorem mapRange.addEquiv_symm (e : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv e).symm = mapRange.addEquiv fun i => (e i).symm :=
  rfl
#align dfinsupp.map_range.add_equiv_symm DFinsupp.mapRange.addEquiv_symm

end MapRange

end DFinsupp

/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `AddMonoidHom.map_sum`, `AddMonoidHom.coe_finset_sum`,
and `AddMonoidHom.finset_sum_apply` for `DFinsupp.sum` and `DFinsupp.sumAddHom` instead of
`Finset.sum`.

We provide these for `AddMonoidHom`, `MonoidHom`, `RingHom`, `AddEquiv`, and `MulEquiv`.

Lemmas for `LinearMap` and `LinearEquiv` are in another file.
-/


section

variable [DecidableEq ι]

namespace MonoidHom

variable {R S : Type*}
variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

#align monoid_hom.map_dfinsupp_prod map_dfinsupp_prodₓ
#align add_monoid_hom.map_dfinsupp_sum map_dfinsupp_sumₓ

@[to_additive (attr := simp, norm_cast)]
theorem coe_dfinsupp_prod [Monoid R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S) :
    ⇑(f.prod g) = f.prod fun a b => ⇑(g a b) :=
  coe_finset_prod _ _
#align monoid_hom.coe_dfinsupp_prod MonoidHom.coe_dfinsupp_prod
#align add_monoid_hom.coe_dfinsupp_sum AddMonoidHom.coe_dfinsupp_sum

@[to_additive]
theorem dfinsupp_prod_apply [Monoid R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S)
    (r : R) : (f.prod g) r = f.prod fun a b => (g a b) r :=
  finset_prod_apply _ _ _
#align monoid_hom.dfinsupp_prod_apply MonoidHom.dfinsupp_prod_apply
#align add_monoid_hom.dfinsupp_sum_apply AddMonoidHom.dfinsupp_sum_apply

end MonoidHom

#align ring_hom.map_dfinsupp_prod map_dfinsupp_prodₓ
#align ring_hom.map_dfinsupp_sum map_dfinsupp_sumₓ
#align mul_equiv.map_dfinsupp_prod map_dfinsupp_prodₓ
#align add_equiv.map_dfinsupp_sum map_dfinsupp_sumₓ

/-! The above lemmas, repeated for `DFinsupp.sumAddHom`. -/


namespace AddMonoidHom

variable {R S : Type*}

open DFinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R →+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h g) f
#align add_monoid_hom.map_dfinsupp_sum_add_hom AddMonoidHom.map_dfinsupp_sumAddHom

theorem dfinsupp_sumAddHom_apply [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) (r : R) :
    (sumAddHom g f) r = sumAddHom (fun i => (eval r).comp (g i)) f :=
  map_dfinsupp_sumAddHom (eval r) f g
#align add_monoid_hom.dfinsupp_sum_add_hom_apply AddMonoidHom.dfinsupp_sumAddHom_apply

@[simp, norm_cast]
theorem coe_dfinsupp_sumAddHom [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) :
    ⇑(sumAddHom g f) = sumAddHom (fun i => (coeFn R S).comp (g i)) f :=
  map_dfinsupp_sumAddHom (coeFn R S) f g
#align add_monoid_hom.coe_dfinsupp_sum_add_hom AddMonoidHom.coe_dfinsupp_sumAddHom

end AddMonoidHom

namespace RingHom

variable {R S : Type*}

open DFinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [NonAssocSemiring R] [NonAssocSemiring S] [∀ i, AddZeroClass (β i)]
    (h : R →+* S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f
#align ring_hom.map_dfinsupp_sum_add_hom RingHom.map_dfinsupp_sumAddHom

end RingHom

namespace AddEquiv

variable {R S : Type*}

open DFinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R ≃+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  DFunLike.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f
#align add_equiv.map_dfinsupp_sum_add_hom AddEquiv.map_dfinsupp_sumAddHom

end AddEquiv

end

section FiniteInfinite

instance DFinsupp.fintype {ι : Sort _} {π : ι → Sort _} [DecidableEq ι] [∀ i, Zero (π i)]
    [Fintype ι] [∀ i, Fintype (π i)] : Fintype (Π₀ i, π i) :=
  Fintype.ofEquiv (∀ i, π i) DFinsupp.equivFunOnFintype.symm
#align dfinsupp.fintype DFinsupp.fintype

instance DFinsupp.infinite_of_left {ι : Sort _} {π : ι → Sort _} [∀ i, Nontrivial (π i)]
    [∀ i, Zero (π i)] [Infinite ι] : Infinite (Π₀ i, π i) := by
  letI := Classical.decEq ι; choose m hm using fun i => exists_ne (0 : π i);
    exact Infinite.of_injective _ (DFinsupp.single_left_injective hm)
#align dfinsupp.infinite_of_left DFinsupp.infinite_of_left

/-- See `DFinsupp.infinite_of_right` for this in instance form, with the drawback that
it needs all `π i` to be infinite. -/
theorem DFinsupp.infinite_of_exists_right {ι : Sort _} {π : ι → Sort _} (i : ι) [Infinite (π i)]
    [∀ i, Zero (π i)] : Infinite (Π₀ i, π i) :=
  letI := Classical.decEq ι
  Infinite.of_injective (fun j => DFinsupp.single i j) DFinsupp.single_injective
#align dfinsupp.infinite_of_exists_right DFinsupp.infinite_of_exists_right

/-- See `DFinsupp.infinite_of_exists_right` for the case that only one `π ι` is infinite. -/
instance DFinsupp.infinite_of_right {ι : Sort _} {π : ι → Sort _} [∀ i, Infinite (π i)]
    [∀ i, Zero (π i)] [Nonempty ι] : Infinite (Π₀ i, π i) :=
  DFinsupp.infinite_of_exists_right (Classical.arbitrary ι)
#align dfinsupp.infinite_of_right DFinsupp.infinite_of_right

end FiniteInfinite
