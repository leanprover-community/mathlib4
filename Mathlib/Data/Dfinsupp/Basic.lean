/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau

! This file was ported from Lean 3 source module data.dfinsupp.basic
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Set.Finite
import Mathbin.GroupTheory.Submonoid.Membership
import Mathbin.GroupTheory.GroupAction.BigOperators
import Mathbin.Data.Finset.Preimage

/-!
# Dependent functions with finite support

For a non-dependent version see `data/finsupp.lean`.

## Notation

This file introduces the notation `Π₀ a, β a` as notation for `dfinsupp β`, mirroring the `α →₀ β`
notation used for `finsupp`. This works for nested binders too, with `Π₀ a b, γ a b` as notation
for `dfinsupp (λ a, dfinsupp (γ a))`.

## Implementation notes

The support is internally represented (in the primed `dfinsupp.support'`) as a `multiset` that
represents a superset of the true support of the function, quotiented by the always-true relation so
that this does not impact equality. This approach has computational benefits over storing a
`finset`; it allows us to add together two finitely-supported functions (`dfinsupp.has_add`) without
having to evaluate the resulting function to recompute its support (which would required
decidability of `b = 0` for `b : β i`).

The true support of the function can still be recovered with `dfinsupp.support`; but these
decidability obligations are now postponed to when the support is actually needed. As a consequence,
there are two ways to sum a `dfinsupp`: with `dfinsupp.sum` which works over an arbitrary function
but requires recomputation of the support and therefore a `decidable` argument; and with
`dfinsupp.sum_add_hom` which requires an additive morphism, using its properties to show that
summing over a superset of the support is sufficient.

`finsupp` takes an altogether different approach here; it uses `classical.decidable` and declares
`finsupp.has_add` as noncomputable. This design difference is independent of the fact that
`dfinsupp` is dependently-typed and `finsupp` is not; in future, we may want to align these two
definitions, or introduce two more definitions for the other combinations of decisions.
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

open BigOperators

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

variable (β)

/-- A dependent function `Π i, β i` with finite support, with notation `Π₀ i, β i`.

Note that `dfinsupp.support` is the preferred API for accessing the support of the function,
`dfinsupp.support'` is a implementation detail that aids computability; see the implementation
notes in this file for more information. -/
structure Dfinsupp [∀ i, Zero (β i)] : Type max u v where mk' ::
  toFun : ∀ i, β i
  support' : Trunc { s : Multiset ι // ∀ i, i ∈ s ∨ to_fun i = 0 }
#align dfinsupp Dfinsupp

variable {β}

-- mathport name: «exprΠ₀ , »
notation3"Π₀ "(...)", "r:(scoped f => Dfinsupp f) => r

-- mathport name: «expr →ₚ »
infixl:25 " →ₚ " => Dfinsupp

namespace Dfinsupp

section Basic

variable [∀ i, Zero (β i)] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

instance funLike : FunLike (Π₀ i, β i) ι β :=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ (h : f₁ = f₂) =>
    by
    subst h
    congr ⟩
#align dfinsupp.fun_like Dfinsupp.funLike

/-- Helper instance for when there are too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (Π₀ i, β i) fun _ => ∀ i, β i :=
  FunLike.hasCoeToFun

@[simp]
theorem toFun_eq_coe (f : Π₀ i, β i) : f.toFun = f :=
  rfl
#align dfinsupp.to_fun_eq_coe Dfinsupp.toFun_eq_coe

@[ext]
theorem ext {f g : Π₀ i, β i} (h : ∀ i, f i = g i) : f = g :=
  FunLike.ext _ _ h
#align dfinsupp.ext Dfinsupp.ext

/-- Deprecated. Use `fun_like.ext_iff` instead. -/
theorem ext_iff {f g : Π₀ i, β i} : f = g ↔ ∀ i, f i = g i :=
  FunLike.ext_iff
#align dfinsupp.ext_iff Dfinsupp.ext_iff

/-- Deprecated. Use `fun_like.coe_injective` instead. -/
theorem coeFn_injective : @Function.Injective (Π₀ i, β i) (∀ i, β i) coeFn :=
  FunLike.coe_injective
#align dfinsupp.coe_fn_injective Dfinsupp.coeFn_injective

instance : Zero (Π₀ i, β i) :=
  ⟨⟨0, Trunc.mk <| ⟨∅, fun i => Or.inr rfl⟩⟩⟩

instance : Inhabited (Π₀ i, β i) :=
  ⟨0⟩

@[simp]
theorem coe_mk' (f : ∀ i, β i) (s) : ⇑(⟨f, s⟩ : Π₀ i, β i) = f :=
  rfl
#align dfinsupp.coe_mk' Dfinsupp.coe_mk'

@[simp]
theorem coe_zero : ⇑(0 : Π₀ i, β i) = 0 :=
  rfl
#align dfinsupp.coe_zero Dfinsupp.coe_zero

theorem zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0 :=
  rfl
#align dfinsupp.zero_apply Dfinsupp.zero_apply

/-- The composition of `f : β₁ → β₂` and `g : Π₀ i, β₁ i` is
  `map_range f hf g : Π₀ i, β₂ i`, well defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled:

* `dfinsupp.map_range.add_monoid_hom`
* `dfinsupp.map_range.add_equiv`
* `dfinsupp.map_range.linear_map`
* `dfinsupp.map_range.linear_equiv`
-/
def mapRange (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (x : Π₀ i, β₁ i) : Π₀ i, β₂ i :=
  ⟨fun i => f i (x i),
    x.support'.map fun s => ⟨s, fun i => (s.2 i).imp_right fun h : x i = 0 => h.symm ▸ hf i⟩⟩
#align dfinsupp.map_range Dfinsupp.mapRange

@[simp]
theorem mapRange_apply (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι) :
    mapRange f hf g i = f i (g i) :=
  rfl
#align dfinsupp.map_range_apply Dfinsupp.mapRange_apply

@[simp]
theorem mapRange_id (h : ∀ i, id (0 : β₁ i) = 0 := fun i => rfl) (g : Π₀ i : ι, β₁ i) :
    mapRange (fun i => (id : β₁ i → β₁ i)) h g = g :=
  by
  ext
  rfl
#align dfinsupp.map_range_id Dfinsupp.mapRange_id

theorem mapRange_comp (f : ∀ i, β₁ i → β₂ i) (f₂ : ∀ i, β i → β₁ i) (hf : ∀ i, f i 0 = 0)
    (hf₂ : ∀ i, f₂ i 0 = 0) (h : ∀ i, (f i ∘ f₂ i) 0 = 0) (g : Π₀ i : ι, β i) :
    mapRange (fun i => f i ∘ f₂ i) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  by
  ext
  simp only [map_range_apply]
#align dfinsupp.map_range_comp Dfinsupp.mapRange_comp

@[simp]
theorem mapRange_zero (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) :
    mapRange f hf (0 : Π₀ i, β₁ i) = 0 := by
  ext
  simp only [map_range_apply, coe_zero, Pi.zero_apply, hf]
#align dfinsupp.map_range_zero Dfinsupp.mapRange_zero

/-- Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i 0 0 = 0`.
Then `zip_with f hf` is a binary operation `Π₀ i, β₁ i → Π₀ i, β₂ i → Π₀ i, β i`. -/
def zipWith (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (x : Π₀ i, β₁ i) (y : Π₀ i, β₂ i) :
    Π₀ i, β i :=
  ⟨fun i => f i (x i) (y i), by
    refine' x.support'.bind fun xs => _
    refine' y.support'.map fun ys => _
    refine' ⟨xs + ys, fun i => _⟩
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
    right; rw [h1, h2, hf]⟩
#align dfinsupp.zip_with Dfinsupp.zipWith

@[simp]
theorem zipWith_apply (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i)
    (g₂ : Π₀ i, β₂ i) (i : ι) : zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
  rfl
#align dfinsupp.zip_with_apply Dfinsupp.zipWith_apply

section Piecewise

variable (x y : Π₀ i, β i) (s : Set ι) [∀ i, Decidable (i ∈ s)]

/-- `x.piecewise y s` is the finitely supported function equal to `x` on the set `s`,
  and to `y` on its complement. -/
def piecewise : Π₀ i, β i :=
  zipWith (fun i x y => if i ∈ s then x else y) (fun _ => if_t_t _ 0) x y
#align dfinsupp.piecewise Dfinsupp.piecewise

theorem piecewise_apply (i : ι) : x.piecewise y s i = if i ∈ s then x i else y i :=
  zipWith_apply _ _ x y i
#align dfinsupp.piecewise_apply Dfinsupp.piecewise_apply

@[simp, norm_cast]
theorem coe_piecewise : ⇑(x.piecewise y s) = s.piecewise x y :=
  by
  ext
  apply piecewise_apply
#align dfinsupp.coe_piecewise Dfinsupp.coe_piecewise

end Piecewise

end Basic

section Algebra

instance [∀ i, AddZeroClass (β i)] : Add (Π₀ i, β i) :=
  ⟨zipWith (fun _ => (· + ·)) fun _ => add_zero 0⟩

theorem add_apply [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
    (g₁ + g₂) i = g₁ i + g₂ i :=
  rfl
#align dfinsupp.add_apply Dfinsupp.add_apply

@[simp]
theorem coe_add [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ + g₂) = g₁ + g₂ :=
  rfl
#align dfinsupp.coe_add Dfinsupp.coe_add

instance [∀ i, AddZeroClass (β i)] : AddZeroClass (Π₀ i, β i) :=
  FunLike.coe_injective.AddZeroClass _ coe_zero coe_add

/-- Note the general `dfinsupp.has_smul` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasNatScalar [∀ i, AddMonoid (β i)] : SMul ℕ (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (· • ·) c) fun _ => nsmul_zero _⟩
#align dfinsupp.has_nat_scalar Dfinsupp.hasNatScalar

theorem nsmul_apply [∀ i, AddMonoid (β i)] (b : ℕ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl
#align dfinsupp.nsmul_apply Dfinsupp.nsmul_apply

@[simp]
theorem coe_nsmul [∀ i, AddMonoid (β i)] (b : ℕ) (v : Π₀ i, β i) : ⇑(b • v) = b • v :=
  rfl
#align dfinsupp.coe_nsmul Dfinsupp.coe_nsmul

instance [∀ i, AddMonoid (β i)] : AddMonoid (Π₀ i, β i) :=
  FunLike.coe_injective.AddMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

/-- Coercion from a `dfinsupp` to a pi type is an `add_monoid_hom`. -/
def coeFnAddMonoidHom [∀ i, AddZeroClass (β i)] : (Π₀ i, β i) →+ ∀ i, β i
    where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add
#align dfinsupp.coe_fn_add_monoid_hom Dfinsupp.coeFnAddMonoidHom

/-- Evaluation at a point is an `add_monoid_hom`. This is the finitely-supported version of
`pi.eval_add_monoid_hom`. -/
def evalAddMonoidHom [∀ i, AddZeroClass (β i)] (i : ι) : (Π₀ i, β i) →+ β i :=
  (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom
#align dfinsupp.eval_add_monoid_hom Dfinsupp.evalAddMonoidHom

instance [∀ i, AddCommMonoid (β i)] : AddCommMonoid (Π₀ i, β i) :=
  FunLike.coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

@[simp]
theorem coe_finset_sum {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) :
    ⇑(∑ a in s, g a) = ∑ a in s, g a :=
  (coeFnAddMonoidHom : _ →+ ∀ i, β i).map_sum g s
#align dfinsupp.coe_finset_sum Dfinsupp.coe_finset_sum

@[simp]
theorem finset_sum_apply {α} [∀ i, AddCommMonoid (β i)] (s : Finset α) (g : α → Π₀ i, β i) (i : ι) :
    (∑ a in s, g a) i = ∑ a in s, g a i :=
  (evalAddMonoidHom i : _ →+ β i).map_sum g s
#align dfinsupp.finset_sum_apply Dfinsupp.finset_sum_apply

instance [∀ i, AddGroup (β i)] : Neg (Π₀ i, β i) :=
  ⟨fun f => f.mapRange (fun _ => Neg.neg) fun _ => neg_zero⟩

theorem neg_apply [∀ i, AddGroup (β i)] (g : Π₀ i, β i) (i : ι) : (-g) i = -g i :=
  rfl
#align dfinsupp.neg_apply Dfinsupp.neg_apply

@[simp]
theorem coe_neg [∀ i, AddGroup (β i)] (g : Π₀ i, β i) : ⇑(-g) = -g :=
  rfl
#align dfinsupp.coe_neg Dfinsupp.coe_neg

instance [∀ i, AddGroup (β i)] : Sub (Π₀ i, β i) :=
  ⟨zipWith (fun _ => Sub.sub) fun _ => sub_zero 0⟩

theorem sub_apply [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  rfl
#align dfinsupp.sub_apply Dfinsupp.sub_apply

@[simp]
theorem coe_sub [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  rfl
#align dfinsupp.coe_sub Dfinsupp.coe_sub

/-- Note the general `dfinsupp.has_smul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasIntScalar [∀ i, AddGroup (β i)] : SMul ℤ (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (· • ·) c) fun _ => zsmul_zero _⟩
#align dfinsupp.has_int_scalar Dfinsupp.hasIntScalar

theorem zsmul_apply [∀ i, AddGroup (β i)] (b : ℤ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl
#align dfinsupp.zsmul_apply Dfinsupp.zsmul_apply

@[simp]
theorem coe_zsmul [∀ i, AddGroup (β i)] (b : ℤ) (v : Π₀ i, β i) : ⇑(b • v) = b • v :=
  rfl
#align dfinsupp.coe_zsmul Dfinsupp.coe_zsmul

instance [∀ i, AddGroup (β i)] : AddGroup (Π₀ i, β i) :=
  FunLike.coe_injective.AddGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

instance [∀ i, AddCommGroup (β i)] : AddCommGroup (Π₀ i, β i) :=
  FunLike.coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

/-- Dependent functions with finite support inherit a semiring action from an action on each
coordinate. -/
instance [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] : SMul γ (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (· • ·) c) fun _ => smul_zero _⟩

theorem smul_apply [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] (b : γ)
    (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl
#align dfinsupp.smul_apply Dfinsupp.smul_apply

@[simp]
theorem coe_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] (b : γ)
    (v : Π₀ i, β i) : ⇑(b • v) = b • v :=
  rfl
#align dfinsupp.coe_smul Dfinsupp.coe_smul

instance {δ : Type _} [Monoid γ] [Monoid δ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    [∀ i, DistribMulAction δ (β i)] [∀ i, SMulCommClass γ δ (β i)] : SMulCommClass γ δ (Π₀ i, β i)
    where smul_comm r s m := ext fun i => by simp only [smul_apply, smul_comm r s (m i)]

instance {δ : Type _} [Monoid γ] [Monoid δ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    [∀ i, DistribMulAction δ (β i)] [SMul γ δ] [∀ i, IsScalarTower γ δ (β i)] :
    IsScalarTower γ δ (Π₀ i, β i)
    where smul_assoc r s m := ext fun i => by simp only [smul_apply, smul_assoc r s (m i)]

instance [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    [∀ i, DistribMulAction γᵐᵒᵖ (β i)] [∀ i, IsCentralScalar γ (β i)] :
    IsCentralScalar γ (Π₀ i, β i)
    where op_smul_eq_smul r m := ext fun i => by simp only [smul_apply, op_smul_eq_smul r (m i)]

/-- Dependent functions with finite support inherit a `distrib_mul_action` structure from such a
structure on each coordinate. -/
instance [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] :
    DistribMulAction γ (Π₀ i, β i) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom FunLike.coe_injective coe_smul

/-- Dependent functions with finite support inherit a module structure from such a structure on
each coordinate. -/
instance [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] : Module γ (Π₀ i, β i) :=
  {
    Dfinsupp.distribMulAction with
    zero_smul := fun c => ext fun i => by simp only [smul_apply, zero_smul, zero_apply]
    add_smul := fun c x y => ext fun i => by simp only [add_apply, smul_apply, add_smul] }

end Algebra

section FilterAndSubtypeDomain

/-- `filter p f` is the function which is `f i` if `p i` is true and 0 otherwise. -/
def filter [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (x : Π₀ i, β i) : Π₀ i, β i :=
  ⟨fun i => if p i then x i else 0,
    x.support'.map fun xs =>
      ⟨xs, fun i => (xs.Prop i).imp_right fun H : x i = 0 => by rw [H, if_t_t]⟩⟩
#align dfinsupp.filter Dfinsupp.filter

@[simp]
theorem filter_apply [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (i : ι) (f : Π₀ i, β i) :
    f.filter p i = if p i then f i else 0 :=
  rfl
#align dfinsupp.filter_apply Dfinsupp.filter_apply

theorem filter_apply_pos [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : p i) : f.filter p i = f i := by simp only [filter_apply, if_pos h]
#align dfinsupp.filter_apply_pos Dfinsupp.filter_apply_pos

theorem filter_apply_neg [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : ¬p i) : f.filter p i = 0 := by simp only [filter_apply, if_neg h]
#align dfinsupp.filter_apply_neg Dfinsupp.filter_apply_neg

theorem filter_pos_add_filter_neg [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i) (p : ι → Prop)
    [DecidablePred p] : (f.filter p + f.filter fun i => ¬p i) = f :=
  ext fun i => by
    simp only [add_apply, filter_apply] <;> split_ifs <;> simp only [add_zero, zero_add]
#align dfinsupp.filter_pos_add_filter_neg Dfinsupp.filter_pos_add_filter_neg

@[simp]
theorem filter_zero [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] :
    (0 : Π₀ i, β i).filter p = 0 := by
  ext
  simp
#align dfinsupp.filter_zero Dfinsupp.filter_zero

@[simp]
theorem filter_add [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f + g).filter p = f.filter p + g.filter p :=
  by
  ext
  simp [ite_add_zero]
#align dfinsupp.filter_add Dfinsupp.filter_add

@[simp]
theorem filter_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] (p : ι → Prop)
    [DecidablePred p] (r : γ) (f : Π₀ i, β i) : (r • f).filter p = r • f.filter p :=
  by
  ext
  simp [smul_ite]
#align dfinsupp.filter_smul Dfinsupp.filter_smul

variable (γ β)

/-- `dfinsupp.filter` as an `add_monoid_hom`. -/
@[simps]
def filterAddMonoidHom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i, β i) →+ Π₀ i, β i where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' := filter_add p
#align dfinsupp.filter_add_monoid_hom Dfinsupp.filterAddMonoidHom

/-- `dfinsupp.filter` as a `linear_map`. -/
@[simps]
def filterLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] (p : ι → Prop)
    [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i, β i
    where
  toFun := filter p
  map_add' := filter_add p
  map_smul' := filter_smul p
#align dfinsupp.filter_linear_map Dfinsupp.filterLinearMap

variable {γ β}

@[simp]
theorem filter_neg [∀ i, AddGroup (β i)] (p : ι → Prop) [DecidablePred p] (f : Π₀ i, β i) :
    (-f).filter p = -f.filter p :=
  (filterAddMonoidHom β p).map_neg f
#align dfinsupp.filter_neg Dfinsupp.filter_neg

@[simp]
theorem filter_sub [∀ i, AddGroup (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f - g).filter p = f.filter p - g.filter p :=
  (filterAddMonoidHom β p).map_sub f g
#align dfinsupp.filter_sub Dfinsupp.filter_sub

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtypeDomain [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (x : Π₀ i, β i) :
    Π₀ i : Subtype p, β i :=
  ⟨fun i => x (i : ι),
    x.support'.map fun xs =>
      ⟨(Multiset.filter p xs).attach.map fun j => ⟨j, (Multiset.mem_filter.1 j.2).2⟩, fun i =>
        (xs.Prop i).imp_left fun H =>
          Multiset.mem_map.2
            ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩⟩
#align dfinsupp.subtype_domain Dfinsupp.subtypeDomain

@[simp]
theorem subtypeDomain_zero [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] :
    subtypeDomain p (0 : Π₀ i, β i) = 0 :=
  rfl
#align dfinsupp.subtype_domain_zero Dfinsupp.subtypeDomain_zero

@[simp]
theorem subtypeDomain_apply [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] {i : Subtype p}
    {v : Π₀ i, β i} : (subtypeDomain p v) i = v i :=
  rfl
#align dfinsupp.subtype_domain_apply Dfinsupp.subtypeDomain_apply

@[simp]
theorem subtypeDomain_add [∀ i, AddZeroClass (β i)] {p : ι → Prop} [DecidablePred p]
    (v v' : Π₀ i, β i) : (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  coeFn_injective rfl
#align dfinsupp.subtype_domain_add Dfinsupp.subtypeDomain_add

@[simp]
theorem subtypeDomain_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    {p : ι → Prop} [DecidablePred p] (r : γ) (f : Π₀ i, β i) :
    (r • f).subtypeDomain p = r • f.subtypeDomain p :=
  coeFn_injective rfl
#align dfinsupp.subtype_domain_smul Dfinsupp.subtypeDomain_smul

variable (γ β)

/-- `subtype_domain` but as an `add_monoid_hom`. -/
@[simps]
def subtypeDomainAddMonoidHom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i : ι, β i) →+ Π₀ i : Subtype p, β i
    where
  toFun := subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' := subtypeDomain_add
#align dfinsupp.subtype_domain_add_monoid_hom Dfinsupp.subtypeDomainAddMonoidHom

/-- `dfinsupp.subtype_domain` as a `linear_map`. -/
@[simps]
def subtypeDomainLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    (p : ι → Prop) [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i : Subtype p, β i
    where
  toFun := subtypeDomain p
  map_add' := subtypeDomain_add
  map_smul' := subtypeDomain_smul
#align dfinsupp.subtype_domain_linear_map Dfinsupp.subtypeDomainLinearMap

variable {γ β}

@[simp]
theorem subtypeDomain_neg [∀ i, AddGroup (β i)] {p : ι → Prop} [DecidablePred p] {v : Π₀ i, β i} :
    (-v).subtypeDomain p = -v.subtypeDomain p :=
  coeFn_injective rfl
#align dfinsupp.subtype_domain_neg Dfinsupp.subtypeDomain_neg

@[simp]
theorem subtypeDomain_sub [∀ i, AddGroup (β i)] {p : ι → Prop} [DecidablePred p]
    {v v' : Π₀ i, β i} : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  coeFn_injective rfl
#align dfinsupp.subtype_domain_sub Dfinsupp.subtypeDomain_sub

end FilterAndSubtypeDomain

variable [dec : DecidableEq ι]

include dec

section Basic

variable [∀ i, Zero (β i)]

omit dec

theorem finite_support (f : Π₀ i, β i) : Set.Finite { i | f i ≠ 0 } := by
  classical exact
      Trunc.induction_on f.support' fun xs =>
        (Multiset.toFinset ↑xs).finite_to_set.Subset fun i H =>
          Multiset.mem_toFinset.2 ((xs.Prop i).resolve_right H)
#align dfinsupp.finite_support Dfinsupp.finite_support

include dec

/-- Create an element of `Π₀ i, β i` from a finset `s` and a function `x`
defined on this `finset`. -/
def mk (s : Finset ι) (x : ∀ i : (↑s : Set ι), β (i : ι)) : Π₀ i, β i :=
  ⟨fun i => if H : i ∈ s then x ⟨i, H⟩ else 0,
    Trunc.mk ⟨s.1, fun i => if H : i ∈ s then Or.inl H else Or.inr <| dif_neg H⟩⟩
#align dfinsupp.mk Dfinsupp.mk

variable {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i} {i : ι}

@[simp]
theorem mk_apply : (mk s x : ∀ i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else 0 :=
  rfl
#align dfinsupp.mk_apply Dfinsupp.mk_apply

theorem mk_of_mem (hi : i ∈ s) : (mk s x : ∀ i, β i) i = x ⟨i, hi⟩ :=
  dif_pos hi
#align dfinsupp.mk_of_mem Dfinsupp.mk_of_mem

theorem mk_of_not_mem (hi : i ∉ s) : (mk s x : ∀ i, β i) i = 0 :=
  dif_neg hi
#align dfinsupp.mk_of_not_mem Dfinsupp.mk_of_not_mem

theorem mk_injective (s : Finset ι) : Function.Injective (@mk ι β _ _ s) :=
  by
  intro x y H
  ext i
  have h1 : (mk s x : ∀ i, β i) i = (mk s y : ∀ i, β i) i := by rw [H]
  cases' i with i hi
  change i ∈ s at hi
  dsimp only [mk_apply, Subtype.coe_mk] at h1
  simpa only [dif_pos hi] using h1
#align dfinsupp.mk_injective Dfinsupp.mk_injective

omit dec

instance unique [∀ i, Subsingleton (β i)] : Unique (Π₀ i, β i) :=
  FunLike.coe_injective.unique
#align dfinsupp.unique Dfinsupp.unique

instance uniqueOfIsEmpty [IsEmpty ι] : Unique (Π₀ i, β i) :=
  FunLike.coe_injective.unique
#align dfinsupp.unique_of_is_empty Dfinsupp.uniqueOfIsEmpty

/-- Given `fintype ι`, `equiv_fun_on_fintype` is the `equiv` between `Π₀ i, β i` and `Π i, β i`.
  (All dependent functions on a finite type are finitely supported.) -/
@[simps apply]
def equivFunOnFintype [Fintype ι] : (Π₀ i, β i) ≃ ∀ i, β i
    where
  toFun := coeFn
  invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun i => Or.inl <| Finset.mem_univ_val _⟩⟩
  left_inv x := coeFn_injective rfl
  right_inv x := rfl
#align dfinsupp.equiv_fun_on_fintype Dfinsupp.equivFunOnFintype

@[simp]
theorem equivFunOnFintype_symm_coe [Fintype ι] (f : Π₀ i, β i) : equivFunOnFintype.symm f = f :=
  Equiv.symm_apply_apply _ _
#align dfinsupp.equiv_fun_on_fintype_symm_coe Dfinsupp.equivFunOnFintype_symm_coe

include dec

/-- The function `single i b : Π₀ i, β i` sends `i` to `b`
and all other points to `0`. -/
def single (i : ι) (b : β i) : Π₀ i, β i :=
  ⟨Pi.single i b,
    Trunc.mk ⟨{i}, fun j => (Decidable.eq_or_ne j i).imp (by simp) fun h => Pi.single_eq_of_ne h _⟩⟩
#align dfinsupp.single Dfinsupp.single

theorem single_eq_pi_single {i b} : ⇑(single i b : Π₀ i, β i) = Pi.single i b :=
  rfl
#align dfinsupp.single_eq_pi_single Dfinsupp.single_eq_pi_single

@[simp]
theorem single_apply {i i' b} :
    (single i b : Π₀ i, β i) i' = if h : i = i' then Eq.recOn h b else 0 :=
  by
  rw [single_eq_pi_single, Pi.single, Function.update]
  simp [@eq_comm _ i i']
#align dfinsupp.single_apply Dfinsupp.single_apply

@[simp]
theorem single_zero (i) : (single i 0 : Π₀ i, β i) = 0 :=
  FunLike.coe_injective <| Pi.single_zero _
#align dfinsupp.single_zero Dfinsupp.single_zero

@[simp]
theorem single_eq_same {i b} : (single i b : Π₀ i, β i) i = b := by
  simp only [single_apply, dif_pos rfl]
#align dfinsupp.single_eq_same Dfinsupp.single_eq_same

theorem single_eq_of_ne {i i' b} (h : i ≠ i') : (single i b : Π₀ i, β i) i' = 0 := by
  simp only [single_apply, dif_neg h]
#align dfinsupp.single_eq_of_ne Dfinsupp.single_eq_of_ne

theorem single_injective {i} : Function.Injective (single i : β i → Π₀ i, β i) := fun x y H =>
  Pi.single_injective β i <| coeFn_injective.eq_iff.mpr H
#align dfinsupp.single_injective Dfinsupp.single_injective

/-- Like `finsupp.single_eq_single_iff`, but with a `heq` due to dependent types -/
theorem single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) :
    Dfinsupp.single i xi = Dfinsupp.single j xj ↔ i = j ∧ HEq xi xj ∨ xi = 0 ∧ xj = 0 :=
  by
  constructor
  · intro h
    by_cases hij : i = j
    · subst hij
      exact Or.inl ⟨rfl, hEq_of_eq (Dfinsupp.single_injective h)⟩
    · have h_coe : ⇑(Dfinsupp.single i xi) = Dfinsupp.single j xj := congr_arg coeFn h
      have hci := congr_fun h_coe i
      have hcj := congr_fun h_coe j
      rw [Dfinsupp.single_eq_same] at hci hcj
      rw [Dfinsupp.single_eq_of_ne (Ne.symm hij)] at hci
      rw [Dfinsupp.single_eq_of_ne hij] at hcj
      exact Or.inr ⟨hci, hcj.symm⟩
  · rintro (⟨rfl, hxi⟩ | ⟨hi, hj⟩)
    · rw [eq_of_hEq hxi]
    · rw [hi, hj, Dfinsupp.single_zero, Dfinsupp.single_zero]
#align dfinsupp.single_eq_single_iff Dfinsupp.single_eq_single_iff

/-- `dfinsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`dfinsupp.single_injective` -/
theorem single_left_injective {b : ∀ i : ι, β i} (h : ∀ i, b i ≠ 0) :
    Function.Injective (fun i => single i (b i) : ι → Π₀ i, β i) := fun a a' H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h _ hb.1).left
#align dfinsupp.single_left_injective Dfinsupp.single_left_injective

@[simp]
theorem single_eq_zero {i : ι} {xi : β i} : single i xi = 0 ↔ xi = 0 :=
  by
  rw [← single_zero i, single_eq_single_iff]
  simp
#align dfinsupp.single_eq_zero Dfinsupp.single_eq_zero

theorem filter_single (p : ι → Prop) [DecidablePred p] (i : ι) (x : β i) :
    (single i x).filter p = if p i then single i x else 0 :=
  by
  ext j
  have := apply_ite (fun x : Π₀ i, β i => x j) (p i) (single i x) 0
  dsimp at this
  rw [filter_apply, this]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · rw [single_eq_of_ne hij, if_t_t, if_t_t]
#align dfinsupp.filter_single Dfinsupp.filter_single

@[simp]
theorem filter_single_pos {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i) :
    (single i x).filter p = single i x := by rw [filter_single, if_pos h]
#align dfinsupp.filter_single_pos Dfinsupp.filter_single_pos

@[simp]
theorem filter_single_neg {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i) :
    (single i x).filter p = 0 := by rw [filter_single, if_neg h]
#align dfinsupp.filter_single_neg Dfinsupp.filter_single_neg

/-- Equality of sigma types is sufficient (but not necessary) to show equality of `dfinsupp`s. -/
theorem single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) :
    Dfinsupp.single i xi = Dfinsupp.single j xj :=
  by
  cases h
  rfl
#align dfinsupp.single_eq_of_sigma_eq Dfinsupp.single_eq_of_sigma_eq

@[simp]
theorem equivFunOnFintype_single [Fintype ι] (i : ι) (m : β i) :
    (@Dfinsupp.equivFunOnFintype ι β _ _) (Dfinsupp.single i m) = Pi.single i m :=
  by
  ext
  simp [Dfinsupp.single_eq_pi_single]
#align dfinsupp.equiv_fun_on_fintype_single Dfinsupp.equivFunOnFintype_single

@[simp]
theorem equivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : β i) :
    (@Dfinsupp.equivFunOnFintype ι β _ _).symm (Pi.single i m) = Dfinsupp.single i m :=
  by
  ext i'
  simp only [← single_eq_pi_single, equiv_fun_on_fintype_symm_coe]
#align dfinsupp.equiv_fun_on_fintype_symm_single Dfinsupp.equivFunOnFintype_symm_single

/-- Redefine `f i` to be `0`. -/
def erase (i : ι) (x : Π₀ i, β i) : Π₀ i, β i :=
  ⟨fun j => if j = i then 0 else x.1 j,
    x.support'.map fun xs => ⟨xs, fun j => (xs.Prop j).imp_right fun H => by simp only [H, if_t_t]⟩⟩
#align dfinsupp.erase Dfinsupp.erase

@[simp]
theorem erase_apply {i j : ι} {f : Π₀ i, β i} : (f.erase i) j = if j = i then 0 else f j :=
  rfl
#align dfinsupp.erase_apply Dfinsupp.erase_apply

@[simp]
theorem erase_same {i : ι} {f : Π₀ i, β i} : (f.erase i) i = 0 := by simp
#align dfinsupp.erase_same Dfinsupp.erase_same

theorem erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' ≠ i) : (f.erase i) i' = f i' := by simp [h]
#align dfinsupp.erase_ne Dfinsupp.erase_ne

theorem piecewise_single_erase (x : Π₀ i, β i) (i : ι) :
    (single i (x i)).piecewise (x.erase i) {i} = x :=
  by
  ext j; rw [piecewise_apply]; split_ifs
  · rw [(id h : j = i), single_eq_same]
  · exact erase_ne h
#align dfinsupp.piecewise_single_erase Dfinsupp.piecewise_single_erase

theorem erase_eq_sub_single {β : ι → Type _} [∀ i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι) :
    f.erase i = f - single i (f i) := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [erase_ne h.symm, single_eq_of_ne h]
#align dfinsupp.erase_eq_sub_single Dfinsupp.erase_eq_sub_single

@[simp]
theorem erase_zero (i : ι) : erase i (0 : Π₀ i, β i) = 0 :=
  ext fun _ => if_t_t _ _
#align dfinsupp.erase_zero Dfinsupp.erase_zero

@[simp]
theorem filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) : f.filter (· ≠ i) = f.erase i :=
  by
  ext1 j
  simp only [Dfinsupp.filter_apply, Dfinsupp.erase_apply, ite_not]
#align dfinsupp.filter_ne_eq_erase Dfinsupp.filter_ne_eq_erase

@[simp]
theorem filter_ne_eq_erase' (f : Π₀ i, β i) (i : ι) : f.filter ((· ≠ ·) i) = f.erase i :=
  by
  rw [← filter_ne_eq_erase f i]
  congr with j
  exact ne_comm
#align dfinsupp.filter_ne_eq_erase' Dfinsupp.filter_ne_eq_erase'

theorem erase_single (j : ι) (i : ι) (x : β i) :
    (single i x).erase j = if i = j then 0 else single i x := by
  rw [← filter_ne_eq_erase, filter_single, ite_not]
#align dfinsupp.erase_single Dfinsupp.erase_single

@[simp]
theorem erase_single_same (i : ι) (x : β i) : (single i x).erase i = 0 := by
  rw [erase_single, if_pos rfl]
#align dfinsupp.erase_single_same Dfinsupp.erase_single_same

@[simp]
theorem erase_single_ne {i j : ι} (x : β i) (h : i ≠ j) : (single i x).erase j = single i x := by
  rw [erase_single, if_neg h]
#align dfinsupp.erase_single_ne Dfinsupp.erase_single_ne

section Update

variable (f : Π₀ i, β i) (i) (b : β i)

/-- Replace the value of a `Π₀ i, β i` at a given point `i : ι` by a given value `b : β i`.
If `b = 0`, this amounts to removing `i` from the support.
Otherwise, `i` is added to it.

This is the (dependent) finitely-supported version of `function.update`. -/
def update : Π₀ i, β i :=
  ⟨Function.update f i b,
    f.support'.map fun s =>
      ⟨i ::ₘ s, fun j => by
        rcases eq_or_ne i j with (rfl | hi)
        · simp
        · obtain hj | (hj : f j = 0) := s.prop j
          · exact Or.inl (Multiset.mem_cons_of_mem hj)
          · exact Or.inr ((Function.update_noteq hi.symm b _).trans hj)⟩⟩
#align dfinsupp.update Dfinsupp.update

variable (j : ι)

@[simp]
theorem coe_update : (f.update i b : ∀ i : ι, β i) = Function.update f i b :=
  rfl
#align dfinsupp.coe_update Dfinsupp.coe_update

@[simp]
theorem update_self : f.update i (f i) = f := by
  ext
  simp
#align dfinsupp.update_self Dfinsupp.update_self

@[simp]
theorem update_eq_erase : f.update i 0 = f.erase i :=
  by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
  · simp [hi.symm]
#align dfinsupp.update_eq_erase Dfinsupp.update_eq_erase

theorem update_eq_single_add_erase {β : ι → Type _} [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = single i b + f.erase i :=
  by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [Function.update_noteq h.symm, h, erase_ne, h.symm]
#align dfinsupp.update_eq_single_add_erase Dfinsupp.update_eq_single_add_erase

theorem update_eq_erase_add_single {β : ι → Type _} [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = f.erase i + single i b :=
  by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [Function.update_noteq h.symm, h, erase_ne, h.symm]
#align dfinsupp.update_eq_erase_add_single Dfinsupp.update_eq_erase_add_single

theorem update_eq_sub_add_single {β : ι → Type _} [∀ i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι)
    (b : β i) : f.update i b = f - single i (f i) + single i b := by
  rw [update_eq_erase_add_single f i b, erase_eq_sub_single f i]
#align dfinsupp.update_eq_sub_add_single Dfinsupp.update_eq_sub_add_single

end Update

end Basic

section AddMonoid

variable [∀ i, AddZeroClass (β i)]

@[simp]
theorem single_add (i : ι) (b₁ b₂ : β i) : single i (b₁ + b₂) = single i b₁ + single i b₂ :=
  ext fun i' => by
    by_cases h : i = i'
    · subst h
      simp only [add_apply, single_eq_same]
    · simp only [add_apply, single_eq_of_ne h, zero_add]
#align dfinsupp.single_add Dfinsupp.single_add

@[simp]
theorem erase_add (i : ι) (f₁ f₂ : Π₀ i, β i) : erase i (f₁ + f₂) = erase i f₁ + erase i f₂ :=
  ext fun _ => by simp [ite_zero_add]
#align dfinsupp.erase_add Dfinsupp.erase_add

variable (β)

/-- `dfinsupp.single` as an `add_monoid_hom`. -/
@[simps]
def singleAddHom (i : ι) : β i →+ Π₀ i, β i
    where
  toFun := single i
  map_zero' := single_zero i
  map_add' := single_add i
#align dfinsupp.single_add_hom Dfinsupp.singleAddHom

/-- `dfinsupp.erase` as an `add_monoid_hom`. -/
@[simps]
def eraseAddHom (i : ι) : (Π₀ i, β i) →+ Π₀ i, β i
    where
  toFun := erase i
  map_zero' := erase_zero i
  map_add' := erase_add i
#align dfinsupp.erase_add_hom Dfinsupp.eraseAddHom

variable {β}

@[simp]
theorem single_neg {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (x : β i) :
    single i (-x) = -single i x :=
  (singleAddHom β i).map_neg x
#align dfinsupp.single_neg Dfinsupp.single_neg

@[simp]
theorem single_sub {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (x y : β i) :
    single i (x - y) = single i x - single i y :=
  (singleAddHom β i).map_sub x y
#align dfinsupp.single_sub Dfinsupp.single_sub

@[simp]
theorem erase_neg {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (f : Π₀ i, β i) :
    (-f).erase i = -f.erase i :=
  (eraseAddHom β i).map_neg f
#align dfinsupp.erase_neg Dfinsupp.erase_neg

@[simp]
theorem erase_sub {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (f g : Π₀ i, β i) :
    (f - g).erase i = f.erase i - g.erase i :=
  (eraseAddHom β i).map_sub f g
#align dfinsupp.erase_sub Dfinsupp.erase_sub

theorem single_add_erase (i : ι) (f : Π₀ i, β i) : single i (f i) + f.erase i = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h <;> simp only [add_apply, single_apply, erase_apply, dif_pos rfl, if_pos, add_zero]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), zero_add]
#align dfinsupp.single_add_erase Dfinsupp.single_add_erase

theorem erase_add_single (i : ι) (f : Π₀ i, β i) : f.erase i + single i (f i) = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h <;> simp only [add_apply, single_apply, erase_apply, dif_pos rfl, if_pos, zero_add]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), add_zero]
#align dfinsupp.erase_add_single Dfinsupp.erase_add_single

protected theorem induction {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (single i b + f)) : p f :=
  by
  cases' f with f s
  induction s using Trunc.induction_on
  cases' s with s H
  induction' s using Multiset.induction_on with i s ih generalizing f
  · have : f = 0 := funext fun i => (H i).resolve_left id
    subst this
    exact h0
  have H2 : p (erase i ⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩) :=
    by
    dsimp only [erase, Trunc.map, Trunc.bind, Trunc.liftOn, Trunc.lift_mk, Function.comp,
      Subtype.coe_mk]
    have H2 : ∀ j, j ∈ s ∨ ite (j = i) 0 (f j) = 0 :=
      by
      intro j
      cases' H j with H2 H2
      · cases' Multiset.mem_cons.1 H2 with H3 H3
        · right
          exact if_pos H3
        · left
          exact H3
      right
      split_ifs <;> [rfl, exact H2]
    have H3 :
      (⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨i ::ₘ s, _⟩⟩ : Π₀ i, β i) =
        ⟨fun j : ι => ite (j = i) 0 (f j), Trunc.mk ⟨s, H2⟩⟩ :=
      ext fun _ => rfl
    rw [H3]
    apply ih
  have H3 : single i _ + _ = (⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩ : Π₀ i, β i) := single_add_erase _ _
  rw [← H3]
  change p (single i (f i) + _)
  cases' Classical.em (f i = 0) with h h
  · rw [h, single_zero, zero_add]
    exact H2
  refine' ha _ _ _ _ h H2
  rw [erase_same]
#align dfinsupp.induction Dfinsupp.induction

theorem induction₂ {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (f + single i b)) : p f :=
  Dfinsupp.induction f h0 fun i b f h1 h2 h3 =>
    have h4 : f + single i b = single i b + f :=
      by
      ext j; by_cases H : i = j
      · subst H
        simp [h1]
      · simp [H]
    Eq.recOn h4 <| ha i b f h1 h2 h3
#align dfinsupp.induction₂ Dfinsupp.induction₂

@[simp]
theorem add_closure_unionᵢ_range_single :
    AddSubmonoid.closure (⋃ i : ι, Set.range (single i : β i → Π₀ i, β i)) = ⊤ :=
  top_unique fun x hx => by
    apply Dfinsupp.induction x
    exact AddSubmonoid.zero_mem _
    exact fun a b f ha hb hf =>
      AddSubmonoid.add_mem _
        (AddSubmonoid.subset_closure <| Set.mem_unionᵢ.2 ⟨a, Set.mem_range_self _⟩) hf
#align dfinsupp.add_closure_Union_range_single Dfinsupp.add_closure_unionᵢ_range_single

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal. -/
theorem add_hom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (single i y) = g (single i y)) : f = g :=
  by
  refine' AddMonoidHom.eq_of_eqOn_denseM add_closure_Union_range_single fun f hf => _
  simp only [Set.mem_unionᵢ, Set.mem_range] at hf
  rcases hf with ⟨x, y, rfl⟩
  apply H
#align dfinsupp.add_hom_ext Dfinsupp.add_hom_ext

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem add_hom_ext' {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ x, f.comp (singleAddHom β x) = g.comp (singleAddHom β x)) : f = g :=
  add_hom_ext fun x => AddMonoidHom.congr_fun (H x)
#align dfinsupp.add_hom_ext' Dfinsupp.add_hom_ext'

end AddMonoid

@[simp]
theorem mk_add [∀ i, AddZeroClass (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i} :
    mk s (x + y) = mk s x + mk s y :=
  ext fun i => by simp only [add_apply, mk_apply] <;> split_ifs <;> [rfl, rw [zero_add]]
#align dfinsupp.mk_add Dfinsupp.mk_add

@[simp]
theorem mk_zero [∀ i, Zero (β i)] {s : Finset ι} : mk s (0 : ∀ i : (↑s : Set ι), β i.1) = 0 :=
  ext fun i => by simp only [mk_apply] <;> split_ifs <;> rfl
#align dfinsupp.mk_zero Dfinsupp.mk_zero

@[simp]
theorem mk_neg [∀ i, AddGroup (β i)] {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} :
    mk s (-x) = -mk s x :=
  ext fun i => by simp only [neg_apply, mk_apply] <;> split_ifs <;> [rfl, rw [neg_zero]]
#align dfinsupp.mk_neg Dfinsupp.mk_neg

@[simp]
theorem mk_sub [∀ i, AddGroup (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i.1} :
    mk s (x - y) = mk s x - mk s y :=
  ext fun i => by simp only [sub_apply, mk_apply] <;> split_ifs <;> [rfl, rw [sub_zero]]
#align dfinsupp.mk_sub Dfinsupp.mk_sub

/-- If `s` is a subset of `ι` then `mk_add_group_hom s` is the canonical additive
group homomorphism from $\prod_{i\in s}\beta_i$ to $\prod_{\mathtt{i : \iota}}\beta_i.$-/
def mkAddGroupHom [∀ i, AddGroup (β i)] (s : Finset ι) : (∀ i : (s : Set ι), β ↑i) →+ Π₀ i : ι, β i
    where
  toFun := mk s
  map_zero' := mk_zero
  map_add' _ _ := mk_add
#align dfinsupp.mk_add_group_hom Dfinsupp.mkAddGroupHom

section

variable [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]

@[simp]
theorem mk_smul {s : Finset ι} (c : γ) (x : ∀ i : (↑s : Set ι), β (i : ι)) :
    mk s (c • x) = c • mk s x :=
  ext fun i => by simp only [smul_apply, mk_apply] <;> split_ifs <;> [rfl, rw [smul_zero]]
#align dfinsupp.mk_smul Dfinsupp.mk_smul

@[simp]
theorem single_smul {i : ι} (c : γ) (x : β i) : single i (c • x) = c • single i x :=
  ext fun i => by
    simp only [smul_apply, single_apply] <;> split_ifs <;> [cases h, rw [smul_zero]] <;> rfl
#align dfinsupp.single_smul Dfinsupp.single_smul

end

section SupportBasic

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

/-- Set `{i | f x ≠ 0}` as a `finset`. -/
def support (f : Π₀ i, β i) : Finset ι :=
  (f.support'.lift fun xs => (Multiset.toFinset ↑xs).filter fun i => f i ≠ 0) <|
    by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, to_fun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨h1, h2⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hy i).resolve_right h2, h2⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨h1, h2⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hx i).resolve_right h2, h2⟩
#align dfinsupp.support Dfinsupp.support

@[simp]
theorem support_mk_subset {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} : (mk s x).support ⊆ s :=
  fun i H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1
#align dfinsupp.support_mk_subset Dfinsupp.support_mk_subset

@[simp]
theorem support_mk'_subset {f : ∀ i, β i} {s : Multiset ι} {h} :
    (mk' f <| Trunc.mk ⟨s, h⟩).support ⊆ s.toFinset := fun i H =>
  Multiset.mem_toFinset.1 <| by simpa using (Finset.mem_filter.1 H).1
#align dfinsupp.support_mk'_subset Dfinsupp.support_mk'_subset

@[simp]
theorem mem_support_to_fun (f : Π₀ i, β i) (i) : i ∈ f.support ↔ f i ≠ 0 :=
  by
  cases' f with f s
  induction s using Trunc.induction_on
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter, Multiset.mem_toFinset, coe_mk']
  exact and_iff_right_of_imp (s.prop i).resolve_right
#align dfinsupp.mem_support_to_fun Dfinsupp.mem_support_to_fun

theorem eq_mk_support (f : Π₀ i, β i) : f = mk f.support fun i => f i :=
  by
  change f = mk f.support fun i => f i.1
  ext i
  by_cases h : f i ≠ 0 <;> [skip, rw [not_not] at h] <;> simp [h]
#align dfinsupp.eq_mk_support Dfinsupp.eq_mk_support

@[simp]
theorem support_zero : (0 : Π₀ i, β i).support = ∅ :=
  rfl
#align dfinsupp.support_zero Dfinsupp.support_zero

theorem mem_support_iff {f : Π₀ i, β i} {i : ι} : i ∈ f.support ↔ f i ≠ 0 :=
  f.mem_support_to_fun _
#align dfinsupp.mem_support_iff Dfinsupp.mem_support_iff

theorem not_mem_support_iff {f : Π₀ i, β i} {i : ι} : i ∉ f.support ↔ f i = 0 :=
  not_iff_comm.1 mem_support_iff.symm
#align dfinsupp.not_mem_support_iff Dfinsupp.not_mem_support_iff

@[simp]
theorem support_eq_empty {f : Π₀ i, β i} : f.support = ∅ ↔ f = 0 :=
  ⟨fun H => ext <| by simpa [Finset.ext_iff] using H, by simp (config := { contextual := true })⟩
#align dfinsupp.support_eq_empty Dfinsupp.support_eq_empty

instance decidableZero : DecidablePred (Eq (0 : Π₀ i, β i)) := fun f =>
  decidable_of_iff _ <| support_eq_empty.trans eq_comm
#align dfinsupp.decidable_zero Dfinsupp.decidableZero

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (i «expr ∉ » s) -/
theorem support_subset_iff {s : Set ι} {f : Π₀ i, β i} :
    ↑f.support ⊆ s ↔ ∀ (i) (_ : i ∉ s), f i = 0 := by
  simp [Set.subset_def] <;> exact forall_congr' fun i => not_imp_comm
#align dfinsupp.support_subset_iff Dfinsupp.support_subset_iff

theorem support_single_ne_zero {i : ι} {b : β i} (hb : b ≠ 0) : (single i b).support = {i} :=
  by
  ext j; by_cases h : i = j
  · subst h
    simp [hb]
  simp [Ne.symm h, h]
#align dfinsupp.support_single_ne_zero Dfinsupp.support_single_ne_zero

theorem support_single_subset {i : ι} {b : β i} : (single i b).support ⊆ {i} :=
  support_mk'_subset
#align dfinsupp.support_single_subset Dfinsupp.support_single_subset

section MapRangeAndZipWith

variable [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

theorem mapRange_def [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] {f : ∀ i, β₁ i → β₂ i}
    {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    mapRange f hf g = mk g.support fun i => f i.1 (g i.1) :=
  by
  ext i
  by_cases h : g i ≠ 0 <;> simp at h <;> simp [h, hf]
#align dfinsupp.map_range_def Dfinsupp.mapRange_def

@[simp]
theorem mapRange_single {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {i : ι} {b : β₁ i} :
    mapRange f hf (single i b) = single i (f i b) :=
  Dfinsupp.ext fun i' => by
    by_cases i = i' <;>
      [·
        subst i'
        simp, simp [h, hf]]
#align dfinsupp.map_range_single Dfinsupp.mapRange_single

variable [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]

theorem support_mapRange {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    (mapRange f hf g).support ⊆ g.support := by simp [map_range_def]
#align dfinsupp.support_map_range Dfinsupp.support_mapRange

theorem zipWith_def {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
    [dec : DecidableEq ι] [∀ i : ι, Zero (β i)] [∀ i : ι, Zero (β₁ i)] [∀ i : ι, Zero (β₂ i)]
    [∀ (i : ι) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i : ι) (x : β₂ i), Decidable (x ≠ 0)]
    {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
    zipWith f hf g₁ g₂ = mk (g₁.support ∪ g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1) :=
  by
  ext i
  by_cases h1 : g₁ i ≠ 0 <;> by_cases h2 : g₂ i ≠ 0 <;> simp only [not_not, Ne.def] at h1 h2 <;>
    simp [h1, h2, hf]
#align dfinsupp.zip_with_def Dfinsupp.zipWith_def

theorem support_zipWith {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i}
    {g₂ : Π₀ i, β₂ i} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  simp [zip_with_def]
#align dfinsupp.support_zip_with Dfinsupp.support_zipWith

end MapRangeAndZipWith

theorem erase_def (i : ι) (f : Π₀ i, β i) : f.erase i = mk (f.support.erase i) fun j => f j.1 :=
  by
  ext j
  by_cases h1 : j = i <;> by_cases h2 : f j ≠ 0 <;> simp at h2 <;> simp [h1, h2]
#align dfinsupp.erase_def Dfinsupp.erase_def

@[simp]
theorem support_erase (i : ι) (f : Π₀ i, β i) : (f.erase i).support = f.support.erase i :=
  by
  ext j
  by_cases h1 : j = i
  simp [h1]
  by_cases h2 : f j ≠ 0 <;> simp at h2 <;> simp [h1, h2]
#align dfinsupp.support_erase Dfinsupp.support_erase

theorem support_update_ne_zero (f : Π₀ i, β i) (i : ι) {b : β i} (h : b ≠ 0) :
    support (f.update i b) = insert i f.support :=
  by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [h]
  · simp [hi.symm]
#align dfinsupp.support_update_ne_zero Dfinsupp.support_update_ne_zero

theorem support_update (f : Π₀ i, β i) (i : ι) (b : β i) [Decidable (b = 0)] :
    support (f.update i b) = if b = 0 then support (f.erase i) else insert i f.support :=
  by
  ext j
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne_zero f _ hb]
#align dfinsupp.support_update Dfinsupp.support_update

section FilterAndSubtypeDomain

variable {p : ι → Prop} [DecidablePred p]

theorem filter_def (f : Π₀ i, β i) : f.filter p = mk (f.support.filter p) fun i => f i.1 := by
  ext i <;> by_cases h1 : p i <;> by_cases h2 : f i ≠ 0 <;> simp at h2 <;> simp [h1, h2]
#align dfinsupp.filter_def Dfinsupp.filter_def

@[simp]
theorem support_filter (f : Π₀ i, β i) : (f.filter p).support = f.support.filter p := by
  ext i <;> by_cases h : p i <;> simp [h]
#align dfinsupp.support_filter Dfinsupp.support_filter

theorem subtypeDomain_def (f : Π₀ i, β i) :
    f.subtypeDomain p = mk (f.support.Subtype p) fun i => f i := by
  ext i <;> by_cases h2 : f i ≠ 0 <;> try simp at h2 <;> dsimp <;> simp [h2]
#align dfinsupp.subtype_domain_def Dfinsupp.subtypeDomain_def

@[simp]
theorem support_subtypeDomain {f : Π₀ i, β i} : (subtypeDomain p f).support = f.support.Subtype p :=
  by
  ext i
  simp
#align dfinsupp.support_subtype_domain Dfinsupp.support_subtypeDomain

end FilterAndSubtypeDomain

end SupportBasic

theorem support_add [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    {g₁ g₂ : Π₀ i, β i} : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
  support_zip_with
#align dfinsupp.support_add Dfinsupp.support_add

@[simp]
theorem support_neg [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    support (-f) = support f := by ext i <;> simp
#align dfinsupp.support_neg Dfinsupp.support_neg

theorem support_smul {γ : Type w} [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (b : γ) (v : Π₀ i, β i) :
    (b • v).support ⊆ v.support :=
  support_map_range
#align dfinsupp.support_smul Dfinsupp.support_smul

instance [∀ i, Zero (β i)] [∀ i, DecidableEq (β i)] : DecidableEq (Π₀ i, β i) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ i ∈ f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ =>
      ext fun i =>
        if h : i ∈ f.support then h₂ i h
        else by
          have hf : f i = 0 := by rwa [mem_support_iff, not_not] at h
          have hg : g i = 0 := by rwa [h₁, mem_support_iff, not_not] at h
          rw [hf, hg],
      by
      rintro rfl
      simp⟩

section Equiv

open Finset

variable {κ : Type _}

/-- Reindexing (and possibly removing) terms of a dfinsupp.-/
noncomputable def comapDomain [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨((Multiset.toFinset ↑s).Preimage h (hh.InjOn _)).val, fun x =>
        (s.Prop (h x)).imp_left fun hx => mem_preimage.mpr <| Multiset.mem_toFinset.mpr hx⟩
#align dfinsupp.comap_domain Dfinsupp.comapDomain

@[simp]
theorem comapDomain_apply [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) (f : Π₀ i, β i)
    (k : κ) : comapDomain h hh f k = f (h k) :=
  rfl
#align dfinsupp.comap_domain_apply Dfinsupp.comapDomain_apply

@[simp]
theorem comapDomain_zero [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) :
    comapDomain h hh (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply, comap_domain_apply, zero_apply]
#align dfinsupp.comap_domain_zero Dfinsupp.comapDomain_zero

@[simp]
theorem comapDomain_add [∀ i, AddZeroClass (β i)] (h : κ → ι) (hh : Function.Injective h)
    (f g : Π₀ i, β i) : comapDomain h hh (f + g) = comapDomain h hh f + comapDomain h hh g :=
  by
  ext
  rw [add_apply, comap_domain_apply, comap_domain_apply, comap_domain_apply, add_apply]
#align dfinsupp.comap_domain_add Dfinsupp.comapDomain_add

@[simp]
theorem comapDomain_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    (h : κ → ι) (hh : Function.Injective h) (r : γ) (f : Π₀ i, β i) :
    comapDomain h hh (r • f) = r • comapDomain h hh f :=
  by
  ext
  rw [smul_apply, comap_domain_apply, smul_apply, comap_domain_apply]
#align dfinsupp.comap_domain_smul Dfinsupp.comapDomain_smul

@[simp]
theorem comapDomain_single [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h)
    (k : κ) (x : β (h k)) : comapDomain h hh (single (h k) x) = single k x :=
  by
  ext
  rw [comap_domain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh.ne hik.symm)]
#align dfinsupp.comap_domain_single Dfinsupp.comapDomain_single

omit dec

/-- A computable version of comap_domain when an explicit left inverse is provided.-/
def comapDomain' [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.map h' s, fun x =>
        (s.Prop (h x)).imp_left fun hx => Multiset.mem_map.mpr ⟨_, hx, hh' _⟩⟩
#align dfinsupp.comap_domain' Dfinsupp.comapDomain'

@[simp]
theorem comapDomain'_apply [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (f : Π₀ i, β i) (k : κ) : comapDomain' h hh' f k = f (h k) :=
  rfl
#align dfinsupp.comap_domain'_apply Dfinsupp.comapDomain'_apply

@[simp]
theorem comapDomain'_zero [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) : comapDomain' h hh' (0 : Π₀ i, β i) = 0 :=
  by
  ext
  rw [zero_apply, comap_domain'_apply, zero_apply]
#align dfinsupp.comap_domain'_zero Dfinsupp.comapDomain'_zero

@[simp]
theorem comapDomain'_add [∀ i, AddZeroClass (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (f g : Π₀ i, β i) :
    comapDomain' h hh' (f + g) = comapDomain' h hh' f + comapDomain' h hh' g :=
  by
  ext
  rw [add_apply, comap_domain'_apply, comap_domain'_apply, comap_domain'_apply, add_apply]
#align dfinsupp.comap_domain'_add Dfinsupp.comapDomain'_add

@[simp]
theorem comapDomain'_smul [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)]
    (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h) (r : γ) (f : Π₀ i, β i) :
    comapDomain' h hh' (r • f) = r • comapDomain' h hh' f :=
  by
  ext
  rw [smul_apply, comap_domain'_apply, smul_apply, comap_domain'_apply]
#align dfinsupp.comap_domain'_smul Dfinsupp.comapDomain'_smul

@[simp]
theorem comapDomain'_single [DecidableEq ι] [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι)
    {h' : ι → κ} (hh' : Function.LeftInverse h' h) (k : κ) (x : β (h k)) :
    comapDomain' h hh' (single (h k) x) = single k x :=
  by
  ext
  rw [comap_domain'_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh'.injective.ne hik.symm)]
#align dfinsupp.comap_domain'_single Dfinsupp.comapDomain'_single

/-- Reindexing terms of a dfinsupp.

This is the dfinsupp version of `equiv.Pi_congr_left'`. -/
@[simps apply]
def equivCongrLeft [∀ i, Zero (β i)] (h : ι ≃ κ) : (Π₀ i, β i) ≃ Π₀ k, β (h.symm k)
    where
  toFun := comapDomain' h.symm h.right_inv
  invFun f :=
    mapRange (fun i => Equiv.cast <| congr_arg β <| h.symm_apply_apply i)
      (fun i =>
        (Equiv.cast_eq_iff_hEq _).mpr <| by
          convert HEq.rfl
          repeat' exact (h.symm_apply_apply i).symm)
      (@comapDomain' _ _ _ _ h _ h.left_inv f)
  left_inv f := by
    ext i
    rw [map_range_apply, comap_domain'_apply, comap_domain'_apply, Equiv.cast_eq_iff_hEq,
      h.symm_apply_apply]
  right_inv f := by
    ext k
    rw [comap_domain'_apply, map_range_apply, comap_domain'_apply, Equiv.cast_eq_iff_hEq,
      h.apply_symm_apply]
#align dfinsupp.equiv_congr_left Dfinsupp.equivCongrLeft

section Curry

variable {α : ι → Type _} {δ : ∀ i, α i → Type v}

-- lean can't find these instances
instance hasAdd₂ [∀ i j, AddZeroClass (δ i j)] : Add (Π₀ (i : ι) (j : α i), δ i j) :=
  @Dfinsupp.hasAdd ι (fun i => Π₀ j, δ i j) _
#align dfinsupp.has_add₂ Dfinsupp.hasAdd₂

instance addZeroClass₂ [∀ i j, AddZeroClass (δ i j)] : AddZeroClass (Π₀ (i : ι) (j : α i), δ i j) :=
  @Dfinsupp.addZeroClass ι (fun i => Π₀ j, δ i j) _
#align dfinsupp.add_zero_class₂ Dfinsupp.addZeroClass₂

instance addMonoid₂ [∀ i j, AddMonoid (δ i j)] : AddMonoid (Π₀ (i : ι) (j : α i), δ i j) :=
  @Dfinsupp.addMonoid ι (fun i => Π₀ j, δ i j) _
#align dfinsupp.add_monoid₂ Dfinsupp.addMonoid₂

instance distribMulAction₂ [Monoid γ] [∀ i j, AddMonoid (δ i j)]
    [∀ i j, DistribMulAction γ (δ i j)] : DistribMulAction γ (Π₀ (i : ι) (j : α i), δ i j) :=
  @Dfinsupp.distribMulAction ι _ (fun i => Π₀ j, δ i j) _ _ _
#align dfinsupp.distrib_mul_action₂ Dfinsupp.distribMulAction₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The natural map between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`.  -/
noncomputable def sigmaCurry [∀ i j, Zero (δ i j)] (f : Π₀ i : Σi, _, δ i.1 i.2) :
    Π₀ (i) (j), δ i j := by
  classical exact
      mk (f.support.image fun i => i.1) fun i =>
        mk (f.support.preimage (Sigma.mk i) <| sigma_mk_injective.inj_on _) fun j => f ⟨i, j⟩
#align dfinsupp.sigma_curry Dfinsupp.sigmaCurry

@[simp]
theorem sigmaCurry_apply [∀ i j, Zero (δ i j)] (f : Π₀ i : Σi, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ := by
  dsimp only [sigma_curry]; by_cases h : f ⟨i, j⟩ = 0
  · rw [h, mk_apply]
    split_ifs
    · rw [mk_apply]
      split_ifs
      · exact h
      · rfl
    · rfl
  · rw [mk_of_mem, mk_of_mem]
    · rfl
    · rw [mem_preimage, mem_support_to_fun]
      exact h
    · rw [mem_image]
      refine' ⟨⟨i, j⟩, _, rfl⟩
      rw [mem_support_to_fun]
      exact h
#align dfinsupp.sigma_curry_apply Dfinsupp.sigmaCurry_apply

@[simp]
theorem sigmaCurry_zero [∀ i j, Zero (δ i j)] : sigmaCurry (0 : Π₀ i : Σi, _, δ i.1 i.2) = 0 :=
  by
  ext (i j)
  rw [sigma_curry_apply]
  rfl
#align dfinsupp.sigma_curry_zero Dfinsupp.sigmaCurry_zero

@[simp]
theorem sigmaCurry_add [∀ i j, AddZeroClass (δ i j)] (f g : Π₀ i : Σi, α i, δ i.1 i.2) :
    @sigmaCurry _ _ δ _ (f + g) = @sigmaCurry _ _ δ _ f + @sigmaCurry ι α δ _ g :=
  by
  ext (i j)
  rw [@add_apply _ (fun i => Π₀ j, δ i j) _ (sigma_curry _), add_apply, sigma_curry_apply,
    sigma_curry_apply, sigma_curry_apply, add_apply]
#align dfinsupp.sigma_curry_add Dfinsupp.sigmaCurry_add

@[simp]
theorem sigmaCurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)] [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ i : Σi, α i, δ i.1 i.2) :
    @sigmaCurry _ _ δ _ (r • f) = r • @sigmaCurry _ _ δ _ f :=
  by
  ext (i j)
  rw [@smul_apply _ _ (fun i => Π₀ j, δ i j) _ _ _ _ (sigma_curry _), smul_apply, sigma_curry_apply,
    sigma_curry_apply, smul_apply]
#align dfinsupp.sigma_curry_smul Dfinsupp.sigmaCurry_smul

@[simp]
theorem sigmaCurry_single [∀ i j, Zero (δ i j)] (ij : Σi, α i) (x : δ ij.1 ij.2) :
    @sigmaCurry _ _ _ _ (single ij x) = single ij.1 (single ij.2 x : Π₀ j, δ ij.1 j) :=
  by
  obtain ⟨i, j⟩ := ij
  ext (i' j')
  dsimp only
  rw [sigma_curry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j j'
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne, single_eq_of_ne hj]
      simpa using hj
  · rw [single_eq_of_ne, single_eq_of_ne hi, zero_apply]
    simpa using hi
#align dfinsupp.sigma_curry_single Dfinsupp.sigmaCurry_single

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The natural map between `Π₀ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`.-/
noncomputable def sigmaUncurry [∀ i j, Zero (δ i j)] (f : Π₀ (i) (j), δ i j) :
    Π₀ i : Σi, _, δ i.1 i.2 where
  toFun i := f i.1 i.2
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.bind ↑s fun i => ((f i).support.map ⟨Sigma.mk i, sigma_mk_injective⟩).val, fun i =>
        by
        simp_rw [Multiset.mem_bind, map_val, Multiset.mem_map, Function.Embedding.coeFn_mk, ←
          Finset.mem_def, mem_support_to_fun]
        obtain hi | (hi : f i.1 = 0) := s.prop i.1
        · by_cases hi' : f i.1 i.2 = 0
          · exact Or.inr hi'
          · exact Or.inl ⟨_, hi, i.2, hi', Sigma.eta _⟩
        · right
          rw [hi, zero_apply]⟩
#align dfinsupp.sigma_uncurry Dfinsupp.sigmaUncurry

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_apply [∀ i j, Zero (δ i j)] (f : Π₀ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j :=
  rfl
#align dfinsupp.sigma_uncurry_apply Dfinsupp.sigmaUncurry_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_zero [∀ i j, Zero (δ i j)] : sigmaUncurry (0 : Π₀ (i) (j), δ i j) = 0 :=
  rfl
#align dfinsupp.sigma_uncurry_zero Dfinsupp.sigmaUncurry_zero

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_add [∀ i j, AddZeroClass (δ i j)] (f g : Π₀ (i) (j), δ i j) :
    sigmaUncurry (f + g) = sigmaUncurry f + sigmaUncurry g :=
  coeFn_injective rfl
#align dfinsupp.sigma_uncurry_add Dfinsupp.sigmaUncurry_add

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem sigmaUncurry_smul [Monoid γ] [∀ i j, AddMonoid (δ i j)] [∀ i j, DistribMulAction γ (δ i j)]
    (r : γ) (f : Π₀ (i) (j), δ i j) : sigmaUncurry (r • f) = r • sigmaUncurry f :=
  coeFn_injective rfl
#align dfinsupp.sigma_uncurry_smul Dfinsupp.sigmaUncurry_smul

@[simp]
theorem sigmaUncurry_single [∀ i j, Zero (δ i j)] (i) (j : α i) (x : δ i j) :
    sigmaUncurry (single i (single j x : Π₀ j : α i, δ i j)) = single ⟨i, j⟩ x :=
  by
  ext ⟨i', j'⟩
  dsimp only
  rw [sigma_uncurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j j'
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hj, single_eq_of_ne]
      simpa using hj
  · rw [single_eq_of_ne hi, single_eq_of_ne, zero_apply]
    simpa using hi
#align dfinsupp.sigma_uncurry_single Dfinsupp.sigmaUncurry_single

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The natural bijection between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`.

This is the dfinsupp version of `equiv.Pi_curry`. -/
noncomputable def sigmaCurryEquiv [∀ i j, Zero (δ i j)] :
    (Π₀ i : Σi, _, δ i.1 i.2) ≃ Π₀ (i) (j), δ i j
    where
  toFun := sigmaCurry
  invFun := sigmaUncurry
  left_inv f := by
    ext ⟨i, j⟩
    rw [sigma_uncurry_apply, sigma_curry_apply]
  right_inv f := by
    ext (i j)
    rw [sigma_curry_apply, sigma_uncurry_apply]
#align dfinsupp.sigma_curry_equiv Dfinsupp.sigmaCurryEquiv

end Curry

variable {α : Option ι → Type v}

/-- Adds a term to a dfinsupp, making a dfinsupp indexed by an `option`.

This is the dfinsupp version of `option.rec`. -/
def extendWith [∀ i, Zero (α i)] (a : α none) (f : Π₀ i, α (some i)) : Π₀ i, α i
    where
  toFun := Option.rec a f
  support' :=
    f.support'.map fun s =>
      ⟨none ::ₘ Multiset.map some s, fun i =>
        Option.rec (Or.inl <| Multiset.mem_cons_self _ _)
          (fun i =>
            (s.Prop i).imp_left fun h => Multiset.mem_cons_of_mem <| Multiset.mem_map_of_mem _ h)
          i⟩
#align dfinsupp.extend_with Dfinsupp.extendWith

@[simp]
theorem extendWith_none [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) :
    f.extendWith a none = a :=
  rfl
#align dfinsupp.extend_with_none Dfinsupp.extendWith_none

@[simp]
theorem extendWith_some [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) (i : ι) :
    f.extendWith a (some i) = f i :=
  rfl
#align dfinsupp.extend_with_some Dfinsupp.extendWith_some

@[simp]
theorem extendWith_single_zero [DecidableEq ι] [∀ i, Zero (α i)] (i : ι) (x : α (some i)) :
    (single i x).extendWith 0 = single (some i) x :=
  by
  ext (_ | j)
  · rw [extend_with_none, single_eq_of_ne (Option.some_ne_none _)]
  · rw [extend_with_some]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).Ne hij)]
#align dfinsupp.extend_with_single_zero Dfinsupp.extendWith_single_zero

@[simp]
theorem extendWith_zero [DecidableEq ι] [∀ i, Zero (α i)] (x : α none) :
    (0 : Π₀ i, α (some i)).extendWith x = single none x :=
  by
  ext (_ | j)
  · rw [extend_with_none, single_eq_same]
  · rw [extend_with_some, single_eq_of_ne (Option.some_ne_none _).symm, zero_apply]
#align dfinsupp.extend_with_zero Dfinsupp.extendWith_zero

include dec

/-- Bijection obtained by separating the term of index `none` of a dfinsupp over `option ι`.

This is the dfinsupp version of `equiv.pi_option_equiv_prod`. -/
@[simps]
noncomputable def equivProdDfinsupp [∀ i, Zero (α i)] : (Π₀ i, α i) ≃ α none × Π₀ i, α (some i)
    where
  toFun f := (f none, comapDomain some (Option.some_injective _) f)
  invFun f := f.2.extendWith f.1
  left_inv f := by
    ext i; cases' i with i
    · rw [extend_with_none]
    · rw [extend_with_some, comap_domain_apply]
  right_inv x := by
    dsimp only
    ext
    · exact extend_with_none x.snd _
    · rw [comap_domain_apply, extend_with_some]
#align dfinsupp.equiv_prod_dfinsupp Dfinsupp.equivProdDfinsupp

theorem equivProdDfinsupp_add [∀ i, AddZeroClass (α i)] (f g : Π₀ i, α i) :
    equivProdDfinsupp (f + g) = equivProdDfinsupp f + equivProdDfinsupp g :=
  Prod.ext (add_apply _ _ _) (comapDomain_add _ _ _ _)
#align dfinsupp.equiv_prod_dfinsupp_add Dfinsupp.equivProdDfinsupp_add

theorem equivProdDfinsupp_smul [Monoid γ] [∀ i, AddMonoid (α i)] [∀ i, DistribMulAction γ (α i)]
    (r : γ) (f : Π₀ i, α i) : equivProdDfinsupp (r • f) = r • equivProdDfinsupp f :=
  Prod.ext (smul_apply _ _ _) (comapDomain_smul _ _ _ _)
#align dfinsupp.equiv_prod_dfinsupp_smul Dfinsupp.equivProdDfinsupp_smul

end Equiv

section ProdAndSum

/-- `prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g i (f i)` over the support of `f`."]
def prod [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] (f : Π₀ i, β i)
    (g : ∀ i, β i → γ) : γ :=
  ∏ i in f.support, g i (f i)
#align dfinsupp.prod Dfinsupp.prod
#align dfinsupp.sum Dfinsupp.sum

@[to_additive]
theorem prod_mapRange_index {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [∀ i, Zero (β₁ i)]
    [∀ i, Zero (β₂ i)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]
    [CommMonoid γ] {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : ∀ i, β₂ i → γ}
    (h0 : ∀ i, h i 0 = 1) : (mapRange f hf g).Prod h = g.Prod fun i b => h i (f i b) :=
  by
  rw [map_range_def]
  refine' (Finset.prod_subset support_mk_subset _).trans _
  · intro i h1 h2
    dsimp
    simp [h1] at h2
    dsimp at h2
    simp [h1, h2, h0]
  · refine' Finset.prod_congr rfl _
    intro i h1
    simp [h1]
#align dfinsupp.prod_map_range_index Dfinsupp.prod_mapRange_index
#align dfinsupp.sum_map_range_index Dfinsupp.sum_mapRange_index

@[to_additive]
theorem prod_zero_index [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {h : ∀ i, β i → γ} : (0 : Π₀ i, β i).Prod h = 1 :=
  rfl
#align dfinsupp.prod_zero_index Dfinsupp.prod_zero_index
#align dfinsupp.sum_zero_index Dfinsupp.sum_zero_index

@[to_additive]
theorem prod_single_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {i : ι} {b : β i} {h : ∀ i, β i → γ} (h_zero : h i 0 = 1) : (single i b).Prod h = h i b :=
  by
  by_cases h : b ≠ 0
  · simp [Dfinsupp.prod, support_single_ne_zero h]
  · rw [not_not] at h
    simp [h, prod_zero_index, h_zero]
    rfl
#align dfinsupp.prod_single_index Dfinsupp.prod_single_index
#align dfinsupp.sum_single_index Dfinsupp.sum_single_index

@[to_additive]
theorem prod_neg_index [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {g : Π₀ i, β i} {h : ∀ i, β i → γ} (h0 : ∀ i, h i 0 = 1) :
    (-g).Prod h = g.Prod fun i b => h i (-b) :=
  prod_mapRange_index h0
#align dfinsupp.prod_neg_index Dfinsupp.prod_neg_index
#align dfinsupp.sum_neg_index Dfinsupp.sum_neg_index

omit dec

@[to_additive]
theorem prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type _} {β₂ : ι₂ → Type _} [DecidableEq ι₁]
    [DecidableEq ι₂] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)]
    [∀ (i) (x : β₂ i), Decidable (x ≠ 0)] [CommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i)
    (h : ∀ i, β₁ i → ∀ i, β₂ i → γ) :
    (f₁.Prod fun i₁ x₁ => f₂.Prod fun i₂ x₂ => h i₁ x₁ i₂ x₂) =
      f₂.Prod fun i₂ x₂ => f₁.Prod fun i₁ x₁ => h i₁ x₁ i₂ x₂ :=
  Finset.prod_comm
#align dfinsupp.prod_comm Dfinsupp.prod_comm
#align dfinsupp.sum_comm Dfinsupp.sum_comm

@[simp]
theorem sum_apply {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)] {f : Π₀ i₁, β₁ i₁}
    {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} {i₂ : ι} : (f.Sum g) i₂ = f.Sum fun i₁ b => g i₁ b i₂ :=
  (evalAddMonoidHom i₂ : (Π₀ i, β i) →+ β i₂).map_sum _ f.support
#align dfinsupp.sum_apply Dfinsupp.sum_apply

include dec

theorem support_sum {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} :
    (f.Sum g).support ⊆ f.support.bUnion fun i => (g i (f i)).support :=
  by
  have :
    ∀ i₁ : ι,
      (f.Sum fun (i : ι₁) (b : β₁ i) => (g i b) i₁) ≠ 0 → ∃ i : ι₁, f i ≠ 0 ∧ ¬(g i (f i)) i₁ = 0 :=
    fun i₁ h =>
    let ⟨i, hi, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨i, mem_support_iff.1 hi, Ne⟩
  simpa [Finset.subset_iff, mem_support_iff, Finset.mem_bunionᵢ, sum_apply] using this
#align dfinsupp.support_sum Dfinsupp.support_sum

@[simp, to_additive]
theorem prod_one [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} : (f.Prod fun i b => (1 : γ)) = 1 :=
  Finset.prod_const_one
#align dfinsupp.prod_one Dfinsupp.prod_one
#align dfinsupp.sum_zero Dfinsupp.sum_zero

@[simp, to_additive]
theorem prod_mul [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h₁ h₂ : ∀ i, β i → γ} :
    (f.Prod fun i b => h₁ i b * h₂ i b) = f.Prod h₁ * f.Prod h₂ :=
  Finset.prod_mul_distrib
#align dfinsupp.prod_mul Dfinsupp.prod_mul
#align dfinsupp.sum_add Dfinsupp.sum_add

@[simp, to_additive]
theorem prod_inv [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommGroup γ]
    {f : Π₀ i, β i} {h : ∀ i, β i → γ} : (f.Prod fun i b => (h i b)⁻¹) = (f.Prod h)⁻¹ :=
  ((invMonoidHom : γ →* γ).map_prod _ f.support).symm
#align dfinsupp.prod_inv Dfinsupp.prod_inv
#align dfinsupp.sum_neg Dfinsupp.sum_neg

@[to_additive]
theorem prod_eq_one [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {f : Π₀ i, β i} {h : ∀ i, β i → γ} (hyp : ∀ i, h i (f i) = 1) : f.Prod h = 1 :=
  Finset.prod_eq_one fun i hi => hyp i
#align dfinsupp.prod_eq_one Dfinsupp.prod_eq_one
#align dfinsupp.sum_eq_zero Dfinsupp.sum_eq_zero

theorem smul_sum {α : Type _} [Monoid α] [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] [DistribMulAction α γ] {f : Π₀ i, β i} {h : ∀ i, β i → γ} {c : α} :
    c • f.Sum h = f.Sum fun a b => c • h a b :=
  Finset.smul_sum
#align dfinsupp.smul_sum Dfinsupp.smul_sum

@[to_additive]
theorem prod_add_index [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {f g : Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) : (f + g).Prod h = f.Prod h * g.Prod h :=
  have f_eq : (∏ i in f.support ∪ g.support, h i (f i)) = f.Prod h :=
    (Finset.prod_subset (Finset.subset_union_left _ _) <| by
        simp (config := { contextual := true }) [mem_support_iff, h_zero]).symm
  have g_eq : (∏ i in f.support ∪ g.support, h i (g i)) = g.Prod h :=
    (Finset.prod_subset (Finset.subset_union_right _ _) <| by
        simp (config := { contextual := true }) [mem_support_iff, h_zero]).symm
  calc
    (∏ i in (f + g).support, h i ((f + g) i)) = ∏ i in f.support ∪ g.support, h i ((f + g) i) :=
      Finset.prod_subset support_add <| by
        simp (config := { contextual := true }) [mem_support_iff, h_zero]
    _ = (∏ i in f.support ∪ g.support, h i (f i)) * ∏ i in f.support ∪ g.support, h i (g i) := by
      simp [h_add, Finset.prod_mul_distrib]
    _ = _ := by rw [f_eq, g_eq]
    
#align dfinsupp.prod_add_index Dfinsupp.prod_add_index
#align dfinsupp.sum_add_index Dfinsupp.sum_add_index

@[to_additive]
theorem dfinsupp_prod_mem [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ]
    {S : Type _} [SetLike S γ] [SubmonoidClass S γ] (s : S) (f : Π₀ i, β i) (g : ∀ i, β i → γ)
    (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.Prod g ∈ s :=
  prod_mem fun i hi => h _ <| mem_support_iff.1 hi
#align dfinsupp_prod_mem dfinsupp_prod_mem
#align dfinsupp_sum_mem dfinsupp_sum_mem

@[simp, to_additive]
theorem prod_eq_prod_fintype [Fintype ι] [∀ i, Zero (β i)] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] (v : Π₀ i, β i) [f : ∀ i, β i → γ] (hf : ∀ i, f i 0 = 1) :
    v.Prod f = ∏ i, f i (Dfinsupp.equivFunOnFintype v i) :=
  by
  suffices (∏ i in v.support, f i (v i)) = ∏ i, f i (v i) by simp [Dfinsupp.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i hi' hi
  rw [mem_support_iff, not_not] at hi
  rw [hi, hf]
#align dfinsupp.prod_eq_prod_fintype Dfinsupp.prod_eq_prod_fintype
#align dfinsupp.sum_eq_sum_fintype Dfinsupp.sum_eq_sum_fintype

/--
When summing over an `add_monoid_hom`, the decidability assumption is not needed, and the result is
also an `add_monoid_hom`.
-/
def sumAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) : (Π₀ i, β i) →+ γ
    where
  toFun f :=
    (f.support'.lift fun s => ∑ i in Multiset.toFinset ↑s, φ i (f i)) <|
      by
      rintro ⟨sx, hx⟩ ⟨sy, hy⟩
      dsimp only [Subtype.coe_mk, to_fun_eq_coe] at *
      have H1 : sx.to_finset ∩ sy.to_finset ⊆ sx.to_finset := Finset.inter_subset_left _ _
      have H2 : sx.to_finset ∩ sy.to_finset ⊆ sy.to_finset := Finset.inter_subset_right _ _
      refine'
        (Finset.sum_subset H1 _).symm.trans
          ((Finset.sum_congr rfl _).trans (Finset.sum_subset H2 _))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        rw [(hy i).resolve_left (mt (And.intro H1) H2), AddMonoidHom.map_zero]
      · intro i H1
        rfl
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        simp only [Multiset.mem_toFinset] at H1 H2
        rw [(hx i).resolve_left (mt (fun H3 => And.intro H3 H1) H2), AddMonoidHom.map_zero]
  map_add' := by
    rintro ⟨f, sf, hf⟩ ⟨g, sg, hg⟩
    change (∑ i in _, _) = (∑ i in _, _) + ∑ i in _, _
    simp only [coe_add, coe_mk', Subtype.coe_mk, Pi.add_apply, map_add, Finset.sum_add_distrib]
    congr 1
    · refine' (Finset.sum_subset _ _).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inl
      · intro i H1 H2
        simp only [Multiset.mem_toFinset, Multiset.mem_add] at H2
        rw [(hf i).resolve_left H2, AddMonoidHom.map_zero]
    · refine' (Finset.sum_subset _ _).symm
      · intro i
        simp only [Multiset.mem_toFinset, Multiset.mem_add]
        exact Or.inr
      · intro i H1 H2
        simp only [Multiset.mem_toFinset, Multiset.mem_add] at H2
        rw [(hg i).resolve_left H2, AddMonoidHom.map_zero]
  map_zero' := rfl
#align dfinsupp.sum_add_hom Dfinsupp.sumAddHom

@[simp]
theorem sumAddHom_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) (i)
    (x : β i) : sumAddHom φ (single i x) = φ i x :=
  by
  dsimp [sum_add_hom, single, Trunc.lift_mk]
  rw [Multiset.toFinset_singleton, Finset.sum_singleton, Pi.single_eq_same]
#align dfinsupp.sum_add_hom_single Dfinsupp.sumAddHom_single

@[simp]
theorem sumAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (sumAddHom f).comp (singleAddHom β i) = f i :=
  AddMonoidHom.ext fun x => sumAddHom_single f i x
#align dfinsupp.sum_add_hom_comp_single Dfinsupp.sumAddHom_comp_single

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
theorem sumAddHom_apply [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [AddCommMonoid γ] (φ : ∀ i, β i →+ γ) (f : Π₀ i, β i) : sumAddHom φ f = f.Sum fun x => φ x :=
  by
  rcases f with ⟨f, s, hf⟩
  change (∑ i in _, _) = ∑ i in Finset.filter _ _, _
  rw [Finset.sum_filter, Finset.sum_congr rfl]
  intro i _
  dsimp only [coe_mk', Subtype.coe_mk] at *
  split_ifs
  rfl
  rw [not_not.mp h, AddMonoidHom.map_zero]
#align dfinsupp.sum_add_hom_apply Dfinsupp.sumAddHom_apply

theorem dfinsupp_sumAddHom_mem [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] {S : Type _}
    [SetLike S γ] [AddSubmonoidClass S γ] (s : S) (f : Π₀ i, β i) (g : ∀ i, β i →+ γ)
    (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : Dfinsupp.sumAddHom g f ∈ s := by
  classical
    rw [Dfinsupp.sumAddHom_apply]
    convert dfinsupp_sum_mem _ _ _ _
    · infer_instance
    exact h
#align dfinsupp_sum_add_hom_mem dfinsupp_sumAddHom_mem

/-- The supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom`; that is, every element in the `supr` can be produced from taking a finite
number of non-zero elements of `S i`, coercing them to `γ`, and summing them. -/
theorem AddSubmonoid.supᵢ_eq_mrange_dfinsupp_sumAddHom [AddCommMonoid γ] (S : ι → AddSubmonoid γ) :
    supᵢ S = (Dfinsupp.sumAddHom fun i => (S i).Subtype).mrange :=
  by
  apply le_antisymm
  · apply supᵢ_le _
    intro i y hy
    exact ⟨Dfinsupp.single i ⟨y, hy⟩, Dfinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsupp_sumAddHom_mem _ v _ fun i _ => (le_supᵢ S i : S i ≤ _) (v i).Prop
#align add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom AddSubmonoid.supᵢ_eq_mrange_dfinsupp_sumAddHom

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom` composed with `dfinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `supr` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
theorem AddSubmonoid.bsupr_eq_mrange_dfinsupp_sumAddHom (p : ι → Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) :
    (⨆ (i) (h : p i), S i) =
      ((sumAddHom fun i => (S i).Subtype).comp (filterAddMonoidHom _ p)).mrange :=
  by
  apply le_antisymm
  · refine' supᵢ₂_le fun i hi y hy => ⟨Dfinsupp.single i ⟨y, hy⟩, _⟩
    rw [AddMonoidHom.comp_apply, filter_add_monoid_hom_apply, filter_single_pos _ _ hi]
    exact sum_add_hom_single _ _ _
  · rintro x ⟨v, rfl⟩
    refine' dfinsupp_sumAddHom_mem _ _ _ fun i hi => _
    refine' AddSubmonoid.mem_supᵢ_of_mem i _
    by_cases hp : p i
    · simp [hp]
    · simp [hp]
#align add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom AddSubmonoid.bsupr_eq_mrange_dfinsupp_sumAddHom

theorem AddSubmonoid.mem_supᵢ_iff_exists_dfinsupp [AddCommMonoid γ] (S : ι → AddSubmonoid γ)
    (x : γ) : x ∈ supᵢ S ↔ ∃ f : Π₀ i, S i, Dfinsupp.sumAddHom (fun i => (S i).Subtype) f = x :=
  SetLike.ext_iff.mp (AddSubmonoid.supᵢ_eq_mrange_dfinsupp_sumAddHom S) x
#align add_submonoid.mem_supr_iff_exists_dfinsupp AddSubmonoid.mem_supᵢ_iff_exists_dfinsupp

/-- A variant of `add_submonoid.mem_supr_iff_exists_dfinsupp` with the RHS fully unfolded. -/
theorem AddSubmonoid.mem_supᵢ_iff_exists_dfinsupp' [AddCommMonoid γ] (S : ι → AddSubmonoid γ)
    [∀ (i) (x : S i), Decidable (x ≠ 0)] (x : γ) :
    x ∈ supᵢ S ↔ ∃ f : Π₀ i, S i, (f.Sum fun i xi => ↑xi) = x :=
  by
  rw [AddSubmonoid.mem_supᵢ_iff_exists_dfinsupp]
  simp_rw [sum_add_hom_apply]
  congr
#align add_submonoid.mem_supr_iff_exists_dfinsupp' AddSubmonoid.mem_supᵢ_iff_exists_dfinsupp'

theorem AddSubmonoid.mem_bsupr_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι → AddSubmonoid γ) (x : γ) :
    (x ∈ ⨆ (i) (h : p i), S i) ↔
      ∃ f : Π₀ i, S i, Dfinsupp.sumAddHom (fun i => (S i).Subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (AddSubmonoid.bsupr_eq_mrange_dfinsupp_sumAddHom p S) x
#align add_submonoid.mem_bsupr_iff_exists_dfinsupp AddSubmonoid.mem_bsupr_iff_exists_dfinsupp

omit dec

theorem sumAddHom_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type _} {β₂ : ι₂ → Type _} {γ : Type _}
    [DecidableEq ι₁] [DecidableEq ι₂] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)]
    [AddCommMonoid γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : ∀ i j, β₁ i →+ β₂ j →+ γ) :
    sumAddHom (fun i₂ => sumAddHom (fun i₁ => h i₁ i₂) f₁) f₂ =
      sumAddHom (fun i₁ => sumAddHom (fun i₂ => (h i₁ i₂).flip) f₂) f₁ :=
  by
  obtain ⟨⟨f₁, s₁, h₁⟩, ⟨f₂, s₂, h₂⟩⟩ := f₁, f₂
  simp only [sum_add_hom, AddMonoidHom.finset_sum_apply, Quotient.liftOn_mk, AddMonoidHom.coe_mk,
    AddMonoidHom.flip_apply, Trunc.lift]
  exact Finset.sum_comm
#align dfinsupp.sum_add_hom_comm Dfinsupp.sumAddHom_comm

include dec

/-- The `dfinsupp` version of `finsupp.lift_add_hom`,-/
@[simps apply symmApply]
def liftAddHom [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] : (∀ i, β i →+ γ) ≃+ ((Π₀ i, β i) →+ γ)
    where
  toFun := sumAddHom
  invFun F i := F.comp (singleAddHom β i)
  left_inv x := by
    ext
    simp
  right_inv ψ := by
    ext
    simp
  map_add' F G := by
    ext
    simp
#align dfinsupp.lift_add_hom Dfinsupp.liftAddHom

/-- The `dfinsupp` version of `finsupp.lift_add_hom_single_add_hom`,-/
@[simp]
theorem liftAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    liftAddHom (singleAddHom β) = AddMonoidHom.id (Π₀ i, β i) :=
  liftAddHom.toEquiv.apply_eq_iff_eq_symm_apply.2 rfl
#align dfinsupp.lift_add_hom_single_add_hom Dfinsupp.liftAddHom_singleAddHom

/-- The `dfinsupp` version of `finsupp.lift_add_hom_apply_single`,-/
theorem liftAddHom_apply_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) (x : β i) : liftAddHom f (single i x) = f i x := by simp
#align dfinsupp.lift_add_hom_apply_single Dfinsupp.liftAddHom_apply_single

/-- The `dfinsupp` version of `finsupp.lift_add_hom_comp_single`,-/
theorem liftAddHom_comp_single [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (f : ∀ i, β i →+ γ)
    (i : ι) : (liftAddHom f).comp (singleAddHom β i) = f i := by simp
#align dfinsupp.lift_add_hom_comp_single Dfinsupp.liftAddHom_comp_single

/-- The `dfinsupp` version of `finsupp.comp_lift_add_hom`,-/
theorem comp_liftAddHom {δ : Type _} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) : g.comp (liftAddHom f) = liftAddHom fun a => g.comp (f a) :=
  liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [lift_add_hom_symm_apply, AddMonoidHom.comp_assoc, lift_add_hom_comp_single]
#align dfinsupp.comp_lift_add_hom Dfinsupp.comp_liftAddHom

@[simp]
theorem sumAddHom_zero [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] :
    (sumAddHom fun i => (0 : β i →+ γ)) = 0 :=
  (liftAddHom : (∀ i, β i →+ γ) ≃+ _).map_zero
#align dfinsupp.sum_add_hom_zero Dfinsupp.sumAddHom_zero

@[simp]
theorem sumAddHom_add [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] (g : ∀ i, β i →+ γ)
    (h : ∀ i, β i →+ γ) : (sumAddHom fun i => g i + h i) = sumAddHom g + sumAddHom h :=
  liftAddHom.map_add _ _
#align dfinsupp.sum_add_hom_add Dfinsupp.sumAddHom_add

@[simp]
theorem sumAddHom_singleAddHom [∀ i, AddCommMonoid (β i)] :
    sumAddHom (singleAddHom β) = AddMonoidHom.id _ :=
  lift_add_hom_single_add_hom
#align dfinsupp.sum_add_hom_single_add_hom Dfinsupp.sumAddHom_singleAddHom

theorem comp_sumAddHom {δ : Type _} [∀ i, AddZeroClass (β i)] [AddCommMonoid γ] [AddCommMonoid δ]
    (g : γ →+ δ) (f : ∀ i, β i →+ γ) : g.comp (sumAddHom f) = sumAddHom fun a => g.comp (f a) :=
  comp_liftAddHom _ _
#align dfinsupp.comp_sum_add_hom Dfinsupp.comp_sumAddHom

theorem sum_sub_index [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [AddCommGroup γ]
    {f g : Π₀ i, β i} {h : ∀ i, β i → γ} (h_sub : ∀ i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) :
    (f - g).Sum h = f.Sum h - g.Sum h :=
  by
  have := (lift_add_hom fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g
  rw [lift_add_hom_apply, sum_add_hom_apply, sum_add_hom_apply, sum_add_hom_apply] at this
  exact this
#align dfinsupp.sum_sub_index Dfinsupp.sum_sub_index

@[to_additive]
theorem prod_finset_sum_index {γ : Type w} {α : Type x} [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] {s : Finset α} {g : α → Π₀ i, β i}
    {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (∏ i in s, (g i).Prod h) = (∑ i in s, g i).Prod h := by
  classical exact
      Finset.induction_on s (by simp [prod_zero_index])
        (by simp (config := { contextual := true }) [prod_add_index, h_zero, h_add])
#align dfinsupp.prod_finset_sum_index Dfinsupp.prod_finset_sum_index
#align dfinsupp.sum_finset_sum_index Dfinsupp.sum_finset_sum_index

@[to_additive]
theorem prod_sum_index {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)]
    [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoid γ] {f : Π₀ i₁, β₁ i₁}
    {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) :
    (f.Sum g).Prod h = f.Prod fun i b => (g i b).Prod h :=
  (prod_finset_sum_index h_zero h_add).symm
#align dfinsupp.prod_sum_index Dfinsupp.prod_sum_index
#align dfinsupp.sum_sum_index Dfinsupp.sum_sum_index

@[simp]
theorem sum_single [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    f.Sum single = f :=
  by
  have := AddMonoidHom.congr_fun lift_add_hom_single_add_hom f
  rw [lift_add_hom_apply, sum_add_hom_apply] at this
  exact this
#align dfinsupp.sum_single Dfinsupp.sum_single

@[to_additive]
theorem prod_subtypeDomain_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoid γ] {v : Π₀ i, β i} {p : ι → Prop} [DecidablePred p] {h : ∀ i, β i → γ}
    (hp : ∀ x ∈ v.support, p x) : ((v.subtypeDomain p).Prod fun i b => h i b) = v.Prod h :=
  Finset.prod_bij (fun p _ => p) (by simp) (by simp) (fun ⟨a₀, ha₀⟩ ⟨a₁, ha₁⟩ => by simp)
    fun i hi => ⟨⟨i, hp i hi⟩, by simpa using hi, rfl⟩
#align dfinsupp.prod_subtype_domain_index Dfinsupp.prod_subtypeDomain_index
#align dfinsupp.sum_subtype_domain_index Dfinsupp.sum_subtypeDomain_index

omit dec

theorem subtypeDomain_sum [∀ i, AddCommMonoid (β i)] {s : Finset γ} {h : γ → Π₀ i, β i}
    {p : ι → Prop} [DecidablePred p] :
    (∑ c in s, h c).subtypeDomain p = ∑ c in s, (h c).subtypeDomain p :=
  (subtypeDomainAddMonoidHom β p).map_sum _ s
#align dfinsupp.subtype_domain_sum Dfinsupp.subtypeDomain_sum

theorem subtypeDomain_finsupp_sum {δ : γ → Type x} [DecidableEq γ] [∀ c, Zero (δ c)]
    [∀ (c) (x : δ c), Decidable (x ≠ 0)] [∀ i, AddCommMonoid (β i)] {p : ι → Prop} [DecidablePred p]
    {s : Π₀ c, δ c} {h : ∀ c, δ c → Π₀ i, β i} :
    (s.Sum h).subtypeDomain p = s.Sum fun c d => (h c d).subtypeDomain p :=
  subtype_domain_sum
#align dfinsupp.subtype_domain_finsupp_sum Dfinsupp.subtypeDomain_finsupp_sum

end ProdAndSum

/-! ### Bundled versions of `dfinsupp.map_range`

The names should match the equivalent bundled `finsupp.map_range` definitions.
-/


section MapRange

omit dec

variable [∀ i, AddZeroClass (β i)] [∀ i, AddZeroClass (β₁ i)] [∀ i, AddZeroClass (β₂ i)]

theorem mapRange_add (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0)
    (hf' : ∀ i x y, f i (x + y) = f i x + f i y) (g₁ g₂ : Π₀ i, β₁ i) :
    mapRange f hf (g₁ + g₂) = mapRange f hf g₁ + mapRange f hf g₂ :=
  by
  ext
  simp only [map_range_apply f, coe_add, Pi.add_apply, hf']
#align dfinsupp.map_range_add Dfinsupp.mapRange_add

/-- `dfinsupp.map_range` as an `add_monoid_hom`. -/
@[simps apply]
def mapRange.addMonoidHom (f : ∀ i, β₁ i →+ β₂ i) : (Π₀ i, β₁ i) →+ Π₀ i, β₂ i
    where
  toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
  map_zero' := mapRange_zero _ _
  map_add' := mapRange_add _ _ fun i => (f i).map_add
#align dfinsupp.map_range.add_monoid_hom Dfinsupp.mapRange.addMonoidHom

@[simp]
theorem mapRange.addMonoidHom_id :
    (mapRange.addMonoidHom fun i => AddMonoidHom.id (β₂ i)) = AddMonoidHom.id _ :=
  AddMonoidHom.ext mapRange_id
#align dfinsupp.map_range.add_monoid_hom_id Dfinsupp.mapRange.addMonoidHom_id

theorem mapRange.addMonoidHom_comp (f : ∀ i, β₁ i →+ β₂ i) (f₂ : ∀ i, β i →+ β₁ i) :
    (mapRange.addMonoidHom fun i => (f i).comp (f₂ i)) =
      (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) :=
  AddMonoidHom.ext <| mapRange_comp (fun i x => f i x) (fun i x => f₂ i x) _ _ _
#align dfinsupp.map_range.add_monoid_hom_comp Dfinsupp.mapRange.addMonoidHom_comp

/-- `dfinsupp.map_range.add_monoid_hom` as an `add_equiv`. -/
@[simps apply]
def mapRange.addEquiv (e : ∀ i, β₁ i ≃+ β₂ i) : (Π₀ i, β₁ i) ≃+ Π₀ i, β₂ i :=
  {
    mapRange.addMonoidHom fun i =>
      (e i).toAddMonoidHom with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero
    left_inv := fun x => by
      rw [← map_range_comp] <;>
        · simp_rw [AddEquiv.symm_comp_self]
          simp
    right_inv := fun x => by
      rw [← map_range_comp] <;>
        · simp_rw [AddEquiv.self_comp_symm]
          simp }
#align dfinsupp.map_range.add_equiv Dfinsupp.mapRange.addEquiv

@[simp]
theorem mapRange.addEquiv_refl :
    (map_range.add_equiv fun i => AddEquiv.refl (β₁ i)) = AddEquiv.refl _ :=
  AddEquiv.ext mapRange_id
#align dfinsupp.map_range.add_equiv_refl Dfinsupp.mapRange.addEquiv_refl

theorem mapRange.addEquiv_trans (f : ∀ i, β i ≃+ β₁ i) (f₂ : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) :=
  AddEquiv.ext <| mapRange_comp (fun i x => f₂ i x) (fun i x => f i x) _ _ _
#align dfinsupp.map_range.add_equiv_trans Dfinsupp.mapRange.addEquiv_trans

@[simp]
theorem mapRange.addEquiv_symm (e : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv e).symm = mapRange.addEquiv fun i => (e i).symm :=
  rfl
#align dfinsupp.map_range.add_equiv_symm Dfinsupp.mapRange.addEquiv_symm

end MapRange

end Dfinsupp

/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `add_monoid_hom.map_sum`, `add_monoid_hom.coe_finset_sum`,
and `add_monoid_hom.finset_sum_apply` for `dfinsupp.sum` and `dfinsupp.sum_add_hom` instead of
`finset.sum`.

We provide these for `add_monoid_hom`, `monoid_hom`, `ring_hom`, `add_equiv`, and `mul_equiv`.

Lemmas for `linear_map` and `linear_equiv` are in another file.
-/


section

variable [DecidableEq ι]

namespace MonoidHom

variable {R S : Type _}

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

@[simp, to_additive]
theorem map_dfinsupp_prod [CommMonoid R] [CommMonoid S] (h : R →* S) (f : Π₀ i, β i)
    (g : ∀ i, β i → R) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  h.map_prod _ _
#align monoid_hom.map_dfinsupp_prod MonoidHom.map_dfinsupp_prod
#align add_monoid_hom.map_dfinsupp_sum AddMonoidHom.map_dfinsupp_sum

@[to_additive]
theorem coe_dfinsupp_prod [Monoid R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S) :
    ⇑(f.Prod g) = f.Prod fun a b => g a b :=
  coe_finset_prod _ _
#align monoid_hom.coe_dfinsupp_prod MonoidHom.coe_dfinsupp_prod
#align add_monoid_hom.coe_dfinsupp_sum AddMonoidHom.coe_dfinsupp_sum

@[simp, to_additive]
theorem dfinsupp_prod_apply [Monoid R] [CommMonoid S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S)
    (r : R) : (f.Prod g) r = f.Prod fun a b => (g a b) r :=
  finset_prod_apply _ _ _
#align monoid_hom.dfinsupp_prod_apply MonoidHom.dfinsupp_prod_apply
#align add_monoid_hom.dfinsupp_sum_apply AddMonoidHom.dfinsupp_sum_apply

end MonoidHom

namespace RingHom

variable {R S : Type _}

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

@[simp]
theorem map_dfinsupp_prod [CommSemiring R] [CommSemiring S] (h : R →+* S) (f : Π₀ i, β i)
    (g : ∀ i, β i → R) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  h.map_prod _ _
#align ring_hom.map_dfinsupp_prod RingHom.map_dfinsupp_prod

@[simp]
theorem map_dfinsupp_sum [NonAssocSemiring R] [NonAssocSemiring S] (h : R →+* S) (f : Π₀ i, β i)
    (g : ∀ i, β i → R) : h (f.Sum g) = f.Sum fun a b => h (g a b) :=
  h.map_sum _ _
#align ring_hom.map_dfinsupp_sum RingHom.map_dfinsupp_sum

end RingHom

namespace MulEquiv

variable {R S : Type _}

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

@[simp, to_additive]
theorem map_dfinsupp_prod [CommMonoid R] [CommMonoid S] (h : R ≃* S) (f : Π₀ i, β i)
    (g : ∀ i, β i → R) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  h.map_prod _ _
#align mul_equiv.map_dfinsupp_prod MulEquiv.map_dfinsupp_prod
#align add_equiv.map_dfinsupp_sum AddEquiv.map_dfinsupp_sum

end MulEquiv

/-! The above lemmas, repeated for `dfinsupp.sum_add_hom`. -/


namespace AddMonoidHom

variable {R S : Type _}

open Dfinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R →+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.comp (g i)) f :=
  congr_fun (comp_liftAddHom h g) f
#align add_monoid_hom.map_dfinsupp_sum_add_hom AddMonoidHom.map_dfinsupp_sumAddHom

@[simp]
theorem dfinsupp_sumAddHom_apply [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) (r : R) :
    (sumAddHom g f) r = sumAddHom (fun i => (eval r).comp (g i)) f :=
  map_dfinsupp_sumAddHom (eval r) f g
#align add_monoid_hom.dfinsupp_sum_add_hom_apply AddMonoidHom.dfinsupp_sumAddHom_apply

theorem coe_dfinsupp_sumAddHom [AddZeroClass R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R →+ S) :
    ⇑(sumAddHom g f) = sumAddHom (fun i => (coeFn R S).comp (g i)) f :=
  map_dfinsupp_sumAddHom (coeFn R S) f g
#align add_monoid_hom.coe_dfinsupp_sum_add_hom AddMonoidHom.coe_dfinsupp_sumAddHom

end AddMonoidHom

namespace RingHom

variable {R S : Type _}

open Dfinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [NonAssocSemiring R] [NonAssocSemiring S] [∀ i, AddZeroClass (β i)]
    (h : R →+* S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  AddMonoidHom.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f
#align ring_hom.map_dfinsupp_sum_add_hom RingHom.map_dfinsupp_sumAddHom

end RingHom

namespace AddEquiv

variable {R S : Type _}

open Dfinsupp

@[simp]
theorem map_dfinsupp_sumAddHom [AddCommMonoid R] [AddCommMonoid S] [∀ i, AddZeroClass (β i)]
    (h : R ≃+ S) (f : Π₀ i, β i) (g : ∀ i, β i →+ R) :
    h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  AddMonoidHom.congr_fun (comp_liftAddHom h.toAddMonoidHom g) f
#align add_equiv.map_dfinsupp_sum_add_hom AddEquiv.map_dfinsupp_sumAddHom

end AddEquiv

end

section FiniteInfinite

instance Dfinsupp.fintype {ι : Sort _} {π : ι → Sort _} [DecidableEq ι] [∀ i, Zero (π i)]
    [Fintype ι] [∀ i, Fintype (π i)] : Fintype (Π₀ i, π i) :=
  Fintype.ofEquiv (∀ i, π i) Dfinsupp.equivFunOnFintype.symm
#align dfinsupp.fintype Dfinsupp.fintype

instance Dfinsupp.infinite_of_left {ι : Sort _} {π : ι → Sort _} [∀ i, Nontrivial (π i)]
    [∀ i, Zero (π i)] [Infinite ι] : Infinite (Π₀ i, π i) := by
  letI := Classical.decEq ι <;> choose m hm using fun i => exists_ne (0 : π i) <;>
    exact Infinite.of_injective _ (Dfinsupp.single_left_injective hm)
#align dfinsupp.infinite_of_left Dfinsupp.infinite_of_left

/-- See `dfinsupp.infinite_of_right` for this in instance form, with the drawback that
it needs all `π i` to be infinite. -/
theorem Dfinsupp.infinite_of_exists_right {ι : Sort _} {π : ι → Sort _} (i : ι) [Infinite (π i)]
    [∀ i, Zero (π i)] : Infinite (Π₀ i, π i) :=
  letI := Classical.decEq ι
  Infinite.of_injective (fun j => Dfinsupp.single i j) Dfinsupp.single_injective
#align dfinsupp.infinite_of_exists_right Dfinsupp.infinite_of_exists_right

/-- See `dfinsupp.infinite_of_exists_right` for the case that only one `π ι` is infinite. -/
instance Dfinsupp.infinite_of_right {ι : Sort _} {π : ι → Sort _} [∀ i, Infinite (π i)]
    [∀ i, Zero (π i)] [Nonempty ι] : Infinite (Π₀ i, π i) :=
  Dfinsupp.infinite_of_exists_right (Classical.arbitrary ι)
#align dfinsupp.infinite_of_right Dfinsupp.infinite_of_right

end FiniteInfinite

