/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Notation.Prod

/-!
# Dependent functions with finite support

For a non-dependent version see `Mathlib/Data/Finsupp/Defs.lean`.

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

assert_not_exists Finset.prod Submonoid

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

variable (β) in
/-- A dependent function `Π i, β i` with finite support, with notation `Π₀ i, β i`.

Note that `DFinsupp.support` is the preferred API for accessing the support of the function,
`DFinsupp.support'` is an implementation detail that aids computability; see the implementation
notes in this file for more information. -/
structure DFinsupp [∀ i, Zero (β i)] : Type max u v where mk' ::
  /-- The underlying function of a dependent function with finite support (aka `DFinsupp`). -/
  toFun : ∀ i, β i
  /-- The support of a dependent function with finite support (aka `DFinsupp`). -/
  support' : Trunc { s : Multiset ι // ∀ i, i ∈ s ∨ toFun i = 0 }

/-- `Π₀ i, β i` denotes the type of dependent functions with finite support `DFinsupp β`. -/
notation3 "Π₀ "(...)", "r:(scoped f => DFinsupp f) => r

namespace DFinsupp

section Basic

variable [∀ i, Zero (β i)] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

instance instDFunLike : DFunLike (Π₀ i, β i) ι β :=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ ↦ fun (h : f₁ = f₂) ↦ by
    subst h
    congr
    subsingleton ⟩

@[simp]
theorem toFun_eq_coe (f : Π₀ i, β i) : f.toFun = f :=
  rfl

@[ext]
theorem ext {f g : Π₀ i, β i} (h : ∀ i, f i = g i) : f = g :=
  DFunLike.ext _ _ h

lemma ne_iff {f g : Π₀ i, β i} : f ≠ g ↔ ∃ i, f i ≠ g i := DFunLike.ne_iff

instance : Zero (Π₀ i, β i) :=
  ⟨⟨0, Trunc.mk <| ⟨∅, fun _ => Or.inr rfl⟩⟩⟩

instance : Inhabited (Π₀ i, β i) :=
  ⟨0⟩

@[simp, norm_cast] lemma coe_mk' (f : ∀ i, β i) (s) : ⇑(⟨f, s⟩ : Π₀ i, β i) = f := rfl

@[simp, norm_cast] lemma coe_zero : ⇑(0 : Π₀ i, β i) = 0 := rfl

theorem zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0 :=
  rfl

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

@[simp]
theorem mapRange_apply (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι) :
    mapRange f hf g i = f i (g i) :=
  rfl

@[simp]
theorem mapRange_id (h : ∀ i, id (0 : β₁ i) = 0 := fun _ => rfl) (g : Π₀ i : ι, β₁ i) :
    mapRange (fun i => (id : β₁ i → β₁ i)) h g = g := by
  ext
  rfl

theorem mapRange_comp (f : ∀ i, β₁ i → β₂ i) (f₂ : ∀ i, β i → β₁ i) (hf : ∀ i, f i 0 = 0)
    (hf₂ : ∀ i, f₂ i 0 = 0) (h : ∀ i, (f i ∘ f₂ i) 0 = 0) (g : Π₀ i : ι, β i) :
    mapRange (fun i => f i ∘ f₂ i) h g = mapRange f hf (mapRange f₂ hf₂ g) := by
  ext
  simp only [mapRange_apply]; rfl

@[simp]
theorem mapRange_zero (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) :
    mapRange f hf (0 : Π₀ i, β₁ i) = 0 := by
  ext
  simp only [mapRange_apply, coe_zero, Pi.zero_apply, hf]

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

@[simp]
theorem zipWith_apply (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i)
    (g₂ : Π₀ i, β₂ i) (i : ι) : zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
  rfl

section Piecewise

variable (x y : Π₀ i, β i) (s : Set ι) [∀ i, Decidable (i ∈ s)]

/-- `x.piecewise y s` is the finitely supported function equal to `x` on the set `s`,
  and to `y` on its complement. -/
def piecewise : Π₀ i, β i :=
  zipWith (fun i x y => if i ∈ s then x else y) (fun _ => ite_self 0) x y

theorem piecewise_apply (i : ι) : x.piecewise y s i = if i ∈ s then x i else y i :=
  rfl

@[simp, norm_cast]
theorem coe_piecewise : ⇑(x.piecewise y s) = s.piecewise x y :=
  rfl

end Piecewise

end Basic

section Algebra

instance [∀ i, AddZeroClass (β i)] : Add (Π₀ i, β i) :=
  ⟨zipWith (fun _ => (· + ·)) fun _ => add_zero 0⟩

theorem add_apply [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) :
    (g₁ + g₂) i = g₁ i + g₂ i :=
  rfl

@[simp, norm_cast]
theorem coe_add [∀ i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ + g₂) = g₁ + g₂ :=
  rfl

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

theorem nsmul_apply [∀ i, AddMonoid (β i)] (b : ℕ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl

@[simp, norm_cast]
theorem coe_nsmul [∀ i, AddMonoid (β i)] (b : ℕ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl

instance [∀ i, AddMonoid (β i)] : AddMonoid (Π₀ i, β i) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

/-- Coercion from a `DFinsupp` to a pi type is an `AddMonoidHom`. -/
def coeFnAddMonoidHom [∀ i, AddZeroClass (β i)] : (Π₀ i, β i) →+ ∀ i, β i where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
lemma coeFnAddMonoidHom_apply [∀ i, AddZeroClass (β i)] (v : Π₀ i, β i) : coeFnAddMonoidHom v = v :=
  rfl

instance addCommMonoid [∀ i, AddCommMonoid (β i)] : AddCommMonoid (Π₀ i, β i) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

instance [∀ i, AddGroup (β i)] : Neg (Π₀ i, β i) :=
  ⟨fun f => f.mapRange (fun _ => Neg.neg) fun _ => neg_zero⟩

theorem neg_apply [∀ i, AddGroup (β i)] (g : Π₀ i, β i) (i : ι) : (-g) i = -g i :=
  rfl

@[simp, norm_cast] lemma coe_neg [∀ i, AddGroup (β i)] (g : Π₀ i, β i) : ⇑(-g) = -g := rfl

instance [∀ i, AddGroup (β i)] : Sub (Π₀ i, β i) :=
  ⟨zipWith (fun _ => Sub.sub) fun _ => sub_zero 0⟩

theorem sub_apply [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  rfl

@[simp, norm_cast]
theorem coe_sub [∀ i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  rfl

/-- Note the general `SMul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasIntScalar [∀ i, AddGroup (β i)] : SMul ℤ (Π₀ i, β i) :=
  ⟨fun c v => v.mapRange (fun _ => (c • ·)) fun _ => zsmul_zero _⟩

theorem zsmul_apply [∀ i, AddGroup (β i)] (b : ℤ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl

@[simp, norm_cast]
theorem coe_zsmul [∀ i, AddGroup (β i)] (b : ℤ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl

instance [∀ i, AddGroup (β i)] : AddGroup (Π₀ i, β i) :=
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

instance addCommGroup [∀ i, AddCommGroup (β i)] : AddCommGroup (Π₀ i, β i) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    fun _ _ => coe_zsmul _ _

end Algebra

section FilterAndSubtypeDomain

/-- `Filter p f` is the function which is `f i` if `p i` is true and 0 otherwise. -/
def filter [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (x : Π₀ i, β i) : Π₀ i, β i :=
  ⟨fun i => if p i then x i else 0,
    x.support'.map fun xs =>
      ⟨xs.1, fun i => (xs.prop i).imp_right fun H : x i = 0 => by simp only [H, ite_self]⟩⟩

@[simp]
theorem filter_apply [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (i : ι) (f : Π₀ i, β i) :
    f.filter p i = if p i then f i else 0 :=
  rfl

theorem filter_apply_pos [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : p i) : f.filter p i = f i := by simp only [filter_apply, if_pos h]

theorem filter_apply_neg [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι}
    (h : ¬p i) : f.filter p i = 0 := by simp only [filter_apply, if_neg h]

theorem filter_pos_add_filter_neg [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i) (p : ι → Prop)
    [DecidablePred p] : (f.filter p + f.filter fun i => ¬p i) = f :=
  ext fun i => by
    simp only [add_apply, filter_apply]; split_ifs <;> simp only [add_zero, zero_add]

@[simp]
theorem filter_zero [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] :
    (0 : Π₀ i, β i).filter p = 0 := by
  ext
  simp

@[simp]
theorem filter_add [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f + g).filter p = f.filter p + g.filter p := by
  ext
  simp [ite_add_zero]

variable (γ β)

/-- `DFinsupp.filter` as an `AddMonoidHom`. -/
@[simps]
def filterAddMonoidHom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i, β i) →+ Π₀ i, β i where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' := filter_add p

variable {γ β}

@[simp]
theorem filter_neg [∀ i, AddGroup (β i)] (p : ι → Prop) [DecidablePred p] (f : Π₀ i, β i) :
    (-f).filter p = -f.filter p :=
  (filterAddMonoidHom β p).map_neg f

@[simp]
theorem filter_sub [∀ i, AddGroup (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f - g).filter p = f.filter p - g.filter p :=
  (filterAddMonoidHom β p).map_sub f g

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

@[simp]
theorem subtypeDomain_zero [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] :
    subtypeDomain p (0 : Π₀ i, β i) = 0 :=
  rfl

@[simp]
theorem subtypeDomain_apply [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] {i : Subtype p}
    {v : Π₀ i, β i} : (subtypeDomain p v) i = v i :=
  rfl

@[simp]
theorem subtypeDomain_add [∀ i, AddZeroClass (β i)] {p : ι → Prop} [DecidablePred p]
    (v v' : Π₀ i, β i) : (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  DFunLike.coe_injective rfl

variable (γ β)

/-- `subtypeDomain` but as an `AddMonoidHom`. -/
@[simps]
def subtypeDomainAddMonoidHom [∀ i, AddZeroClass (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i : ι, β i) →+ Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_zero' := subtypeDomain_zero
  map_add' := subtypeDomain_add

variable {γ β}

@[simp]
theorem subtypeDomain_neg [∀ i, AddGroup (β i)] {p : ι → Prop} [DecidablePred p] {v : Π₀ i, β i} :
    (-v).subtypeDomain p = -v.subtypeDomain p :=
  DFunLike.coe_injective rfl

@[simp]
theorem subtypeDomain_sub [∀ i, AddGroup (β i)] {p : ι → Prop} [DecidablePred p]
    {v v' : Π₀ i, β i} : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  DFunLike.coe_injective rfl

end FilterAndSubtypeDomain

section Basic

variable [∀ i, Zero (β i)]

theorem finite_support (f : Π₀ i, β i) : Set.Finite { i | f i ≠ 0 } :=
  Trunc.induction_on f.support' fun xs ↦
    xs.1.finite_toSet.subset fun i H ↦ ((xs.prop i).resolve_right H)

section DecidableEq
variable [DecidableEq ι]

/-- Create an element of `Π₀ i, β i` from a finset `s` and a function `x`
defined on this `Finset`. -/
def mk (s : Finset ι) (x : ∀ i : (↑s : Set ι), β (i : ι)) : Π₀ i, β i :=
  ⟨fun i => if H : i ∈ s then x ⟨i, H⟩ else 0,
    Trunc.mk ⟨s.1, fun i => if H : i ∈ s then Or.inl H else Or.inr <| dif_neg H⟩⟩

variable {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i} {i : ι}

@[simp]
theorem mk_apply : (mk s x : ∀ i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else 0 :=
  rfl

theorem mk_of_mem (hi : i ∈ s) : (mk s x : ∀ i, β i) i = x ⟨i, hi⟩ :=
  dif_pos hi

theorem mk_of_notMem (hi : i ∉ s) : (mk s x : ∀ i, β i) i = 0 :=
  dif_neg hi

@[deprecated (since := "2025-05-23")] alias mk_of_not_mem := mk_of_notMem

theorem mk_injective (s : Finset ι) : Function.Injective (@mk ι β _ _ s) := by
  intro x y H
  ext i
  have h1 : (mk s x : ∀ i, β i) i = (mk s y : ∀ i, β i) i := by rw [H]
  obtain ⟨i, hi : i ∈ s⟩ := i
  dsimp only [mk_apply, Subtype.coe_mk] at h1
  simpa only [dif_pos hi] using h1

end DecidableEq

instance unique [∀ i, Subsingleton (β i)] : Unique (Π₀ i, β i) :=
  DFunLike.coe_injective.unique

instance uniqueOfIsEmpty [IsEmpty ι] : Unique (Π₀ i, β i) :=
  DFunLike.coe_injective.unique

/-- Given `Fintype ι`, `equivFunOnFintype` is the `Equiv` between `Π₀ i, β i` and `Π i, β i`.
  (All dependent functions on a finite type are finitely supported.) -/
@[simps apply]
def equivFunOnFintype [Fintype ι] : (Π₀ i, β i) ≃ ∀ i, β i where
  toFun := (⇑)
  invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl <| Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl

@[simp]
theorem equivFunOnFintype_symm_coe [Fintype ι] (f : Π₀ i, β i) : equivFunOnFintype.symm f = f :=
  Equiv.symm_apply_apply _ _

variable [DecidableEq ι]

/-- The function `single i b : Π₀ i, β i` sends `i` to `b`
and all other points to `0`. -/
def single (i : ι) (b : β i) : Π₀ i, β i :=
  ⟨Pi.single i b,
    Trunc.mk ⟨{i}, fun j => (Decidable.eq_or_ne j i).imp (by simp) fun h => Pi.single_eq_of_ne h _⟩⟩

theorem single_eq_pi_single {i b} : ⇑(single i b : Π₀ i, β i) = Pi.single i b :=
  rfl

@[simp]
theorem single_apply {i i' b} :
    (single i b : Π₀ i, β i) i' = if h : i = i' then Eq.recOn h b else 0 := by
  rw [single_eq_pi_single, Pi.single, Function.update]
  simp [@eq_comm _ i i']

@[simp]
theorem single_zero (i) : (single i 0 : Π₀ i, β i) = 0 :=
  DFunLike.coe_injective <| Pi.single_zero _

theorem single_eq_same {i b} : (single i b : Π₀ i, β i) i = b := by
  simp only [single_apply, dite_eq_ite, ite_true]

theorem single_eq_of_ne {i i' b} (h : i ≠ i') : (single i b : Π₀ i, β i) i' = 0 := by
  simp only [single_apply, dif_neg h]

theorem single_injective {i} : Function.Injective (single i : β i → Π₀ i, β i) := fun _ _ H =>
  Pi.single_injective i <| DFunLike.coe_injective.eq_iff.mpr H

/-- Like `Finsupp.single_eq_single_iff`, but with a `HEq` due to dependent types -/
theorem single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) :
    DFinsupp.single i xi = DFinsupp.single j xj ↔ i = j ∧ xi ≍ xj ∨ xi = 0 ∧ xj = 0 := by
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

/-- `DFinsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`DFinsupp.single_injective` -/
theorem single_left_injective {b : ∀ i : ι, β i} (h : ∀ i, b i ≠ 0) :
    Function.Injective (fun i => single i (b i) : ι → Π₀ i, β i) := fun _ _ H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h _ hb.1).left

@[simp]
theorem single_eq_zero {i : ι} {xi : β i} : single i xi = 0 ↔ xi = 0 := by
  rw [← single_zero i, single_eq_single_iff]
  simp

theorem single_ne_zero {i : ι} {xi : β i} : single i xi ≠ 0 ↔ xi ≠ 0 :=
  single_eq_zero.not

theorem filter_single (p : ι → Prop) [DecidablePred p] (i : ι) (x : β i) :
    (single i x).filter p = if p i then single i x else 0 := by
  ext j
  have := apply_ite (fun x : Π₀ i, β i => x j) (p i) (single i x) 0
  dsimp at this
  rw [filter_apply, this]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · rw [single_eq_of_ne hij, ite_self, ite_self]

@[simp]
theorem filter_single_pos {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i) :
    (single i x).filter p = single i x := by rw [filter_single, if_pos h]

@[simp]
theorem filter_single_neg {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i) :
    (single i x).filter p = 0 := by rw [filter_single, if_neg h]

/-- Equality of sigma types is sufficient (but not necessary) to show equality of `DFinsupp`s. -/
theorem single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) :
    DFinsupp.single i xi = DFinsupp.single j xj := by
  cases h
  rfl

@[simp]
theorem equivFunOnFintype_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp.equivFunOnFintype ι β _ _) (DFinsupp.single i m) = Pi.single i m := by
  ext x
  dsimp [Pi.single, Function.update]
  simp [@eq_comm _ i]

@[simp]
theorem equivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp.equivFunOnFintype ι β _ _).symm (Pi.single i m) = DFinsupp.single i m := by
  ext i'
  simp only [← single_eq_pi_single, equivFunOnFintype_symm_coe]

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

@[simp]
theorem erase_apply {i j : ι} {f : Π₀ i, β i} : (f.erase i) j = if j = i then 0 else f j :=
  rfl

theorem erase_same {i : ι} {f : Π₀ i, β i} : (f.erase i) i = 0 := by simp

theorem erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' ≠ i) : (f.erase i) i' = f i' := by simp [h]

theorem piecewise_single_erase (x : Π₀ i, β i) (i : ι) :
    (single i (x i)).piecewise (x.erase i) {i} = x := by
  ext j; rw [piecewise_apply]; split_ifs with h
  · rw [(id h : j = i), single_eq_same]
  · exact erase_ne h

theorem erase_eq_sub_single {β : ι → Type*} [∀ i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι) :
    f.erase i = f - single i (f i) := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [erase_ne h.symm, single_eq_of_ne h]

@[simp]
theorem erase_zero (i : ι) : erase i (0 : Π₀ i, β i) = 0 :=
  ext fun _ => ite_self _

@[simp]
theorem filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) : f.filter (· ≠ i) = f.erase i := by
  ext1 j
  simp only [DFinsupp.filter_apply, DFinsupp.erase_apply, ite_not]

@[simp]
theorem filter_ne_eq_erase' (f : Π₀ i, β i) (i : ι) : f.filter (i ≠ ·) = f.erase i := by
  rw [← filter_ne_eq_erase f i]
  congr with j
  exact ne_comm

theorem erase_single (j : ι) (i : ι) (x : β i) :
    (single i x).erase j = if i = j then 0 else single i x := by
  rw [← filter_ne_eq_erase, filter_single, ite_not]

@[simp]
theorem erase_single_same (i : ι) (x : β i) : (single i x).erase i = 0 := by
  rw [erase_single, if_pos rfl]

@[simp]
theorem erase_single_ne {i j : ι} (x : β i) (h : i ≠ j) : (single i x).erase j = single i x := by
  rw [erase_single, if_neg h]

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
          · exact Or.inr ((Function.update_of_ne hi.symm b _).trans hj)⟩⟩

variable (j : ι)

@[simp, norm_cast] lemma coe_update : (f.update i b : ∀ i : ι, β i) = Function.update f i b := rfl

@[simp]
theorem update_self : f.update i (f i) = f := by
  ext
  simp

@[simp]
theorem update_eq_erase : f.update i 0 = f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
  · simp [hi.symm]

theorem update_eq_single_add_erase {β : ι → Type*} [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = single i b + f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]

theorem update_eq_erase_add_single {β : ι → Type*} [∀ i, AddZeroClass (β i)] (f : Π₀ i, β i)
    (i : ι) (b : β i) : f.update i b = f.erase i + single i b := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [h, h.symm]

theorem update_eq_sub_add_single {β : ι → Type*} [∀ i, AddGroup (β i)] (f : Π₀ i, β i) (i : ι)
    (b : β i) : f.update i b = f - single i (f i) + single i b := by
  rw [update_eq_erase_add_single f i b, erase_eq_sub_single f i]

end Update

end Basic

section DecidableEq
variable [DecidableEq ι]

section AddMonoid

variable [∀ i, AddZeroClass (β i)]

@[simp]
theorem single_add (i : ι) (b₁ b₂ : β i) : single i (b₁ + b₂) = single i b₁ + single i b₂ :=
  (zipWith_single_single (fun _ => (· + ·)) _ b₁ b₂).symm

@[simp]
theorem erase_add (i : ι) (f₁ f₂ : Π₀ i, β i) : erase i (f₁ + f₂) = erase i f₁ + erase i f₂ :=
  ext fun _ => by simp [ite_zero_add]

variable (β)

/-- `DFinsupp.single` as an `AddMonoidHom`. -/
@[simps]
def singleAddHom (i : ι) : β i →+ Π₀ i, β i where
  toFun := single i
  map_zero' := single_zero i
  map_add' := single_add i

/-- `DFinsupp.erase` as an `AddMonoidHom`. -/
@[simps]
def eraseAddHom (i : ι) : (Π₀ i, β i) →+ Π₀ i, β i where
  toFun := erase i
  map_zero' := erase_zero i
  map_add' := erase_add i

variable {β}

@[simp]
theorem single_neg {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (x : β i) :
    single i (-x) = -single i x :=
  (singleAddHom β i).map_neg x

@[simp]
theorem single_sub {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (x y : β i) :
    single i (x - y) = single i x - single i y :=
  (singleAddHom β i).map_sub x y

@[simp]
theorem erase_neg {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (f : Π₀ i, β i) :
    (-f).erase i = -f.erase i :=
  (eraseAddHom β i).map_neg f

@[simp]
theorem erase_sub {β : ι → Type v} [∀ i, AddGroup (β i)] (i : ι) (f g : Π₀ i, β i) :
    (f - g).erase i = f.erase i - g.erase i :=
  (eraseAddHom β i).map_sub f g

theorem single_add_erase (i : ι) (f : Π₀ i, β i) : single i (f i) + f.erase i = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, add_zero, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), zero_add]

theorem erase_add_single (i : ι) (f : Π₀ i, β i) : f.erase i + single i (f i) = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [add_apply, single_apply, erase_apply, zero_add, dite_eq_ite, if_true]
    else by
      simp only [add_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), add_zero]

protected theorem induction {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (single i b + f)) : p f := by
  obtain ⟨f, s⟩ := f
  induction' s using Trunc.induction_on with s
  obtain ⟨s, H⟩ := s
  induction' s using Multiset.induction_on with i s ih generalizing f
  · have : f = 0 := funext fun i => (H i).resolve_left (Multiset.notMem_zero _)
    subst this
    exact h0
  have H2 : p (erase i ⟨f, Trunc.mk ⟨i ::ₘ s, H⟩⟩) := by
    dsimp only [erase, Trunc.map, Trunc.bind, Trunc.liftOn, Trunc.lift_mk,
      Function.comp, Subtype.coe_mk]
    have H2 : ∀ j, j ∈ s ∨ ite (j = i) 0 (f j) = 0 := by
      intro j
      rcases H j with H2 | H2
      · rcases Multiset.mem_cons.1 H2 with H3 | H3
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
  rcases Classical.em (f i = 0) with h | h
  · rw [h, single_zero, zero_add]
    exact H2
  refine ha _ _ _ ?_ h H2
  rw [erase_same]

theorem induction₂ {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (f + single i b)) : p f :=
  DFinsupp.induction f h0 fun i b f h1 h2 h3 =>
    have h4 : f + single i b = single i b + f := by
      ext j; by_cases H : i = j
      · subst H
        simp [h1]
      · simp [H]
    Eq.recOn h4 <| ha i b f h1 h2 h3

end AddMonoid

@[simp]
theorem mk_add [∀ i, AddZeroClass (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i} :
    mk s (x + y) = mk s x + mk s y :=
  ext fun i => by simp only [add_apply, mk_apply]; split_ifs <;> [rfl; rw [zero_add]]

@[simp]
theorem mk_zero [∀ i, Zero (β i)] {s : Finset ι} : mk s (0 : ∀ i : (↑s : Set ι), β i.1) = 0 :=
  ext fun i => by simp only [mk_apply]; split_ifs <;> rfl

@[simp]
theorem mk_neg [∀ i, AddGroup (β i)] {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} :
    mk s (-x) = -mk s x :=
  ext fun i => by simp only [neg_apply, mk_apply]; split_ifs <;> [rfl; rw [neg_zero]]

@[simp]
theorem mk_sub [∀ i, AddGroup (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i.1} :
    mk s (x - y) = mk s x - mk s y :=
  ext fun i => by simp only [sub_apply, mk_apply]; split_ifs <;> [rfl; rw [sub_zero]]

/-- If `s` is a subset of `ι` then `mk_addGroupHom s` is the canonical additive
group homomorphism from $\prod_{i\in s}\beta_i$ to $\prod_{\mathtt{i : \iota}}\beta_i$. -/
def mkAddGroupHom [∀ i, AddGroup (β i)] (s : Finset ι) :
    (∀ i : (s : Set ι), β ↑i) →+ Π₀ i : ι, β i where
  toFun := mk s
  map_zero' := mk_zero
  map_add' _ _ := mk_add

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

@[simp]
theorem support_mk_subset {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} : (mk s x).support ⊆ s :=
  fun _ H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1

@[simp]
theorem support_mk'_subset {f : ∀ i, β i} {s : Multiset ι} {h} :
    (mk' f <| Trunc.mk ⟨s, h⟩).support ⊆ s.toFinset := fun i H =>
  Multiset.mem_toFinset.1 <| by simpa using (Finset.mem_filter.1 H).1

@[simp]
theorem mem_support_toFun (f : Π₀ i, β i) (i) : i ∈ f.support ↔ f i ≠ 0 := by
  obtain ⟨f, s⟩ := f
  induction' s using Trunc.induction_on with s
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter, Multiset.mem_toFinset, coe_mk']
  exact and_iff_right_of_imp (s.prop i).resolve_right

theorem eq_mk_support (f : Π₀ i, β i) : f = mk f.support fun i => f i := by aesop

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
    simp; rfl

/-- Equivalence between all dependent finitely supported functions `f : Π₀ i, β i` and type
of pairs `⟨s : Finset ι, f : ∀ i : s, {x : β i // x ≠ 0}⟩`. -/
@[simps! apply_fst apply_snd_coe]
def sigmaFinsetFunEquiv : (Π₀ i, β i) ≃ Σ s : Finset ι, ∀ i : s, {x : β i // x ≠ 0} :=
  (Equiv.sigmaFiberEquiv DFinsupp.support).symm.trans (.sigmaCongrRight subtypeSupportEqEquiv)

@[simp]
theorem support_zero : (0 : Π₀ i, β i).support = ∅ :=
  rfl

theorem mem_support_iff {f : Π₀ i, β i} {i : ι} : i ∈ f.support ↔ f i ≠ 0 :=
  f.mem_support_toFun _

theorem notMem_support_iff {f : Π₀ i, β i} {i : ι} : i ∉ f.support ↔ f i = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[deprecated (since := "2025-05-23")] alias not_mem_support_iff := notMem_support_iff

@[simp]
theorem support_eq_empty {f : Π₀ i, β i} : f.support = ∅ ↔ f = 0 :=
  ⟨fun H => ext <| by simpa [Finset.ext_iff] using H, by simp +contextual⟩

instance decidableZero [∀ (i) (x : β i), Decidable (x = 0)] (f : Π₀ i, β i) : Decidable (f = 0) :=
  f.support'.recOnSubsingleton <| fun s =>
    decidable_of_iff (∀ i ∈ s.val, f i = 0) <| by
      constructor
      case mpr => rintro rfl _ _; rfl
      case mp =>
        intro hs₁; ext i
        -- This instance prevent consuming `DecidableEq ι` in the next `by_cases`.
        letI := Classical.propDecidable
        by_cases hs₂ : i ∈ s.val
        case pos => exact hs₁ _ hs₂
        case neg => exact (s.prop i).resolve_left hs₂

theorem support_subset_iff {s : Set ι} {f : Π₀ i, β i} : ↑f.support ⊆ s ↔ ∀ i ∉ s, f i = 0 := by
  simpa [Set.subset_def] using forall_congr' fun i => not_imp_comm

theorem support_single_ne_zero {i : ι} {b : β i} (hb : b ≠ 0) : (single i b).support = {i} := by
  ext j; by_cases h : i = j
  · subst h
    simp [hb]
  simp [Ne.symm h, h]

theorem support_single_subset {i : ι} {b : β i} : (single i b).support ⊆ {i} :=
  support_mk'_subset

section MapRangeAndZipWith

variable [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

theorem mapRange_def [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] {f : ∀ i, β₁ i → β₂ i}
    {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    mapRange f hf g = mk g.support fun i => f i.1 (g i.1) := by
  ext i
  by_cases h : g i ≠ 0 <;> simp at h <;> simp [h, hf]

@[simp]
theorem mapRange_single {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {i : ι} {b : β₁ i} :
    mapRange f hf (single i b) = single i (f i b) :=
  DFinsupp.ext fun i' => by
    by_cases h : i = i'
    · subst i'
      simp
    · simp [h, hf]

omit [DecidableEq ι] in
theorem mapRange_injective (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) :
    Function.Injective (mapRange f hf) ↔ ∀ i, Function.Injective (f i) := by
  classical exact ⟨fun h i x y eq ↦ single_injective (@h (single i x) (single i y) <| by
    simpa using congr_arg _ eq), fun h _ _ eq ↦ DFinsupp.ext fun i ↦ h i congr($eq i)⟩

omit [DecidableEq ι] in
theorem mapRange_surjective (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) :
    Function.Surjective (mapRange f hf) ↔ ∀ i, Function.Surjective (f i) := by
  classical
  refine ⟨fun h i u ↦ ?_, fun h x ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h (single i u)
    exact ⟨x i, by simpa using congr($hx i)⟩
  · obtain ⟨x, s, hs⟩ := x
    have (i : ι) : ∃ u : β₁ i, f i u = x i ∧ (x i = 0 → u = 0) :=
      (eq_or_ne (x i) 0).elim
        (fun h ↦ ⟨0, (hf i).trans h.symm, fun _ ↦ rfl⟩)
        (fun h' ↦ by
          obtain ⟨u, hu⟩ := h i (x i)
          exact ⟨u, hu, fun h'' ↦ (h' h'').elim⟩)
    choose y hy using this
    refine ⟨⟨y, Trunc.mk ⟨s, fun i ↦ ?_⟩⟩, ext fun i ↦ ?_⟩
    · exact (hs i).imp_right (hy i).2
    · simp [(hy i).1]

variable [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]

theorem support_mapRange {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    (mapRange f hf g).support ⊆ g.support := by simp [mapRange_def]

theorem zipWith_def {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
    [dec : DecidableEq ι] [∀ i : ι, Zero (β i)] [∀ i : ι, Zero (β₁ i)] [∀ i : ι, Zero (β₂ i)]
    [∀ (i : ι) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i : ι) (x : β₂ i), Decidable (x ≠ 0)]
    {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
    zipWith f hf g₁ g₂ = mk (g₁.support ∪ g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1) := by
  ext i
  by_cases h1 : g₁ i ≠ 0 <;> by_cases h2 : g₂ i ≠ 0 <;> simp only [not_not, Ne] at h1 h2 <;>
    simp [h1, h2, hf]

theorem support_zipWith {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i}
    {g₂ : Π₀ i, β₂ i} : (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  simp [zipWith_def]

end MapRangeAndZipWith

theorem erase_def (i : ι) (f : Π₀ i, β i) : f.erase i = mk (f.support.erase i) fun j => f j.1 := by
  ext j
  by_cases h1 : j = i <;> by_cases h2 : f j ≠ 0 <;> simp at h2 <;> simp [h1, h2]

@[simp]
theorem support_erase (i : ι) (f : Π₀ i, β i) : (f.erase i).support = f.support.erase i := by
  ext j
  by_cases h1 : j = i
  · simp only [h1, mem_support_toFun, erase_apply, ite_true, ne_eq, not_true,
      Finset.mem_erase, false_and]
  by_cases h2 : f j ≠ 0 <;> simp at h2 <;> simp [h1, h2]

theorem support_update_ne_zero (f : Π₀ i, β i) (i : ι) {b : β i} (h : b ≠ 0) :
    support (f.update i b) = insert i f.support := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [h]
  · simp [hi.symm]

theorem support_update (f : Π₀ i, β i) (i : ι) (b : β i) [Decidable (b = 0)] :
    support (f.update i b) = if b = 0 then support (f.erase i) else insert i f.support := by
  ext j
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne_zero f _ hb]

section FilterAndSubtypeDomain

variable {p : ι → Prop} [DecidablePred p]

theorem filter_def (f : Π₀ i, β i) : f.filter p = mk (f.support.filter p) fun i => f i.1 := by
  ext i; by_cases h1 : p i <;> by_cases h2 : f i ≠ 0 <;> simp at h2 <;> simp [h1, h2]

@[simp]
theorem support_filter (f : Π₀ i, β i) : (f.filter p).support = {x ∈ f.support | p x} := by
  ext i; by_cases h : p i <;> simp [h]

theorem subtypeDomain_def (f : Π₀ i, β i) :
    f.subtypeDomain p = mk (f.support.subtype p) fun i => f i := by
  ext i; by_cases h2 : f i ≠ 0 <;> try simp at h2; simp [h2]

@[simp]
theorem support_subtypeDomain {f : Π₀ i, β i} :
    (subtypeDomain p f).support = f.support.subtype p := by
  ext i
  simp

end FilterAndSubtypeDomain

end SupportBasic

theorem support_add [∀ i, AddZeroClass (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    {g₁ g₂ : Π₀ i, β i} : (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
  support_zipWith

@[simp]
theorem support_neg [∀ i, AddGroup (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    support (-f) = support f := by ext i; simp

instance [∀ i, Zero (β i)] [∀ i, DecidableEq (β i)] : DecidableEq (Π₀ i, β i) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ i ∈ f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ => ext fun i => if h : i ∈ f.support then h₂ i h else by
      have hf : f i = 0 := by rwa [mem_support_iff, not_not] at h
      have hg : g i = 0 := by rwa [h₁, mem_support_iff, not_not] at h
      rw [hf, hg],
     by rintro rfl; simp⟩

end DecidableEq

section Equiv

open Finset

variable {κ κ' : Type*}

/-- Reindexing (and possibly removing) terms of a dfinsupp. -/
noncomputable def comapDomain [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨(s.1.finite_toSet.preimage hh.injOn).toFinset.val, fun x =>
        (s.prop (h x)).imp_left fun hx => (Set.Finite.mem_toFinset _).mpr <| hx⟩

@[simp]
theorem comapDomain_apply [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) (f : Π₀ i, β i)
    (k : κ) : comapDomain h hh f k = f (h k) :=
  rfl

@[simp]
theorem comapDomain_id [∀ i, Zero (β i)] : comapDomain (β := β) id Function.injective_id = id := by
  ext; rfl

@[simp]
theorem comapDomain_comp [∀ i, Zero (β i)]
    (h : κ → ι) (hh : Function.Injective h)
    (h' : κ' → κ) (hh' : Function.Injective h') :
    comapDomain h' hh' ∘ comapDomain h hh = comapDomain (β := β) (h ∘ h') (hh.comp hh') := by
  ext; rfl

@[simp]
theorem comapDomain_comapDomain [∀ i, Zero (β i)]
    (h : κ → ι) (hh : Function.Injective h)
    (h' : κ' → κ) (hh' : Function.Injective h') (f : Π₀ i, β i) :
    comapDomain h' hh' (comapDomain h hh f) = comapDomain (h ∘ h') (hh.comp hh') f := by
  ext; rfl

@[simp]
theorem comapDomain_zero [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) :
    comapDomain h hh (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply, comapDomain_apply, zero_apply]

@[simp]
theorem comapDomain_add [∀ i, AddZeroClass (β i)] (h : κ → ι) (hh : Function.Injective h)
    (f g : Π₀ i, β i) : comapDomain h hh (f + g) = comapDomain h hh f + comapDomain h hh g := by
  ext
  rw [add_apply, comapDomain_apply, comapDomain_apply, comapDomain_apply, add_apply]

@[simp]
theorem comapDomain_single [DecidableEq ι] [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι)
    (hh : Function.Injective h) (k : κ) (x : β (h k)) :
    comapDomain h hh (single (h k) x) = single k x := by
  ext i
  rw [comapDomain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh.ne hik.symm)]

/-- A computable version of comap_domain when an explicit left inverse is provided. -/
def comapDomain' [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (f : Π₀ i, β i) : Π₀ k, β (h k) where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.map h' s.1, fun x =>
        (s.prop (h x)).imp_left fun hx => Multiset.mem_map.mpr ⟨_, hx, hh' _⟩⟩

@[simp]
theorem comapDomain'_apply [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (f : Π₀ i, β i) (k : κ) : comapDomain' h hh' f k = f (h k) :=
  rfl

@[simp]
theorem comapDomain'_id [∀ i, Zero (β i)] :
    comapDomain' (β := β) id (h' := id) (fun _ => rfl) = id := by
  ext; rfl

@[simp]
theorem comapDomain'_comp [∀ i, Zero (β i)]
    (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (h₂ : κ' → κ) {h'₂ : κ → κ'} (hh'₂ : Function.LeftInverse h'₂ h₂):
    comapDomain' h₂ hh'₂ ∘ comapDomain' h hh' = comapDomain' (β := β) (h ∘ h₂) (hh'.comp hh'₂) := by
  ext; rfl

@[simp]
theorem comapDomain'_comapDomain' [∀ i, Zero (β i)]
    (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (h₂ : κ' → κ) {h'₂ : κ → κ'} (hh'₂ : Function.LeftInverse h'₂ h₂) (f : Π₀ i, β i) :
    comapDomain' h₂ hh'₂ (comapDomain' h hh' f) = comapDomain' (h ∘ h₂) (hh'.comp hh'₂) f := by
  ext; rfl

@[simp]
theorem comapDomain'_zero [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) : comapDomain' h hh' (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply, comapDomain'_apply, zero_apply]

@[simp]
theorem comapDomain'_add [∀ i, AddZeroClass (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (f g : Π₀ i, β i) :
    comapDomain' h hh' (f + g) = comapDomain' h hh' f + comapDomain' h hh' g := by
  ext
  rw [add_apply, comapDomain'_apply, comapDomain'_apply, comapDomain'_apply, add_apply]

@[simp]
theorem comapDomain'_single [DecidableEq ι] [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι)
    {h' : ι → κ} (hh' : Function.LeftInverse h' h) (k : κ) (x : β (h k)) :
    comapDomain' h hh' (single (h k) x) = single k x := by
  ext i
  rw [comapDomain'_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh'.injective.ne hik.symm)]

section mapRange.equiv
variable [∀ i, Zero (β i)] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]
/-- `DFinsupp.mapRange` as an equiv.

Note that while `he'` is redundant, it allows `equiv_symm` to fire in both directions, as the
proof is carried around. -/
@[simps apply]
def mapRange.equiv (e : ∀ i, β i ≃ β₁ i)
    (he : ∀ i, e i 0 = 0)
    (he' : ∀ i, (e i).symm 0 = 0 := fun i => (e i).symm_apply_eq.2 (he i).symm) :
    (Π₀ i, β i) ≃ (Π₀ i, β₁ i) where
  toFun := mapRange (fun i x => e i x) he
  invFun := mapRange (fun i x => (e i).symm x) he'
  left_inv x := by rw [← mapRange_comp] <;> simp [Equiv.symm_comp_self]
  right_inv x := by rw [← mapRange_comp] <;> simp [Equiv.self_comp_symm]

@[simp]
theorem mapRange.equiv_refl :
    mapRange.equiv (fun i => Equiv.refl (β i)) (fun _ => rfl) = Equiv.refl (Π₀ i, β i) :=
  Equiv.ext mapRange_id

theorem mapRange.equiv_trans (e : ∀ i, β i ≃ β₁ i) (he he') (e₂ : ∀ i, β₁ i ≃ β₂ i) (he₂ he₂') :
    (mapRange.equiv (fun i => (e i).trans (e₂ i))
          (fun i => by rw [Equiv.trans_apply, he, he₂])
          (fun i => by rw [Equiv.symm_trans_apply, he₂', he']) :
        (Π₀ i, β i) ≃ _) =
      (mapRange.equiv e he he').trans (mapRange.equiv e₂ he₂ he₂') :=
  Equiv.ext <| mapRange_comp _ _ he₂ he (fun i => (congrArg (e₂ i) (he i)).trans (he₂ i))

@[simp]
theorem mapRange.equiv_symm (e : ∀ i, β i ≃ β₁ i) (he he') :
    ((mapRange.equiv e he he').symm : (Π₀ i, β₁ i) ≃ _) =
      mapRange.equiv (fun i => (e i).symm) he' he :=
  Equiv.ext fun _ => rfl

end mapRange.equiv

private def equivCongrLeft_aux_proof [∀ i, Zero (β i)] (h : ι ≃ κ) (i : ι) :
    (Equiv.cast <| congr_arg β <| h.symm_apply_apply i) 0 = 0 :=
  (Equiv.cast_eq_iff_heq _).mpr <| by rw [h.symm_apply_apply]

/-- Reindexing terms of a dfinsupp.

This is the dfinsupp version of `Equiv.piCongrLeft'`. -/
@[simps apply]
def equivCongrLeft [∀ i, Zero (β i)] (h : ι ≃ κ) : (Π₀ i, β i) ≃ Π₀ k, β (h.symm k) where
  toFun := comapDomain' h.symm h.right_inv
  invFun f := mapRange (fun i => _) (equivCongrLeft_aux_proof h) (comapDomain' h h.left_inv f)
  left_inv f := by
    ext i
    rw [mapRange_apply, comapDomain'_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.symm_apply_apply]
  right_inv f := by
    ext k
    rw [comapDomain'_apply, mapRange_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.apply_symm_apply]

@[simp]
theorem equivCongrLeft_refl [∀ i, Zero (β i)] :
    equivCongrLeft (Equiv.refl ι) = Equiv.refl (Π₀ i, β i) := by
  ext; rfl

theorem equivCongrLeft_symm [∀ i, Zero (β i)] (h : ι ≃ κ) :
    (equivCongrLeft h).symm =
      (equivCongrLeft (β := fun i => β (h.symm i)) h.symm).trans
        (mapRange.equiv (fun _ => Equiv.cast _) (equivCongrLeft_aux_proof h)) := by
  ext; rfl

theorem equivCongrLeft_symm' [∀ i, Zero (β i)] (h : κ ≃ ι) :
    equivCongrLeft (β := β) h.symm =
      (mapRange.equiv (fun _ => Equiv.cast _) (equivCongrLeft_aux_proof h.symm)).symm.trans
        (equivCongrLeft (β := fun i => β (h i)) h).symm := by
  ext; simp [equivCongrLeft]

@[simp]
theorem equivCongrLeft_trans [∀ i, Zero (β i)] (h : ι ≃ κ) (h' : κ ≃ κ') :
    equivCongrLeft (h.trans h') =
      (equivCongrLeft h).trans (equivCongrLeft (β := fun _ => β _) h') := by
  ext; rfl

section SigmaCurry

variable {α : ι → Type*} {δ : ∀ i, α i → Type v}

instance hasAdd₂ [∀ i j, AddZeroClass (δ i j)] : Add (Π₀ (i : ι) (j : α i), δ i j) :=
  inferInstance

instance addZeroClass₂ [∀ i j, AddZeroClass (δ i j)] : AddZeroClass (Π₀ (i : ι) (j : α i), δ i j) :=
  inferInstance

instance addMonoid₂ [∀ i j, AddMonoid (δ i j)] : AddMonoid (Π₀ (i : ι) (j : α i), δ i j) :=
  inferInstance

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

@[simp]
theorem extendWith_none [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) :
    f.extendWith a none = a :=
  rfl

@[simp]
theorem extendWith_some [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) (i : ι) :
    f.extendWith a (some i) = f i :=
  rfl

@[simp]
theorem extendWith_single_zero [DecidableEq ι] [∀ i, Zero (α i)] (i : ι) (x : α (some i)) :
    (single i x).extendWith 0 = single (some i) x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_of_ne (Option.some_ne_none _)]
  · rw [extendWith_some]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).ne hij)]

@[simp]
theorem extendWith_zero [DecidableEq ι] [∀ i, Zero (α i)] (x : α none) :
    (0 : Π₀ i, α (some i)).extendWith x = single none x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_same]
  · rw [extendWith_some, single_eq_of_ne (Option.some_ne_none _).symm, zero_apply]

/-- Bijection obtained by separating the term of index `none` of a dfinsupp over `Option ι`.

This is the dfinsupp version of `Equiv.piOptionEquivProd`. -/
@[simps]
noncomputable def equivProdDFinsupp [∀ i, Zero (α i)] :
    (Π₀ i, α i) ≃ α none × Π₀ i, α (some i) where
  toFun f := (f none, comapDomain some (Option.some_injective _) f)
  invFun f := f.2.extendWith f.1
  left_inv f := by
    ext i; obtain - | i := i
    · rw [extendWith_none]
    · rw [extendWith_some, comapDomain_apply]
  right_inv x := by
    dsimp only
    ext
    · exact extendWith_none x.snd _
    · rw [comapDomain_apply, extendWith_some]

theorem equivProdDFinsupp_add [∀ i, AddZeroClass (α i)] (f g : Π₀ i, α i) :
    equivProdDFinsupp (f + g) = equivProdDFinsupp f + equivProdDFinsupp g :=
  Prod.ext (add_apply _ _ _) (comapDomain_add _ (Option.some_injective _) _ _)

end Equiv

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

/-- `DFinsupp.mapRange` as an `AddMonoidHom`. -/
@[simps apply]
def mapRange.addMonoidHom (f : ∀ i, β₁ i →+ β₂ i) : (Π₀ i, β₁ i) →+ Π₀ i, β₂ i where
  toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
  map_zero' := mapRange_zero _ _
  map_add' := mapRange_add _ (fun i => (f i).map_zero) fun i => (f i).map_add

@[simp]
theorem mapRange.addMonoidHom_id :
    (mapRange.addMonoidHom fun i => AddMonoidHom.id (β₂ i)) = AddMonoidHom.id _ :=
  AddMonoidHom.ext mapRange_id

theorem mapRange.addMonoidHom_comp (f : ∀ i, β₁ i →+ β₂ i) (f₂ : ∀ i, β i →+ β₁ i) :
    (mapRange.addMonoidHom fun i => (f i).comp (f₂ i)) =
      (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) := by
  refine AddMonoidHom.ext <| mapRange_comp (fun i x => f i x) (fun i x => f₂ i x) ?_ ?_ ?_
  · intros; apply map_zero
  · intros; apply map_zero
  · intros; dsimp; simp only [map_zero]

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

@[simp]
theorem mapRange.addEquiv_refl :
    (mapRange.addEquiv fun i => AddEquiv.refl (β₁ i)) = AddEquiv.refl _ :=
  AddEquiv.ext mapRange_id

theorem mapRange.addEquiv_trans (f : ∀ i, β i ≃+ β₁ i) (f₂ : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv fun i => (f i).trans (f₂ i)) =
      (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) := by
  refine AddEquiv.ext <| mapRange_comp (fun i x => f₂ i x) (fun i x => f i x) ?_ ?_ ?_
  · intros; apply map_zero
  · intros; apply map_zero
  · intros; dsimp; simp only [map_zero]

@[simp]
theorem mapRange.addEquiv_symm (e : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv e).symm = mapRange.addEquiv fun i => (e i).symm :=
  rfl

end MapRange

end DFinsupp
