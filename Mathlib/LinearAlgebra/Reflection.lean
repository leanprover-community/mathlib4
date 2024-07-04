/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.FiniteSpan

/-!
# Reflections in linear algebra

Given an element `x` in a module `M` together with a linear form `f` on `M` such that `f x = 2`, the
map `y ↦ y - (f y) • x` is an involutive endomorphism of `M`, such that:
 1. the kernel of `f` is fixed,
 2. the point `x ↦ -x`.

Such endomorphisms are often called reflections of the module `M`. When `M` carries an inner product
for which `x` is perpendicular to the kernel of `f`, then (with mild assumptions) the endomorphism
is characterised by properties 1 and 2 above, and is a linear isometry.

## Main definitions / results:

 * `Module.preReflection`: the definition of the map `y ↦ y - (f y) • x`. Its main utility lies in
   the fact that it does not require the assumption `f x = 2`, giving the user freedom to defer
   discharging this proof obligation.
 * `Module.reflection`: the definition of the map `y ↦ y - (f y) • x`. This requires the assumption
   that `f x = 2` but by way of compensation it produces a linear equivalence rather than a mere
   linear map.
 * `Module.Dual.eq_of_preReflection_mapsTo`: a uniqueness result about reflections preserving
   finite spanning sets that is useful in the theory of root data / systems.

## TODO

Related definitions of reflection exists elsewhere in the library. These more specialised
definitions, which require an ambient `InnerProductSpace` structure, are `reflection` (of type
`LinearIsometryEquiv`) and `EuclideanGeometry.reflection` (of type `AffineIsometryEquiv`). We
should connect (or unify) these definitions with `Module.reflecton` defined here.

-/

open Set Function Pointwise
open Module hiding Finite
open Submodule (span)

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : M) (f : Dual R M) (y : M)

namespace Module

/-- Given an element `x` in a module `M` and a linear form `f` on `M`, we define the endomorphism
of `M` for which `y ↦ y - (f y) • x`.

One is typically interested in this endomorphism when `f x = 2`; this definition exists to allow the
user defer discharging this proof obligation. See also `Module.reflection`. -/
def preReflection : End R M :=
  LinearMap.id - f.smulRight x

lemma preReflection_apply :
    preReflection x f y = y - (f y) • x := by
  simp [preReflection]

variable {x f}

lemma preReflection_apply_self (h : f x = 2) :
    preReflection x f x = - x := by
  rw [preReflection_apply, h, two_smul]; abel

lemma involutive_preReflection (h : f x = 2) :
    Involutive (preReflection x f) :=
  fun y ↦ by simp [h, smul_sub, two_smul, preReflection_apply]

lemma preReflection_preReflection (g : Dual R M) (h : f x = 2) :
    preReflection (preReflection x f y) (preReflection f (Dual.eval R M x) g) =
    (preReflection x f) ∘ₗ (preReflection y g) ∘ₗ (preReflection x f) := by
  ext m
  simp only [h, preReflection_apply, mul_comm (g x) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

/-- Given an element `x` in a module `M` and a linear form `f` on `M` for which `f x = 2`, we define
the endomorphism of `M` for which `y ↦ y - (f y) • x`.

It is an involutive endomorphism of `M` fixing the kernel of `f` for which `x ↦ -x`. -/
def reflection (h : f x = 2) : M ≃ₗ[R] M :=
  { preReflection x f, (involutive_preReflection h).toPerm with }

lemma reflection_apply (h : f x = 2) :
    reflection h y = y - (f y) • x :=
  preReflection_apply x f y

@[simp]
lemma reflection_apply_self (h : f x = 2) :
    reflection h x = - x :=
  preReflection_apply_self h

lemma involutive_reflection (h : f x = 2) :
    Involutive (reflection h) :=
  involutive_preReflection h

@[simp]
lemma reflection_symm (h : f x = 2) :
    (reflection h).symm = reflection h :=
  rfl

lemma invOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) :
    InvOn (reflection h) (reflection h) Φ Φ :=
  ⟨fun x _ ↦ involutive_reflection h x, fun x _ ↦ involutive_reflection h x⟩

lemma bijOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) (h' : MapsTo (reflection h) Φ Φ) :
    BijOn (reflection h) Φ Φ :=
  (invOn_reflection_of_mapsTo h).bijOn h' h'

/-- See also `Module.Dual.eq_of_preReflection_mapsTo'` for a variant of this lemma which
applies when `Φ` does not span.

This rather technical-looking lemma exists because it is exactly what is needed to establish various
uniqueness results for root data / systems. One might regard this lemma as lying at the boundary of
linear algebra and combinatorics since the finiteness assumption is the key. -/
lemma Dual.eq_of_preReflection_mapsTo [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} (hx : x ≠ 0) {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    f = g := by
  let u := reflection hg₁ * reflection hf₁
  have hu : u = LinearMap.id (R := R) (M := M) + (f - g).smulRight x := by
    ext y
    simp only [u, reflection_apply, hg₁, two_smul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.id_coe, LinearEquiv.coe_coe, LinearMap.mul_apply, LinearMap.add_apply, id_eq,
      LinearMap.coe_smulRight, LinearMap.sub_apply, map_sub, map_smul, sub_add_cancel_left,
      smul_neg, sub_neg_eq_add, sub_smul]
    abel
  replace hu : ∀ (n : ℕ),
      ↑(u ^ n) = LinearMap.id (R := R) (M := M) + (n : R) • (f - g).smulRight x := by
    intros n
    induction n with
    | zero => simp
    | succ n ih =>
      have : ((f - g).smulRight x).comp ((n : R) • (f - g).smulRight x) = 0 := by
        ext; simp [hf₁, hg₁]
      rw [pow_succ', LinearEquiv.coe_toLinearMap_mul, ih, hu, add_mul, mul_add, mul_add]
      simp_rw [LinearMap.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp, this, add_zero,
        add_assoc, Nat.cast_succ, add_smul, one_smul]
  suffices IsOfFinOrder u by
    obtain ⟨n, hn₀, hn₁⟩ := isOfFinOrder_iff_pow_eq_one.mp this
    replace hn₁ : (↑(u ^ n) : M →ₗ[R] M) = LinearMap.id := LinearEquiv.toLinearMap_inj.mpr hn₁
    simpa [hn₁, hn₀.ne', hx, sub_eq_zero] using hu n
  exact u.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo hΦ₁ hΦ₂ (hg₂.comp hf₂)

/-- This rather technical-looking lemma exists because it is exactly what is needed to establish a
uniqueness result for root data. See the doc string of `Module.Dual.eq_of_preReflection_mapsTo` for
further remarks. -/
lemma Dual.eq_of_preReflection_mapsTo' [CharZero R] [NoZeroSMulDivisors R M]
    {x : M} (hx : x ≠ 0) {Φ : Set M} (hΦ₁ : Φ.Finite) (hx' : x ∈ span R Φ) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    (span R Φ).subtype.dualMap f = (span R Φ).subtype.dualMap g := by
  set Φ' : Set (span R Φ) := range (inclusion <| Submodule.subset_span (R := R) (s := Φ))
  rw [← finite_coe_iff] at hΦ₁
  have hΦ'₁ : Φ'.Finite := finite_range (inclusion Submodule.subset_span)
  have hΦ'₂ : span R Φ' = ⊤ := by simp [Φ']
  let x' : span R Φ := ⟨x, hx'⟩
  have hx' : x' ≠ 0 := Subtype.coe_ne_coe.1 hx
  have this : ∀ {F : Dual R M}, MapsTo (preReflection x F) Φ Φ →
      MapsTo (preReflection x' ((span R Φ).subtype.dualMap F)) Φ' Φ' := by
    intro F hF ⟨y, hy⟩ hy'
    simp only [Φ', range_inclusion, SetLike.coe_sort_coe, mem_setOf_eq] at hy' ⊢
    exact hF hy'
  exact eq_of_preReflection_mapsTo hx' hΦ'₁ hΦ'₂ hf₁ (this hf₂) hg₁ (this hg₂)

variable {y}
variable {g : Dual R M}

lemma eq_of_mapsTo_reflection_of_mem [NoZeroSMulDivisors ℤ M] {Φ : Set M} (hΦ : Φ.Finite)
    (hfx : f x = 2) (hgy : g y = 2) (hgx : g x = 2) (hfy : f y = 2)
    (hxfΦ : MapsTo (preReflection x f) Φ Φ)
    (hygΦ : MapsTo (preReflection y g) Φ Φ)
    (hyΦ : y ∈ Φ) :
    x = y := by
  have : _root_.Finite Φ := hΦ
  set sxy : M ≃ₗ[R] M := (Module.reflection hgy).trans (Module.reflection hfx)
  have hb : BijOn sxy Φ Φ :=
    (bijOn_reflection_of_mapsTo hfx hxfΦ).comp (bijOn_reflection_of_mapsTo hgy hygΦ)
  have hsxy : ∀ n : ℕ, (sxy^[n]) y = y + (2 * n : ℤ) • (x - y) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [iterate_succ', comp_apply, ih, zsmul_sub, map_add, LinearEquiv.trans_apply,
        reflection_apply_self, map_neg, reflection_apply, hfy, two_smul, neg_sub, map_sub,
        map_zsmul, hgx, smul_neg, smul_add, Nat.cast_succ, mul_add, mul_one, add_smul, sxy]
      abel
  set f' : ℕ → Φ := fun n ↦ ⟨(sxy^[n]) y, by
    rw [← IsFixedPt.image_iterate hb.image_eq n]; exact mem_image_of_mem _ hyΦ⟩
  have : ¬ Injective f' := not_injective_infinite_finite f'
  contrapose! this
  intros n m hnm
  rw [Subtype.mk_eq_mk, hsxy, hsxy, add_right_inj, ← sub_eq_zero, ← sub_smul, smul_eq_zero,
    sub_eq_zero, sub_eq_zero] at hnm
  simpa using hnm.resolve_right this

lemma injOn_dualMap_subtype_span_range_range {ι : Type*} [NoZeroSMulDivisors ℤ M]
    {r : ι ↪ M} {c : ι → Dual R M} (hfin : (range r).Finite)
    (h_two : ∀ i, c i (r i) = 2)
    (h_mapsTo : ∀ i, MapsTo (preReflection (r i) (c i)) (range r) (range r)) :
    InjOn (span R (range r)).subtype.dualMap (range c) := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  suffices ∀ k, c i (r k) = c j (r k) by
    rw [← EmbeddingLike.apply_eq_iff_eq r]
    exact eq_of_mapsTo_reflection_of_mem (f := c i) (g := c j) hfin (h_two i) (h_two j)
      (by rw [← this, h_two]) (by rw [this, h_two]) (h_mapsTo i) (h_mapsTo j) (mem_range_self j)
  intro k
  simpa using LinearMap.congr_fun hij ⟨r k, Submodule.subset_span (mem_range_self k)⟩

end Module
