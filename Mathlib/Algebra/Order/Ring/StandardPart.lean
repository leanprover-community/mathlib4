/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Ring.Archimedean
public import Mathlib.Algebra.Ring.Subring.Order
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Order.Quotient
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.Data.Real.CompleteField

/-!
# Standard part function

Given a finite element in a non-archimedean field, the standard part function rounds it to the
unique closest real number. That is, it chops off any infinitesimals.

Let `K` be a linearly ordered field. The subset of finite elements (i.e. those bounded by a natural
number) is a `ValuationSubring`, which means we can construct its residue field
`FiniteResidueField`, roughly corresponding to the finite elements quotiented by infinitesimals.
This field inherits a `LinearOrder` instance, which makes it into an Archimedean linearly ordered
field, meaning we can uniquely embed it in the reals.

Given a finite element of the field, the `ArchimedeanClass.stdPart` function returns the real number
corresponding to this unique embedding. This function generalizes, among other things, the standard
part function on `Hyperreal`.

## TODO

Redefine `Hyperreal.st` in terms of `ArchimedeanClass.stdPart`.

## References

* https://en.wikipedia.org/wiki/Standard_part_function
-/

@[expose] public section

namespace ArchimedeanClass
variable
  {K : Type*} [LinearOrder K] [Field K] [IsOrderedRing K] {x y : K}
  {R : Type*} [LinearOrder R] [CommRing R] [IsOrderedRing R] [Archimedean R]

/-! ### Finite residue field -/

variable (K) in
/-- The valuation subring of elements in non-negative Archimedean classes, i.e. elements bounded by
some natural number. -/
noncomputable def FiniteElement : Type _ :=
  (addValuation K).toValuation.valuationSubring

namespace FiniteElement

instance : CommRing (FiniteElement K) := by
  unfold FiniteElement; infer_instance

instance : IsDomain (FiniteElement K) := by
  unfold FiniteElement; infer_instance

instance : ValuationRing (FiniteElement K) := by
  unfold FiniteElement; infer_instance

instance : LinearOrder (FiniteElement K) := by
  unfold FiniteElement; infer_instance

instance : IsStrictOrderedRing (FiniteElement K) := by
  unfold FiniteElement; infer_instance

@[simp] theorem val_zero : (0 : FiniteElement K).1 = 0 := rfl
@[simp] theorem val_one : (1 : FiniteElement K).1 = 1 := rfl
@[simp] theorem val_add (x y : FiniteElement K) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem val_sub (x y : FiniteElement K) : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem val_mul (x y : FiniteElement K) : (x * y).1 = x.1 * y.1 := rfl

@[ext] theorem ext {x y : FiniteElement K} (h : x.1 = y.1) : x = y := Subtype.ext h

/-- The constructor for `FiniteElement`. -/
protected def mk (x : K) (h : 0 ≤ mk x) : FiniteElement K := ⟨x, h⟩

@[simp] theorem mk_zero (h : 0 ≤ mk (0 : K)) : FiniteElement.mk 0 h = 0 := rfl
@[simp] theorem mk_one (h : 0 ≤ mk (1 : K)) : FiniteElement.mk 1 h = 1 := rfl
@[simp] theorem mk_natCast {n : ℕ} (h : 0 ≤ mk (n : K)) : FiniteElement.mk (n : K) h = n := rfl
@[simp] theorem mk_intCast {n : ℤ} (h : 0 ≤ mk (n : K)) : FiniteElement.mk (n : K) h = n := rfl

@[simp]
theorem mk_neg {x : K} (h : 0 ≤ mk x) :
    -FiniteElement.mk x h = FiniteElement.mk (-x) (by rwa [mk_neg]) :=
  rfl

theorem not_isUnit_iff_mk_pos {x : FiniteElement K} : ¬ IsUnit x ↔ 0 < mk x.1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem isUnit_iff_mk_eq_zero {x : FiniteElement K} : IsUnit x ↔ mk x.1 = 0 := by
  rw [← not_iff_not, not_isUnit_iff_mk_pos, lt_iff_not_ge, x.2.ge_iff_eq']

end FiniteElement

variable (K) in
/-- The residue field of `FiniteElement`. This quotient inherits an order from `K`,
which makes it into a linearly ordered Archimedean field. -/
def FiniteResidueField : Type _ :=
  IsLocalRing.ResidueField (FiniteElement K)

namespace FiniteResidueField

noncomputable instance : Field (FiniteResidueField K) :=
  inferInstanceAs (Field (IsLocalRing.ResidueField _))

#adaptation_note /-- Removed `private':
This had been private, but while disabling `set_option backward.privateInPublic` as a global option
we have made it public again. -/
theorem ordConnected_preimage_mk' : ∀ x, Set.OrdConnected <| Quotient.mk
    (Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))) ⁻¹' {x} := by
  refine fun x ↦ ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Submodule.quotientRel_def,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply hy.trans_le (mk_antitoneOn _ _ _) <;> simpa

noncomputable instance : LinearOrder (FiniteResidueField K) :=
  @Quotient.instLinearOrder _ _ _ ordConnected_preimage_mk' (Classical.decRel _)

/-- The quotient map from finite elements on the field to the associated residue field. -/
def mk : FiniteElement K →+*o FiniteResidueField K where
  monotone' _ _ h := Quotient.mk_monotone h
  __ := IsLocalRing.residue (FiniteElement K)

@[induction_eliminator]
theorem ind {motive : FiniteResidueField K → Prop} (mk : ∀ x, motive (mk x)) : ∀ x, motive x :=
  Quotient.ind mk

instance ordConnected_preimage_mk :
    ∀ x, Set.OrdConnected (mk ⁻¹' ({x} : Set (FiniteResidueField K))) :=
  ordConnected_preimage_mk'

theorem mk_eq_mk {x y : FiniteElement K} : mk x = mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1) := by
  apply Quotient.eq.trans
  rw [Submodule.quotientRel_def, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    FiniteElement.not_isUnit_iff_mk_pos, AddSubgroupClass.coe_sub]

theorem mk_eq_zero {x : FiniteElement K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1 := by
  apply mk_eq_mk.trans
  simp

theorem mk_ne_zero {x : FiniteElement K} : mk x ≠ 0 ↔ ArchimedeanClass.mk x.1 = 0 := by
  rw [ne_eq, mk_eq_zero, not_lt, x.2.ge_iff_eq']

theorem mk_le_mk {x y : FiniteElement K} : mk x ≤ mk y ↔ x ≤ y ∨ mk x = mk y := by
  refine (Quotient.mk_le_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

theorem mk_lt_mk {x y : FiniteElement K} : mk x < mk y ↔ x < y ∧ mk x ≠ mk y := by
  refine (Quotient.mk_lt_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

theorem lt_of_mk_lt_mk {x y : FiniteElement K} (h : mk x < mk y) : x < y :=
  (mk_lt_mk.1 h).1

private theorem mul_le_mul_of_nonneg_left' {x y z : FiniteResidueField K} (h : x ≤ y) (hz : 0 ≤ z) :
    z * x ≤ z * y := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  rw [← map_mul, ← map_mul]
  rw [← map_zero mk] at hz
  rw [mk_le_mk] at h hz ⊢
  grind [mul_le_mul_of_nonneg_left]

instance : IsOrderedRing (FiniteResidueField K) where
  zero_le_one := mk.monotone' zero_le_one
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    obtain h | h := mk_le_mk.1 h
    · exact mk.monotone' <| add_le_add_left h _
    · rw [h]
  mul_le_mul_of_nonneg_left _ hx _ _ h := mul_le_mul_of_nonneg_left' h hx
  mul_le_mul_of_nonneg_right x hx y z h := by
    simp_rw [mul_comm _ x]
    exact mul_le_mul_of_nonneg_left' h hx

instance : Archimedean (FiniteResidueField K) where
  arch x y hy := by
    induction x with | mk x
    induction y with | mk y
    obtain hx | hx := le_or_gt (mk x) 0
    · use 0
      rwa [zero_nsmul]
    · obtain ⟨n, hn⟩ := ((mk_ne_zero.1 hy.ne').trans (mk_ne_zero.1 hx.ne').symm).le
      refine ⟨n, mk.monotone' ?_⟩
      change x.1 ≤ n • y.1
      convert ← hn
      · exact abs_of_pos <| lt_of_mk_lt_mk hx
      · exact abs_of_pos <| lt_of_mk_lt_mk hy

/-- An embedding from an Archimedean field into `K` induces an embedding into
`FiniteResidueField K`. -/
def ofArchimedean (f : R →+*o K) : R →+*o FiniteResidueField K where
  toFun r := mk <| .mk _ (mk_map_nonneg_of_archimedean f r)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    simp_rw [map_add]
    exact mk.map_add
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
  map_mul' x y := by
    simp_rw [map_mul]
    exact mk.map_mul
      (.mk _ (mk_map_nonneg_of_archimedean f x)) (.mk _ (mk_map_nonneg_of_archimedean f y))
  monotone' x y h := mk.monotone' <| f.monotone' h

theorem ofArchimedean_apply (f : R →+*o K) (r : R) :
    ofArchimedean f r = mk (.mk _ (mk_map_nonneg_of_archimedean f r)) :=
  rfl

theorem ofArchimedean_injective (f : R →+*o K) : Function.Injective (ofArchimedean f) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  contrapose! hr
  rw [ofArchimedean_apply, mk_ne_zero]
  exact mk_map_of_archimedean' f hr

@[simp]
theorem ofArchimedean_inj (f : R →+*o K) {x y : R} :
    ofArchimedean f x = ofArchimedean f y ↔ x = y :=
  (ofArchimedean_injective f).eq_iff

end FiniteResidueField

/-! ### Standard part -/

/-- The standard part of a `FiniteElement` is the unique real number with an infinitesimal
difference.

For any infinite inputs, this function outputs a junk value of 0. -/
@[no_expose]
noncomputable def stdPart (x : K) : ℝ :=
  if h : 0 ≤ mk x then
    OrderRingHom.comp default FiniteResidueField.mk (.mk x h) else 0

theorem stdPart_of_mk_ne_zero (h : mk x ≠ 0) : stdPart x = 0 := by
  obtain h | h := h.lt_or_gt
  · exact dif_neg h.not_ge
  · rw [stdPart, dif_pos h.le, OrderRingHom.comp_apply, FiniteResidueField.mk_eq_zero.2 h,
      map_zero]

theorem stdPart_of_mk_nonneg (f : FiniteResidueField K →+*o ℝ) (h : 0 ≤ mk x) :
    stdPart x = f (.mk <| .mk x h) := by
  rw [stdPart, dif_pos h, OrderRingHom.comp_apply]
  congr
  exact Subsingleton.allEq _ _

@[simp]
theorem stdPart_zero : stdPart (0 : K) = 0 := by
  rw [stdPart, dif_pos] <;> simp

@[simp]
theorem stdPart_one : stdPart (1 : K) = 1 := by
  rw [stdPart, dif_pos] <;> simp

@[simp]
theorem stdPart_neg (x : K) : stdPart (-x) = -stdPart x := by
  simp_rw [stdPart, ArchimedeanClass.mk_neg]
  split_ifs
  · rw [← FiniteElement.mk_neg, map_neg]
  · simp

@[simp]
theorem stdPart_inv (x : K) : stdPart x⁻¹ = (stdPart x)⁻¹ := by
  obtain hx | hx := eq_or_ne (mk x) 0
  · unfold stdPart
    have hx' : 0 ≤ mk x⁻¹ := by simp_all
    rw [dif_pos hx.ge, dif_pos hx']
    · apply eq_inv_of_mul_eq_one_left
      suffices FiniteElement.mk x⁻¹ hx' * .mk x hx.ge = 1 by
        rw [← map_mul, this, map_one]
      ext
      apply inv_mul_cancel₀
      aesop
  · rw [stdPart_of_mk_ne_zero hx, stdPart_of_mk_ne_zero, inv_zero]
    rwa [mk_inv, neg_ne_zero]

theorem stdPart_add (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) :
    stdPart (x + y) = stdPart x + stdPart y := by
  unfold stdPart
  rw [dif_pos hx, dif_pos hy, dif_pos]
  exact map_add _ (FiniteElement.mk x hx) (.mk y hy)

theorem stdPart_sub (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) :
    stdPart (x - y) = stdPart x - stdPart y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, stdPart_add hx, stdPart_neg]
  rwa [mk_neg]

theorem stdPart_mul {x y : K} (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) :
    stdPart (x * y) = stdPart x * stdPart y := by
  unfold stdPart
  rw [dif_pos hx, dif_pos hy, dif_pos]
  exact map_mul _ (FiniteElement.mk x hx) (.mk y hy)

theorem stdPart_div (hx : 0 ≤ mk x) (hy : 0 ≤ -mk y) :
    stdPart (x / y) = stdPart x / stdPart y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, stdPart_mul hx, stdPart_inv]
  rwa [mk_inv]

@[simp]
theorem stdPart_intCast (n : ℤ) : stdPart (n : K) = n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [stdPart, dif_pos]
    · rw [FiniteElement.mk_intCast]
      simp
    · rw [mk_intCast hn]

@[simp]
theorem stdPart_natCast (n : ℕ) : stdPart (n : K) = n :=
  mod_cast stdPart_intCast n

@[simp]
theorem stdPart_ofNat (n : ℕ) [n.AtLeastTwo] : stdPart (ofNat(n) : K) = n :=
  stdPart_natCast n

@[simp]
theorem stdPart_ratCast (q : ℚ) : stdPart (q : K) = q := by
  cases q with | div n d hd
  simp_rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [stdPart_div]
    · simp
    · rw [mk_intCast hn]
    · rw [mk_natCast hd, neg_zero]

@[simp]
theorem stdPart_real (f : ℝ →+*o K) (r : ℝ) : stdPart (f r) = r := by
  rw [stdPart, dif_pos]
  exact r.ringHom_apply <| OrderRingHom.comp _ (FiniteResidueField.ofArchimedean f)

theorem ofArchimedean_stdPart (f : ℝ →+*o K) (hx : 0 ≤ mk x) :
    FiniteResidueField.ofArchimedean f (stdPart x) = .mk (.mk x hx) := by
  rw [stdPart, dif_pos hx, ← OrderRingHom.comp_apply, ← OrderRingHom.comp_assoc,
    OrderRingHom.comp_apply, OrderRingHom.apply_eq_self]

/-- The standard part of `x` is the unique real `r` such that `x - r` is infinitesimal. -/
theorem mk_sub_pos_iff (f : ℝ →+*o K) {r : ℝ} (hx : 0 ≤ mk x) :
    0 < mk (x - f r) ↔ stdPart x = r := by
  refine (FiniteResidueField.mk_eq_zero
    (x := .mk x hx - .mk _ (mk_map_nonneg_of_archimedean f r))).symm.trans ?_
  rw [map_sub, ← FiniteResidueField.ofArchimedean_apply, ← ofArchimedean_stdPart f hx,
    sub_eq_zero, FiniteResidueField.ofArchimedean_inj f]

theorem mk_sub_stdPart_pos (f : ℝ →+*o K) (hx : 0 ≤ mk x) : 0 < mk (x - f (stdPart x)) :=
  (mk_sub_pos_iff f hx).2 rfl

end ArchimedeanClass
