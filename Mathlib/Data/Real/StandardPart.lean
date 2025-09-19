/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.CompleteField
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Order.Quotient

/-!
# Standard part function

Let `K` be a linearly ordered field. The subset of finite elements (i.e. those bounded by a natural
number) is a `ValuationSubring`, which means we can construct its residue field
`FiniteResidueField`, roughly corresponding to the finite elements quotiented by infinitesimals.
This field inherits a `LinearOrder` instance, which makes it into an Archimedean linearly ordered
field, meaning we can uniquely embed it in the reals.

Given a finite element of the field, the `ArchimedeanClass.standardPart` function returns the real
number corresponding to this unique embedding. This function generalizes, among other things, the
standard part function on `Hyperreal`.

## Todo

Redefine `Hyperreal.st` in terms of `ArchimedeanClass.standardPart`.
-/

namespace ArchimedeanClass
variable
  {K : Type*} [LinearOrder K] [Field K] [IsOrderedRing K] {x y : K}
  {R : Type*} [LinearOrder R] [CommRing R] [IsOrderedRing R] [Archimedean R]

/-! ### Finite residue field -/

variable (K) in
/-- The valuation subring of elements in non-negative Archimedean classes, i.e. elements bounded by
some natural number. -/
protected noncomputable def Finite : ValuationSubring K :=
  (addValuation K).toValuation.valuationSubring

namespace Finite

@[simp] theorem mem_finite_iff {x : K} : x ∈ ArchimedeanClass.Finite K ↔ 0 ≤ mk x := .rfl

theorem mem_map_of_archimedean (f : R →+*o K) (r : R) : f r ∈ ArchimedeanClass.Finite K := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · rw [mem_finite_iff, mk_map_of_archimedean' f hr]

@[simp]
theorem mk_zero (h : 0 ∈ ArchimedeanClass.Finite K) :
    (⟨0, h⟩ : ArchimedeanClass.Finite K) = 0 := rfl

@[simp]
theorem mk_one (h : 1 ∈ ArchimedeanClass.Finite K) :
    (⟨1, h⟩ : ArchimedeanClass.Finite K) = 1 := rfl

@[simp]
theorem mk_neg (x : K) (h : -x ∈ ArchimedeanClass.Finite K) :
    (⟨-x, h⟩ : ArchimedeanClass.Finite K) = -⟨x, neg_mem_iff.1 h⟩ := rfl

@[simp]
theorem mk_natCast (n : ℕ) (h : (n : K) ∈ ArchimedeanClass.Finite K) :
    (⟨n, h⟩ : ArchimedeanClass.Finite K) = n := rfl

@[simp]
theorem mk_intCast (n : ℤ) (h : (n : K) ∈ ArchimedeanClass.Finite K) :
    (⟨n, h⟩ : ArchimedeanClass.Finite K) = n := rfl

instance : IsStrictOrderedRing (ArchimedeanClass.Finite K) where
  zero_le_one := zero_le_one (α := K)
  add_le_add_left _ _ h _ := add_le_add_left (α := K) h _
  le_of_add_le_add_left x y z := le_of_add_le_add_left (α := K)
  mul_lt_mul_of_pos_left x y z := by
    have := IsOrderedRing.toIsStrictOrderedRing K
    exact mul_lt_mul_of_pos_left (α := K)
  mul_lt_mul_of_pos_right x y z := by
    have := IsOrderedRing.toIsStrictOrderedRing K
    exact mul_lt_mul_of_pos_right (α := K)

theorem not_isUnit_iff_mk_pos {x : ArchimedeanClass.Finite K} : ¬ IsUnit x ↔ 0 < mk x.1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem isUnit_iff_mk_eq_zero {x : ArchimedeanClass.Finite K} : IsUnit x ↔ mk x.1 = 0 := by
  rw [← not_iff_not, Finite.not_isUnit_iff_mk_pos, lt_iff_not_ge, x.2.ge_iff_eq']

end Finite

variable (K) in
/-- The residue field of `ArchimedeanClass.Finite`. By choosing arbitrary representatives from `K`,
we can make this into a linearly ordered Archimedean field. -/
def FiniteResidueField : Type _ :=
  IsLocalRing.ResidueField (ArchimedeanClass.Finite K)

namespace FiniteResidueField

noncomputable instance : Field (FiniteResidueField K) :=
  inferInstanceAs (Field (IsLocalRing.ResidueField _))

private theorem ordConnected_preimage_mk' :
    ∀ x, Set.OrdConnected (Quotient.mk
      (Submodule.quotientRel (IsLocalRing.maximalIdeal (ArchimedeanClass.Finite K))) ⁻¹' {x}) := by
  refine fun x ↦ ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Submodule.quotientRel_def,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Finite.not_isUnit_iff_mk_pos] at hy ⊢
  apply hy.trans_le (mk_antitoneOn _ _ _) <;> simpa

noncomputable instance : LinearOrder (FiniteResidueField K) :=
  @Quotient.linearOrder _ _ _ ordConnected_preimage_mk' (Classical.decRel _)

/-- The quotient map from finite elements on the field to the associated residue field. -/
def mk : ArchimedeanClass.Finite K →+*o FiniteResidueField K where
  monotone' _ _ h := Quotient.mk_monotone h
  __ := IsLocalRing.residue (ArchimedeanClass.Finite K)

@[induction_eliminator]
theorem ind {motive : FiniteResidueField K → Prop} (mk : ∀ x, motive (mk x)) : ∀ x, motive x :=
  Quotient.ind mk

instance ordConnected_preimage_mk :
    ∀ x, Set.OrdConnected (mk ⁻¹' ({x} : Set (FiniteResidueField K))) :=
  ordConnected_preimage_mk'

theorem mk_eq_mk {x y : ArchimedeanClass.Finite K} :
    mk x = mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1) := by
  apply Quotient.eq.trans
  rw [Submodule.quotientRel_def, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Finite.not_isUnit_iff_mk_pos, AddSubgroupClass.coe_sub]

theorem mk_eq_zero {x : ArchimedeanClass.Finite K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1 := by
  apply mk_eq_mk.trans
  simp

theorem mk_ne_zero {x : ArchimedeanClass.Finite K} : mk x ≠ 0 ↔ ArchimedeanClass.mk x.1 = 0 := by
  rw [ne_eq, mk_eq_zero, not_lt, x.2.ge_iff_eq']

theorem mk_le_mk {x y : ArchimedeanClass.Finite K} : mk x ≤ mk y ↔ x ≤ y ∨ mk x = mk y := by
  refine (Quotient.mk_le_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

theorem mk_lt_mk {x y : ArchimedeanClass.Finite K} : mk x < mk y ↔ x < y ∧ mk x ≠ mk y := by
  refine (Quotient.mk_lt_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

theorem lt_of_mk_lt_mk {x y : ArchimedeanClass.Finite K} (h : mk x < mk y) : x < y :=
  (mk_lt_mk.1 h).1

private theorem mul_lt_mul_of_pos_left' {x y z : FiniteResidueField K} (h : x < y) (hz : 0 < z) :
    z * x < z * y := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  rw [← map_mul, ← map_mul]
  rw [← map_zero mk] at hz
  rw [mk_lt_mk] at h hz ⊢
  aesop

instance : IsStrictOrderedRing (FiniteResidueField K) where
  zero_le_one := mk.monotone' zero_le_one
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    obtain h | h := mk_le_mk.1 h
    · exact mk.monotone' <| add_le_add_left h _
    · rw [h]
  le_of_add_le_add_left x y z h := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    obtain h | h := mk_le_mk.1 h
    · exact mk.monotone' <| le_of_add_le_add_left h
    · apply le_of_eq
      simpa using h
  mul_lt_mul_of_pos_left _ _ _ := mul_lt_mul_of_pos_left'
  mul_lt_mul_of_pos_right x y z := by simp_rw [mul_comm _ z]; exact mul_lt_mul_of_pos_left'

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
@[simps!]
def ofArchimedean (f : R →+*o K) : R →+*o FiniteResidueField K where
  toFun r := mk ⟨f r, Finite.mem_map_of_archimedean f r⟩
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    simp_rw [map_add]
    exact mk.map_add ⟨_, Finite.mem_map_of_archimedean f x⟩ ⟨_, Finite.mem_map_of_archimedean f y⟩
  map_mul' x y := by
    simp_rw [map_mul]
    exact mk.map_mul ⟨_, Finite.mem_map_of_archimedean f x⟩ ⟨_, Finite.mem_map_of_archimedean f y⟩
  monotone' x y h := mk.monotone' <| f.monotone' h

end FiniteResidueField

/-! ### Standard part -/

/-- The standard part of an `ArchimedeanClass.Finite` element is the unique real number with an
infinitesimal difference. -/
noncomputable def standardPart (x : K) : ℝ :=
  if h : 0 ≤ mk x then
    (LinearOrderedField.inducedOrderRingHom _ _).comp FiniteResidueField.mk ⟨x, h⟩ else 0

theorem standardPart_of_mk_ne_zero (h : mk x ≠ 0) : standardPart x = 0 := by
  obtain h | h := h.lt_or_gt
  · exact dif_neg h.not_ge
  · rw [standardPart, dif_pos h.le, OrderRingHom.comp_apply, FiniteResidueField.mk_eq_zero.2 h,
      map_zero]

theorem standardPart_of_mk_nonneg (f : FiniteResidueField K →+*o ℝ) (h : 0 ≤ mk x) :
    standardPart x = f (.mk ⟨x, h⟩) := by
  rw [standardPart, dif_pos h, OrderRingHom.comp_apply]
  congr
  exact Subsingleton.allEq _ _

@[simp]
theorem standardPart_zero : standardPart (0 : K) = 0 := by
  rw [standardPart, dif_pos] <;> simp

@[simp]
theorem standardPart_one : standardPart (1 : K) = 1 := by
  rw [standardPart, dif_pos] <;> simp

@[simp]
theorem standardPart_neg (x : K) : standardPart (-x) = -standardPart x := by
  simp_rw [standardPart, ArchimedeanClass.mk_neg]
  split_ifs <;> simp

@[simp]
theorem standardPart_inv (x : K) : standardPart x⁻¹ = (standardPart x)⁻¹ := by
  obtain hx | hx := eq_or_ne (mk x) 0
  · unfold standardPart
    have hx' : 0 ≤ mk x⁻¹ := by simp_all
    rw [dif_pos hx.ge, dif_pos hx']
    · apply eq_inv_of_mul_eq_one_left
      suffices (⟨x⁻¹, hx'⟩ : ArchimedeanClass.Finite K) * ⟨x, hx.ge⟩ = 1 by
        rw [← map_mul, this, map_one]
      ext
      apply inv_mul_cancel₀
      aesop
  · rw [standardPart_of_mk_ne_zero hx, standardPart_of_mk_ne_zero, inv_zero]
    rwa [mk_inv, neg_ne_zero]

theorem standardPart_add (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) :
    standardPart (x + y) = standardPart x + standardPart y := by
  unfold standardPart
  rw [dif_pos hx, dif_pos hy, dif_pos]
  exact map_add (M := ArchimedeanClass.Finite K) _ ⟨x, hx⟩ ⟨y, hy⟩

theorem standardPart_sub (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) :
    standardPart (x - y) = standardPart x - standardPart y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, standardPart_add hx, standardPart_neg]
  rwa [mk_neg]

theorem standardPart_mul {x y : K} (hx : 0 ≤ mk x) (hy : 0 ≤ mk y) :
    standardPart (x * y) = standardPart x * standardPart y := by
  unfold standardPart
  rw [dif_pos hx, dif_pos hy, dif_pos]
  exact map_mul (M := ArchimedeanClass.Finite K) _ ⟨x, hx⟩ ⟨y, hy⟩

theorem standardPart_div (hx : 0 ≤ mk x) (hy : 0 ≤ -mk y) :
    standardPart (x / y) = standardPart x / standardPart y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, standardPart_mul hx, standardPart_inv]
  rwa [mk_inv]

@[simp]
theorem standardPart_intCast (n : ℤ) : standardPart (n : K) = n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [standardPart, dif_pos]
    · simp
    · rw [mk_intCast hn]

@[simp]
theorem standardPart_natCast (n : ℕ) : standardPart (n : K) = n := by
  exact_mod_cast standardPart_intCast n

@[simp]
theorem standardPart_ratCast (q : ℚ) : standardPart (q : K) = q := by
  have := IsOrderedRing.toIsStrictOrderedRing K
  cases q with | div n d hd
  simp_rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [standardPart_div]
    · simp
    · rw [mk_intCast hn]
    · rw [mk_natCast hd, neg_zero]

@[simp]
theorem standardPart_real (f : ℝ →+*o K) (r : ℝ) : standardPart (f r) = r := by
  rw [standardPart, dif_pos]
  exact r.ringHom_apply
    ((LinearOrderedField.inducedOrderRingHom _ ℝ).comp (FiniteResidueField.ofArchimedean f))

end ArchimedeanClass
