/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.Algebra.Algebra.Spectrum

/-!
# Quasiregularity and quasispectrum

For a non-unital ring `R`, an element `r : R` is *quasiregular* if it is invertible in the monoid
`(R, ∘)` where `x ∘ y := y + x + x * y` with identity `0 : R`. We implement this both as a type
synonym `PreQuasiregular` which has an associated `Monoid` instance (note: *not* an `AddMonoid`
instance despite the fact that `0 : R` is the identity in this monoid) so that one may access
the quasiregular elements of `R` as `(PreQuasiregular R)ˣ`, but also as a predicate
`IsQuasiregular`.

Quasiregularity is closely tied to invertibility. Indeed, `(PreQuasiregular A)ˣ` is isomorphic to
the subgroup of `Unitization R A` whose scalar part is `1`, whenever `A` is a non-unital
`R`-algebra, and moreover this isomorphism is implemented by the map
`(x : A) ↦ (1 + x : Unitization R A)`. It is because of this isomorphism, and the associated ties
with multiplicative invertibility, that we choose a `Monoid` (as opposed to an `AddMonoid`)
structure on `PreQuasiregular`.  In addition, in unital rings, we even have
`IsQuasiregular x ↔ IsUnit (1 + x)`.

The *quasispectrum* of `a : A` (with respect to `R`) is defined in terms of quasiregularity, and
this is the natural analogue of the `spectrum` for non-unital rings. Indeed, it is true that
`quasispectrum R a = spectrum R a ∪ {0}` when `A` is unital.

In Mathlib, the quasispectrum is the domain of the continuous functions associated to the
*non-unital* continuous functional calculus.

## Main definitions

+ `PreQuasiregular R`: a structure wrapping `R` that inherits a distinct `Monoid` instance when `R`
  is a non-unital semiring.
+ `Unitization.unitsFstOne`: the subgroup with carrier `{ x : (Unitization R A)ˣ | x.fst = 1 }`.
+ `unitsFstOne_mulEquiv_quasiregular`: the group isomorphism between
  `Unitization.unitsFstOne` and the units of `PreQuasiregular` (i.e., the quasiregular elements)
  which sends `(1, x) ↦ x`.
+ `IsQuasiregular x`: the proposition that `x : R` is a unit with respect to the monoid structure on
  `PreQuasiregular R`, i.e., there is some `u : (PreQuasiregular R)ˣ` such that `u.val` is
  identified with `x` (via the natural equivalence between `R` and `PreQuasiregular R`).
+ `quasispectrum R a`: in an algebra over the semifield `R`, this is the set
  `{r : R | (hr : IsUnit r) → ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}`, which should be thought of
  as a version of the `spectrum` which is applicable in non-unital algebras.

## Main theorems

+ `isQuasiregular_iff_isUnit`: in a unital ring, `x` is quasiregular if and only if `1 + x` is
  a unit.
+ `quasispectrum_eq_spectrum_union_zero`: in a unital algebra `A` over a semifield `R`, the
  quasispectrum of `a : A` is the `spectrum` with zero added.
+ `Unitization.isQuasiregular_inr_iff`: `a : A` is quasiregular if and only if it is quasiregular
  in `Unitization R A` (via the coercion `Unitization.inr`).
+ `Unitization.quasispectrum_eq_spectrum_inr`: the quasispectrum of `a` in a non-unital `R`-algebra
  `A` is precisely the spectrum of `a` in the unitization.
  in `Unitization R A` (via the coercion `Unitization.inr`).
-/

/-- A type synonym for non-unital rings where an alternative monoid structure is introduced.
If `R` is a non-unital semiring, then `PreQuasiregular R` is equipped with the monoid structure
with binary operation `fun x y ↦ y + x + x * y` and identity `0`. Elements of `R` which are
invertible in this monoid satisfy the predicate `IsQuasiregular`. -/
structure PreQuasiregular (R : Type*) where
  /-- The value wrapped into a term of `PreQuasiregular`. -/
  val : R

namespace PreQuasiregular

variable {R : Type*} [NonUnitalSemiring R]

/-- The identity map between `R` and `PreQuasiregular R`. -/
@[simps]
def equiv : R ≃ PreQuasiregular R where
  toFun := .mk
  invFun := PreQuasiregular.val
  left_inv _ := rfl
  right_inv _ := rfl

instance instOne : One (PreQuasiregular R) where
  one := equiv 0

@[simp]
lemma val_one : (1 : PreQuasiregular R).val = 0 := rfl

instance instMul : Mul (PreQuasiregular R) where
  mul x y := .mk (y.val + x.val + x.val * y.val)

@[simp]
lemma val_mul (x y : PreQuasiregular R) : (x * y).val = y.val + x.val + x.val * y.val := rfl

instance instMonoid : Monoid (PreQuasiregular R) where
  one := equiv 0
  mul x y := .mk (y.val + x.val + x.val * y.val)
  mul_one _ := equiv.symm.injective <| by simp [-EmbeddingLike.apply_eq_iff_eq]
  one_mul _ := equiv.symm.injective <| by simp [-EmbeddingLike.apply_eq_iff_eq]
  mul_assoc x y z := equiv.symm.injective <| by simp [mul_add, add_mul, mul_assoc]; abel

@[simp]
lemma inv_add_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u⁻¹.val.val + u.val.val + u.val.val * u⁻¹.val.val = 0 := by
  simpa [-Units.mul_inv] using congr($(u.mul_inv).val)

@[simp]
lemma add_inv_add_mul_eq_zero (u : (PreQuasiregular R)ˣ) :
    u.val.val + u⁻¹.val.val + u⁻¹.val.val * u.val.val = 0 := by
  simpa [-Units.inv_mul] using congr($(u.inv_mul).val)

end PreQuasiregular

namespace Unitization
open PreQuasiregular

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A]
  [SMulCommClass R A A]

variable (R A) in
/-- The subgroup of the units of `Unitization R A` whose scalar part is `1`. -/
def unitsFstOne : Subgroup (Unitization R A)ˣ where
  carrier := {x | x.val.fst = 1}
  one_mem' := rfl
  mul_mem' {x} {y} (hx : fst x.val = 1) (hy : fst y.val = 1) := by simp [hx, hy]
  inv_mem' {x} (hx : fst x.val = 1) := by
    simpa [-Units.mul_inv, hx] using congr(fstHom R A $(x.mul_inv))

@[simp]
lemma mem_unitsFstOne {x : (Unitization R A)ˣ} : x ∈ unitsFstOne R A ↔ x.val.fst = 1 := Iff.rfl

@[simp]
lemma unitsFstOne_val_val_fst (x : (unitsFstOne R A)) : x.val.val.fst = 1 :=
  mem_unitsFstOne.mp x.property

@[simp]
lemma unitsFstOne_val_inv_val_fst (x : (unitsFstOne R A)) : x.val⁻¹.val.fst = 1 :=
  mem_unitsFstOne.mp x⁻¹.property

variable (R) in
/-- If `A` is a non-unital `R`-algebra, then the subgroup of units of `Unitization R A` whose
scalar part is `1 : R` (i.e., `Unitization.unitsFstOne`) is isomorphic to the group of units of
`PreQuasiregular A`. -/
@[simps]
def unitsFstOne_mulEquiv_quasiregular : unitsFstOne R A ≃* (PreQuasiregular A)ˣ where
  toFun x :=
    { val := equiv x.val.val.snd
      inv := equiv x⁻¹.val.val.snd
      val_inv := equiv.symm.injective <| by
        simpa [-Units.mul_inv] using congr(snd $(x.val.mul_inv))
      inv_val := equiv.symm.injective <| by
        simpa [-Units.inv_mul] using congr(snd $(x.val.inv_mul)) }
  invFun x :=
    { val :=
      { val := 1 + equiv.symm x.val
        inv := 1 + equiv.symm x⁻¹.val
        val_inv := by
          convert congr((1 + $(inv_add_add_mul_eq_zero x) : Unitization R A)) using 1
          · simp only [mul_one, equiv_symm_apply, one_mul, inr_zero, add_zero, mul_add, add_mul,
              inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero]
        inv_val := by
          convert congr((1 + $(add_inv_add_mul_eq_zero x) : Unitization R A)) using 1
          · simp only [mul_one, equiv_symm_apply, one_mul, inr_zero, add_zero, mul_add, add_mul,
              inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero] }
      property := by simp }
  left_inv x := Subtype.ext <| Units.ext <| by simpa using x.val.val.inl_fst_add_inr_snd_eq
  right_inv x := Units.ext <| by simp [-equiv_symm_apply]
  map_mul' x y := Units.ext <| equiv.symm.injective <| by simp

end Unitization

section PreQuasiregular

open PreQuasiregular

variable {R : Type*} [NonUnitalSemiring R]

/-- In a non-unital semiring `R`, an element `x : R` satisfies `IsQuasiregular` if it is a unit
under the monoid operation `fun x y ↦ y + x + x * y`. -/
def IsQuasiregular (x : R) : Prop :=
  ∃ u : (PreQuasiregular R)ˣ, equiv.symm u.val = x

@[simp]
lemma isQuasiregular_zero : IsQuasiregular 0 := ⟨1, rfl⟩

lemma isQuasiregular_iff {x : R} :
    IsQuasiregular x ↔ ∃ y, y + x + x * y = 0 ∧ x + y + y * x = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨equiv.symm u⁻¹.val, by simp⟩
  · rintro ⟨y, hy₁, hy₂⟩
    refine ⟨⟨equiv x, equiv y, ?_, ?_⟩, rfl⟩
    all_goals
      apply equiv.symm.injective
      assumption

end PreQuasiregular

lemma IsQuasiregular.map {F R S : Type*} [NonUnitalSemiring R] [NonUnitalSemiring S]
    [FunLike F R S] [NonUnitalRingHomClass F R S] (f : F) {x : R} (hx : IsQuasiregular x) :
    IsQuasiregular (f x) := by
  rw [isQuasiregular_iff] at hx ⊢
  obtain ⟨y, hy₁, hy₂⟩ := hx
  exact ⟨f y, by simpa using And.intro congr(f $(hy₁)) congr(f $(hy₂))⟩

lemma IsQuasiregular.isUnit_one_add {R : Type*} [Semiring R] {x : R} (hx : IsQuasiregular x) :
    IsUnit (1 + x) := by
  obtain ⟨y, hy₁, hy₂⟩ := isQuasiregular_iff.mp hx
  refine ⟨⟨1 + x, 1 + y, ?_, ?_⟩, rfl⟩
  · convert congr(1 + $(hy₁)) using 1 <;> first | noncomm_ring | simp
  · convert congr(1 + $(hy₂)) using 1 <;> first | noncomm_ring | simp

lemma isQuasiregular_iff_isUnit {R : Type*} [Ring R] {x : R} :
    IsQuasiregular x ↔ IsUnit (1 + x) := by
  refine ⟨IsQuasiregular.isUnit_one_add, fun hx ↦ ?_⟩
  rw [isQuasiregular_iff]
  use hx.unit⁻¹ - 1
  constructor
  case' h.left => have := congr($(hx.mul_val_inv) - 1)
  case' h.right => have := congr($(hx.val_inv_mul) - 1)
  all_goals
    rw [← sub_add_cancel (↑hx.unit⁻¹ : R) 1, sub_self] at this
    convert this using 1
    noncomm_ring

-- interestingly, this holds even in the semiring case.
lemma isQuasiregular_iff_isUnit' (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalSemiring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] {x : A} :
    IsQuasiregular x ↔ IsUnit (1 + x : Unitization R A) := by
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨u, rfl⟩
    exact (Unitization.unitsFstOne_mulEquiv_quasiregular R).symm u |>.val.isUnit
  · exact ⟨(Unitization.unitsFstOne_mulEquiv_quasiregular R) ⟨hx.unit, by simp⟩, by simp⟩

variable (R : Type*) {A : Type*} [CommSemiring R] [NonUnitalRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/-- If `A` is a non-unital `R`-algebra, the `R`-quasispectrum of `a : A` consists of those `r : R`
such that if `r` is invertible (in `R`), then `-(r⁻¹ • a)` is not quasiregular.

The quasispectrum is precisely the spectrum in the unitization when `R` is a commutative ring.
See `Unitization.quasispectrum_eq_spectrum_inr`. -/
def quasispectrum (a : A) : Set R :=
  {r : R | (hr : IsUnit r) → ¬ IsQuasiregular (-(hr.unit⁻¹ • a))}

variable {R} in
lemma quasispectrum.not_isUnit_mem (a : A) {r : R} (hr : ¬ IsUnit r) : r ∈ quasispectrum R a :=
  fun hr' ↦ (hr hr').elim

@[simp]
lemma quasispectrum.zero_mem [Nontrivial R] (a : A) : 0 ∈ quasispectrum R a :=
  quasispectrum.not_isUnit_mem a <| by simp

instance quasispectrum.instZero [Nontrivial R] (a : A) : Zero (quasispectrum R a) where
  zero := ⟨0, quasispectrum.zero_mem R a⟩

variable {R}

@[simp]
lemma quasispectrum.coe_zero [Nontrivial R] (a : A) : (0 : quasispectrum R a) = (0 : R) := rfl

lemma quasispectrum.mem_of_not_quasiregular (a : A) {r : Rˣ}
    (hr : ¬ IsQuasiregular (-(r⁻¹ • a))) : (r : R) ∈ quasispectrum R a :=
  fun _ ↦ by simpa using hr

lemma quasispectrum_eq_spectrum_union (R : Type*) {A : Type*} [CommSemiring R]
    [Ring A] [Algebra R A] (a : A) : quasispectrum R a = spectrum R a ∪ {r : R | ¬ IsUnit r} := by
  ext r
  rw [quasispectrum]
  simp only [Set.mem_setOf_eq, Set.mem_union, ← imp_iff_or_not, spectrum.mem_iff]
  congr! 1 with hr
  rw [not_iff_not, isQuasiregular_iff_isUnit, ← sub_eq_add_neg, Algebra.algebraMap_eq_smul_one]
  exact (IsUnit.smul_sub_iff_sub_inv_smul hr.unit a).symm

lemma quasispectrum_eq_spectrum_union_zero (R : Type*) {A : Type*} [Semifield R] [Ring A]
    [Algebra R A] (a : A) : quasispectrum R a = spectrum R a ∪ {0} := by
  convert quasispectrum_eq_spectrum_union R a
  ext x
  simp

namespace Unitization

lemma isQuasiregular_inr_iff (a : A) :
    IsQuasiregular (a : Unitization R A) ↔ IsQuasiregular a := by
  refine ⟨fun ha ↦ ?_, IsQuasiregular.map (inrNonUnitalAlgHom R A)⟩
  rw [isQuasiregular_iff] at ha ⊢
  obtain ⟨y, hy₁, hy₂⟩ := ha
  lift y to A using by simpa using congr(fstHom R A $(hy₁))
  refine ⟨y, ?_, ?_⟩ <;> exact inr_injective (R := R) <| by simpa

lemma zero_mem_spectrum_inr (R S : Type*) {A : Type*} [CommSemiring R]
    [CommRing S] [Nontrivial S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    0 ∈ spectrum R (a : Unitization S A) := by
  rw [spectrum.zero_mem_iff]
  rintro ⟨u, hu⟩
  simpa [-Units.mul_inv, hu] using congr($(u.mul_inv).fst)

lemma mem_spectrum_inr_of_not_isUnit {R A : Type*} [CommRing R]
    [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    (a : A) (r : R) (hr : ¬ IsUnit r) : r ∈ spectrum R (a : Unitization R A) :=
  fun h ↦ hr <| by simpa using h.map (fstHom R A)

lemma quasispectrum_eq_spectrum_inr (R : Type*) {A : Type*} [CommRing R] [Ring A]
    [Algebra R A] (a : A) : quasispectrum R a = spectrum R (a : Unitization R A) := by
  ext r
  have : { r | ¬ IsUnit r} ⊆ spectrum R _ := mem_spectrum_inr_of_not_isUnit a
  rw [← Set.union_eq_left.mpr this, ← quasispectrum_eq_spectrum_union]
  apply forall_congr' fun hr ↦ ?_
  rw [not_iff_not, Units.smul_def, Units.smul_def, ← inr_smul, ← inr_neg, isQuasiregular_inr_iff]

lemma quasispectrum_eq_spectrum_inr' (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasispectrum R a = spectrum R (a : Unitization S A) := by
  ext r
  have := Set.singleton_subset_iff.mpr (zero_mem_spectrum_inr R S a)
  rw [← Set.union_eq_self_of_subset_right this, ← quasispectrum_eq_spectrum_union_zero]
  apply forall_congr' fun x ↦ ?_
  rw [not_iff_not, Units.smul_def, Units.smul_def, ← inr_smul, ← inr_neg, isQuasiregular_inr_iff]
