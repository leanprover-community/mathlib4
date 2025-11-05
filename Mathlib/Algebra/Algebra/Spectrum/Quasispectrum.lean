/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Algebra.Unitization

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
  `A` is precisely the spectrum of `a` in `Unitization R A` (via the coercion `Unitization.inr`).
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
          · simp only [mul_one, equiv_symm_apply, one_mul, mul_add, add_mul, inr_add, inr_mul]
            abel
          · simp only [inr_zero, add_zero]
        inv_val := by
          convert congr((1 + $(add_inv_add_mul_eq_zero x) : Unitization R A)) using 1
          · simp only [mul_one, equiv_symm_apply, one_mul, mul_add, add_mul, inr_add, inr_mul]
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

lemma isQuasiregular_iff' {x : R} : IsQuasiregular x ↔ IsUnit (PreQuasiregular.equiv x) := by
  simp only [IsQuasiregular, IsUnit, Equiv.apply_symm_apply,
    ← PreQuasiregular.equiv (R := R).injective.eq_iff]

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
  · convert congr(1 + $(hy₁)) using 1 <;> [noncomm_ring; simp]
  · convert congr(1 + $(hy₂)) using 1 <;> [noncomm_ring; simp]

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
  [Module R A]

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

theorem quasispectrum.nonempty [Nontrivial R] (a : A) : (quasispectrum R a).Nonempty :=
  Set.nonempty_of_mem <| quasispectrum.zero_mem R a

instance quasispectrum.instZero [Nontrivial R] (a : A) : Zero (quasispectrum R a) where
  zero := ⟨0, quasispectrum.zero_mem R a⟩

variable {R}

/-- A version of `NonUnitalAlgHom.quasispectrum_apply_subset` which allows for `quasispectrum R`,
where `R` is a *semi*ring, but `φ` must still function over a scalar ring `S`. In this case, we
need `S` to be explicit. The primary use case is, for instance, `R := ℝ≥0` and `S := ℝ` or
`S := ℂ`. -/
lemma NonUnitalAlgHom.quasispectrum_apply_subset' {F R : Type*} (S : Type*) {A B : Type*}
    [CommSemiring R] [Semiring S] [NonUnitalRing A] [NonUnitalRing B] [Module R S]
    [Module S A] [Module R A] [Module S B] [Module R B] [IsScalarTower R S A] [IsScalarTower R S B]
    [FunLike F A B] [NonUnitalAlgHomClass F S A B] (φ : F) (a : A) :
    quasispectrum R (φ a) ⊆ quasispectrum R a := by
  refine Set.compl_subset_compl.mp fun x ↦ ?_
  simp only [quasispectrum, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_not,
    forall_exists_index]
  refine fun hx this ↦ ⟨hx, ?_⟩
  rw [Units.smul_def, ← smul_one_smul S] at this ⊢
  simpa [- smul_assoc] using this.map φ

/-- If `φ` is non-unital algebra homomorphism over a scalar ring `R`, then
`quasispectrum R (φ a) ⊆ quasispectrum R a`. -/
lemma NonUnitalAlgHom.quasispectrum_apply_subset {F R A B : Type*}
    [CommRing R] [NonUnitalRing A] [NonUnitalRing B] [Module R A] [Module R B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] (φ : F) (a : A) :
    quasispectrum R (φ a) ⊆ quasispectrum R a :=
  NonUnitalAlgHom.quasispectrum_apply_subset' R φ a

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

lemma spectrum_subset_quasispectrum (R : Type*) {A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    (a : A) : spectrum R a ⊆ quasispectrum R a :=
  quasispectrum_eq_spectrum_union R a ▸ Set.subset_union_left

lemma quasispectrum_eq_spectrum_union_zero (R : Type*) {A : Type*} [Semifield R] [Ring A]
    [Algebra R A] (a : A) : quasispectrum R a = spectrum R a ∪ {0} := by
  convert quasispectrum_eq_spectrum_union R a
  simp

lemma mem_quasispectrum_iff {R A : Type*} [Semifield R] [Ring A]
    [Algebra R A] {a : A} {x : R} :
    x ∈ quasispectrum R a ↔ x = 0 ∨ x ∈ spectrum R a := by
  simp [quasispectrum_eq_spectrum_union_zero]

namespace Unitization
variable [IsScalarTower R A A] [SMulCommClass R A A]

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
  fun h ↦ hr <| by simpa [map_sub] using h.map (fstHom R A)

lemma quasispectrum_eq_spectrum_inr (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a : A) :
    quasispectrum R a = spectrum R (a : Unitization R A) := by
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

lemma quasispectrum_inr_eq (R S : Type*) {A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] (a : A) :
    quasispectrum R (a : Unitization S A) = quasispectrum R a := by
  rw [quasispectrum_eq_spectrum_union_zero, quasispectrum_eq_spectrum_inr' R S]
  simpa using zero_mem_spectrum_inr _ _ _

end Unitization

lemma quasispectrum.mul_comm {R A : Type*} [CommRing R] [NonUnitalRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (a b : A) :
    quasispectrum R (a * b) = quasispectrum R (b * a) := by
  rw [← Set.inter_union_compl (quasispectrum R (a * b)) {r | IsUnit r},
    ← Set.inter_union_compl (quasispectrum R (b * a)) {r | IsUnit r}]
  congr! 1
  · simpa [Set.inter_comm _ {r | IsUnit r}, Unitization.quasispectrum_eq_spectrum_inr,
      Unitization.inr_mul] using spectrum.setOf_isUnit_inter_mul_comm _ _
  · rw [Set.inter_eq_right.mpr, Set.inter_eq_right.mpr]
    all_goals exact fun _ ↦ quasispectrum.not_isUnit_mem _

/-- A class for `𝕜`-algebras with a partial order where the ordering is compatible with the
(quasi)spectrum. -/
class NonnegSpectrumClass (𝕜 A : Type*) [CommSemiring 𝕜] [PartialOrder 𝕜]
    [NonUnitalRing A] [PartialOrder A]
    [Module 𝕜 A] : Prop where
  quasispectrum_nonneg_of_nonneg : ∀ a : A, 0 ≤ a → ∀ x ∈ quasispectrum 𝕜 a, 0 ≤ x

export NonnegSpectrumClass (quasispectrum_nonneg_of_nonneg)

namespace NonnegSpectrumClass

lemma iff_spectrum_nonneg {𝕜 A : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] : NonnegSpectrumClass 𝕜 A ↔ ∀ a : A, 0 ≤ a → ∀ x ∈ spectrum 𝕜 a, 0 ≤ x := by
  simp [show NonnegSpectrumClass 𝕜 A ↔ _ from ⟨fun ⟨h⟩ ↦ h, (⟨·⟩)⟩,
    quasispectrum_eq_spectrum_union_zero]

alias ⟨_, of_spectrum_nonneg⟩ := iff_spectrum_nonneg

lemma nonneg_of_mem_quasispectrum {𝕜 : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜] [PartialOrder A]
    [Module 𝕜 A] [NonnegSpectrumClass 𝕜 A] {a : A} (ha : 0 ≤ a) {x : 𝕜}
    (hx : x ∈ quasispectrum 𝕜 a) : 0 ≤ x := quasispectrum_nonneg_of_nonneg a ha x hx

grind_pattern nonneg_of_mem_quasispectrum => x ∈ quasispectrum 𝕜 a

end NonnegSpectrumClass

lemma spectrum_nonneg_of_nonneg {𝕜 A : Type*} [CommSemiring 𝕜] [PartialOrder 𝕜]
    [Ring A] [PartialOrder A]
    [Algebra 𝕜 A] [NonnegSpectrumClass 𝕜 A] ⦃a : A⦄ (ha : 0 ≤ a) ⦃x : 𝕜⦄ (hx : x ∈ spectrum 𝕜 a) :
    0 ≤ x :=
  NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg a ha x (spectrum_subset_quasispectrum 𝕜 a hx)

grind_pattern spectrum_nonneg_of_nonneg => x ∈ spectrum 𝕜 a

/-! ### Restriction of the spectrum -/

/-- Given an element `a : A` of an `S`-algebra, where `S` is itself an `R`-algebra, we say that
the spectrum of `a` restricts via a function `f : S → R` if `f` is a left inverse of
`algebraMap R S`, and `f` is a right inverse of `algebraMap R S` on `spectrum S a`.

For example, when `f = Complex.re` (so `S := ℂ` and `R := ℝ`), `SpectrumRestricts a f` means that
the `ℂ`-spectrum of `a` is contained within `ℝ`. This arises naturally when `a` is selfadjoint
and `A` is a C⋆-algebra.

This is the property allows us to restrict a continuous functional calculus over `S` to a
continuous functional calculus over `R`. -/
structure QuasispectrumRestricts
    {R S A : Type*} [CommSemiring R] [CommSemiring S] [NonUnitalRing A]
    [Module R A] [Module S A] [Algebra R S] (a : A) (f : S → R) : Prop where
  /-- `f` is a right inverse of `algebraMap R S` when restricted to `quasispectrum S a`. -/
  rightInvOn : (quasispectrum S a).RightInvOn f (algebraMap R S)
  /-- `f` is a left inverse of `algebraMap R S`. -/
  left_inv : Function.LeftInverse f (algebraMap R S)

lemma quasispectrumRestricts_iff
    {R S A : Type*} [CommSemiring R] [CommSemiring S] [NonUnitalRing A]
    [Module R A] [Module S A] [Algebra R S] (a : A) (f : S → R) :
    QuasispectrumRestricts a f ↔ (quasispectrum S a).RightInvOn f (algebraMap R S) ∧
      Function.LeftInverse f (algebraMap R S) :=
  ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

@[simp]
theorem quasispectrum.algebraMap_mem_iff (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r ∈ quasispectrum S a ↔ r ∈ quasispectrum R a := by
  simp_rw [Unitization.quasispectrum_eq_spectrum_inr' _ S a, spectrum.algebraMap_mem_iff]

protected alias ⟨quasispectrum.of_algebraMap_mem, quasispectrum.algebraMap_mem⟩ :=
  quasispectrum.algebraMap_mem_iff

@[simp]
theorem quasispectrum.preimage_algebraMap (S : Type*) {R A : Type*} [Semifield R] [Field S]
    [NonUnitalRing A] [Algebra R S] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [Module R A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' quasispectrum S a = quasispectrum R a :=
  Set.ext fun _ => quasispectrum.algebraMap_mem_iff _

namespace QuasispectrumRestricts

section NonUnital

variable {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Module R A] [Module S A]
variable [Algebra R S] {a : A} {f : S → R}

protected theorem map_zero (h : QuasispectrumRestricts a f) : f 0 = 0 := by
  rw [← h.left_inv 0, map_zero (algebraMap R S)]

theorem of_subset_range_algebraMap (hf : f.LeftInverse (algebraMap R S))
    (h : quasispectrum S a ⊆ Set.range (algebraMap R S)) : QuasispectrumRestricts a f where
  rightInvOn := fun s hs => by obtain ⟨r, rfl⟩ := h hs; rw [hf r]
  left_inv := hf

lemma of_quasispectrum_eq {a b : A} {f : S → R} (ha : QuasispectrumRestricts a f)
    (h : quasispectrum S a = quasispectrum S b) : QuasispectrumRestricts b f where
  rightInvOn := h ▸ ha.rightInvOn
  left_inv := ha.left_inv

variable [IsScalarTower S A A] [SMulCommClass S A A]

lemma mul_comm_iff {f : S → R} {a b : A} :
    QuasispectrumRestricts (a * b) f ↔ QuasispectrumRestricts (b * a) f := by
  simp only [quasispectrumRestricts_iff, quasispectrum.mul_comm]

alias ⟨mul_comm, _⟩ := mul_comm_iff

variable [IsScalarTower R S A]

theorem algebraMap_image (h : QuasispectrumRestricts a f) :
    algebraMap R S '' quasispectrum R a = quasispectrum S a := by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [quasispectrum.preimage_algebraMap] using
      (quasispectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨quasispectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

theorem image (h : QuasispectrumRestricts a f) : f '' quasispectrum S a = quasispectrum R a := by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

theorem apply_mem (h : QuasispectrumRestricts a f) {s : S} (hs : s ∈ quasispectrum S a) :
    f s ∈ quasispectrum R a :=
  h.image ▸ ⟨s, hs, rfl⟩

theorem subset_preimage (h : QuasispectrumRestricts a f) :
    quasispectrum S a ⊆ f ⁻¹' quasispectrum R a :=
  h.image ▸ (quasispectrum S a).subset_preimage_image f

protected lemma comp {R₁ R₂ R₃ A : Type*} [Semifield R₁] [Field R₂] [Field R₃]
    [NonUnitalRing A] [Module R₁ A] [Module R₂ A] [Module R₃ A] [Algebra R₁ R₂] [Algebra R₂ R₃]
    [Algebra R₁ R₃] [IsScalarTower R₁ R₂ R₃] [IsScalarTower R₂ R₃ A] [IsScalarTower R₃ A A]
    [SMulCommClass R₃ A A] {a : A} {f : R₃ → R₂} {g : R₂ → R₁} {e : R₃ → R₁} (hfge : g ∘ f = e)
    (hf : QuasispectrumRestricts a f) (hg : QuasispectrumRestricts a g) :
    QuasispectrumRestricts a e where
  left_inv := by
    convert hfge ▸ hf.left_inv.comp hg.left_inv
    congrm(⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))
  rightInvOn := by
    convert hfge ▸ hg.rightInvOn.comp hf.rightInvOn fun _ ↦ hf.apply_mem
    congrm(⇑$(IsScalarTower.algebraMap_eq R₁ R₂ R₃))

end NonUnital

end QuasispectrumRestricts

/-- A (reducible) alias of `QuasispectrumRestricts` which enforces stronger type class assumptions
on the types involved, as it's really intended for the `spectrum`. The separate definition also
allows for dot notation. -/
@[reducible]
def SpectrumRestricts
    {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R A] [Algebra S A] [Algebra R S] (a : A) (f : S → R) : Prop :=
  QuasispectrumRestricts a f

namespace SpectrumRestricts

section Unital

variable {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
variable [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R}

theorem rightInvOn (h : SpectrumRestricts a f) : (spectrum S a).RightInvOn f (algebraMap R S) :=
  (QuasispectrumRestricts.rightInvOn h).mono <| spectrum_subset_quasispectrum _ _

theorem of_rightInvOn (h₁ : Function.LeftInverse f (algebraMap R S))
    (h₂ : (spectrum S a).RightInvOn f (algebraMap R S)) : SpectrumRestricts a f where
  rightInvOn x hx := by
    obtain (rfl | hx) := mem_quasispectrum_iff.mp hx
    · simpa using h₁ 0
    · exact h₂ hx
  left_inv := h₁

lemma _root_.spectrumRestricts_iff :
    SpectrumRestricts a f ↔ (spectrum S a).RightInvOn f (algebraMap R S) ∧
      Function.LeftInverse f (algebraMap R S) :=
  ⟨fun h ↦ ⟨h.rightInvOn, h.left_inv⟩, fun h ↦ .of_rightInvOn h.2 h.1⟩

theorem of_subset_range_algebraMap (hf : f.LeftInverse (algebraMap R S))
    (h : spectrum S a ⊆ Set.range (algebraMap R S)) : SpectrumRestricts a f where
  rightInvOn := fun s hs => by
    rw [mem_quasispectrum_iff] at hs
    obtain (rfl | hs) := hs
    · simpa using hf 0
    · obtain ⟨r, rfl⟩ := h hs
      rw [hf r]
  left_inv := hf

lemma of_spectrum_eq {a b : A} {f : S → R} (ha : SpectrumRestricts a f)
    (h : spectrum S a = spectrum S b) : SpectrumRestricts b f where
  rightInvOn := by
    rw [quasispectrum_eq_spectrum_union_zero, ← h, ← quasispectrum_eq_spectrum_union_zero]
    exact QuasispectrumRestricts.rightInvOn ha
  left_inv := ha.left_inv

lemma mul_comm_iff {R S A : Type*} [Semifield R] [Field S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] {a b : A} {f : S → R} :
    SpectrumRestricts (a * b) f ↔ SpectrumRestricts (b * a) f :=
  QuasispectrumRestricts.mul_comm_iff

alias ⟨mul_comm, _⟩ := mul_comm_iff

variable [IsScalarTower R S A]

theorem algebraMap_image (h : SpectrumRestricts a f) :
    algebraMap R S '' spectrum R a = spectrum S a := by
  refine Set.eq_of_subset_of_subset ?_ fun s hs => ⟨f s, ?_⟩
  · simpa only [spectrum.preimage_algebraMap] using
      (spectrum S a).image_preimage_subset (algebraMap R S)
  exact ⟨spectrum.of_algebraMap_mem S ((h.rightInvOn hs).symm ▸ hs), h.rightInvOn hs⟩

theorem image (h : SpectrumRestricts a f) : f '' spectrum S a = spectrum R a := by
  simp only [← h.algebraMap_image, Set.image_image, h.left_inv _, Set.image_id']

theorem apply_mem (h : SpectrumRestricts a f) {s : S} (hs : s ∈ spectrum S a) :
    f s ∈ spectrum R a :=
  h.image ▸ ⟨s, hs, rfl⟩

theorem subset_preimage (h : SpectrumRestricts a f) : spectrum S a ⊆ f ⁻¹' spectrum R a :=
  h.image ▸ (spectrum S a).subset_preimage_image f

end Unital

end SpectrumRestricts

theorem quasispectrumRestricts_iff_spectrumRestricts_inr (S : Type*) {R A : Type*} [Semifield R]
    [Field S] [NonUnitalRing A] [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A]
    [SMulCommClass S A A] [IsScalarTower R S A] {a : A} {f : S → R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitization S A) f := by
  rw [quasispectrumRestricts_iff, spectrumRestricts_iff,
    ← Unitization.quasispectrum_eq_spectrum_inr']

/-- The difference from `quasispectrumRestricts_iff_spectrumRestricts_inr` is that the
`Unitization` may be taken with respect to a different scalar field. -/
lemma quasispectrumRestricts_iff_spectrumRestricts_inr'
    {R S' A : Type*} (S : Type*) [Semifield R] [Semifield S'] [Field S] [NonUnitalRing A]
    [Module R A] [Module S' A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [Algebra R S'] [Algebra S' S] [Algebra R S] [IsScalarTower S' S A] [IsScalarTower R S A]
    {a : A} {f : S' → R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts (a : Unitization S A) f := by
  simp only [quasispectrumRestricts_iff, SpectrumRestricts, Unitization.quasispectrum_inr_eq]

theorem quasispectrumRestricts_iff_spectrumRestricts {R S A : Type*} [Semifield R] [Semifield S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] {a : A} {f : S → R} :
    QuasispectrumRestricts a f ↔ SpectrumRestricts a f := by rfl
