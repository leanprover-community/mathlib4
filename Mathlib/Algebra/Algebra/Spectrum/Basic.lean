/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Star.Pointwise
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Nonunits
public import Mathlib.Tactic.NoncommRing

/-!
# Spectrum of an element in an algebra
This file develops the basic theory of the spectrum of an element of an algebra.
This theory will serve as the foundation for spectral theory in Banach algebras.

## Main definitions

* `resolventSet a : Set R`: the resolvent set of an element `a : A` where
  `A` is an `R`-algebra.
* `spectrum a : Set R`: the spectrum of an element `a : A` where
  `A` is an `R`-algebra.
* `resolvent : R → A`: the resolvent function is `fun r ↦ (↑ₐ r - a)⁻¹ʳ`, and hence
  when `r ∈ resolvent R A`, it is actually the inverse of the unit `(↑ₐ r - a)`.

## Main statements

* `spectrum.unit_smul_eq_smul` and `spectrum.smul_eq_smul`: units in the scalar ring commute
  (multiplication) with the spectrum, and over a field even `0` commutes with the spectrum.
* `spectrum.left_add_coset_eq`: elements of the scalar ring commute (addition) with the spectrum.
* `spectrum.unit_mem_mul_comm` and `spectrum.preimage_units_mul_comm`: the
  units (of `R`) in `σ (a*b)` coincide with those in `σ (b*a)`.
* `spectrum.scalar_eq`: in a nontrivial algebra over a field, the spectrum of a scalar is
  a singleton.

## Notation

* `σ a` : `spectrum R a` of `a : A`
-/

@[expose] public section


open Set

open scoped Pointwise Ring

universe u v

section Defs

variable (R : Type u) {A : Type v}
variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "↑ₐ" => algebraMap R A

-- definition and basic properties
/-- Given a commutative ring `R` and an `R`-algebra `A`, the *resolvent set* of `a : A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is a unit of the
algebra `A`. -/
def resolventSet (a : A) : Set R :=
  {r : R | IsUnit (↑ₐ r - a)}

/-- Given a commutative ring `R` and an `R`-algebra `A`, the *spectrum* of `a : A`
is the `Set R` consisting of those `r : R` for which `r•1 - a` is not a unit of the
algebra `A`.

The spectrum is simply the complement of the resolvent set. -/
def spectrum (a : A) : Set R :=
  (resolventSet R a)ᶜ

variable {R}

/-- Given an `a : A` where `A` is an `R`-algebra, the *resolvent* is
    a map `R → A` which sends `r : R` to `(algebraMap R A r - a)⁻¹` when
    `r ∈ resolvent R A` and `0` when `r ∈ spectrum R A`. -/
noncomputable def resolvent (a : A) (r : R) : A := (↑ₐ r - a)⁻¹ʳ

/-- The unit `1 - r⁻¹ • a` constructed from `r • 1 - a` when the latter is a unit. -/
@[simps]
noncomputable def IsUnit.subInvSMul {r : Rˣ} {s : R} {a : A} (h : IsUnit <| r • ↑ₐ s - a) : Aˣ where
  val := ↑ₐ s - r⁻¹ • a
  inv := r • ↑h.unit⁻¹
  val_inv := by rw [mul_smul_comm, ← smul_mul_assoc, smul_sub, smul_inv_smul, h.mul_val_inv]
  inv_val := by rw [smul_mul_assoc, ← mul_smul_comm, smul_sub, smul_inv_smul, h.val_inv_mul]

end Defs

namespace spectrum

section ScalarSemiring

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

theorem mem_iff {r : R} {a : A} : r ∈ σ a ↔ ¬IsUnit (↑ₐ r - a) :=
  Iff.rfl

theorem notMem_iff {r : R} {a : A} : r ∉ σ a ↔ IsUnit (↑ₐ r - a) := by
  simp [mem_iff]

variable (R)

theorem zero_mem_iff {a : A} : (0 : R) ∈ σ a ↔ ¬IsUnit a := by
  rw [mem_iff, map_zero, zero_sub, IsUnit.neg_iff]

alias ⟨not_isUnit_of_zero_mem, zero_mem⟩ := spectrum.zero_mem_iff

theorem zero_notMem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUnit a := by
  rw [zero_mem_iff, Classical.not_not]

alias ⟨isUnit_of_zero_notMem, zero_notMem⟩ := spectrum.zero_notMem_iff

@[simp]
lemma _root_.Units.zero_notMem_spectrum (a : Aˣ) : 0 ∉ spectrum R (a : A) :=
  spectrum.zero_notMem R a.isUnit

lemma subset_singleton_zero_compl {a : A} (ha : IsUnit a) : spectrum R a ⊆ {0}ᶜ :=
  Set.subset_compl_singleton_iff.mpr <| spectrum.zero_notMem R ha

variable {R}

theorem mem_resolventSet_of_left_right_inverse {r : R} {a b c : A} (h₁ : (↑ₐ r - a) * b = 1)
    (h₂ : c * (↑ₐ r - a) = 1) : r ∈ resolventSet R a :=
  Units.isUnit ⟨↑ₐ r - a, b, h₁, by rwa [← left_inv_eq_right_inv h₂ h₁]⟩

theorem mem_resolventSet_iff {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (↑ₐ r - a) :=
  Iff.rfl

@[simp]
theorem algebraMap_mem_iff (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} {r : R} :
    algebraMap R S r ∈ spectrum S a ↔ r ∈ spectrum R a := by
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, one_smul]

protected alias ⟨of_algebraMap_mem, algebraMap_mem⟩ := spectrum.algebraMap_mem_iff

@[simp]
theorem preimage_algebraMap (S : Type*) {R A : Type*} [CommSemiring R] [CommSemiring S]
    [Ring A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] {a : A} :
    algebraMap R S ⁻¹' spectrum S a = spectrum R a :=
  Set.ext fun _ => spectrum.algebraMap_mem_iff _

@[simp]
theorem resolventSet_of_subsingleton [Subsingleton A] (a : A) : resolventSet R a = Set.univ := by
  simp_rw [resolventSet, Subsingleton.elim (algebraMap R A _ - a) 1, isUnit_one, Set.setOf_true]

@[simp]
theorem of_subsingleton [Subsingleton A] (a : A) : spectrum R a = ∅ := by
  rw [spectrum, resolventSet_of_subsingleton, Set.compl_univ]

theorem resolvent_eq {a : A} {r : R} (h : r ∈ resolventSet R a) : resolvent a r = ↑h.unit⁻¹ :=
  Ring.inverse_unit h.unit

theorem units_smul_resolvent {r : Rˣ} {s : R} {a : A} :
    r • resolvent a (s : R) = resolvent (r⁻¹ • a) (r⁻¹ • s : R) := by
  by_cases h : s ∈ spectrum R a
  · rw [mem_iff] at h
    simp only [resolvent, Algebra.algebraMap_eq_smul_one] at *
    rw [smul_assoc, ← smul_sub]
    have h' : ¬IsUnit (r⁻¹ • (s • (1 : A) - a)) := fun hu =>
      h (by simpa only [smul_inv_smul] using IsUnit.smul r hu)
    simp only [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h', smul_zero]
  · simp only [resolvent]
    have h' : IsUnit (r • algebraMap R A (r⁻¹ • s) - a) := by
      simpa [Algebra.algebraMap_eq_smul_one, smul_assoc] using notMem_iff.mp h
    rw [← h'.val_subInvSMul, ← (notMem_iff.mp h).unit_spec, Ring.inverse_unit, Ring.inverse_unit,
      h'.val_inv_subInvSMul]
    simp only [Algebra.algebraMap_eq_smul_one, smul_assoc, smul_inv_smul]

theorem units_smul_resolvent_self {r : Rˣ} {a : A} :
    r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R) := by
  simpa only [Units.smul_def, smul_eq_mul, Units.inv_mul] using
    @units_smul_resolvent _ _ _ _ _ r r a

/-- The resolvent is a unit when the argument is in the resolvent set. -/
theorem isUnit_resolvent {r : R} {a : A} : r ∈ resolventSet R a ↔ IsUnit (resolvent a r) :=
  isUnit_ringInverse.symm

theorem inv_mem_resolventSet {r : Rˣ} {a : Aˣ} (h : (r : R) ∈ resolventSet R (a : A)) :
    (↑r⁻¹ : R) ∈ resolventSet R (↑a⁻¹ : A) := by
  rw [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, ← Units.smul_def] at h ⊢
  rw [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv, IsUnit.sub_iff]
  have h₁ : (a : A) * (r • (↑a⁻¹ : A) - 1) = r • (1 : A) - a := by
    rw [mul_sub, mul_smul_comm, a.mul_inv, mul_one]
  have h₂ : (r • (↑a⁻¹ : A) - 1) * a = r • (1 : A) - a := by
    rw [sub_mul, smul_mul_assoc, a.inv_mul, one_mul]
  have hcomm : Commute (a : A) (r • (↑a⁻¹ : A) - 1) := by rwa [← h₂] at h₁
  exact (hcomm.isUnit_mul_iff.mp (h₁.symm ▸ h)).2

theorem inv_mem_iff {r : Rˣ} {a : Aˣ} : (r : R) ∈ σ (a : A) ↔ (↑r⁻¹ : R) ∈ σ (↑a⁻¹ : A) :=
  not_iff_not.2 <| ⟨inv_mem_resolventSet, inv_mem_resolventSet⟩

theorem zero_mem_resolventSet_of_unit (a : Aˣ) : 0 ∈ resolventSet R (a : A) := by
  simpa only [mem_resolventSet_iff, ← notMem_iff, zero_notMem_iff] using a.isUnit

theorem ne_zero_of_mem_of_unit {a : Aˣ} {r : R} (hr : r ∈ σ (a : A)) : r ≠ 0 := fun hn =>
  (hn ▸ hr) (zero_mem_resolventSet_of_unit a)

theorem add_mem_iff {a : A} {r s : R} : r + s ∈ σ a ↔ r ∈ σ (-↑ₐ s + a) := by
  simp only [mem_iff, sub_neg_eq_add, ← sub_sub, map_add]

theorem add_mem_add_iff {a : A} {r s : R} : r + s ∈ σ (↑ₐ s + a) ↔ r ∈ σ a := by
  rw [add_mem_iff, neg_add_cancel_left]

theorem smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} : r • s ∈ σ (r • a) ↔ s ∈ σ a := by
  simp only [mem_iff, Algebra.algebraMap_eq_smul_one, smul_assoc, ← smul_sub, isUnit_smul_iff]

theorem unit_smul_eq_smul (a : A) (r : Rˣ) : σ (r • a) = r • σ a := by
  ext x
  have x_eq : x = r • r⁻¹ • x := by simp
  nth_rw 1 [x_eq]
  rw [smul_mem_smul_iff]
  constructor
  · exact fun h => ⟨r⁻¹ • x, ⟨h, show r • r⁻¹ • x = x by simp⟩⟩
  · rintro ⟨w, _, (x'_eq : r • w = x)⟩
    simpa [← x'_eq]

-- `r ∈ σ(a*b) ↔ r ∈ σ(b*a)` for any `r : Rˣ`
theorem unit_mem_mul_comm {a b : A} {r : Rˣ} : ↑r ∈ σ (a * b) ↔ ↑r ∈ σ (b * a) := by
  have h₁ : ∀ x y : A, IsUnit (1 - x * y) → IsUnit (1 - y * x) := by
    refine fun x y h => ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, ?_, ?_⟩, rfl⟩
    · calc
        (1 - y * x) * (1 + y * (IsUnit.unit h).inv * x) =
            1 - y * x + y * ((1 - x * y) * h.unit.inv) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.mul_val_inv, mul_one, sub_add_cancel]
    · calc
        (1 + y * (IsUnit.unit h).inv * x) * (1 - y * x) =
            1 - y * x + y * (h.unit.inv * (1 - x * y)) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.val_inv_mul, mul_one, sub_add_cancel]
  have := Iff.intro (h₁ (r⁻¹ • a) b) (h₁ b (r⁻¹ • a))
  rw [mul_smul_comm r⁻¹ b a] at this
  simpa only [mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one, ← Units.smul_def,
    IsUnit.smul_sub_iff_sub_inv_smul, smul_mul_assoc]

theorem preimage_units_mul_comm (a b : A) :
    ((↑) : Rˣ → R) ⁻¹' σ (a * b) = (↑) ⁻¹' σ (b * a) :=
  Set.ext fun _ => unit_mem_mul_comm

theorem setOf_isUnit_inter_mul_comm (a b : A) :
    {r | IsUnit r} ∩ σ (a * b) = {r | IsUnit r} ∩ σ (b * a) := by
  ext r
  simpa using fun hr : IsUnit r ↦ unit_mem_mul_comm (r := hr.unit)

section Star

variable [InvolutiveStar R] [StarRing A] [StarModule R A]

theorem star_mem_resolventSet_iff {r : R} {a : A} :
    star r ∈ resolventSet R a ↔ r ∈ resolventSet R (star a) := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
    simpa only [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one, star_sub, star_smul,
      star_star, star_one] using IsUnit.star h

protected theorem map_star (a : A) : σ (star a) = star (σ a) := by
  ext
  simpa only [Set.mem_star, mem_iff, not_iff_not] using star_mem_resolventSet_iff.symm

end Star

end ScalarSemiring

section ScalarRing

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

theorem subset_subalgebra {S R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S R A] {s : S} (a : s) :
    spectrum R (a : A) ⊆ spectrum R a :=
  Set.compl_subset_compl.mpr fun _ ↦ IsUnit.map (SubalgebraClass.val s)

theorem singleton_add_eq (a : A) (r : R) : {r} + σ a = σ (↑ₐ r + a) :=
  ext fun x => by
    rw [singleton_add, image_add_left, mem_preimage, add_comm, add_mem_iff, map_neg, neg_neg]

theorem add_singleton_eq (a : A) (r : R) : σ a + {r} = σ (a + ↑ₐ r) :=
  add_comm {r} (σ a) ▸ add_comm (algebraMap R A r) a ▸ singleton_add_eq a r

theorem vadd_eq (a : A) (r : R) : r +ᵥ σ a = σ (↑ₐ r + a) :=
  singleton_add.symm.trans <| singleton_add_eq a r

theorem _root_.resolventSet_neg (a : A) : resolventSet R (-a) = -resolventSet R a :=
  Set.ext fun x => by
    simp only [mem_neg, mem_resolventSet_iff, map_neg, ← neg_add', IsUnit.neg_iff, sub_neg_eq_add]

theorem neg_eq (a : A) : -σ a = σ (-a) := by
  rw [spectrum, Set.compl_neg, spectrum, resolventSet_neg]

theorem singleton_sub_eq (a : A) (r : R) : {r} - σ a = σ (↑ₐ r - a) := by
  rw [sub_eq_add_neg, neg_eq, singleton_add_eq, sub_eq_add_neg]

theorem sub_singleton_eq (a : A) (r : R) : σ a - {r} = σ (a - ↑ₐ r) := by
  simpa only [neg_sub, neg_eq] using congr_arg Neg.neg (singleton_sub_eq a r)

end ScalarRing

section ScalarSemifield

variable {R : Type u} {A : Type v} [Semifield R] [Ring A] [Algebra R A]

@[simp]
lemma inv₀_mem_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (a : A) ↔ r ∈ spectrum R (↑a⁻¹ : A) := by
  obtain (rfl | hr) := eq_or_ne r 0
  · simp
  · lift r to Rˣ using hr.isUnit
    simp [inv_mem_iff]

lemma inv₀_mem_inv_iff {r : R} {a : Aˣ} :
    r⁻¹ ∈ spectrum R (↑a⁻¹ : A) ↔ r ∈ spectrum R (a : A) := by
  simp

alias ⟨of_inv₀_mem, inv₀_mem⟩ := inv₀_mem_iff
alias ⟨of_inv₀_mem_inv, inv₀_mem_inv⟩ := inv₀_mem_inv_iff

end ScalarSemifield

section ScalarField

variable {𝕜 : Type u} {A : Type v}
variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

local notation "σ" => spectrum 𝕜

local notation "↑ₐ" => algebraMap 𝕜 A

/-- Without the assumption `Nontrivial A`, then `0 : A` would be invertible. -/
@[simp]
theorem zero_eq [Nontrivial A] : σ (0 : A) = {0} := by
  refine Set.Subset.antisymm ?_ (by simp [Algebra.algebraMap_eq_smul_one, mem_iff])
  rw [spectrum, Set.compl_subset_comm]
  intro k hk
  rw [Set.mem_compl_singleton_iff] at hk
  have : IsUnit (Units.mk0 k hk • (1 : A)) := IsUnit.smul (Units.mk0 k hk) isUnit_one
  simpa [mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one]

@[simp]
theorem scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k} := by
  rw [← add_zero (↑ₐ k), ← singleton_add_eq, zero_eq, Set.singleton_add_singleton, add_zero]

@[simp]
theorem one_eq [Nontrivial A] : σ (1 : A) = {1} :=
  calc
    σ (1 : A) = σ (↑ₐ 1) := by rw [Algebra.algebraMap_eq_smul_one, one_smul]
    _ = {1} := scalar_eq 1

/-- the assumption `(σ a).Nonempty` is necessary and cannot be removed without
further conditions on the algebra `A` and scalar field `𝕜`. -/
theorem smul_eq_smul [Nontrivial A] (k : 𝕜) (a : A) (ha : (σ a).Nonempty) :
    σ (k • a) = k • σ a := by
  rcases eq_or_ne k 0 with (rfl | h)
  · simpa [ha, zero_smul_set] using (show {(0 : 𝕜)} = (0 : Set 𝕜) from rfl)
  · exact unit_smul_eq_smul a (Units.mk0 k h)

theorem nonzero_mul_comm (a b : A) : σ (a * b) \ {0} = σ (b * a) \ {0} := by
  suffices h : ∀ x y : A, σ (x * y) \ {0} ⊆ σ (y * x) \ {0} from
    Set.eq_of_subset_of_subset (h a b) (h b a)
  rintro _ _ k ⟨k_mem, k_ne⟩
  change ((Units.mk0 k k_ne) : 𝕜) ∈ _ at k_mem
  exact ⟨unit_mem_mul_comm.mp k_mem, k_ne⟩

protected theorem map_inv (a : Aˣ) : (σ (a : A))⁻¹ = σ (↑a⁻¹ : A) := by
  ext
  simp

end ScalarField

end spectrum

namespace AlgHom

section CommSemiring

variable {F R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [FunLike F A B] [AlgHomClass F R A B]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

theorem mem_resolventSet_apply (φ : F) {a : A} {r : R} (h : r ∈ resolventSet R a) :
    r ∈ resolventSet R ((φ : A → B) a) := by
  simpa only [map_sub, AlgHomClass.commutes] using h.map φ

theorem spectrum_apply_subset (φ : F) (a : A) : σ ((φ : A → B) a) ⊆ σ a := fun _ =>
  mt (mem_resolventSet_apply φ)

end CommSemiring

section CommRing

variable {F R A : Type*} [CommRing R] [Ring A] [Algebra R A]
variable [FunLike F A R] [AlgHomClass F R A R]

local notation "σ" => spectrum R

local notation "↑ₐ" => algebraMap R A

theorem apply_mem_spectrum [Nontrivial R] (φ : F) (a : A) : φ a ∈ σ a := by
  have h : ↑ₐ (φ a) - a ∈ RingHom.ker (φ : A →+* R) := by
    simp only [RingHom.mem_ker, map_sub, RingHom.coe_coe, AlgHomClass.commutes,
      Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  simp only [spectrum.mem_iff, ← mem_nonunits_iff,
    coe_subset_nonunits (RingHom.ker_ne_top (φ : A →+* R)) h]

end CommRing

end AlgHom

@[simp]
theorem AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiring R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] [EquivLike F A B] [AlgEquivClass F R A B] (f : F) (a : A) :
    spectrum R (f a) = spectrum R a :=
  Set.Subset.antisymm (AlgHom.spectrum_apply_subset _ _) <| by
    simpa using AlgHom.spectrum_apply_subset (AlgEquivClass.toAlgEquiv f : A ≃ₐ[R] B).symm (f a)

section ConjugateUnits

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Conjugation by a unit preserves the spectrum, inverse on right. -/
@[simp]
lemma spectrum.units_conjugate {a : A} {u : Aˣ} :
    spectrum R (u * a * u⁻¹) = spectrum R a := by
  suffices ∀ (b : A) (v : Aˣ), spectrum R (v * b * v⁻¹) ⊆ spectrum R b by
    refine le_antisymm (this a u) ?_
    apply le_of_eq_of_le ?_ <| this (u * a * u⁻¹) u⁻¹
    simp [mul_assoc]
  intro a u μ hμ
  rw [spectrum.mem_iff] at hμ ⊢
  contrapose hμ
  simpa [mul_sub, sub_mul, Algebra.right_comm] using u.isUnit.mul hμ |>.mul u⁻¹.isUnit

/-- Conjugation by a unit preserves the spectrum, inverse on left. -/
@[simp]
lemma spectrum.units_conjugate' {a : A} {u : Aˣ} :
    spectrum R (u⁻¹ * a * u) = spectrum R a := by
  simpa using spectrum.units_conjugate (u := u⁻¹)

end ConjugateUnits
