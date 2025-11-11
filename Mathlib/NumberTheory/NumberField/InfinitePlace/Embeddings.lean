/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot
-/
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Embeddings of number fields

This file defines the embeddings of a number field and, in particular, the embeddings into
the field of complex numbers.

## Main Definitions and Results

* `NumberField.Embeddings.range_eval_eq_rootSet_minpoly`: let `x ∈ K` with `K` a number field and
  let `A` be an algebraically closed field of char. 0. Then the images of `x` under the
  embeddings of `K` in `A` are exactly the roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.

## Tags

number field, embeddings
-/

open scoped Finset

namespace NumberField.Embeddings

section Fintype

open Module

variable (K : Type*) [Field K] [NumberField K]
variable (A : Type*) [Field A] [CharZero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : Fintype (K →+* A) :=
  Fintype.ofEquiv (K →ₐ[ℚ] A) RingHom.equivRatAlgHom.symm

variable [IsAlgClosed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
theorem card : Fintype.card (K →+* A) = finrank ℚ K := by
  rw [Fintype.ofEquiv_card RingHom.equivRatAlgHom.symm, AlgHom.card]

instance : Nonempty (K →+* A) := by
  rw [← Fintype.card_pos_iff, NumberField.Embeddings.card K A]
  exact Module.finrank_pos

end Fintype

section Roots

open Set Polynomial

variable (K A : Type*) [Field K] [NumberField K] [Field A] [Algebra ℚ A] [IsAlgClosed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
theorem range_eval_eq_rootSet_minpoly :
    (range fun φ : K →+* A => φ x) = (minpoly ℚ x).rootSet A := by
  convert (NumberField.isAlgebraic K).range_eval_eq_rootSet_minpoly A x using 1
  ext a
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ.toRatAlgHom, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ.toRingHom, hφ⟩⟩

end Roots

section Bounded

open Module Polynomial Set

variable {K : Type*} [Field K] [NumberField K]
variable {A : Type*} [NormedField A] [IsAlgClosed A] [NormedAlgebra ℚ A]

theorem coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ‖φ x‖ ≤ B) (i : ℕ) :
    ‖(minpoly ℚ x).coeff i‖ ≤ max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2) := by
  have hx := Algebra.IsSeparable.isIntegral ℚ x
  rw [← norm_algebraMap' A, ← coeff_map (algebraMap ℚ A)]
  refine coeff_bdd_of_roots_le _ (minpoly.monic hx)
      (IsAlgClosed.splits_codomain _) (minpoly.natDegree_le x) (fun z hz => ?_) i
  classical
  rw [← Multiset.mem_toFinset] at hz
  obtain ⟨φ, rfl⟩ := (range_eval_eq_rootSet_minpoly K A x).symm.subset hz
  exact h φ

variable (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
theorem finite_of_norm_le (B : ℝ) : {x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* A, ‖φ x‖ ≤ B}.Finite := by
  classical
  let C := Nat.ceil (max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2))
  have := bUnion_roots_finite (algebraMap ℤ K) (finrank ℚ K) (finite_Icc (-C : ℤ) C)
  refine this.subset fun x hx => ?_; simp_rw [mem_iUnion]
  have h_map_ℚ_minpoly := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx.1
  refine ⟨_, ⟨?_, fun i => ?_⟩, mem_rootSet.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval ℤ x⟩⟩
  · rw [← (minpoly.monic hx.1).natDegree_map (algebraMap ℤ ℚ), ← h_map_ℚ_minpoly]
    exact minpoly.natDegree_le x
  rw [mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
  refine (Eq.trans_le ?_ <| coeff_bdd_of_norm_le hx.2 i).trans (Nat.le_ceil _)
  rw [h_map_ℚ_minpoly, coeff_map, eq_intCast, Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
theorem pow_eq_one_of_norm_eq_one {x : K} (hxi : IsIntegral ℤ x) (hx : ∀ φ : K →+* A, ‖φ x‖ = 1) :
    ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1 := by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    @Set.Infinite.exists_ne_map_eq_of_mapsTo _ _ _ _ (x ^ · : ℕ → K) Set.infinite_univ
      (by exact fun a _ => ⟨hxi.pow a, fun φ => by simp [hx φ]⟩) (finite_of_norm_le K A (1 : ℝ))
  wlog hlt : b < a
  · exact this K A hxi hx b a habne.symm h.symm (habne.lt_or_gt.resolve_right hlt)
  refine ⟨a - b, tsub_pos_of_lt hlt, ?_⟩
  rw [← Nat.sub_add_cancel hlt.le, pow_add, mul_left_eq_self₀] at h
  refine h.resolve_right fun hp => ?_
  specialize hx (IsAlgClosed.lift (R := ℚ)).toRingHom
  rw [eq_zero_of_pow_eq_zero hp, map_zero, norm_zero] at hx; norm_num at hx

end Bounded

end NumberField.Embeddings

section Place

variable {K : Type*} [Field K] {A : Type*} [NormedDivisionRing A] [Nontrivial A] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def NumberField.place : AbsoluteValue K ℝ :=
  (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp φ.injective

@[simp]
theorem NumberField.place_apply (x : K) : (NumberField.place φ) x = norm (φ x) := rfl

end Place

namespace NumberField.ComplexEmbedding

open Complex NumberField

open scoped ComplexConjugate

variable (K : Type*) [Field K] {k : Type*} [Field k]

/--
A (random) lift of the complex embedding `φ : k →+* ℂ` to an extension `K` of `k`.
-/
noncomputable def lift [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k →+* ℂ) : K →+* ℂ := by
  letI := φ.toAlgebra
  exact (IsAlgClosed.lift (R := k)).toRingHom

@[simp]
theorem lift_comp_algebraMap [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k →+* ℂ) :
    (lift K φ).comp (algebraMap k K) = φ := by
  unfold lift
  letI := φ.toAlgebra
  rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, RingHom.algebraMap_toAlgebra']

@[simp]
theorem lift_algebraMap_apply [Algebra k K] [Algebra.IsAlgebraic k K] (φ : k →+* ℂ) (x : k) :
    lift K φ (algebraMap k K x) = φ x :=
  RingHom.congr_fun (lift_comp_algebraMap K φ) x

variable {K}

/-- The conjugate of a complex embedding as a complex embedding. -/
abbrev conjugate (φ : K →+* ℂ) : K →+* ℂ := star φ

@[simp]
theorem conjugate_comp (φ : K →+* ℂ) (σ : k →+* K) :
    (conjugate φ).comp σ = conjugate (φ.comp σ) :=
  rfl

@[simp]
theorem conjugate_coe_eq (φ : K →+* ℂ) (x : K) : (conjugate φ) x = conj (φ x) := rfl

theorem place_conjugate (φ : K →+* ℂ) : place (conjugate φ) = place φ := by
  ext; simp only [place_apply, norm_conj, conjugate_coe_eq]

/-- An embedding into `ℂ` is real if it is fixed by complex conjugation. -/
abbrev IsReal (φ : K →+* ℂ) : Prop := IsSelfAdjoint φ

theorem isReal_iff {φ : K →+* ℂ} : IsReal φ ↔ conjugate φ = φ := isSelfAdjoint_iff

theorem isReal_conjugate_iff {φ : K →+* ℂ} : IsReal (conjugate φ) ↔ IsReal φ :=
  IsSelfAdjoint.star_iff

/-- A real embedding as a ring homomorphism from `K` to `ℝ` . -/
def IsReal.embedding {φ : K →+* ℂ} (hφ : IsReal φ) : K →+* ℝ where
  toFun x := (φ x).re
  map_one' := by simp only [map_one, one_re]
  map_mul' := by
    simp only [Complex.conj_eq_iff_im.mp (RingHom.congr_fun hφ _), map_mul, mul_re,
      mul_zero, tsub_zero, forall_const]
  map_zero' := by simp only [map_zero, zero_re]
  map_add' := by simp only [map_add, add_re, forall_const]

@[simp]
theorem IsReal.coe_embedding_apply {φ : K →+* ℂ} (hφ : IsReal φ) (x : K) :
    (hφ.embedding x : ℂ) = φ x := by
  apply Complex.ext
  · rfl
  · rw [ofReal_im, eq_comm, ← Complex.conj_eq_iff_im]
    exact RingHom.congr_fun hφ x

lemma IsReal.comp (f : k →+* K) {φ : K →+* ℂ} (hφ : IsReal φ) :
    IsReal (φ.comp f) := by ext1 x; simpa using RingHom.congr_fun hφ (f x)

lemma isReal_comp_iff {f : k ≃+* K} {φ : K →+* ℂ} :
    IsReal (φ.comp (f : k →+* K)) ↔ IsReal φ :=
  ⟨fun H ↦ by convert H.comp f.symm.toRingHom; ext1; simp, IsReal.comp _⟩

lemma exists_comp_symm_eq_of_comp_eq [Algebra k K] [IsGalois k K] (φ ψ : K →+* ℂ)
    (h : φ.comp (algebraMap k K) = ψ.comp (algebraMap k K)) :
    ∃ σ : Gal(K/k), φ.comp σ.symm = ψ := by
  letI := (φ.comp (algebraMap k K)).toAlgebra
  letI := φ.toAlgebra
  have : IsScalarTower k K ℂ := IsScalarTower.of_algebraMap_eq' rfl
  let ψ' : K →ₐ[k] ℂ := { ψ with commutes' := fun r ↦ (RingHom.congr_fun h r).symm }
  use (AlgHom.restrictNormal' ψ' K).symm
  ext1 x
  exact AlgHom.restrictNormal_commutes ψ' K x

variable [Algebra k K] (φ : K →+* ℂ) (σ : Gal(K/k))

/--
`IsConj φ σ` states that `σ : Gal(K/k)` is the conjugation under the embedding `φ : K →+* ℂ`.
-/
def IsConj : Prop := conjugate φ = φ.comp σ

variable {φ σ}

lemma IsConj.eq (h : IsConj φ σ) (x) : φ (σ x) = star (φ x) := RingHom.congr_fun h.symm x

lemma IsConj.ext {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁) (h₂ : IsConj φ σ₂) : σ₁ = σ₂ :=
  AlgEquiv.ext fun x ↦ φ.injective ((h₁.eq x).trans (h₂.eq x).symm)

lemma IsConj.ext_iff {σ₁ σ₂ : Gal(K/k)} (h₁ : IsConj φ σ₁) : σ₁ = σ₂ ↔ IsConj φ σ₂ :=
  ⟨fun e ↦ e ▸ h₁, h₁.ext⟩

lemma IsConj.isReal_comp (h : IsConj φ σ) : IsReal (φ.comp (algebraMap k K)) := by
  ext1 x
  simp only [conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply, ← h.eq,
    starRingEnd_apply, AlgEquiv.commutes]

lemma isConj_one_iff : IsConj φ (1 : Gal(K/k)) ↔ IsReal φ := Iff.rfl

alias ⟨_, IsReal.isConjGal_one⟩ := ComplexEmbedding.isConj_one_iff

lemma isConj_ne_one_iff (hσ : IsConj φ σ) :
    σ ≠ 1 ↔ ¬ IsReal φ :=
  not_iff_not.mpr ⟨fun h ↦ isConj_one_iff.mp (h ▸ hσ),
    fun h ↦ (IsConj.ext_iff hσ).mpr h.isConjGal_one⟩

lemma IsConj.symm (hσ : IsConj φ σ) :
    IsConj φ σ.symm := RingHom.ext fun x ↦ by simpa using congr_arg star (hσ.eq (σ.symm x))

lemma isConj_symm : IsConj φ σ.symm ↔ IsConj φ σ :=
  ⟨IsConj.symm, IsConj.symm⟩

lemma isConj_apply_apply (hσ : IsConj φ σ) (x : K) :
    σ (σ x) = x := by
  simp [← φ.injective.eq_iff, hσ.eq]

theorem IsConj.comp (hσ : IsConj φ σ) (ν : Gal(K/k)) :
    IsConj (φ.comp ν) (ν⁻¹ * σ * ν) := by
  ext
  simpa [← AlgEquiv.mul_apply, ← mul_assoc] using RingHom.congr_fun hσ _

lemma orderOf_isConj_two_of_ne_one (hσ : IsConj φ σ) (hσ' : σ ≠ 1) :
    orderOf σ = 2 :=
  orderOf_eq_prime_iff.mpr ⟨by ext; simpa using isConj_apply_apply hσ _, hσ'⟩

section Extension

variable {K : Type*} (L : Type*) [Field K] [Field L] (ψ : K →+* ℂ) [Algebra K L]

/-- If `L/K` and `ψ : K →+* ℂ`, then the type of `ComplexEmbedding.Extension L ψ` consists of all
`φ : L →+* ℂ` such that `φ.comp (algebraMap K L) = ψ`. -/
protected abbrev Extension := { φ : L →+* ℂ // φ.comp (algebraMap K L) = ψ }

namespace Extension

variable (φ : ComplexEmbedding.Extension L ψ) {L ψ}

theorem comp_eq : φ.1.comp (algebraMap K L) = ψ := φ.2

theorem conjugate_comp_ne (h : ¬IsReal ψ) : (conjugate φ).comp (algebraMap K L) ≠ ψ := by
  simp_all [ComplexEmbedding.isReal_iff, comp_eq]

theorem not_isReal_of_not_isReal (h : ¬IsReal ψ) : ¬IsReal φ.1 :=
  mt (IsReal.comp _) (comp_eq φ ▸ h)

end Extension

variable (K) {L ψ}

/-- If `L/K` and `φ : L →+* ℂ`, then `IsMixed K φ` if the image of `φ` is complex while the image
of `φ` restricted to `K` is real.

This is the complex embedding analogue of `InfinitePlace.IsRamified K w`, where
`w : InfinitePlace L`. It is not the same concept because conjugation of `φ` in this case
leads to two distinct mixed embeddings but only a single ramified place `w`, leading to a
two-to-one isomorphism between them. -/
abbrev IsMixed (φ : L →+* ℂ) :=
  ComplexEmbedding.IsReal (φ.comp (algebraMap K L)) ∧ ¬ComplexEmbedding.IsReal φ

/-- If `L/K` and `φ : L →+* ℂ`, then `IsMixed K φ` if `φ` is not mixed in `K`, i.e., `φ` is real
if and only if it's restriction to `K` is.

This is the complex embedding analogue of `InfinitePlace.IsUnramified K w`, where
`w : InfinitePlace L`. In this case there is an isomorphism between unmixed embeddings and
unramified infinite places. -/
abbrev IsUnmixed (φ : L →+* ℂ) := IsReal (φ.comp (algebraMap K L)) → IsReal φ

theorem IsUnmixed.isReal_iff_isReal {φ : L →+* ℂ} (h : IsUnmixed K φ) :
    IsReal (φ.comp (algebraMap K L)) ↔ IsReal φ := by
  aesop (add simp [IsReal.comp])

end Extension

end NumberField.ComplexEmbedding
