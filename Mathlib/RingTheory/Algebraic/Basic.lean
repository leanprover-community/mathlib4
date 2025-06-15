/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Adjoin.Polynomial
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/

universe u v w

open Polynomial

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

@[nontriviality]
theorem is_transcendental_of_subsingleton [Subsingleton R] (x : A) : Transcendental R x :=
  fun ⟨p, h, _⟩ => h <| Subsingleton.elim p 0

variable {R}

theorem IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic R a) : Nontrivial R := by
  contrapose! h
  rw [not_nontrivial_iff_subsingleton] at h
  apply is_transcendental_of_subsingleton

variable (R A)

theorem Algebra.IsAlgebraic.nontrivial [alg : Algebra.IsAlgebraic R A] : Nontrivial R :=
  (alg.1 0).nontrivial

instance (priority := low) Algebra.transcendental_of_subsingleton [Subsingleton R] :
    Algebra.Transcendental R A :=
  ⟨⟨0, is_transcendental_of_subsingleton R 0⟩⟩

theorem Polynomial.transcendental_X : Transcendental R (X (R := R)) := by
  simp [transcendental_iff]

variable {R A}

theorem IsAlgebraic.of_aeval {r : A} (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ nonZeroDivisors R) (H : IsAlgebraic R (aeval r f)) :
    IsAlgebraic R r := by
  obtain ⟨p, h1, h2⟩ := H
  have : (p.comp f).coeff (p.natDegree * f.natDegree) ≠ 0 := fun h ↦ h1 <| by
    rwa [coeff_comp_degree_mul_degree hf,
      mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hf' _),
      leadingCoeff_eq_zero] at h
  exact ⟨p.comp f, fun h ↦ this (by simp [h]), by rwa [aeval_comp]⟩

theorem Transcendental.aeval {r : A} (H : Transcendental R r) (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ nonZeroDivisors R) :
    Transcendental R (aeval r f) := fun h ↦ H (h.of_aeval f hf hf')

/-- If `r : A` and `f : R[X]` are transcendental over `R`, then `Polynomial.aeval r f` is also
transcendental over `R`. For the converse, see `Transcendental.of_aeval` and
`transcendental_aeval_iff`. -/
theorem Transcendental.aeval_of_transcendental {r : A} (H : Transcendental R r)
    {f : R[X]} (hf : Transcendental R f) : Transcendental R (Polynomial.aeval r f) := by
  rw [transcendental_iff] at H hf ⊢
  intro p hp
  exact hf _ (H _ (by rwa [← aeval_comp, comp_eq_aeval] at hp))

/-- If `Polynomial.aeval r f` is transcendental over `R`, then `f : R[X]` is also
transcendental over `R`. In fact, the `r` is also transcendental over `R` provided that `R`
is a field (see `transcendental_aeval_iff`). -/
theorem Transcendental.of_aeval {r : A} {f : R[X]}
    (H : Transcendental R (Polynomial.aeval r f)) : Transcendental R f := by
  rw [transcendental_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp, comp_eq_aeval, hp, map_zero])

theorem IsAlgebraic.of_aeval_of_transcendental {r : A} {f : R[X]}
    (H : IsAlgebraic R (aeval r f)) (hf : Transcendental R f) : IsAlgebraic R r := by
  contrapose H
  exact Transcendental.aeval_of_transcendental H hf

theorem Polynomial.transcendental (f : R[X]) (hf : f.natDegree ≠ 0)
    (hf' : f.leadingCoeff ∈ nonZeroDivisors R) :
    Transcendental R f := by
  simpa using (transcendental_X R).aeval f hf hf'

theorem isAlgebraic_iff_not_injective {x : A} :
    IsAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) := by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]

/-- An element `x` is transcendental over `R` if and only if the map `Polynomial.aeval x`
is injective. This is similar to `algebraicIndependent_iff_injective_aeval`. -/
theorem transcendental_iff_injective {x : A} :
    Transcendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] →ₐ[R] A) :=
  isAlgebraic_iff_not_injective.not_left

/-- An element `x` is transcendental over `R` if and only if the kernel of the ring homomorphism
`Polynomial.aeval x` is the zero ideal. This is similar to `algebraicIndependent_iff_ker_eq_bot`. -/
theorem transcendental_iff_ker_eq_bot {x : A} :
    Transcendental R x ↔ RingHom.ker (aeval (R := R) x) = ⊥ := by
  rw [transcendental_iff_injective, RingHom.injective_iff_ker_eq_bot]

theorem Algebra.isAlgebraic_of_not_injective (h : ¬ Function.Injective (algebraMap R A)) :
    Algebra.IsAlgebraic R A where
  isAlgebraic a := isAlgebraic_iff_not_injective.mpr
    fun inj ↦ h <| by convert inj.comp C_injective; ext; simp

theorem Algebra.injective_of_transcendental [h : Algebra.Transcendental R A] :
    Function.Injective (algebraMap R A) := by
  rw [transcendental_iff_not_isAlgebraic] at h
  contrapose! h
  exact isAlgebraic_of_not_injective h

end

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]
variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]
variable [IsScalarTower R S A]

theorem isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A) :=
  ⟨_, X_ne_zero, aeval_X 0⟩

/-- An element of `R` is algebraic, when viewed as an element of the `R`-algebra `A`. -/
theorem isAlgebraic_algebraMap [Nontrivial R] (x : R) : IsAlgebraic R (algebraMap R A x) :=
  ⟨_, X_sub_C_ne_zero x, by rw [map_sub, aeval_X, aeval_C, sub_self]⟩

theorem isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A) := by
  rw [← map_one (algebraMap R A)]
  exact isAlgebraic_algebraMap 1

theorem isAlgebraic_nat [Nontrivial R] (n : ℕ) : IsAlgebraic R (n : A) := by
  rw [← map_natCast (_ : R →+* A) n]
  exact isAlgebraic_algebraMap (Nat.cast n)

theorem isAlgebraic_int [Nontrivial R] (n : ℤ) : IsAlgebraic R (n : A) := by
  rw [← map_intCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Int.cast n)

theorem isAlgebraic_rat (R : Type u) {A : Type v} [DivisionRing A] [Field R] [Algebra R A] (n : ℚ) :
    IsAlgebraic R (n : A) := by
  rw [← map_ratCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Rat.cast n)

theorem isAlgebraic_of_mem_rootSet {R : Type u} {A : Type v} [CommRing R] [Field A] [Algebra R A]
    {p : R[X]} {x : A} (hx : x ∈ p.rootSet A) : IsAlgebraic R x :=
  ⟨p, ne_zero_of_mem_rootSet hx, aeval_eq_zero_of_mem_rootSet hx⟩

variable (S) in
theorem IsLocalization.isAlgebraic [Nontrivial R] (M : Submonoid R) [IsLocalization M S] :
    Algebra.IsAlgebraic R S where
  isAlgebraic x := by
    obtain rfl | hx := eq_or_ne x 0
    · exact isAlgebraic_zero
    have ⟨⟨r, m⟩, h⟩ := surj M x
    refine ⟨C m.1 * X - C r, fun eq ↦ hx ?_, by simpa [sub_eq_zero, mul_comm x] using h⟩
    rwa [← eq_mk'_iff_mul_eq, show r = 0 by simpa using congr(coeff $eq 0), mk'_zero] at h

open IsScalarTower

protected theorem IsAlgebraic.algebraMap {a : S} :
    IsAlgebraic R a → IsAlgebraic R (algebraMap S A a) := fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebraMap_apply, hf₂, map_zero]⟩

section

variable {B : Type*} [Ring B] [Algebra R B]

/-- This is slightly more general than `IsAlgebraic.algebraMap` in that it
  allows noncommutative intermediate rings `A`. -/
protected theorem IsAlgebraic.algHom (f : A →ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩

theorem isAlgebraic_algHom_iff (f : A →ₐ[R] B) (hf : Function.Injective f)
    {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a :=
  ⟨fun ⟨p, hp0, hp⟩ ↦ ⟨p, hp0, hf <| by rwa [map_zero, ← f.comp_apply, ← aeval_algHom]⟩,
    IsAlgebraic.algHom f⟩

section RingHom

omit [Algebra R S] [Algebra S A] [IsScalarTower R S A] [Algebra R B]
variable [Algebra S B] {FRS FAB : Type*}

section

variable [FunLike FRS R S] [RingHomClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB) {a : A}

theorem IsAlgebraic.ringHom_of_comp_eq (halg : IsAlgebraic R a)
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic S (g a) := by
  obtain ⟨p, h1, h2⟩ := halg
  refine ⟨p.map f, (Polynomial.map_ne_zero_iff hf).2 h1, ?_⟩
  change aeval ((g : A →+* B) a) _ = 0
  rw [← map_aeval_eq_aeval_map h, h2, map_zero]

theorem Transcendental.of_ringHom_of_comp_eq (H : Transcendental S (g a))
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental R a := fun halg ↦ H (halg.ringHom_of_comp_eq f g hf h)

theorem Algebra.IsAlgebraic.ringHom_of_comp_eq [Algebra.IsAlgebraic R A]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B := by
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hg b
  exact (Algebra.IsAlgebraic.isAlgebraic a).ringHom_of_comp_eq f g hf h

theorem Algebra.Transcendental.of_ringHom_of_comp_eq [H : Algebra.Transcendental S B]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental R A := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg ↦ H (halg.ringHom_of_comp_eq f g hf hg h)

theorem IsAlgebraic.of_ringHom_of_comp_eq (halg : IsAlgebraic S (g a))
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic R a := by
  obtain ⟨p, h1, h2⟩ := halg
  obtain ⟨q, rfl⟩ := map_surjective (f : R →+* S) hf p
  refine ⟨q, fun h' ↦ by simp [h'] at h1, hg ?_⟩
  change aeval ((g : A →+* B) a) _ = 0 at h2
  change (g : A →+* B) _ = _
  rw [map_zero, map_aeval_eq_aeval_map h, h2]

theorem Transcendental.ringHom_of_comp_eq (H : Transcendental R a)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental S (g a) := fun halg ↦ H (halg.of_ringHom_of_comp_eq f g hf hg h)

theorem Algebra.IsAlgebraic.of_ringHom_of_comp_eq [Algebra.IsAlgebraic S B]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic R A :=
  ⟨fun a ↦ (Algebra.IsAlgebraic.isAlgebraic (g a)).of_ringHom_of_comp_eq f g hf hg h⟩

theorem Algebra.Transcendental.ringHom_of_comp_eq [H : Algebra.Transcendental R A]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg ↦ H (halg.of_ringHom_of_comp_eq f g hf hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

theorem isAlgebraic_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    IsAlgebraic S (g a) ↔ IsAlgebraic R a :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) hg h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.injective f) h⟩

theorem transcendental_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    Transcendental S (g a) ↔ Transcendental R a :=
  not_congr (isAlgebraic_ringHom_iff_of_comp_eq f g hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [EquivLike FAB A B] [RingEquivClass FAB A B]
  (f : FRS) (g : FAB)

theorem Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B ↔ Algebra.IsAlgebraic R A :=
  ⟨fun H ↦ H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) (EquivLike.injective g) h,
    fun H ↦ H.ringHom_of_comp_eq f g (EquivLike.injective f) (EquivLike.surjective g) h⟩

theorem Algebra.transcendental_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B ↔ Algebra.Transcendental R A := by
  simp_rw [Algebra.transcendental_iff_not_isAlgebraic,
    Algebra.isAlgebraic_ringHom_iff_of_comp_eq f g h]

end

end RingHom

theorem Algebra.IsAlgebraic.of_injective (f : A →ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsAlgebraic R B] : Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (isAlgebraic_algHom_iff f hf).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩

/-- Transfer `Algebra.IsAlgebraic` across an `AlgEquiv`. -/
theorem AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B)
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic R B :=
  Algebra.IsAlgebraic.of_injective e.symm.toAlgHom e.symm.injective

theorem AlgEquiv.isAlgebraic_iff (e : A ≃ₐ[R] B) :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R B :=
  ⟨fun _ ↦ e.isAlgebraic, fun _ ↦ e.symm.isAlgebraic⟩

end

theorem isAlgebraic_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    IsAlgebraic R (algebraMap S A a) ↔ IsAlgebraic R a :=
  isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S A) h

theorem transcendental_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    Transcendental R (algebraMap S A a) ↔ Transcendental R a := by
  simp_rw [Transcendental, isAlgebraic_algebraMap_iff h]

namespace Subalgebra

theorem isAlgebraic_iff_isAlgebraic_val {S : Subalgebra R A} {x : S} :
    _root_.IsAlgebraic R x ↔ _root_.IsAlgebraic R x.1 :=
  (isAlgebraic_algHom_iff S.val Subtype.val_injective).symm

theorem isAlgebraic_of_isAlgebraic_bot {x : S} (halg : _root_.IsAlgebraic (⊥ : Subalgebra R S) x) :
    _root_.IsAlgebraic R x :=
  halg.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id rfl

theorem isAlgebraic_bot_iff (h : Function.Injective (algebraMap R S)) {x : S} :
    _root_.IsAlgebraic (⊥ : Subalgebra R S) x ↔ _root_.IsAlgebraic R x :=
  isAlgebraic_ringHom_iff_of_comp_eq (Algebra.botEquivOfInjective h).symm (RingHom.id S)
    Function.injective_id (by rfl)

variable (R S) in
theorem algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left
    [Algebra.IsAlgebraic (⊥ : Subalgebra R S) S] : Algebra.IsAlgebraic R S :=
  Algebra.IsAlgebraic.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id (by ext; rfl)

theorem algebra_isAlgebraic_bot_left_iff (h : Function.Injective (algebraMap R S)) :
    Algebra.IsAlgebraic (⊥ : Subalgebra R S) S ↔ Algebra.IsAlgebraic R S := by
  simp_rw [Algebra.isAlgebraic_def, isAlgebraic_bot_iff h]

instance algebra_isAlgebraic_bot_right [Nontrivial R] :
    Algebra.IsAlgebraic R (⊥ : Subalgebra R S) :=
  ⟨by rintro ⟨_, x, rfl⟩; exact isAlgebraic_algebraMap _⟩

end Subalgebra

theorem IsAlgebraic.of_pow {r : A} {n : ℕ} (hn : 0 < n) (ht : IsAlgebraic R (r ^ n)) :
    IsAlgebraic R r :=
  have ⟨p, p_nonzero, hp⟩ := ht
  ⟨_, by rwa [expand_ne_zero hn], by rwa [expand_aeval n p r]⟩

theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :
    Transcendental R (r ^ n) := fun ht' ↦ ht <| ht'.of_pow hn

lemma IsAlgebraic.invOf {x : S} [Invertible x] (h : IsAlgebraic R x) : IsAlgebraic R (⅟ x) := by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p.reverse, by simpa using hp, ?_⟩
  rwa [Polynomial.aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, ← Polynomial.aeval_def]

lemma IsAlgebraic.invOf_iff {x : S} [Invertible x] :
    IsAlgebraic R (⅟ x) ↔ IsAlgebraic R x :=
  ⟨IsAlgebraic.invOf, IsAlgebraic.invOf⟩

lemma IsAlgebraic.inv_iff {K} [Field K] [Algebra R K] {x : K} :
    IsAlgebraic R (x⁻¹) ↔ IsAlgebraic R x := by
  by_cases hx : x = 0
  · simp [hx]
  letI := invertibleOfNonzero hx
  exact IsAlgebraic.invOf_iff (R := R) (x := x)

alias ⟨_, IsAlgebraic.inv⟩ := IsAlgebraic.inv_iff

end zero_ne_one

section

variable {K L R S A : Type*}

section Ring

section CommRing

variable [CommRing R] [CommRing S] [Ring A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- If `x` is algebraic over `R`, then `x` is algebraic over `S` when `S` is an extension of `R`,
  and the map from `R` to `S` is injective. -/
theorem IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (A_alg : IsAlgebraic R x) : IsAlgebraic S x :=
  let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩

@[deprecated (since := "2024-11-18")]
alias IsAlgebraic.tower_top_of_injective := IsAlgebraic.extendScalars

/-- A special case of `IsAlgebraic.extendScalars`. This is extracted as a theorem
  because in some cases `IsAlgebraic.extendScalars` will just runs out of memory. -/
theorem IsAlgebraic.tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A ≤ B) {x : S}
    (h : IsAlgebraic A x) : IsAlgebraic B x := by
  letI : Algebra A B := (Subalgebra.inclusion hle).toAlgebra
  haveI : IsScalarTower A B S := .of_algebraMap_eq fun _ ↦ rfl
  exact h.extendScalars (Subalgebra.inclusion_injective hle)

/-- If `x` is transcendental over `S`, then `x` is transcendental over `R` when `S` is an extension
  of `R`, and the map from `R` to `S` is injective. -/
theorem Transcendental.restrictScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (h : Transcendental S x) : Transcendental R x := fun H ↦ h (H.extendScalars hinj)

@[deprecated (since := "2024-11-18")]
alias Transcendental.of_tower_top_of_injective := Transcendental.restrictScalars

/-- A special case of `Transcendental.restrictScalars`. This is extracted as a theorem
  because in some cases `Transcendental.restrictScalars` will just runs out of memory. -/
theorem Transcendental.of_tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A ≤ B) {x : S}
    (h : Transcendental B x) : Transcendental A x :=
  fun H ↦ h (H.tower_top_of_subalgebra_le hle)

/-- If A is an algebraic algebra over R, then A is algebraic over S when S is an extension of R,
  and the map from `R` to `S` is injective. -/
theorem Algebra.IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S))
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic S A :=
  ⟨fun _ ↦ _root_.IsAlgebraic.extendScalars hinj (Algebra.IsAlgebraic.isAlgebraic _)⟩

@[deprecated (since := "2024-11-18")]
alias Algebra.IsAlgebraic.tower_top_of_injective := Algebra.IsAlgebraic.extendScalars

theorem Algebra.IsAlgebraic.tower_bot_of_injective [Algebra.IsAlgebraic R A]
    (hinj : Function.Injective (algebraMap S A)) :
    Algebra.IsAlgebraic R S where
  isAlgebraic x := by
    simpa [isAlgebraic_algebraMap_iff hinj] using isAlgebraic (R := R) (A := A) (algebraMap _ _ x)

end CommRing

section Field

variable [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
variable (L)

/-- If `x` is algebraic over `K`, then `x` is algebraic over `L` when `L` is an extension of `K` -/
@[stacks 09GF "part one"]
theorem IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebraic K x) :
    IsAlgebraic L x :=
  A_alg.extendScalars (algebraMap K L).injective

variable {L} (K) in
/-- If `x` is transcendental over `L`, then `x` is transcendental over `K` when
  `L` is an extension of `K` -/
theorem Transcendental.of_tower_top {x : A} (h : Transcendental L x) :
    Transcendental K x := fun H ↦ h (H.tower_top L)

/-- If A is an algebraic algebra over K, then A is algebraic over L when L is an extension of K -/
@[stacks 09GF "part two"]
theorem Algebra.IsAlgebraic.tower_top [Algebra.IsAlgebraic K A] : Algebra.IsAlgebraic L A :=
  Algebra.IsAlgebraic.extendScalars (algebraMap K L).injective

variable (K) (A)

theorem Algebra.IsAlgebraic.tower_bot (K L A : Type*) [CommRing K] [Field L] [Ring A]
    [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
    [Nontrivial A] [Algebra.IsAlgebraic K A] :
    Algebra.IsAlgebraic K L :=
  tower_bot_of_injective (algebraMap L A).injective

end Field

end Ring

section NoZeroSMulDivisors

namespace Algebra.IsAlgebraic

variable [CommRing K] [Field L] [Algebra K L]

theorem algHom_bijective [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L] (f : L →ₐ[K] L) :
    Function.Bijective f := by
  refine ⟨f.injective, fun b ↦ ?_⟩
  obtain ⟨p, hp, he⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) b
  let f' : p.rootSet L → p.rootSet L := (rootSet_maps_to' (fun x ↦ x) f).restrict f _ _
  have : f'.Surjective := Finite.injective_iff_surjective.1
    fun _ _ h ↦ Subtype.eq <| f.injective <| Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_rootSet.2 ⟨hp, he⟩⟩
  exact ⟨a, Subtype.ext_iff.1 ha⟩

theorem algHom_bijective₂ [NoZeroSMulDivisors K L] [DivisionRing R] [Algebra K R]
    [Algebra.IsAlgebraic K L] (f : L →ₐ[K] R) (g : R →ₐ[K] L) :
    Function.Bijective f ∧ Function.Bijective g :=
  (g.injective.bijective₂_of_surjective f.injective (algHom_bijective <| g.comp f).2).symm

theorem bijective_of_isScalarTower [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L]
    [DivisionRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ (IsScalarTower.toAlgHom K L R) f).2

theorem bijective_of_isScalarTower' [Field R] [Algebra K R]
    [NoZeroSMulDivisors K R]
    [Algebra.IsAlgebraic K R] [Algebra L R] [IsScalarTower K L R] (f : R →ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ f (IsScalarTower.toAlgHom K L R)).1

variable (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[simps]
noncomputable def algEquivEquivAlgHom [NoZeroSMulDivisors K L] [Algebra.IsAlgebraic K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) where
  toFun ϕ := ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (algHom_bijective ϕ)
  map_mul' _ _ := rfl

end Algebra.IsAlgebraic

end NoZeroSMulDivisors

end

section

variable {R S : Type*} [CommRing R] [Ring S] [Algebra R S]

theorem IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero
    {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ nonZeroDivisors S) :
    ∃ q : R[X], q.coeff 0 ≠ 0 ∧ aeval s q = 0 := by
  obtain ⟨p, hp0, hp⟩ := hRs
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  simp only [C_0, sub_zero, X_pow_mul, X_dvd_iff] at hpq hq
  rw [hpq, map_mul, aeval_X_pow] at hp
  exact ⟨q, hq, (nonZeroDivisors S).pow_mem hs (rootMultiplicity 0 p) (aeval s q) hp⟩

theorem IsAlgebraic.exists_nonzero_eq_adjoin_mul
    {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ nonZeroDivisors S) :
    ∃ᵉ (t ∈ Algebra.adjoin R {s}) (r ≠ (0 : R)), s * t = algebraMap R S r := by
  have ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have ⟨p, hp⟩ := X_dvd_sub_C (p := q)
  refine ⟨aeval s p, aeval_mem_adjoin_singleton _ _, _, neg_ne_zero.mpr hq0, ?_⟩
  apply_fun aeval s at hp
  rwa [map_sub, hq, zero_sub, map_mul, aeval_X, aeval_C, ← map_neg, eq_comm] at hp

theorem IsAlgebraic.exists_nonzero_dvd
    {s : S} (hRs : IsAlgebraic R s) (hs : s ∈ nonZeroDivisors S) :
    ∃ r : R, r ≠ 0 ∧ s ∣ algebraMap R S r := by
  obtain ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have key := map_dvd (aeval s) (X_dvd_sub_C (p := q))
  rw [map_sub, hq, zero_sub, dvd_neg, aeval_X, aeval_C] at key
  exact ⟨q.coeff 0, hq0, key⟩

namespace Algebra.IsAlgebraic

variable (S : Type*) {A : Type*} [CommRing S] [NoZeroDivisors S] [Algebra R S]
  [alg : Algebra.IsAlgebraic R S] [Ring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

open Function (Injective) in
theorem injective_tower_top (inj : Injective (algebraMap R A)) : Injective (algebraMap S A) := by
  refine (injective_iff_map_eq_zero _).mpr fun s eq ↦ of_not_not fun ne ↦ ?_
  have ⟨r, ne, dvd⟩ := (alg.1 s).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ne)
  refine ne (inj <| map_zero (algebraMap R A) ▸ zero_dvd_iff.mp ?_)
  simp_rw [← eq, IsScalarTower.algebraMap_apply R S A, map_dvd (algebraMap S A) dvd]

variable (R A)

theorem faithfulSMul_tower_top [FaithfulSMul R A] : FaithfulSMul S A := by
  rw [faithfulSMul_iff_algebraMap_injective] at *
  exact injective_tower_top S ‹_›

end Algebra.IsAlgebraic

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `b` is algebraic over `R`. -/
theorem IsAlgebraic.exists_smul_eq_mul
    (a : S) {b : S} (hRb : IsAlgebraic R b) (hb : b ∈ nonZeroDivisors S) :
    ∃ᵉ (c : S) (d ≠ (0 : R)), d • a = b * c :=
  have ⟨r, hr, s, h⟩ := hRb.exists_nonzero_dvd hb
  ⟨s * a, r, hr, by rw [Algebra.smul_def, h, mul_assoc]⟩

variable (R)

/-- A fraction `(a : S) / (b : S)` can be reduced to `(c : S) / (d : R)`,
if `b` is algebraic over `R`. -/
theorem Algebra.IsAlgebraic.exists_smul_eq_mul [NoZeroDivisors S] [Algebra.IsAlgebraic R S]
    (a : S) {b : S} (hb : b ≠ 0) :
    ∃ᵉ (c : S) (d ≠ (0 : R)), d • a = b * c :=
  (isAlgebraic b).exists_smul_eq_mul a (mem_nonZeroDivisors_of_ne_zero hb)

end

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : Subalgebra K L)

theorem inv_eq_of_aeval_divX_ne_zero {x : L} {p : K[X]} (aeval_ne : aeval x (divX p) ≠ 0) :
    x⁻¹ = aeval x (divX p) / (aeval x p - algebraMap _ _ (p.coeff 0)) := by
  rw [inv_eq_iff_eq_inv, inv_div, eq_comm, div_eq_iff, sub_eq_iff_eq_add, mul_comm]
  conv_lhs => rw [← divX_mul_X_add p]
  · rw [map_add, map_mul, aeval_X, aeval_C]
  · exact aeval_ne

theorem inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : K[X]} (aeval_eq : aeval x p = 0)
    (coeff_zero_ne : p.coeff 0 ≠ 0) : x⁻¹ = -(aeval x (divX p) / algebraMap _ _ (p.coeff 0)) := by
  convert inv_eq_of_aeval_divX_ne_zero (p := p) (L := L)
    (mt (fun h => (algebraMap K L).injective ?_) coeff_zero_ne) using 1
  · rw [aeval_eq, zero_sub, div_neg]
  rw [RingHom.map_zero]
  convert aeval_eq
  conv_rhs => rw [← divX_mul_X_add p]
  rw [map_add, map_mul, h, zero_mul, zero_add, aeval_C]

theorem Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : K[X]}
    (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 ≠ 0) : (x⁻¹ : L) ∈ A := by
  suffices (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (divX p) by
    rw [this]
    exact A.smul_mem (aeval x _).2 _
  have : aeval (x : L) p = 0 := by rw [Subalgebra.aeval_coe, aeval_eq, Subalgebra.coe_zero]
  -- Porting note: this was a long sequence of `rw`.
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne, div_eq_inv_mul, Algebra.smul_def]
  simp only [aeval_coe, Submonoid.coe_mul, Subsemiring.coe_toSubmonoid, coe_toSubsemiring,
    coe_algebraMap]
  rw [map_inv₀, map_neg, inv_neg, neg_mul]

theorem Subalgebra.inv_mem_of_algebraic {x : A} (hx : _root_.IsAlgebraic K (x : L)) :
    (x⁻¹ : L) ∈ A := by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  rw [Subalgebra.aeval_coe, Subalgebra.coe_eq_zero] at aeval_eq
  revert ne_zero aeval_eq
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a hp ha _ih _ne_zero aeval_eq
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq ?_
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
  · intro p hp ih _ne_zero aeval_eq
    rw [map_mul, aeval_X, mul_eq_zero] at aeval_eq
    rcases aeval_eq with aeval_eq | x_eq
    · exact ih hp aeval_eq
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      exact A.zero_mem

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
@[stacks 0BID]
theorem Subalgebra.isField_of_algebraic [Algebra.IsAlgebraic K L] : IsField A :=
  { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
    mul_inv_cancel := fun {a} ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (Algebra.IsAlgebraic.isAlgebraic (a : L))⟩,
        Subtype.ext (mul_inv_cancel₀ (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }

end Field

section Infinite

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Nontrivial R]

theorem Transcendental.infinite {x : A} (hx : Transcendental R x) : Infinite A :=
  .of_injective _ (transcendental_iff_injective.mp hx)

variable (R A) in
theorem Algebra.Transcendental.infinite [Algebra.Transcendental R A] : Infinite A :=
  have ⟨x, hx⟩ := ‹Algebra.Transcendental R A›
  hx.infinite

end Infinite
