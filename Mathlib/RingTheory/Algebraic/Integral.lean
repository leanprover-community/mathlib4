/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Algebraic elements and integral elements

This file relates algebraic and integral elements of an algebra, by proving every integral element
is algebraic and that every algebraic element over a field is integral.

## Main results

* `IsIntegral.isAlgebraic`, `Algebra.IsIntegral.isAlgebraic`: integral implies algebraic.
* `isAlgebraic_iff_isIntegral`, `Algebra.isAlgebraic_iff_isIntegral`: integral iff algebraic
  over a field.
* `IsAlgebraic.of_finite`, `Algebra.IsAlgebraic.of_finite`: finite-dimensional (as module) implies
  algebraic.
* `IsAlgebraic.exists_integral_multiple`: an algebraic element has a multiple which is integral
* `IsAlgebraic.iff_exists_smul_integral`: If `R` is reduced and `S` is an `R`-algebra with
  injective `algebraMap`, then an element of `S` is algebraic over `R` iff some `R`-multiple
  is integral over `R`.
* `Algebra.IsAlgebraic.trans'`: If `A/S/R` is a tower of algebras and both `A/S` and `S/R` are
  algebraic, then `A/R` is also algebraic, provided that `S` has no zero divisors and
  `algebraMap S A` is injective (so `S` can be regarded as an `R`-subalgebra of `A`).
* `Subalgebra.algebraicClosure`: If `R` is a domain and `S` is an arbitrary `R`-algebra,
  then the elements of `S` that are algebraic over `R` form a subalgebra.
* `Transcendental.extendScalars`: an element of an `R`-algebra that is transcendental over `R`
  remains transcendental over any algebraic `R`-subalgebra that has no zero divisors.
-/

assert_not_exists LocalRing

universe u v w

open Polynomial

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]
variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]
variable [IsScalarTower R S A]

/-- An integral element of an algebra is algebraic. -/
theorem IsIntegral.isAlgebraic [Nontrivial R] {x : A} : IsIntegral R x → IsAlgebraic R x :=
  fun ⟨p, hp, hpx⟩ => ⟨p, hp.ne_zero, hpx⟩

instance Algebra.IsIntegral.isAlgebraic [Nontrivial R] [Algebra.IsIntegral R A] :
    Algebra.IsAlgebraic R A := ⟨fun a ↦ (Algebra.IsIntegral.isIntegral a).isAlgebraic⟩

end zero_ne_one

section Field

variable {K : Type u} {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- An element of an algebra over a field is algebraic if and only if it is integral. -/
theorem isAlgebraic_iff_isIntegral {x : A} : IsAlgebraic K x ↔ IsIntegral K x := by
  refine ⟨?_, IsIntegral.isAlgebraic⟩
  rintro ⟨p, hp, hpx⟩
  refine ⟨_, monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [← aeval_def, map_mul, hpx, zero_mul]

protected theorem Algebra.isAlgebraic_iff_isIntegral :
    Algebra.IsAlgebraic K A ↔ Algebra.IsIntegral K A := by
  rw [Algebra.isAlgebraic_def, Algebra.isIntegral_def,
      forall_congr' fun _ ↦ isAlgebraic_iff_isIntegral]

alias ⟨IsAlgebraic.isIntegral, _⟩ := isAlgebraic_iff_isIntegral

/-- This used to be an `alias` of `Algebra.isAlgebraic_iff_isIntegral` but that would make
`Algebra.IsAlgebraic K A` an explicit parameter instead of instance implicit. -/
protected instance Algebra.IsAlgebraic.isIntegral [Algebra.IsAlgebraic K A] :
    Algebra.IsIntegral K A := Algebra.isAlgebraic_iff_isIntegral.mp ‹_›

theorem Algebra.IsAlgebraic.of_isIntegralClosure (R B C : Type*) [CommRing R] [Nontrivial R]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] [Algebra B C]
    [IsScalarTower R B C] [IsIntegralClosure B R C] : Algebra.IsAlgebraic R B :=
  have := IsIntegralClosure.isIntegral_algebra R (A := B) C
  inferInstance

end Field

section

variable (K L : Type*) {R S A : Type*}

section Ring

section Field

variable [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

theorem IsAlgebraic.of_finite (e : A) [FiniteDimensional K A] : IsAlgebraic K e :=
  (IsIntegral.of_finite K e).isAlgebraic

variable (A)

/-- A field extension is algebraic if it is finite. -/
@[stacks 09GG "first part"]
instance Algebra.IsAlgebraic.of_finite [FiniteDimensional K A] : Algebra.IsAlgebraic K A :=
  (IsIntegral.of_finite K A).isAlgebraic

end Field

end Ring

section CommRing

variable {K L} [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]

/-- If L is an algebraic field extension of K and A is an algebraic algebra over L,
then A is algebraic over K. -/
@[stacks 09GJ]
protected theorem Algebra.IsAlgebraic.trans
    [L_alg : Algebra.IsAlgebraic K L] [A_alg : Algebra.IsAlgebraic L A] :
    Algebra.IsAlgebraic K A := by
  rw [Algebra.isAlgebraic_iff_isIntegral] at L_alg A_alg ⊢
  exact Algebra.IsIntegral.trans L

end CommRing

section Field

variable {K L} [Field K] [Ring A] [Algebra K A]

/-- If `K` is a field, `r : A` and `f : K[X]`, then `Polynomial.aeval r f` is
transcendental over `K` if and only if `r` and `f` are both transcendental over `K`.
See also `Transcendental.aeval_of_transcendental` and `Transcendental.of_aeval`. -/
@[simp]
theorem transcendental_aeval_iff {r : A} {f : K[X]} :
    Transcendental K (Polynomial.aeval r f) ↔ Transcendental K r ∧ Transcendental K f := by
  refine ⟨fun h ↦ ⟨?_, h.of_aeval⟩, fun ⟨h1, h2⟩ ↦ h1.aeval_of_transcendental h2⟩
  rw [Transcendental] at h ⊢
  contrapose! h
  rw [isAlgebraic_iff_isIntegral] at h ⊢
  exact .of_mem_of_fg _ h.fg_adjoin_singleton _ (aeval_mem_adjoin_singleton _ _)

variable [Field L] [Algebra K L]

theorem AlgHom.bijective [FiniteDimensional K L] (ϕ : L →ₐ[K] L) : Function.Bijective ϕ :=
  (Algebra.IsAlgebraic.of_finite K L).algHom_bijective ϕ

variable (K L) in
/-- Bijection between algebra equivalences and algebra homomorphisms -/
noncomputable abbrev algEquivEquivAlgHom [FiniteDimensional K L] :
    (L ≃ₐ[K] L) ≃* (L →ₐ[K] L) :=
  Algebra.IsAlgebraic.algEquivEquivAlgHom K L

end Field

end

variable {R S A : Type*} [CommRing R] [CommRing S] [Ring A]
variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable {z : A} {z' : S}

namespace IsAlgebraic

theorem exists_integral_multiple (hz : IsAlgebraic R z)
    (inj : Function.Injective (algebraMap R A)) :
    ∃ y ≠ (0 : R), IsIntegral R (y • z) := by
  have ⟨p, p_ne_zero, px⟩ := hz
  set a := p.leadingCoeff
  have a_ne_zero : a ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp p_ne_zero
  have x_integral : IsIntegral R (algebraMap R A a * z) :=
    ⟨p.integralNormalization, monic_integralNormalization p_ne_zero,
      integralNormalization_aeval_eq_zero px fun _ ↦ (map_eq_zero_iff _ inj).mp⟩
  exact ⟨_, a_ne_zero, Algebra.smul_def a z ▸ x_integral⟩

@[deprecated (since := "2024-11-30")]
alias _root_.exists_integral_multiple := exists_integral_multiple

theorem _root_.Algebra.IsAlgebraic.exists_integral_multiples [NoZeroDivisors R]
    [alg : Algebra.IsAlgebraic R A] (inj : Function.Injective (algebraMap R A)) (s : Finset A) :
    ∃ y ≠ (0 : R), ∀ z ∈ s, IsIntegral R (y • z) := by
  have := Algebra.IsAlgebraic.nontrivial R A
  choose r hr int using fun x ↦ (alg.1 x).exists_integral_multiple inj
  refine ⟨∏ x ∈ s, r x, Finset.prod_ne_zero_iff.mpr fun _ _ ↦ hr _, fun _ h ↦ ?_⟩
  classical rw [← Finset.prod_erase_mul _ _ h, mul_smul]
  exact (int _).smul _

theorem of_smul_isIntegral {y : R} (hy : ¬ IsNilpotent y)
    (h : IsIntegral R (y • z)) : IsAlgebraic R z := by
  have ⟨p, monic, eval0⟩ := h
  refine ⟨p.comp (C y * X), fun h ↦ ?_, by simpa [aeval_comp, Algebra.smul_def] using eval0⟩
  apply_fun (coeff · p.natDegree) at h
  have hy0 : y ≠ 0 := by rintro rfl; exact hy .zero
  rw [coeff_zero, ← mul_one p.natDegree, ← natDegree_C_mul_X y hy0,
    coeff_comp_degree_mul_degree, monic, one_mul, leadingCoeff_C_mul_X] at h
  · exact hy ⟨_, h⟩
  · rw [natDegree_C_mul_X _ hy0]; rintro ⟨⟩

theorem of_smul {y : R} (hy : y ∈ nonZeroDivisors R)
    (h : IsAlgebraic R (y • z)) : IsAlgebraic R z :=
  have ⟨p, hp, eval0⟩ := h
  ⟨_, mt (comp_C_mul_X_eq_zero_iff hy).mp hp, by simpa [aeval_comp, Algebra.smul_def] using eval0⟩

theorem iff_exists_smul_integral [IsReduced R] (inj : Function.Injective (algebraMap R A)) :
    IsAlgebraic R z ↔ ∃ y ≠ (0 : R), IsIntegral R (y • z) :=
  ⟨(exists_integral_multiple · inj), fun ⟨_, hy, int⟩ ↦
    of_smul_isIntegral (by rwa [isNilpotent_iff_eq_zero]) int⟩

section trans

variable (R) [NoZeroDivisors S] (inj : Function.Injective (algebraMap S A))
include inj

theorem restrictScalars_of_isIntegral [int : Algebra.IsIntegral R S]
    {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a := by
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
    fun h ↦ hRS <| .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  have := hRS.noZeroDivisors _ (map_zero _) (map_mul _)
  have ⟨s, hs, int_s⟩ := h.exists_integral_multiple inj
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R S
    exact (is_transcendental_of_subsingleton _ _ h).elim
  have ⟨r, hr, _, e⟩ := (int.1 s).isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hs)
  refine .of_smul_isIntegral (y := r) (by rwa [isNilpotent_iff_eq_zero]) ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R S,
    e, ← Algebra.smul_def, mul_comm, mul_smul]
  exact isIntegral_trans _ (int_s.smul _)

theorem restrictScalars [Algebra.IsAlgebraic R S]
    {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a := by
  have ⟨p, hp, eval0⟩ := h
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
    fun h ↦ hRS <| .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  have := hRS.noZeroDivisors _ (map_zero _) (map_mul _)
  classical
  have ⟨r, hr, int⟩ := Algebra.IsAlgebraic.exists_integral_multiples hRS (p.support.image (coeff p))
  let p := (r • p).toSubring (integralClosure R S).toSubring fun s hs ↦ by
    obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp hs
    exact int _ (Finset.mem_image_of_mem _ <| support_smul _ _ hn)
  have : IsAlgebraic (integralClosure R S) a := by
    refine ⟨p, ?_, ?_⟩
    · have := NoZeroSMulDivisors.of_algebraMap_injective hRS
      simpa only [← Polynomial.map_ne_zero_iff (f := Subring.subtype _) Subtype.val_injective,
        p, map_toSubring, smul_ne_zero_iff] using And.intro hr hp
    rw [← eval_map_algebraMap, Subalgebra.algebraMap_eq, ← map_map, ← Subalgebra.toSubring_subtype,
      map_toSubring, eval_map_algebraMap, ← AlgHom.restrictScalars_apply R,
      map_smul, AlgHom.restrictScalars_apply, eval0, smul_zero]
  exact restrictScalars_of_isIntegral _ (by exact inj.comp Subtype.val_injective) this

theorem _root_.IsIntegral.trans_isAlgebraic [alg : Algebra.IsAlgebraic R S]
    {a : A} (h : IsIntegral S a) : IsAlgebraic R a := by
  cases subsingleton_or_nontrivial A
  · have := Algebra.IsAlgebraic.nontrivial R S
    exact Subsingleton.elim a 0 ▸ isAlgebraic_zero
  · have := Module.nontrivial S A
    exact h.isAlgebraic.restrictScalars _ inj

end trans

variable [nzd : NoZeroDivisors R] {a b : S} (ha : IsAlgebraic R a) (hb : IsAlgebraic R b)
include ha
omit nzd

protected lemma neg : IsAlgebraic R (-a) :=
  have ⟨p, h, eval0⟩ := ha
  ⟨algEquivAevalNegX p, EmbeddingLike.map_ne_zero_iff.mpr h, by simpa [← comp_eq_aeval, aeval_comp]⟩

protected lemma smul (r : R) : IsAlgebraic R (r • a) :=
  have ⟨_, hp, eval0⟩ := ha
  ⟨_, scaleRoots_ne_zero hp r, Algebra.smul_def r a ▸ scaleRoots_aeval_eq_zero eval0⟩

protected lemma nsmul (n : ℕ) : IsAlgebraic R (n • a) :=
  Nat.cast_smul_eq_nsmul R n a ▸ ha.smul _

protected lemma zsmul (n : ℤ) : IsAlgebraic R (n • a) :=
  Int.cast_smul_eq_zsmul R n a ▸ ha.smul _

include hb nzd

protected lemma mul : IsAlgebraic R (a * b) := by
  refine (em _).elim (fun h ↦ ?_) fun h ↦ (Algebra.isAlgebraic_of_not_injective h).1 _
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple h
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple h
  refine (IsAlgebraic.iff_exists_smul_integral h).mpr ⟨_, mul_ne_zero a0 b0, ?_⟩
  simp_rw [Algebra.smul_def, map_mul, mul_mul_mul_comm, ← Algebra.smul_def]
  exact int_a.mul int_b

protected lemma add : IsAlgebraic R (a + b) := by
  refine (em _).elim (fun h ↦ ?_) fun h ↦ (Algebra.isAlgebraic_of_not_injective h).1 _
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple h
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple h
  refine (IsAlgebraic.iff_exists_smul_integral h).mpr ⟨_, mul_ne_zero b0 a0, ?_⟩
  rw [smul_add, mul_smul, mul_comm, mul_smul]
  exact (int_a.smul _).add (int_b.smul _)

protected lemma sub : IsAlgebraic R (a - b) :=
  sub_eq_add_neg a b ▸ ha.add hb.neg

omit hb
protected lemma pow (n : ℕ) : IsAlgebraic R (a ^ n) :=
  have := ha.nontrivial
  n.rec (pow_zero a ▸ isAlgebraic_one) fun _ h ↦ pow_succ a _ ▸ h.mul ha

end IsAlgebraic

namespace Algebra

variable (R) [NoZeroDivisors S] (inj : Function.Injective (algebraMap S A))
include inj

/-- Transitivity of algebraicity for algebras over domains. -/
theorem IsAlgebraic.trans' [Algebra.IsAlgebraic R S] [alg : Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (alg.1 _).restrictScalars _ inj⟩

theorem IsIntegral.trans_isAlgebraic [Algebra.IsIntegral R S] [alg : Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (alg.1 _).restrictScalars_of_isIntegral _ inj⟩

theorem IsAlgebraic.trans_isIntegral [Algebra.IsAlgebraic R S] [int : Algebra.IsIntegral S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (int.1 _).trans_isAlgebraic _ inj⟩

end Algebra

variable (R S)
/-- If `R` is a domain and `S` is an arbitrary `R`-algebra, then the elements of `S`
that are algebraic over `R` form a subalgebra. -/
def Subalgebra.algebraicClosure [IsDomain R] : Subalgebra R S where
  carrier := {s | _root_.IsAlgebraic R s}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' := isAlgebraic_algebraMap

theorem integralClosure_le_algebraicClosure [IsDomain R] :
    integralClosure R S ≤ Subalgebra.algebraicClosure R S :=
  fun _ ↦ IsIntegral.isAlgebraic

theorem Subalgebra.algebraicClosure_eq_integralClosure {K} [Field K] [Algebra K S] :
    algebraicClosure K S = integralClosure K S :=
  SetLike.ext fun _ ↦ isAlgebraic_iff_isIntegral

instance [IsDomain R] : Algebra.IsAlgebraic R (Subalgebra.algebraicClosure R S) :=
  (Subalgebra.isAlgebraic_iff _).mp fun _ ↦ id

variable {R S}

theorem Algebra.isAlgebraic_adjoin_iff [IsDomain R] {s : Set S} :
    (adjoin R s).IsAlgebraic ↔ ∀ x ∈ s, IsAlgebraic R x :=
  Algebra.adjoin_le_iff (S := Subalgebra.algebraicClosure R S)

theorem Algebra.isAlgebraic_adjoin_of_nonempty [NoZeroDivisors R] {s : Set S} (hs : s.Nonempty) :
    (adjoin R s).IsAlgebraic ↔ ∀ x ∈ s, IsAlgebraic R x :=
  ⟨fun h x hx ↦ h _ (subset_adjoin hx), fun h ↦
    have ⟨x, hx⟩ := hs
    have := (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨‹_›, (h x hx).nontrivial⟩
    isAlgebraic_adjoin_iff.mpr h⟩

theorem Algebra.isAlgebraic_adjoin_singleton_iff [NoZeroDivisors R] {s : S} :
    (adjoin R {s}).IsAlgebraic ↔ IsAlgebraic R s :=
  (isAlgebraic_adjoin_of_nonempty <| Set.singleton_nonempty s).trans forall_eq

theorem IsAlgebraic.of_mul [NoZeroDivisors R] {y z : S} (hy : y ∈ nonZeroDivisors S)
    (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y * z)) : IsAlgebraic R z := by
  have ⟨t, ht, r, hr, eq⟩ := alg_y.exists_nonzero_eq_adjoin_mul hy
  have := alg_yz.mul (Algebra.isAlgebraic_adjoin_singleton_iff.mpr alg_y _ ht)
  rw [mul_right_comm, eq, ← Algebra.smul_def] at this
  exact this.of_smul (mem_nonZeroDivisors_of_ne_zero hr)

namespace Transcendental

section

variable {a : A} (ha : Transcendental R a)
include ha

lemma extendScalars_of_isIntegral [NoZeroDivisors S] [Algebra.IsIntegral R S]
    (inj : Function.Injective (algebraMap S A)) : Transcendental S a := by
  contrapose ha
  rw [Transcendental, not_not] at ha ⊢
  exact ha.restrictScalars_of_isIntegral _ inj

lemma extendScalars [NoZeroDivisors S] [Algebra.IsAlgebraic R S]
    (inj : Function.Injective (algebraMap S A)) : Transcendental S a := by
  contrapose ha
  rw [Transcendental, not_not] at ha ⊢
  exact ha.restrictScalars _ inj

end

variable {a : S} (ha : Transcendental R a)
include ha

protected lemma integralClosure [NoZeroDivisors S] :
    Transcendental (integralClosure R S) a :=
  ha.extendScalars_of_isIntegral Subtype.val_injective

lemma subalgebraAlgebraicClosure [IsDomain R] [NoZeroDivisors S] :
    Transcendental (Subalgebra.algebraicClosure R S) a :=
  ha.extendScalars Subtype.val_injective

end Transcendental
