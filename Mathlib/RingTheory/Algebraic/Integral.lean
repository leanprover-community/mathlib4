/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.BaseChange

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
* `Algebra.IsAlgebraic.trans`: If `A/S/R` is a tower of algebras and both `A/S` and `S/R` are
  algebraic, then `A/R` is also algebraic, provided that `S` has no zero divisors.
* `Subalgebra.algebraicClosure`: If `R` is a domain and `S` is an arbitrary `R`-algebra,
  then the elements of `S` that are algebraic over `R` form a subalgebra.
* `Transcendental.extendScalars`: an element of an `R`-algebra that is transcendental over `R`
  remains transcendental over any algebraic `R`-subalgebra that has no zero divisors.
-/

assert_not_exists IsLocalRing

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

variable (K L R : Type*) {A : Type*}

section Ring

variable [CommRing R] [Nontrivial R] [Ring A] [Algebra R A]

theorem IsAlgebraic.of_finite (e : A) [Module.Finite R A] : IsAlgebraic R e :=
  (IsIntegral.of_finite R e).isAlgebraic

variable (A)

/-- A field extension is algebraic if it is finite. -/
@[stacks 09GG "first part"]
instance Algebra.IsAlgebraic.of_finite [Module.Finite R A] : Algebra.IsAlgebraic R A :=
  (IsIntegral.of_finite R A).isAlgebraic

end Ring

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

theorem exists_integral_multiple (hz : IsAlgebraic R z) : ∃ y ≠ (0 : R), IsIntegral R (y • z) := by
  by_cases inj : Function.Injective (algebraMap R A); swap
  · rw [injective_iff_map_eq_zero] at inj; push_neg at inj
    have ⟨r, eq, ne⟩ := inj
    exact ⟨r, ne, by simpa [← algebraMap_smul A, eq, zero_smul] using isIntegral_zero⟩
  have ⟨p, p_ne_zero, px⟩ := hz
  set a := p.leadingCoeff
  have a_ne_zero : a ≠ 0 := mt Polynomial.leadingCoeff_eq_zero.mp p_ne_zero
  have x_integral : IsIntegral R (algebraMap R A a * z) :=
    ⟨p.integralNormalization, monic_integralNormalization p_ne_zero,
      integralNormalization_aeval_eq_zero px fun _ ↦ (map_eq_zero_iff _ inj).mp⟩
  exact ⟨_, a_ne_zero, Algebra.smul_def a z ▸ x_integral⟩

variable (R) in
theorem _root_.Algebra.IsAlgebraic.exists_integral_multiples [NoZeroDivisors R]
    [alg : Algebra.IsAlgebraic R A] (s : Finset A) :
    ∃ y ≠ (0 : R), ∀ z ∈ s, IsIntegral R (y • z) := by
  have := Algebra.IsAlgebraic.nontrivial R A
  choose r hr int using fun x ↦ (alg.1 x).exists_integral_multiple
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

theorem iff_exists_smul_integral [IsReduced R] :
    IsAlgebraic R z ↔ ∃ y ≠ (0 : R), IsIntegral R (y • z) :=
  ⟨(exists_integral_multiple ·), fun ⟨_, hy, int⟩ ↦
    of_smul_isIntegral (by rwa [isNilpotent_iff_eq_zero]) int⟩

section restrictScalars

variable (R) [NoZeroDivisors S]

/-!
The next theorem may fail if only `R` is assumed to be a domain but `S` is not: for example, let
`S = R[X] ⧸ (X² - X)` and let `A` be the subalgebra of `S[Y]` generated by `XY`.
`A` is algebraic over `S` because any element `∑ᵢ sᵢ(XY)ⁱ` is a root of the polynomial
`(X - 1)(Z - s₀)` in `S[Z]`, because `X(X - 1) = X² - X = 0` in `S`.
However, `XY` is a transcendental element in `A` over `R`, because `∑ᵢ rᵢ(XY)ⁱ = 0` in `S[Y]`
implies all `rᵢXⁱ = 0` (i.e., `r₀ = 0` and `rᵢX = 0` for `i > 0`) in `S`,
which implies `rᵢ = 0` in `R`. This example is inspired by the comment
https://mathoverflow.net/questions/482944/when-do-algebraic-elements-form-a-subalgebra#comment1257632_482944. -/

theorem restrictScalars_of_isIntegral [int : Algebra.IsIntegral R S]
    {a : A} (h : IsAlgebraic S a) : IsAlgebraic R a := by
  by_cases hRS : Function.Injective (algebraMap R S)
  on_goal 2 => exact (Algebra.isAlgebraic_of_not_injective
    fun h ↦ hRS <| .of_comp (IsScalarTower.algebraMap_eq R S A ▸ h)).1 _
  have := hRS.noZeroDivisors _ (map_zero _) (map_mul _)
  have ⟨s, hs, int_s⟩ := h.exists_integral_multiple
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
  have ⟨r, hr, int⟩ := Algebra.IsAlgebraic.exists_integral_multiples R (p.support.image (coeff p))
  let p := (r • p).toSubring (integralClosure R S).toSubring fun s hs ↦ by
    obtain ⟨n, hn, rfl⟩ := mem_coeffs_iff.mp hs
    exact int _ (Finset.mem_image_of_mem _ <| support_smul _ _ hn)
  have : IsAlgebraic (integralClosure R S) a := by
    refine ⟨p, ?_, ?_⟩
    · have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
      simpa only [← Polynomial.map_ne_zero_iff (f := Subring.subtype _) Subtype.val_injective,
        p, map_toSubring, smul_ne_zero_iff] using And.intro hr hp
    rw [← eval_map_algebraMap, Subalgebra.algebraMap_eq, ← map_map, ← Subalgebra.toSubring_subtype,
      map_toSubring, eval_map_algebraMap, ← AlgHom.restrictScalars_apply R,
      map_smul, AlgHom.restrictScalars_apply, eval0, smul_zero]
  exact restrictScalars_of_isIntegral _ this

theorem _root_.IsIntegral.trans_isAlgebraic [alg : Algebra.IsAlgebraic R S]
    {a : A} (h : IsIntegral S a) : IsAlgebraic R a := by
  cases subsingleton_or_nontrivial A
  · have := Algebra.IsAlgebraic.nontrivial R S
    exact Subsingleton.elim a 0 ▸ isAlgebraic_zero
  · have := Module.nontrivial S A
    exact h.isAlgebraic.restrictScalars _

end restrictScalars

section Ring

variable (s : S) {a : A} (ha : IsAlgebraic R a)
include ha

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

omit [Algebra S A] [IsScalarTower R S A] in
lemma tmul [FaithfulSMul R S] : IsAlgebraic S (s ⊗ₜ[R] a) := by
  rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul']
  have ⟨p, h, eval0⟩ := ha
  refine .smul ⟨p.map (algebraMap R S),
    (Polynomial.map_ne_zero_iff <| FaithfulSMul.algebraMap_injective ..).mpr h, ?_⟩ _
  rw [← Algebra.TensorProduct.includeRight_apply, ← AlgHom.coe_toRingHom (A := A),
    ← map_aeval_eq_aeval_map (by ext; simp), eval0, map_zero]

end Ring

section CommRing

variable [NoZeroDivisors R] {a b : S} (ha : IsAlgebraic R a) (hb : IsAlgebraic R b)
include ha hb

protected lemma mul : IsAlgebraic R (a * b) := by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero a0 b0, ?_⟩
  simp_rw [Algebra.smul_def, map_mul, mul_mul_mul_comm, ← Algebra.smul_def]
  exact int_a.mul int_b

protected lemma add : IsAlgebraic R (a + b) := by
  have ⟨ra, a0, int_a⟩ := ha.exists_integral_multiple
  have ⟨rb, b0, int_b⟩ := hb.exists_integral_multiple
  refine IsAlgebraic.iff_exists_smul_integral.mpr ⟨_, mul_ne_zero b0 a0, ?_⟩
  rw [smul_add, mul_smul, mul_comm, mul_smul]
  exact (int_a.smul _).add (int_b.smul _)

protected lemma sub : IsAlgebraic R (a - b) :=
  sub_eq_add_neg a b ▸ ha.add hb.neg

omit hb
protected lemma pow (n : ℕ) : IsAlgebraic R (a ^ n) :=
  have := ha.nontrivial
  n.rec (pow_zero a ▸ isAlgebraic_one) fun _ h ↦ pow_succ a _ ▸ h.mul ha

end CommRing

end IsAlgebraic

namespace Algebra

variable (R S A) [NoZeroDivisors S]

/-- Transitivity of algebraicity for algebras over domains. -/
@[stacks 09GJ] theorem IsAlgebraic.trans [Algebra.IsAlgebraic R S] [alg : Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (alg.1 _).restrictScalars _⟩

@[deprecated (since := "2025-02-08")] alias IsAlgebraic.trans' := IsAlgebraic.trans

theorem IsIntegral.trans_isAlgebraic [Algebra.IsIntegral R S] [alg : Algebra.IsAlgebraic S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (alg.1 _).restrictScalars_of_isIntegral _⟩

theorem IsAlgebraic.trans_isIntegral [Algebra.IsAlgebraic R S] [int : Algebra.IsIntegral S A] :
    Algebra.IsAlgebraic R A :=
  ⟨fun _ ↦ (int.1 _).trans_isAlgebraic _⟩

variable {A}

protected theorem IsIntegral.isAlgebraic_iff [Algebra.IsIntegral R S] [FaithfulSMul R S]
    {a : A} : IsAlgebraic R a ↔ IsAlgebraic S a :=
  ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars_of_isIntegral _⟩

theorem IsIntegral.isAlgebraic_iff_top [Algebra.IsIntegral R S]
    [FaithfulSMul R S] : Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S A := by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsIntegral.isAlgebraic_iff R S]

protected theorem IsAlgebraic.isAlgebraic_iff [Algebra.IsAlgebraic R S] [FaithfulSMul R S]
    {a : A} : IsAlgebraic R a ↔ IsAlgebraic S a :=
  ⟨.extendScalars (FaithfulSMul.algebraMap_injective ..), .restrictScalars _⟩

theorem IsAlgebraic.isAlgebraic_iff_top [Algebra.IsAlgebraic R S]
    [FaithfulSMul R S] : Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic S A := by
  simp_rw [Algebra.isAlgebraic_def, Algebra.IsAlgebraic.isAlgebraic_iff R S]

theorem IsAlgebraic.isAlgebraic_iff_bot [Algebra.IsAlgebraic S A] [FaithfulSMul S A] :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R S :=
  ⟨fun _ ↦ .tower_bot_of_injective (FaithfulSMul.algebraMap_injective S A), fun _ ↦ .trans R S A⟩

end Algebra

variable (R S)
/-- If `R` is a domain and `S` is an arbitrary `R`-algebra, then the elements of `S`
that are algebraic over `R` form a subalgebra. -/
def Subalgebra.algebraicClosure [IsDomain R] : Subalgebra R S where
  carrier := {s | IsAlgebraic R s}
  mul_mem' ha hb := ha.mul hb
  add_mem' ha hb := ha.add hb
  algebraMap_mem' := isAlgebraic_algebraMap

theorem Subalgebra.mem_algebraicClosure [IsDomain R] {x : S} :
    x ∈ algebraicClosure R S ↔ IsAlgebraic R x := Iff.rfl

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

/-- In an algebra generated by a single algebraic element over a domain `R`, every element is
algebraic. This may fail when `R` is not a domain: see https://mathoverflow.net/a/132192/ for
an example. -/
theorem Algebra.isAlgebraic_adjoin_singleton_iff [NoZeroDivisors R] {s : S} :
    (adjoin R {s}).IsAlgebraic ↔ IsAlgebraic R s :=
  (isAlgebraic_adjoin_of_nonempty <| Set.singleton_nonempty s).trans forall_eq

theorem IsAlgebraic.of_mul [NoZeroDivisors R] {y z : S} (hy : y ∈ nonZeroDivisors S)
    (alg_y : IsAlgebraic R y) (alg_yz : IsAlgebraic R (y * z)) : IsAlgebraic R z := by
  have ⟨t, ht, r, hr, eq⟩ := alg_y.exists_nonzero_eq_adjoin_mul hy
  have := alg_yz.mul (Algebra.isAlgebraic_adjoin_singleton_iff.mpr alg_y _ ht)
  rw [mul_right_comm, eq, ← Algebra.smul_def] at this
  exact this.of_smul (mem_nonZeroDivisors_of_ne_zero hr)

open Algebra in
omit [Algebra R A] [IsScalarTower R S A] in
theorem IsAlgebraic.adjoin_of_forall_isAlgebraic [NoZeroDivisors S] {s t : Set S}
    (alg : ∀ x ∈ s \ t, IsAlgebraic (adjoin R t) x) {a : A}
    (ha : IsAlgebraic (adjoin R s) a) : IsAlgebraic (adjoin R t) a := by
  set Rs := adjoin R s
  set Rt := adjoin R t
  let Rts := adjoin Rt s
  let _ : Algebra Rs Rts := (Subalgebra.inclusion
    (T := Rts.restrictScalars R) <| adjoin_le <| by apply subset_adjoin).toAlgebra
  have : IsScalarTower Rs Rts A := .of_algebraMap_eq fun ⟨a, _⟩ ↦ rfl
  have : Algebra.IsAlgebraic Rt Rts := by
    have := ha.nontrivial
    have := Subtype.val_injective (p := (· ∈ Rs)).nontrivial
    have := (isDomain_iff_noZeroDivisors_and_nontrivial Rt).mpr ⟨inferInstance, inferInstance⟩
    rw [← Subalgebra.isAlgebraic_iff, isAlgebraic_adjoin_iff]
    intro x hs
    by_cases ht : x ∈ t
    · exact isAlgebraic_algebraMap (⟨x, subset_adjoin ht⟩ : Rt)
    exact alg _ ⟨hs, ht⟩
  have : IsAlgebraic Rts a := ha.extendScalars (by apply Subalgebra.inclusion_injective)
  exact this.restrictScalars Rt

namespace Transcendental

section

variable (S) [NoZeroDivisors S] {a : A} (ha : Transcendental R a)
include ha

lemma extendScalars_of_isIntegral [Algebra.IsIntegral R S] :
    Transcendental S a := by
  contrapose ha
  rw [Transcendental, not_not] at ha ⊢
  exact ha.restrictScalars_of_isIntegral _

lemma extendScalars [Algebra.IsAlgebraic R S] : Transcendental S a := by
  contrapose ha
  rw [Transcendental, not_not] at ha ⊢
  exact ha.restrictScalars _

end

variable [NoZeroDivisors S] {a : S} (ha : Transcendental R a)
include ha

protected lemma integralClosure : Transcendental (integralClosure R S) a :=
  ha.extendScalars_of_isIntegral _

lemma subalgebraAlgebraicClosure [IsDomain R] :
    Transcendental (Subalgebra.algebraicClosure R S) a := ha.extendScalars _

end Transcendental

namespace Algebra

variable (R S) [NoZeroDivisors S] [FaithfulSMul R S] {a : A}

protected theorem IsIntegral.transcendental_iff [Algebra.IsIntegral R S] :
    Transcendental R a ↔ Transcendental S a :=
  ⟨(·.extendScalars_of_isIntegral _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

protected theorem IsAlgebraic.transcendental_iff [Algebra.IsAlgebraic R S] :
    Transcendental R a ↔ Transcendental S a :=
  ⟨(·.extendScalars _), (·.restrictScalars (FaithfulSMul.algebraMap_injective R S))⟩

end Algebra

open scoped nonZeroDivisors

namespace Algebra.IsAlgebraic

section IsFractionRing

variable (R S) (R' S' : Type*) [CommRing S'] [FaithfulSMul R S] [alg : Algebra.IsAlgebraic R S]
  [NoZeroDivisors S] [Algebra S S'] [IsFractionRing S S']

instance : IsLocalization (algebraMapSubmonoid S R⁰) S' :=
  have := (FaithfulSMul.algebraMap_injective R S).noZeroDivisors _ (map_zero _) (map_mul _)
  (IsLocalization.iff_of_le_of_exists_dvd _ S⁰
    (map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective ..) le_rfl)
    fun s hs ↦ have ⟨r, ne, eq⟩ := (alg.1 s).exists_nonzero_dvd hs
    ⟨_, ⟨r, mem_nonZeroDivisors_of_ne_zero ne, rfl⟩, eq⟩).mpr inferInstance

variable [Algebra R S'] [IsScalarTower R S S']

instance : IsLocalizedModule R⁰ (IsScalarTower.toAlgHom R S S').toLinearMap :=
  isLocalizedModule_iff_isLocalization.mpr inferInstance

variable [CommRing R'] [Algebra R R'] [IsFractionRing R R']

theorem isBaseChange_of_isFractionRing [Module R' S'] [IsScalarTower R R' S'] :
    IsBaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap :=
  (isLocalizedModule_iff_isBaseChange R⁰ ..).mp inferInstance

variable [Algebra R' S'] [IsScalarTower R R' S']

instance : IsPushout R R' S S' := (isPushout_iff ..).mpr <| isBaseChange_of_isFractionRing ..
instance : IsPushout R S R' S' := .symm inferInstance

end IsFractionRing

variable (R) (R' : Type*) (S : Type u) [CommRing R'] [CommRing S] [Algebra R S]
  [Algebra R R'] [IsFractionRing R R'] [FaithfulSMul R S] [Algebra.IsAlgebraic R S]

section

variable [NoZeroDivisors S] (S' : Type v) [CommRing S'] [Algebra R S'] [Algebra S S'] [Module R' S']
  [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsFractionRing S S']

theorem lift_rank_of_isFractionRing :
    Cardinal.lift.{u} (Module.rank R' S') = Cardinal.lift.{v} (Module.rank R S) := by
  rw [IsLocalization.rank_eq R' R⁰ le_rfl,
    IsLocalizedModule.lift_rank_eq R⁰ (IsScalarTower.toAlgHom R S S').toLinearMap le_rfl]

theorem finrank_of_isFractionRing : Module.finrank R' S' = Module.finrank R S := by
  simpa using congr_arg Cardinal.toNat (lift_rank_of_isFractionRing ..)

theorem rank_of_isFractionRing (S' : Type u) [CommRing S'] [Algebra R S'] [Algebra S S']
    [Module R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] [IsFractionRing S S'] :
    Module.rank R' S' = Module.rank R S := by
  simpa using lift_rank_of_isFractionRing R R' S S'

end

attribute [local instance] FractionRing.liftAlgebra in
theorem rank_fractionRing [IsDomain S] :
    Module.rank (FractionRing R) (FractionRing S) = Module.rank R S :=
  rank_of_isFractionRing ..

end Algebra.IsAlgebraic

section Polynomial

attribute [local instance] Polynomial.algebra MvPolynomial.algebraMvPolynomial

section

variable (R S) [NoZeroDivisors R]

-- TODO: `PolynomialModule` version
theorem rank_polynomial_polynomial : Module.rank R[X] S[X] = Module.rank R S :=
  ((Algebra.isPushout_iff ..).mp inferInstance).rank_eq

theorem rank_mvPolynomial_mvPolynomial (σ : Type u) :
    Module.rank (MvPolynomial σ R) (MvPolynomial σ S) = Cardinal.lift.{u} (Module.rank R S) := by
  have := Algebra.isPushout_iff R (MvPolynomial σ R) S (MvPolynomial σ S)
    |>.mp inferInstance |>.lift_rank_eq
  rwa [Cardinal.lift_id', Cardinal.lift_umax] at this

end

variable [alg : Algebra.IsAlgebraic R S]

section Pushout

variable (R S) (R' : Type*) [CommRing R'] [Algebra R R'] [NoZeroDivisors R'] [FaithfulSMul R R']

open TensorProduct in
instance Algebra.IsAlgebraic.tensorProduct : Algebra.IsAlgebraic R' (R' ⊗[R] S) where
  isAlgebraic p :=
    have := IsAlgebraic.nontrivial R S
    have := (FaithfulSMul.algebraMap_injective R R').nontrivial
    p.induction_on isAlgebraic_zero (fun _ s ↦ .tmul _ <| alg.1 s) (fun _ _ ↦ .add)

variable (S' : Type*) [CommRing S'] [Algebra R S'] [Algebra S S'] [Algebra R' S']
  [IsScalarTower R R' S'] [IsScalarTower R S S']

theorem Algebra.IsPushout.isAlgebraic' [IsPushout R R' S S'] : Algebra.IsAlgebraic R' S' :=
  (equiv R R' S S').isAlgebraic

theorem Algebra.IsPushout.isAlgebraic [h : IsPushout R S R' S'] : Algebra.IsAlgebraic R' S' :=
  have := h.symm; (equiv R R' S S').isAlgebraic

end Pushout

instance [NoZeroDivisors R] : Algebra.IsAlgebraic R[X] S[X] := Algebra.IsPushout.isAlgebraic R S ..

instance [NoZeroDivisors S] : Algebra.IsAlgebraic R[X] S[X] := by
  by_cases h : Function.Injective (algebraMap R S)
  · have := h.noZeroDivisors _ (map_zero _) (map_mul _); infer_instance
  rw [← Polynomial.map_injective_iff] at h
  exact Algebra.isAlgebraic_of_not_injective h

theorem Polynomial.exists_dvd_map_of_isAlgebraic [NoZeroDivisors S] {f : S[X]} (hf : f ≠ 0) :
    ∃ g : R[X], g ≠ 0 ∧ f ∣ g.map (algebraMap R S) :=
  (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

instance {σ} [NoZeroDivisors R] : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial σ S) :=
  Algebra.IsPushout.isAlgebraic R S ..

instance {σ} [NoZeroDivisors S] : Algebra.IsAlgebraic (MvPolynomial σ R) (MvPolynomial σ S) := by
  by_cases h : Function.Injective (algebraMap R S)
  · have := h.noZeroDivisors _ (map_zero _) (map_mul _); infer_instance
  rw [← MvPolynomial.map_injective_iff] at h
  exact Algebra.isAlgebraic_of_not_injective h

theorem MvPolynomial.exists_dvd_map_of_isAlgebraic {σ}
    [NoZeroDivisors S] {f : MvPolynomial σ S} (hf : f ≠ 0) :
    ∃ g : MvPolynomial σ R, g ≠ 0 ∧ f ∣ g.map (algebraMap R S) :=
  (Algebra.IsAlgebraic.isAlgebraic f).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hf)

variable [IsDomain S] [FaithfulSMul R S]

attribute [local instance] FractionRing.liftAlgebra

instance : Algebra.IsPushout R (FractionRing R[X]) S (FractionRing S[X]) :=
  (Algebra.IsPushout.comp_iff _ R[X] _ S[X]).mpr inferInstance

instance : Algebra.IsPushout R S (FractionRing R[X]) (FractionRing S[X]) := .symm inferInstance

instance {σ : Type*} :
    Algebra.IsPushout R (FractionRing (MvPolynomial σ R)) S (FractionRing (MvPolynomial σ S)) :=
  (Algebra.IsPushout.comp_iff _ (MvPolynomial σ R) _ (MvPolynomial σ S)).mpr inferInstance

instance {σ : Type*} :
    Algebra.IsPushout R S (FractionRing (MvPolynomial σ R)) (FractionRing (MvPolynomial σ S)) :=
  .symm inferInstance

namespace Algebra.IsAlgebraic

@[stacks 0G1M] theorem rank_fractionRing_polynomial :
    Module.rank (FractionRing R[X]) (FractionRing S[X]) = Module.rank R S := by
  have := (FaithfulSMul.algebraMap_injective R S).isDomain
  rw [rank_fractionRing, rank_polynomial_polynomial]

open Cardinal in
@[stacks 0G1M] theorem rank_fractionRing_mvPolynomial (σ : Type u) :
    Module.rank (FractionRing (MvPolynomial σ R)) (FractionRing (MvPolynomial σ S)) =
    lift.{u} (Module.rank R S) := by
  have := (FaithfulSMul.algebraMap_injective R S).isDomain
  rw [rank_fractionRing, rank_mvPolynomial_mvPolynomial]

end Algebra.IsAlgebraic

end Polynomial
