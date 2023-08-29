/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Trace

#align_import ring_theory.dedekind_domain.integral_closure from "leanprover-community/mathlib"@"4cf7ca0e69e048b006674cf4499e5c7d296a89e0"

/-!
# Integral closure of Dedekind domains

This file shows the integral closure of a Dedekind domain (in particular, the ring of integers
of a number field) is a Dedekind domain.

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

variable [IsDomain A]

section IsIntegralClosure

/-! ### `IsIntegralClosure` section

We show that an integral closure of a Dedekind domain in a finite separable
field extension is again a Dedekind domain. This implies the ring of integers
of a number field is a Dedekind domain. -/


open Algebra

open scoped BigOperators

variable [Algebra A K] [IsFractionRing A K]

variable (L : Type*) [Field L] (C : Type*) [CommRing C]

variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

variable [Algebra C L] [IsIntegralClosure C A L] [Algebra A C] [IsScalarTower A C L]

/- If `L` is a separable extension of `K = Frac(A)` and `L` has no zero smul divisors by `A`,
then `L` is the localization of the integral closure `C` of `A` in `L` at `A⁰`. -/
theorem IsIntegralClosure.isLocalization [IsSeparable K L] [NoZeroSMulDivisors A L] :
    IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L := by
  haveI : IsDomain C :=
    (IsIntegralClosure.equiv A C L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  haveI : NoZeroSMulDivisors A C := IsIntegralClosure.noZeroSMulDivisors A L
  -- ⊢ IsLocalization (algebraMapSubmonoid C A⁰) L
  refine' ⟨_, fun z => _, fun {x y} => ⟨fun h => ⟨1, _⟩, _⟩⟩
  · rintro ⟨_, x, hx, rfl⟩
    -- ⊢ IsUnit (↑(algebraMap C L) ↑{ val := ↑(algebraMap A C) x, property := (_ : ∃  …
    rw [isUnit_iff_ne_zero, map_ne_zero_iff _ (IsIntegralClosure.algebraMap_injective C A L),
      Subtype.coe_mk, map_ne_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective A C)]
    exact mem_nonZeroDivisors_iff_ne_zero.mp hx
    -- 🎉 no goals
  · obtain ⟨m, hm⟩ :=
      IsIntegral.exists_multiple_integral_of_isLocalization A⁰ z (IsSeparable.isIntegral K z)
    obtain ⟨x, hx⟩ : ∃ x, algebraMap C L x = m • z := IsIntegralClosure.isIntegral_iff.mp hm
    -- ⊢ ∃ x, z * ↑(algebraMap C L) ↑x.snd = ↑(algebraMap C L) x.fst
    refine' ⟨⟨x, algebraMap A C m, m, SetLike.coe_mem m, rfl⟩, _⟩
    -- ⊢ z * ↑(algebraMap C L) ↑(x, { val := ↑(algebraMap A C) ↑m, property := (_ : ∃ …
    rw [Subtype.coe_mk, ← IsScalarTower.algebraMap_apply, hx, mul_comm, Submonoid.smul_def,
      smul_def]
  · simp only [IsIntegralClosure.algebraMap_injective C A L h]
    -- 🎉 no goals
  · rintro ⟨⟨_, m, hm, rfl⟩, h⟩
    -- ⊢ ↑(algebraMap C L) x = ↑(algebraMap C L) y
    refine' congr_arg (algebraMap C L) ((mul_right_inj' _).mp h)
    -- ⊢ ↑{ val := ↑(algebraMap A C) m, property := (_ : ∃ a, a ∈ ↑A⁰ ∧ ↑(algebraMap  …
    rw [Subtype.coe_mk, map_ne_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective A C)]
    -- ⊢ m ≠ 0
    exact mem_nonZeroDivisors_iff_ne_zero.mp hm
    -- 🎉 no goals
#align is_integral_closure.is_localization IsIntegralClosure.isLocalization

variable [FiniteDimensional K L]

variable {A K L}

theorem IsIntegralClosure.range_le_span_dualBasis [IsSeparable K L] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι K L) (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    LinearMap.range ((Algebra.linearMap C L).restrictScalars A) ≤
    Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceForm_nondegenerate K L) b) := by
  let db := (traceForm K L).dualBasis (traceForm_nondegenerate K L) b
  -- ⊢ LinearMap.range (↑A (Algebra.linearMap C L)) ≤ Submodule.span A (Set.range ↑ …
  rintro _ ⟨x, rfl⟩
  -- ⊢ ↑(↑A (Algebra.linearMap C L)) x ∈ Submodule.span A (Set.range ↑(BilinForm.du …
  simp only [LinearMap.coe_restrictScalars, Algebra.linearMap_apply]
  -- ⊢ ↑(algebraMap C L) x ∈ Submodule.span A (Set.range ↑(BilinForm.dualBasis (tra …
  have hx : IsIntegral A (algebraMap C L x) := (IsIntegralClosure.isIntegral A L x).algebraMap
  -- ⊢ ↑(algebraMap C L) x ∈ Submodule.span A (Set.range ↑(BilinForm.dualBasis (tra …
  rsuffices ⟨c, x_eq⟩ : ∃ c : ι → A, algebraMap C L x = ∑ i, c i • db i
  -- ⊢ ↑(algebraMap C L) x ∈ Submodule.span A (Set.range ↑(BilinForm.dualBasis (tra …
  · rw [x_eq]
    -- ⊢ ∑ i : ι, c i • ↑db i ∈ Submodule.span A (Set.range ↑(BilinForm.dualBasis (tr …
    refine' Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span _)
    -- ⊢ ↑db i ∈ Set.range ↑(BilinForm.dualBasis (traceForm K L) (_ : BilinForm.Nonde …
    rw [Set.mem_range]
    -- ⊢ ∃ y, ↑(BilinForm.dualBasis (traceForm K L) (_ : BilinForm.Nondegenerate (tra …
    exact ⟨i, rfl⟩
    -- 🎉 no goals
  suffices ∃ c : ι → K, (∀ i, IsIntegral A (c i)) ∧ algebraMap C L x = ∑ i, c i • db i by
    obtain ⟨c, hc, hx⟩ := this
    have hc' : ∀ i, IsLocalization.IsInteger A (c i) := fun i =>
      IsIntegrallyClosed.isIntegral_iff.mp (hc i)
    use fun i => Classical.choose (hc' i)
    refine' hx.trans (Finset.sum_congr rfl fun i _ => _)
    conv_lhs => rw [← Classical.choose_spec (hc' i)]
    rw [← IsScalarTower.algebraMap_smul K (Classical.choose (hc' i)) (db i)]
  refine' ⟨fun i => db.repr (algebraMap C L x) i, fun i => _, (db.sum_repr _).symm⟩
  -- ⊢ IsIntegral A ((fun i => ↑(↑db.repr (↑(algebraMap C L) x)) i) i)
  simp_rw [BilinForm.dualBasis_repr_apply]
  -- ⊢ IsIntegral A (BilinForm.bilin (traceForm K L) (↑(algebraMap C L) x) (↑b i))
  exact isIntegral_trace (isIntegral_mul hx (hb_int i))
  -- 🎉 no goals
#align is_integral_closure.range_le_span_dual_basis IsIntegralClosure.range_le_span_dualBasis

theorem integralClosure_le_span_dualBasis [IsSeparable K L] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) (hb_int : ∀ i, IsIntegral A (b i)) [IsIntegrallyClosed A] :
    Subalgebra.toSubmodule (integralClosure A L) ≤
    Submodule.span A (Set.range <| (traceForm K L).dualBasis (traceForm_nondegenerate K L) b) := by
  refine' le_trans _ (IsIntegralClosure.range_le_span_dualBasis (integralClosure A L) b hb_int)
  -- ⊢ ↑Subalgebra.toSubmodule (integralClosure A L) ≤ LinearMap.range (↑A (Algebra …
  intro x hx
  -- ⊢ x ∈ LinearMap.range (↑A (Algebra.linearMap { x // x ∈ integralClosure A L }  …
  exact ⟨⟨x, hx⟩, rfl⟩
  -- 🎉 no goals
#align integral_closure_le_span_dual_basis integralClosure_le_span_dualBasis

variable (A K)

/-- Send a set of `x`s in a finite extension `L` of the fraction field of `R`
to `(y : R) • x ∈ integralClosure R L`. -/
theorem exists_integral_multiples (s : Finset L) :
    ∃ (y : _) (_ : y ≠ (0 : A)), ∀ x ∈ s, IsIntegral A (y • x) := by
  haveI := Classical.decEq L
  -- ⊢ ∃ y x, ∀ (x : L), x ∈ s → IsIntegral A (y • x)
  refine' s.induction _ _
  -- ⊢ ∃ y x, ∀ (x : L), x ∈ ∅ → IsIntegral A (y • x)
  · use 1, one_ne_zero
    -- ⊢ ∀ (x : L), x ∈ ∅ → IsIntegral A (1 • x)
    rintro x ⟨⟩
    -- 🎉 no goals
  · rintro x s hx ⟨y, hy, hs⟩
    -- ⊢ ∃ y x_1, ∀ (x_2 : L), x_2 ∈ insert x s → IsIntegral A (y • x_2)
    have := exists_integral_multiple
      ((IsFractionRing.isAlgebraic_iff A K L).mpr (isAlgebraic_of_finite _ _ x))
      ((injective_iff_map_eq_zero (algebraMap A L)).mp ?_)
    rcases this with ⟨x', y', hy', hx'⟩
    -- ⊢ ∃ y x_1, ∀ (x_2 : L), x_2 ∈ insert x s → IsIntegral A (y • x_2)
    refine' ⟨y * y', mul_ne_zero hy hy', fun x'' hx'' => _⟩
    -- ⊢ IsIntegral A ((y * y') • x'')
    rcases Finset.mem_insert.mp hx'' with (rfl | hx'')
    · rw [mul_smul, Algebra.smul_def, Algebra.smul_def, mul_comm _ x'', hx']
      -- ⊢ IsIntegral A (↑(algebraMap A L) y * ↑x')
      exact isIntegral_mul isIntegral_algebraMap x'.2
      -- 🎉 no goals
    · rw [mul_comm, mul_smul, Algebra.smul_def]
      -- ⊢ IsIntegral A (↑(algebraMap A L) y' * y • x'')
      exact isIntegral_mul isIntegral_algebraMap (hs _ hx'')
      -- 🎉 no goals
    · rw [IsScalarTower.algebraMap_eq A K L]
      -- ⊢ Function.Injective ↑(RingHom.comp (algebraMap K L) (algebraMap A K))
      apply (algebraMap K L).injective.comp
      -- ⊢ Function.Injective fun x => ↑(algebraMap A K) x
      exact IsFractionRing.injective _ _
      -- 🎉 no goals
#align exists_integral_multiples exists_integral_multiples

variable (L)

/-- If `L` is a finite extension of `K = Frac(A)`,
then `L` has a basis over `A` consisting of integral elements. -/
theorem FiniteDimensional.exists_is_basis_integral :
    ∃ (s : Finset L) (b : Basis s K L), ∀ x, IsIntegral A (b x) := by
  letI := Classical.decEq L
  -- ⊢ ∃ s b, ∀ (x : { x // x ∈ s }), IsIntegral A (↑b x)
  letI : IsNoetherian K L := IsNoetherian.iff_fg.2 inferInstance
  -- ⊢ ∃ s b, ∀ (x : { x // x ∈ s }), IsIntegral A (↑b x)
  let s' := IsNoetherian.finsetBasisIndex K L
  -- ⊢ ∃ s b, ∀ (x : { x // x ∈ s }), IsIntegral A (↑b x)
  let bs' := IsNoetherian.finsetBasis K L
  -- ⊢ ∃ s b, ∀ (x : { x // x ∈ s }), IsIntegral A (↑b x)
  obtain ⟨y, hy, his'⟩ := exists_integral_multiples A K (Finset.univ.image bs')
  -- ⊢ ∃ s b, ∀ (x : { x // x ∈ s }), IsIntegral A (↑b x)
  have hy' : algebraMap A L y ≠ 0 := by
    refine' mt ((injective_iff_map_eq_zero (algebraMap A L)).mp _ _) hy
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  refine ⟨s', bs'.map {Algebra.lmul _ _ (algebraMap A L y) with
    toFun := fun x => algebraMap A L y * x
    invFun := fun x => (algebraMap A L y)⁻¹ * x
    left_inv := ?_
    right_inv := ?_}, ?_⟩
  · intro x; simp only [inv_mul_cancel_left₀ hy']
    -- ⊢ (fun x => (↑(algebraMap A L) y)⁻¹ * x) (AddHom.toFun { toAddHom := { toFun : …
             -- 🎉 no goals
  · intro x; simp only [mul_inv_cancel_left₀ hy']
    -- ⊢ AddHom.toFun { toAddHom := { toFun := fun x => ↑(algebraMap A L) y * x, map_ …
             -- 🎉 no goals
  · rintro ⟨x', hx'⟩
    -- ⊢ IsIntegral A
    simp only [Algebra.smul_def, Finset.mem_image, exists_prop, Finset.mem_univ,
      true_and_iff] at his'
    simp only [Basis.map_apply, LinearEquiv.coe_mk]
    -- ⊢ IsIntegral A (↑(algebraMap A L) y * ↑(IsNoetherian.finsetBasis K L) { val := …
    exact his' _ ⟨_, rfl⟩
    -- 🎉 no goals
#align finite_dimensional.exists_is_basis_integral FiniteDimensional.exists_is_basis_integral

variable [IsSeparable K L]

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian over `A`. -/
theorem IsIntegralClosure.isNoetherian [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherian A C := by
  haveI := Classical.decEq L
  -- ⊢ IsNoetherian A C
  obtain ⟨s, b, hb_int⟩ := FiniteDimensional.exists_is_basis_integral A K L
  -- ⊢ IsNoetherian A C
  let b' := (traceForm K L).dualBasis (traceForm_nondegenerate K L) b
  -- ⊢ IsNoetherian A C
  letI := isNoetherian_span_of_finite A (Set.finite_range b')
  -- ⊢ IsNoetherian A C
  let f : C →ₗ[A] Submodule.span A (Set.range b') :=
    (Submodule.ofLe (IsIntegralClosure.range_le_span_dualBasis C b hb_int)).comp
      ((Algebra.linearMap C L).restrictScalars A).rangeRestrict
  refine' isNoetherian_of_ker_bot f _
  -- ⊢ LinearMap.ker f = ⊥
  rw [LinearMap.ker_comp, Submodule.ker_ofLe, Submodule.comap_bot, LinearMap.ker_codRestrict]
  -- ⊢ LinearMap.ker (↑A (Algebra.linearMap C L)) = ⊥
  exact LinearMap.ker_eq_bot_of_injective (IsIntegralClosure.algebraMap_injective C A L)
  -- 🎉 no goals
#align is_integral_closure.is_noetherian IsIntegralClosure.isNoetherian

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure `C` of `A` in `L` is
Noetherian. -/
theorem IsIntegralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing C :=
  isNoetherianRing_iff.mpr <| isNoetherian_of_tower A (IsIntegralClosure.isNoetherian A K L C)
#align is_integral_closure.is_noetherian_ring IsIntegralClosure.isNoetherianRing

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a principal ring
and `L` has no zero smul divisors by `A`, the integral closure `C` of `A` in `L` is
a free `A`-module. -/
theorem IsIntegralClosure.module_free [NoZeroSMulDivisors A L] [IsPrincipalIdealRing A] :
    Module.Free A C := by
  haveI : NoZeroSMulDivisors A C := IsIntegralClosure.noZeroSMulDivisors A L
  -- ⊢ Module.Free A C
  haveI : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L _
  -- ⊢ Module.Free A C
  exact Module.free_of_finite_type_torsion_free'
  -- 🎉 no goals
#align is_integral_closure.module_free IsIntegralClosure.module_free

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a principal ring
and `L` has no zero smul divisors by `A`, the `A`-rank of the integral closure `C` of `A` in `L`
is equal to the `K`-rank of `L`. -/
theorem IsIntegralClosure.rank [IsPrincipalIdealRing A] [NoZeroSMulDivisors A L] :
    FiniteDimensional.finrank A C = FiniteDimensional.finrank K L := by
  haveI : Module.Free A C := IsIntegralClosure.module_free A K L C
  -- ⊢ FiniteDimensional.finrank A C = FiniteDimensional.finrank K L
  haveI : IsNoetherian A C := IsIntegralClosure.isNoetherian A K L C
  -- ⊢ FiniteDimensional.finrank A C = FiniteDimensional.finrank K L
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C A⁰) L :=
    IsIntegralClosure.isLocalization A K L C
  let b := Basis.localizationLocalization K A⁰ L (Module.Free.chooseBasis A C)
  -- ⊢ FiniteDimensional.finrank A C = FiniteDimensional.finrank K L
  rw [FiniteDimensional.finrank_eq_card_chooseBasisIndex, FiniteDimensional.finrank_eq_card_basis b]
  -- 🎉 no goals
#align is_integral_closure.rank IsIntegralClosure.rank

variable {A K}

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is
integrally closed and Noetherian, the integral closure of `A` in `L` is
Noetherian. -/
theorem integralClosure.isNoetherianRing [IsIntegrallyClosed A] [IsNoetherianRing A] :
    IsNoetherianRing (integralClosure A L) :=
  IsIntegralClosure.isNoetherianRing A K L (integralClosure A L)
#align integral_closure.is_noetherian_ring integralClosure.isNoetherianRing

variable (A K) [IsDomain C]

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure `C` of `A` in `L` is a Dedekind domain.

Can't be an instance since `A`, `K` or `L` can't be inferred. See also the instance
`integralClosure.isDedekindDomain_fractionRing` where `K := FractionRing A`
and `C := integralClosure A L`.
-/
theorem IsIntegralClosure.isDedekindDomain [IsDedekindDomain A] : IsDedekindDomain C :=
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  { IsIntegralClosure.isNoetherianRing A K L C,
    Ring.DimensionLEOne.isIntegralClosure A L C,
    (isIntegrallyClosed_iff L).mpr fun {x} hx =>
      ⟨IsIntegralClosure.mk' C x (isIntegral_trans (IsIntegralClosure.isIntegral_algebra A L) _ hx),
        IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain C }
#align is_integral_closure.is_dedekind_domain IsIntegralClosure.isDedekindDomain

/- If `L` is a finite separable extension of `K = Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

Can't be an instance since `K` can't be inferred. See also the instance
`integralClosure.isDedekindDomain_fractionRing` where `K := FractionRing A`.
-/
theorem integralClosure.isDedekindDomain [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)
#align integral_closure.is_dedekind_domain integralClosure.isDedekindDomain

variable [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]

variable [FiniteDimensional (FractionRing A) L] [IsSeparable (FractionRing A) L]

/- If `L` is a finite separable extension of `Frac(A)`, where `A` is a Dedekind domain,
the integral closure of `A` in `L` is a Dedekind domain.

See also the lemma `integralClosure.isDedekindDomain` where you can choose
the field of fractions yourself.
-/
instance integralClosure.isDedekindDomain_fractionRing [IsDedekindDomain A] :
    IsDedekindDomain (integralClosure A L) :=
  integralClosure.isDedekindDomain A (FractionRing A) L
#align integral_closure.is_dedekind_domain_fraction_ring integralClosure.isDedekindDomain_fractionRing

end IsIntegralClosure
