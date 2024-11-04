/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.AdjoinRoot.Defs
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Adjoining roots of polynomials


## Main definitions and results

* `lift_hom (x : S) (hfx : aeval x f = 0) : AdjoinRoot f →ₐ[R] S`, the algebra
  homomorphism from R[X]/(f) to S extending `algebraMap R S` and sending `X` to `x`

* `equiv : (AdjoinRoot f →ₐ[F] E) ≃ {x // x ∈ f.aroots E}` a
  bijection between algebra homomorphisms from `AdjoinRoot` and roots of `f` in `S`

-/

noncomputable section

open scoped Classical

open Polynomial

universe u v w

variable {R : Type u} {S : Type v} {K : Type w}

open Polynomial Ideal

namespace AdjoinRoot

section CommRing

variable [CommRing R] (f : R[X])

protected theorem nontrivial [IsDomain R] (h : degree f ≠ 0) : Nontrivial (AdjoinRoot f) :=
  Ideal.Quotient.nontrivial
    (by
      simp_rw [Ne, span_singleton_eq_top, Polynomial.isUnit_iff, not_exists, not_and]
      rintro x hx rfl
      exact h (degree_C hx.ne_zero))

instance isScalarTower_right [DistribSMul S R] [IsScalarTower S R R] :
    IsScalarTower S (AdjoinRoot f) (AdjoinRoot f) :=
  Ideal.Quotient.isScalarTower_right

instance [CommSemiring S] [Algebra S R] : Algebra S (AdjoinRoot f) :=
  Ideal.Quotient.algebra S

@[simp]
theorem algebraMap_eq : algebraMap R (AdjoinRoot f) = of f :=
  rfl

variable (S)

theorem algebraMap_eq' [CommSemiring S] [Algebra S R] :
    algebraMap S (AdjoinRoot f) = (of f).comp (algebraMap S R) :=
  rfl

variable {S}

theorem finiteType : Algebra.FiniteType R (AdjoinRoot f) :=
  (Algebra.FiniteType.polynomial R).of_surjective _ (Ideal.Quotient.mkₐ_surjective R _)

theorem finitePresentation : Algebra.FinitePresentation R (AdjoinRoot f) :=
  (Algebra.FinitePresentation.polynomial R).quotient (Submodule.fg_span_singleton f)

variable {f}

/-- Two `R`-`AlgHom` from `AdjoinRoot f` to the same `R`-algebra are the same iff
    they agree on `root f`. -/
@[ext]
theorem algHom_ext [Semiring S] [Algebra R S] {g₁ g₂ : AdjoinRoot f →ₐ[R] S}
    (h : g₁ (root f) = g₂ (root f)) : g₁ = g₂ :=
  Ideal.Quotient.algHom_ext R <| Polynomial.algHom_ext h


@[simp]
theorem aeval_eq (p : R[X]) : aeval (root f) p = mk f p :=
  Polynomial.induction_on p
    (fun x => by
      rw [aeval_C]
      rfl)
    (fun p q ihp ihq => by rw [map_add, RingHom.map_add, ihp, ihq]) fun n x _ => by
    rw [_root_.map_mul, aeval_C, map_pow, aeval_X, RingHom.map_mul, mk_C, RingHom.map_pow, mk_X]
    rfl

theorem adjoinRoot_eq_top : Algebra.adjoin R ({root f} : Set (AdjoinRoot f)) = ⊤ := by
  refine Algebra.eq_top_iff.2 fun x => ?_
  induction x using AdjoinRoot.induction_on with
    | ih p => exact (Algebra.adjoin_singleton_eq_range_aeval R (root f)).symm ▸ ⟨p, aeval_eq p⟩

@[simp]
theorem eval₂_root (f : R[X]) : f.eval₂ (of f) (root f) = 0 := by
  rw [← algebraMap_eq, ← aeval_def, aeval_eq, mk_self]

theorem isRoot_root (f : R[X]) : IsRoot (f.map (of f)) (root f) := by
  rw [IsRoot, eval_map, eval₂_root]

theorem isAlgebraic_root (hf : f ≠ 0) : IsAlgebraic R (root f) :=
  ⟨f, hf, eval₂_root f⟩

variable [CommRing S] {i : R →+* S} {a : S} (h : f.eval₂ i a = 0)
variable (f) [Algebra R S]

/-- Produce an algebra homomorphism `AdjoinRoot f →ₐ[R] S` sending `root f` to
a root of `f` in `S`. -/
def liftHom (x : S) (hfx : aeval x f = 0) : AdjoinRoot f →ₐ[R] S :=
  { lift (algebraMap R S) x hfx with
    commutes' := fun r => show lift _ _ hfx r = _ from lift_of hfx }

@[simp]
theorem coe_liftHom (x : S) (hfx : aeval x f = 0) :
    (liftHom f x hfx : AdjoinRoot f →+* S) = lift (algebraMap R S) x hfx :=
  rfl

@[simp]
theorem aeval_algHom_eq_zero (ϕ : AdjoinRoot f →ₐ[R] S) : aeval (ϕ (root f)) f = 0 := by
  have h : ϕ.toRingHom.comp (of f) = algebraMap R S := RingHom.ext_iff.mpr ϕ.commutes
  rw [aeval_def, ← h, ← RingHom.map_zero ϕ.toRingHom, ← eval₂_root f, hom_eval₂]
  rfl

@[simp]
theorem liftHom_eq_algHom (f : R[X]) (ϕ : AdjoinRoot f →ₐ[R] S) :
    liftHom f (ϕ (root f)) (aeval_algHom_eq_zero f ϕ) = ϕ := by
  suffices AlgHom.equalizer ϕ (liftHom f (ϕ (root f)) (aeval_algHom_eq_zero f ϕ)) = ⊤ by
    exact (AlgHom.ext fun x => (SetLike.ext_iff.mp this x).mpr Algebra.mem_top).symm
  rw [eq_top_iff, ← adjoinRoot_eq_top, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
  exact (@lift_root _ _ _ _ _ _ _ (aeval_algHom_eq_zero f ϕ)).symm

variable (hfx : aeval a f = 0)

@[simp]
theorem liftHom_mk {g : R[X]} : liftHom f a hfx (mk f g) = aeval a g :=
  lift_mk hfx g

@[simp]
theorem liftHom_root : liftHom f a hfx (root f) = a :=
  lift_root hfx

@[simp]
theorem liftHom_of {x : R} : liftHom f a hfx (of f x) = algebraMap _ _ x :=
  lift_of hfx

section AdjoinInv

@[simp]
theorem root_isInv (r : R) : of _ r * root (C r * X - 1) = 1 := by
  convert sub_eq_zero.1 ((eval₂_sub _).symm.trans <| eval₂_root <| C r * X - 1) <;>
    simp only [eval₂_mul, eval₂_C, eval₂_X, eval₂_one]

theorem algHom_subsingleton {S : Type*} [CommRing S] [Algebra R S] {r : R} :
    Subsingleton (AdjoinRoot (C r * X - 1) →ₐ[R] S) :=
  ⟨fun f g =>
    algHom_ext
      (@inv_unique _ _ (algebraMap R S r) _ _
        (by rw [← f.commutes, ← _root_.map_mul, algebraMap_eq, root_isInv, map_one])
        (by rw [← g.commutes, ← _root_.map_mul, algebraMap_eq, root_isInv, map_one]))⟩

end AdjoinInv

section Prime

variable {f}

theorem isDomain_of_prime (hf : Prime f) : IsDomain (AdjoinRoot f) :=
  (Ideal.Quotient.isDomain_iff_prime (span {f} : Ideal R[X])).mpr <|
    (Ideal.span_singleton_prime hf.ne_zero).mpr hf

theorem noZeroSMulDivisors_of_prime_of_degree_ne_zero [IsDomain R] (hf : Prime f)
    (hf' : f.degree ≠ 0) : NoZeroSMulDivisors R (AdjoinRoot f) :=
  haveI := isDomain_of_prime hf
  NoZeroSMulDivisors.iff_algebraMap_injective.mpr (of.injective_of_degree_ne_zero hf')

end Prime

end CommRing

section Irreducible

variable [Field K] {f : K[X]}

instance span_maximal_of_irreducible [Fact (Irreducible f)] : (span {f}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible <| Fact.out

noncomputable instance instGroupWithZero [Fact (Irreducible f)] : GroupWithZero (AdjoinRoot f) :=
  Quotient.groupWithZero (span {f} : Ideal K[X])

noncomputable instance instField [Fact (Irreducible f)] : Field (AdjoinRoot f) where
  __ := instCommRing _
  __ := instGroupWithZero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by
    rw [← map_natCast (of f), ← map_natCast (of f), ← map_div₀, ← NNRat.cast_def]; rfl
  ratCast_def q := by
    rw [← map_natCast (of f), ← map_intCast (of f), ← map_div₀, ← Rat.cast_def]; rfl
  nnqsmul_def q x :=
    AdjoinRoot.induction_on f (C := fun y ↦ q • y = (of f) q * y) x fun p ↦ by
      simp only [smul_mk, of, RingHom.comp_apply, ← (mk f).map_mul, Polynomial.nnqsmul_eq_C_mul]
  qsmul_def q x :=
    -- Porting note: I gave the explicit motive and changed `rw` to `simp`.
    AdjoinRoot.induction_on f (C := fun y ↦ q • y = (of f) q * y) x fun p ↦ by
      simp only [smul_mk, of, RingHom.comp_apply, ← (mk f).map_mul, Polynomial.qsmul_eq_C_mul]

theorem coe_injective (h : degree f ≠ 0) : Function.Injective ((↑) : K → AdjoinRoot f) :=
  have := AdjoinRoot.nontrivial f h
  (of f).injective

theorem coe_injective' [Fact (Irreducible f)] : Function.Injective ((↑) : K → AdjoinRoot f) :=
  (of f).injective

variable (f)

theorem mul_div_root_cancel [Fact (Irreducible f)] :
    (X - C (root f)) * ((f.map (of f)) / (X - C (root f))) = f.map (of f) :=
  mul_div_eq_iff_isRoot.2 <| isRoot_root _

end Irreducible

section IsNoetherianRing

instance [CommRing R] [IsNoetherianRing R] {f : R[X]} : IsNoetherianRing (AdjoinRoot f) :=
  Ideal.Quotient.isNoetherianRing _

end IsNoetherianRing

section Equiv

section minpoly

variable [CommRing R] [CommRing S] [Algebra R S] (x : S) (R)

open Algebra Polynomial

/-- The surjective algebra morphism `R[X]/(minpoly R x) → R[x]`.
If `R` is a integrally closed domain and `x` is integral, this is an isomorphism,
see `minpoly.equivAdjoin`. -/
@[simps!]
def Minpoly.toAdjoin : AdjoinRoot (minpoly R x) →ₐ[R] adjoin R ({x} : Set S) :=
  liftHom _ ⟨x, self_mem_adjoin_singleton R x⟩
    (by simp [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe])

variable {R x}

theorem Minpoly.toAdjoin_apply' (a : AdjoinRoot (minpoly R x)) :
    Minpoly.toAdjoin R x a =
      liftHom (minpoly R x) (⟨x, self_mem_adjoin_singleton R x⟩ : adjoin R ({x} : Set S))
        (by simp [← Subalgebra.coe_eq_zero, aeval_subalgebra_coe]) a :=
  rfl

theorem Minpoly.toAdjoin.apply_X :
    Minpoly.toAdjoin R x (mk (minpoly R x) X) = ⟨x, self_mem_adjoin_singleton R x⟩ := by
  simp [toAdjoin]

variable (R x)

theorem Minpoly.toAdjoin.surjective : Function.Surjective (Minpoly.toAdjoin R x) := by
  rw [← range_top_iff_surjective, _root_.eq_top_iff, ← adjoin_adjoin_coe_preimage]
  exact adjoin_le fun ⟨y₁, y₂⟩ h ↦ ⟨mk (minpoly R x) X, by simpa [toAdjoin] using h.symm⟩

end minpoly

end Equiv


variable [Field K] {f : K[X]}

theorem isIntegral_root (hf : f ≠ 0) : IsIntegral K (root f) :=
  (isAlgebraic_root hf).isIntegral

theorem minpoly_root (hf : f ≠ 0) : minpoly K (root f) = f * C f.leadingCoeff⁻¹ := by
  have f'_monic : Monic _ := monic_mul_leadingCoeff_inv hf
  refine (minpoly.unique K _ f'_monic ?_ ?_).symm
  · rw [_root_.map_mul, aeval_eq, mk_self, zero_mul]
  intro q q_monic q_aeval
  have commutes : (lift (algebraMap K (AdjoinRoot f)) (root f) q_aeval).comp (mk q) = mk f := by
    ext
    · simp only [RingHom.comp_apply, mk_C, lift_of]
      rfl
    · simp only [RingHom.comp_apply, mk_X, lift_root]
  rw [degree_eq_natDegree f'_monic.ne_zero, degree_eq_natDegree q_monic.ne_zero,
    Nat.cast_le, natDegree_mul hf, natDegree_C, add_zero]
  · apply natDegree_le_of_dvd
    · have : mk f q = 0 := by rw [← commutes, RingHom.comp_apply, mk_self, RingHom.map_zero]
      exact mk_eq_zero.1 this
    · exact q_monic.ne_zero
  · rwa [Ne, C_eq_zero, inv_eq_zero, leadingCoeff_eq_zero]

end AdjoinRoot

/-- If `L / K` is an integral extension, `K` is a domain, `L` is a field, then any irreducible
polynomial over `L` divides some monic irreducible polynomial over `K`. -/
theorem Irreducible.exists_dvd_monic_irreducible_of_isIntegral {K L : Type*}
    [CommRing K] [IsDomain K] [Field L] [Algebra K L] [Algebra.IsIntegral K L] {f : L[X]}
    (hf : Irreducible f) : ∃ g : K[X], g.Monic ∧ Irreducible g ∧ f ∣ g.map (algebraMap K L) := by
  haveI := Fact.mk hf
  have h := hf.ne_zero
  have h2 := isIntegral_trans (R := K) _ (AdjoinRoot.isIntegral_root h)
  have h3 := (AdjoinRoot.minpoly_root h) ▸ minpoly.dvd_map_of_isScalarTower K L (AdjoinRoot.root f)
  exact ⟨_, minpoly.monic h2, minpoly.irreducible h2, dvd_of_mul_right_dvd h3⟩
