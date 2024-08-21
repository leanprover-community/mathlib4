import Mathlib.Algebra.Module.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Setup of Almost Ring Theory

In this file we define the basic setup of almost ring theory, and basic notations in almost

AlmostZero

AlmostInjective

AlmostSurjective

AlmostIsom

AlmostFree

AlmostFree module over V = Almost Free module over V/m

Goal: Lemma 4.1. Let M be an A-module which is π-adically complete and without π-torsion; let d ≥ 0. Then the A-module M is almost free of rank d if and only if the A/πA-module M/πM is almost free of rank d.

4.2 Let K be a perfectoid field of characteristic p, and L/K a finite field exten- sion. Then the OK-module OL (= the integral closure of OK inside L) is almost free of rank |L : K|. (char p case)
-/

section Almost

open scoped TensorProduct

open Module LinearMap

variable {V : Type*} [CommRing V] (m : Ideal V)

class AlmostBasicSetup : Prop where
  isIdempotent : IsIdempotentElem m
  flat_tensor : Flat V (m ⊗[V] m) -- not used in early definitions and properties

attribute [instance] AlmostBasicSetup.flat_tensor

section AddCommMonoid

variable (M N : Type*)
    [AddCommMonoid M] [AddCommMonoid N] [Module V M] [Module V N]

class Module.AlmostZero : Prop where
  almost_zero: m ≤ Module.annihilator V M

-- `Question: Defs and theorems uses 3 levels of assumptions`
-- variable (m : Ideal V) -- (h : IsIdempotentElem m) -- (hm : Flat V m) which make theorem proving easier than (hm2 : Flat V (m ⊗[V] m)) -- Leave comments `TODO: ... [GR Thm x.y.z]`

variable {M N} in
def LinearMap.AlmostInjective (f : M →ₗ[V] N) : Prop := AlmostZero m (ker f)

end AddCommMonoid

variable (M N : Type*)
    [AddCommGroup M] [AddCommGroup N] [Module V M] [Module V N]

variable {M N} in
def LinearMap.AlmostSurjective (f : M →ₗ[V] N) : Prop := AlmostZero m (N ⧸ (range f)) -- AlmostZero m (coker f)

structure AlmostIsom extends M →ₗ[V] N where
  almost_inj : AlmostInjective m toLinearMap
  almost_surj : AlmostSurjective m toLinearMap

structure AlmostFreeOfRankData (d : ℕ) :=
  toFun : m → (Fin d → m) →ₗ[V] M
  ann_kernel : ∀ x : m, (x : V) ∈ (ker (toFun x)).annihilator
  -- ann_cokernel : ∀ x : m, (x : V) ∈ (cokernel (toFun x)).annihilator

-- should build api shell over this class
class IsAlmostFreeOfRank (d : ℕ) : Prop where
  almost_free : Nonempty (AlmostFreeOfRankData m M d)
-- def AlmostFreeOfRank.ofMap
#check Submodule.span
-- π ∙ M
def AlmostFreeOfRank.ofQuotient (d : ℕ) (π : m) (f : AlmostFreeOfRankData (⊥ : Ideal (V⧸(V ∙ (π : V)))) (M ⧸ (Ideal.span {(π:V)} • (⊤ : Submodule V M) )) d) : AlmostFreeOfRankData m M d := sorry

-- A surjective to B with ker generate by π, scalar tower
variable (A B : Type*)

end Almost

section PerfectoidField

open Valued

class PerfectoidField (K : Type*) (p : ℕ) [Field K] [Valued K NNReal] [CompleteSpace K] where
  exists_p_mem_span_pow_p : ∃ π : 𝒪[K], ¬ IsUnit π ∧ (p : 𝒪[K]) ∈ Ideal.span {π ^ p}
  exist_p_th_root : ∀ x : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])}, ∃ y : 𝒪[K]⧸Ideal.span {(p : 𝒪[K])} , x = y ^ p
  
