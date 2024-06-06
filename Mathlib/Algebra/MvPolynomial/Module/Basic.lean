/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Finiteness

/-!
# Multivariate polynomial module

In this file, we define the multivariate polynomial module for an `R`-module `M`
with variables indexed by an arbitrary (possibly infinite) type `σ`.
Mathematicially this is the module $M[X_i : i \in σ]$ over $R[X_i : i \in σ]$.
See the docstring of `PolynomialModule` for details on why we want to keep this
type separate from `MvPolynomial`.

We also define, given an interpretation `T : σ → A` of our variables in a
commutative `R`-algebra `A` and an `A`-module `M`, an `MvPolynomial σ R`-module
`Module.MvAEval R M T`, which is a type synonym of `M` with the action of a
polynomial `f` given by `f • m = MvPolynomial.aeval T f • m`.
In particular `X i • m = T i • m`.
-/
universe u v
open Set Function MvPolynomial BigOperators

namespace Module
/--
Suppose `σ` is an indexing type, `T : σ → A` a `σ`-indexed family of elements
of an `R`-algebra `A` and `M` is an `A`-module. Loosely speaking,
`Module.MvAEval R M T` is the `MvPolynomial σ R`-module with elements `m : M`,
where the action of a polynomial $f$ is given by $f • m = f(X i ↦ T i) • m$.

More precisely, `Module.MvAEval R M T` has elements `Module.MvAEval.of R M T m`
for `m : M`, and the action of `f` is `f • of R M T m = of R M T (aeval T f • m)`.
-/
@[nolint unusedArguments]
def MvAEval (R M : Type*) {A σ : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M] (_ : σ → A) := M

instance MvAEval.instAddCommGroup {R A M σ} [CommSemiring R] [CommSemiring A]
    (T : σ → A) [Algebra R A] [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower R A M] : AddCommGroup <| MvAEval R M T :=
  inferInstanceAs (AddCommGroup M)

variable {R A M σ} [CommSemiring R] [CommSemiring A] (T : σ → A) [Algebra R A]
  [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]

namespace MvAEval

instance instAddCommMonoid : AddCommMonoid <| MvAEval R M T := inferInstanceAs (AddCommMonoid M)

instance instModuleOrig : Module R <| MvAEval R M T := inferInstanceAs (Module R M)

instance instFiniteOrig [Finite R M] : Finite R <| MvAEval R M T := inferInstanceAs (Finite R M)

instance instModulePolynomial : Module (MvPolynomial σ R) <| MvAEval R M T :=
  compHom M (aeval T).toRingHom

variable (R M)
/--
The canonical linear equivalence between `M` and `Module.MvAEval R M a` as an `R`-module.
-/
def of : M ≃ₗ[R] MvAEval R M T :=
  LinearEquiv.refl _ _

variable {R M}

lemma of_aeval_smul (f : MvPolynomial σ R) (m : M) :
    of R M T (aeval T f • m) = f • of R M T m := rfl

@[simp] lemma of_symm_smul (f : MvPolynomial σ R) (m : MvAEval R M T) :
    (of R M T).symm (f • m) = aeval T f • (of R M T).symm m := rfl

@[simp] lemma C_smul (c : R) (m : MvAEval R M T) :
    (C c : MvPolynomial σ R) • m = c • m :=
  (of R M T).symm.injective <| by simp

lemma X_smul_of (i : σ) (m : M) :
    (X i : MvPolynomial σ R) • (of R M T m) = of R M T (T i • m) := by
  rw [← of_aeval_smul, aeval_X]

lemma of_symm_X_smul (i : σ) (m : MvAEval R M T) :
    (of R M T).symm ((X i : MvPolynomial σ R) • m) = T i • (of R M T).symm m := by
  rw [of_symm_smul, aeval_X]

instance instIsScalarTowerOrigPolynomial :
    IsScalarTower R (MvPolynomial σ R) <| MvAEval R M T where
  smul_assoc r f m := by
    apply (of R M T).symm.injective
    rw [of_symm_smul, map_smul, smul_assoc, map_smul, of_symm_smul]

instance instFinitePolynomial [Finite R M] : Finite (MvPolynomial σ R) <| MvAEval R M T :=
  Finite.of_restrictScalars_finite R _ _

/-- Construct an `MvPolynomial σ R`-linear map out of `MvAEval R M T` from a
`R`-linear map out of `M`. -/
def _root_.LinearMap.ofMvAEval {N} [AddCommMonoid N] [Module R N]
    [Module (MvPolynomial σ R) N] [IsScalarTower R (MvPolynomial σ R) N]
    (f : M →ₗ[R] N) (hf : ∀ i m, f (T i • m) = (X i : MvPolynomial σ R) • f m) :
    MvAEval R M T →ₗ[MvPolynomial σ R] N where
  __ := f ∘ₗ (of R M T).symm
  map_smul' p m := by
    dsimp
    induction' p using induction_on generalizing m
    <;> simp only [← algebraMap_eq, AlgHom.commutes, algebraMap_smul,
      map_smul, map_add, add_smul, map_mul, aeval_X, mul_smul]
    · congr <;> apply_assumption
    · rw [← hf, ← of_symm_X_smul]; apply_assumption

lemma annihilator_eq_ker_aeval [FaithfulSMul A M] :
    annihilator (MvPolynomial σ R) (MvAEval R M T) = RingHom.ker (aeval T) := by
  ext p
  simp_rw [mem_annihilator, RingHom.mem_ker]
  conv_lhs => change ∀ m : M, aeval T p • m = 0; intro m; rw [← zero_smul A m]
  exact Iff.trans Function.funext_iff.symm smul_left_injective'.eq_iff

@[simp]
lemma annihilator_top_eq_ker_aeval [FaithfulSMul A M] :
    (⊤ : Submodule (MvPolynomial σ R) <| MvAEval R M T).annihilator =
      RingHom.ker (aeval T) :=
  Eq.trans (Submodule.annihilator_top) (annihilator_eq_ker_aeval T)

section Submodule

variable {p : Submodule R M} (hp : ∀ i, p ≤ p.comap (Algebra.lsmul R R M (T i)))
  {q : Submodule (MvPolynomial σ R) <| MvAEval R M T}

variable (R M) in
/-- We can turn an `MvPolynomial σ R`-submodule into an `R`-submodule by
forgetting the action of `X`. -/
def comapSubmodule :
    CompleteLatticeHom (Submodule (MvPolynomial σ R) <| MvAEval R M T) (Submodule R M) :=
  (Submodule.orderIsoMapComap (of R M T)).symm.toCompleteLatticeHom.comp <|
    Submodule.restrictScalarsLatticeHom R (MvPolynomial σ R) (MvAEval R M T)

@[simp] lemma mem_comapSubmodule {x : M} :
    x ∈ comapSubmodule R M T q ↔ of R M T x ∈ q :=
  Iff.rfl

@[simp] lemma comapSubmodule_le_comap (i : σ) :
    comapSubmodule R M T q ≤
      (comapSubmodule R M T q).comap (Algebra.lsmul R R M (T i)) := by
  intro m hm
  simpa only [Submodule.mem_comap, Algebra.lsmul_coe, mem_comapSubmodule,
    ← X_smul_of] using q.smul_mem (X i) hm

/-- An `R`-submodule which is stable under the actions of the `T i` can be
promoted to an `MvPolynomial σ R`-submodule. -/
def mapSubmodule : Submodule (MvPolynomial σ R) <| MvAEval R M T :=
  { toAddSubmonoid := p.toAddSubmonoid.map (of R M T)
    smul_mem' := by
      rintro f - ⟨m : M, h : m ∈ p, rfl⟩
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid]
      refine ⟨aeval T f • m, ?_, of_aeval_smul T f m⟩
      induction' f using induction_on with r f g hf hg f i ih generalizing m
      <;> simp only [aeval_C, aeval_X, algebraMap_smul,
        map_add, map_mul, add_smul, mul_smul]
      · exact p.smul_mem r h
      · exact p.add_mem (hf m h) (hg m h)
      · exact ih (T i • m) (hp i h) }

@[simp] lemma mem_mapSubmodule {m : MvAEval R M T} :
    m ∈ mapSubmodule T hp ↔ (of R M T).symm m ∈ p :=
  ⟨fun ⟨_, hm, hm'⟩ ↦ hm'.symm ▸ hm, fun hm ↦ ⟨(of R M T).symm m, hm, rfl⟩⟩

@[simp] lemma mapSubmodule_comapSubmodule (h := comapSubmodule_le_comap T) :
    mapSubmodule T (p := comapSubmodule R M T q) h = q := by
  ext; simp

@[simp] lemma comapSubmodule_mapSubmodule :
    comapSubmodule R M T (mapSubmodule T hp) = p := by
  ext; simp

variable (R M)

lemma injective_comapSubmodule : Injective (comapSubmodule R M T) := by
  intro q₁ q₂ hq
  rw [← mapSubmodule_comapSubmodule (q := q₁), ← mapSubmodule_comapSubmodule (q := q₂)]
  simp_rw [hq]

lemma range_comapSubmodule :
    range (comapSubmodule R M T) = {p | ∀ i, p ≤ p.comap (Algebra.lsmul R R M (T i))} :=
  le_antisymm (fun _ ⟨_, hq⟩ ↦ hq ▸ comapSubmodule_le_comap T)
    (fun _ hp ↦ ⟨mapSubmodule T hp, comapSubmodule_mapSubmodule T hp⟩)

end Submodule

end MvAEval

-- TODO: Provide a more complete API for `MvAEval'` mirroring `MvAEval`
section

def MvAEval'.auxRing (Φ : σ → M →ₗ[R] M) (_ : ∀ i j, Φ i ∘ₗ Φ j = Φ j ∘ₗ Φ i) :=
  Algebra.adjoin R (range Φ)

variable (Φ : σ → M →ₗ[R] M) (h : ∀ i j, Φ i ∘ₗ Φ j = Φ j ∘ₗ Φ i)

instance : CommSemiring (MvAEval'.auxRing Φ h) :=
  Algebra.adjoinCommSemiringOfComm R <| by
    simpa only [mem_range, forall_exists_index, forall_apply_eq_imp_iff]

/--
Given an `R`-module `M`, a family of linear maps `Φ : σ → M →ₗ[R] M`, and a
proof `h` that the maps in the family pairwise commute, `Module.MvAEval' Φ h`
is loosely speaking the `MvPolynomial σ R`-module with elements `m : M`, where
the action of a polynomial $f$ is given by $f • m = f(X i ↦ Φ i) • m$.
We can't define this directly in terms of `MvEval` and `Φ` like in the
univariate case, since `aeval` for multivariate polynomials only works for
commutative algebras (the univariate polynomial ring is the free algebra on one
generator, but the multivariate polynomial ring on `σ` is only the free
*commutative* algebra on `σ`). So we use `aeval` with `Φ` modified so that its
codomain is restricted to the `R`-subalgebra of `M →ₗ[R] M` generated by `Φ`.

`Module.MvAEval'` is defined as a special case of `Module.MvAEval` in which the
`R`-algebra is `Algebra.adjoin R (range Φ)`. We use a type synonym
`MvAEval'.auxRing Φ h` which includes the proof `h` so that a `CommSemiring`
instance may be defined. -/
abbrev MvAEval' := MvAEval R M (A := MvAEval'.auxRing Φ h) <|
  Subtype.coind Φ fun i => Algebra.subset_adjoin <| Set.mem_range_self i

namespace MvAEval'

/--
A more explicit version of `MvAEval.of`.
-/
abbrev of' : M ≃ₗ[R] MvAEval' Φ h := MvAEval.of R M _

variable {h}

/--
The canonical linear equivalence between `M` and `Module.MvAEval' h` as an `R`-module.
-/
abbrev of : M ≃ₗ[R] MvAEval' Φ h := of' Φ h

variable {Φ}

lemma X_smul_of (i : σ) (m : M) :
    (X i : MvPolynomial σ R) • (of Φ m : MvAEval' Φ h) = of Φ (Φ i m) :=
  letI := Fact.mk h; MvAEval.X_smul_of _ i m

lemma of_symm_X_smul (i : σ) (m : MvAEval' Φ h) :
    (of Φ).symm ((X i : MvPolynomial σ R) • m) = Φ i ((of Φ).symm m) :=
  letI := Fact.mk h; MvAEval.of_symm_X_smul _ i m

end MvAEval'

end

end Module

/-- The module of multivariate polynomials with coefficients in an `R`-module
`M` over the multivariable polynomial of `R`

We require all the module instances `Module S (MvPolynomialModule σ R M)` to factor
through `R` except `Module (MvPolynomial σ R) (MvPolynomialModule σ R M)`.
This is also the reason why `R` is included in the alias, or else there will be two
different instances of `Module (MvPolynomial σ R) (MvPolynomialModule σ (MvPolynomial σ R))`.
-/
@[nolint unusedArguments]
def MvPolynomialModule (σ R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M] :=
  (σ →₀ ℕ) →₀ M

noncomputable instance (σ R M : Type*) [CommSemiring R] [AddCommGroup M] [Module R M] :
    AddCommGroup (MvPolynomialModule σ R M) := Finsupp.instAddCommGroup

variable {σ} (R : Type*) {M} [DecidableEq σ] [CommSemiring R] [AddCommMonoid M] [Module R M]

instance : Inhabited (MvPolynomialModule σ R M) := Finsupp.instInhabited
noncomputable instance : AddCommMonoid (MvPolynomialModule σ R M) := Finsupp.instAddCommMonoid

namespace MvPolynomialModule

@[semireducible]
noncomputable instance polynomialModule :
    Module (MvPolynomial σ R) (MvPolynomialModule σ R M) :=
  inferInstanceAs <| Module (MvPolynomial σ R) <|
    Module.MvAEval' (fun i => Finsupp.lmapDomain M R fun f =>
                                f.update i (f i + 1)) <| by
      intros i j
      cases' Decidable.eq_or_ne i j with h h
      · subst h; simp only [comp_apply, Finsupp.update_idem]
      · simp_rw [← Finsupp.lmapDomain_comp, Function.comp_def,
          Finsupp.coe_update, update_apply, if_neg h, if_neg h.symm,
          Finsupp.update_comm _ h]

section

variable {S : Type*} [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M]

/-- This is required to have the `IsScalarTower S R M` instance to avoid diamonds. -/
@[nolint unusedArguments]
noncomputable instance : Module S (MvPolynomialModule σ R M) :=
  Finsupp.module (σ →₀ ℕ) M

instance (M : Type u) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower S R M] :
    IsScalarTower S R (MvPolynomialModule σ R M) :=
  Finsupp.isScalarTower _ _

instance isScalarTower' (M : Type u) [AddCommMonoid M] [Module R M]
    [Module S M] [IsScalarTower S R M] :
    IsScalarTower S (MvPolynomial σ R) (MvPolynomialModule σ R M) where
  smul_assoc x y z :=
    haveI : IsScalarTower R (MvPolynomial σ R) (MvPolynomialModule σ R M) :=
      Module.MvAEval.instIsScalarTowerOrigPolynomial (Subtype.coind _ _)
    by rw [← algebraMap_smul R x y, ← algebraMap_smul R x (y • z), smul_assoc]

end

/-- The monomial `m * x ^ i`, where `i` is a multi-index. This is defeq to
`Finsupp.lsingle`, and is redefined here so that it has the desired type signature. -/
noncomputable def monomial (i : σ →₀ ℕ) : M →ₗ[R] MvPolynomialModule σ R M :=
  Finsupp.lsingle i

/-- `C m` is the constant polynomial with value `m`. -/
noncomputable def C : M →ₗ[R] MvPolynomialModule σ R M := monomial R 0

variable {R}

theorem induction_linear {P : MvPolynomialModule σ R M → Prop}
    (f : MvPolynomialModule σ R M) (h0 : P 0)
    (hadd : ∀ f g, P f → P g → P (f + g))
    (hsingle : ∀ a b, P (monomial R a b)) : P f :=
  Finsupp.induction_linear f h0 hadd hsingle

/-- The finite set of all `a : σ →₀ ℕ` such that `X^a` has a non-zero coefficient. -/
def support (p : MvPolynomialModule σ R M) := Finsupp.support p

/-- The coefficient of the monomial `X^a` in the multi-variable polynomial `p`. -/
def coeff (a : σ →₀ ℕ) : MvPolynomialModule σ R M →ₗ[R] M :=
  Finsupp.lapply a

@[simp]
theorem mem_support_iff {p : MvPolynomialModule σ R M} {a : σ →₀ ℕ} :
    a ∈ p.support ↔ coeff a p ≠ 0 := by
  rw [support, Finsupp.mem_support_iff]; rfl

@[ext]
theorem ext (p q : MvPolynomialModule σ R M) : (∀ a, coeff a p = coeff a q) → p = q :=
  Finsupp.ext

theorem ext_iff (p q : MvPolynomialModule σ R M) : p = q ↔ ∀ m, coeff m p = coeff m q :=
  ⟨fun h m => congrArg (coeff m) h, ext p q⟩

theorem monomial_zero {s : σ →₀ ℕ} : monomial R s (0 : M) = 0 :=
  Finsupp.single_zero _

@[simp]
theorem monomial_zero' :
    (monomial R (0 : σ →₀ ℕ) : M → MvPolynomialModule σ R M) = C R :=
  rfl

@[simp]
theorem monomial_eq_zero {s : σ →₀ ℕ} {m : M} : monomial R s m = 0 ↔ m = 0 :=
  Finsupp.single_eq_zero

theorem monomial_single_add {e : ℕ} {i : σ} {a : σ →₀ ℕ} {m : M} :
    monomial R (Finsupp.single i e + a) m =
      (X i ^ e : MvPolynomial σ R) • monomial R a m := by
  induction' e with e ih
  · rw [pow_zero, one_smul, Finsupp.single_zero, zero_add]
  · rw [pow_succ', mul_smul, Nat.add_comm, Finsupp.single_add, add_assoc, ← ih]
    generalize Finsupp.single i e + a = b; clear ih e a
    refine Eq.trans ?_ (Module.MvAEval'.X_smul_of i _).symm
    change Finsupp.single _ _ = Finsupp.mapDomain _ (Finsupp.single _ _)
    simp_rw [Finsupp.mapDomain_single, Finsupp.update_eq_erase_add_single,
      Finsupp.single_add, ← add_assoc, Finsupp.erase_add_single, add_comm]

theorem X_pow_smul_C_eq_monomial {e : ℕ} {i : σ} {m : M} :
    (X i ^ e : MvPolynomial σ R) • C R m = monomial R (Finsupp.single i e) m := by
  rw [← monomial_zero', ← monomial_single_add, add_zero]

theorem X_smul_C_eq_monomial {i : σ} {m : M} :
    (X i : MvPolynomial σ R) • C R m = monomial R (Finsupp.single i 1) m := by
  rw [← X_pow_smul_C_eq_monomial, pow_one]

@[simp]
theorem monomial_smul_monomial (a : σ →₀ ℕ) (r : R) (b : σ →₀ ℕ) (m : M) :
    MvPolynomial.monomial a r • monomial R b m = monomial R (a + b) (r • m) := by
  conv_lhs => rw [← mul_one r]
  simp only [← smul_eq_mul, map_smul, smul_assoc]
  refine congrArg (r • ·) ?_
  induction' a using Finsupp.induction with _ _ _ _ _ ih
  · rw [MvPolynomial.monomial_zero', MvPolynomial.C_1, one_smul, zero_add]
  · rw [MvPolynomial.monomial_single_add, mul_smul, ih, add_assoc, monomial_single_add]

@[simp]
lemma monomial_smul_C (a : σ →₀ ℕ) (r : R) (m : M) :
    MvPolynomial.monomial a r • C R m = r • monomial R a m := by
  simp_rw [C, monomial_smul_monomial, add_zero, map_smul]

theorem monomial_eq {m : M} {a : σ →₀ ℕ} :
    monomial R a m = (a.prod fun n e => X n ^ e : MvPolynomial σ R) • C R m := by
  rw [← one_smul R (monomial R a m), ← monomial_smul_C,
    MvPolynomial.monomial_eq, C_1, one_mul]

-- Seems more reasonable to do `a.prod (X · ^ ·)` imo but this
-- is consistent with `prod_X_pow_eq_monomial`
@[simp]
lemma prod_X_pow_smul_eq_monomial (a : σ →₀ ℕ) (m : M) :
    (∏ i in a.support, X i ^ a i : MvPolynomial σ R) • C R m = monomial R a m :=
  monomial_eq.symm

@[simp]
theorem support_sum_monomial_coeff (p : MvPolynomialModule σ R M) :
    (∑ v in p.support, monomial R v (coeff v p)) = p :=
  Finsupp.sum_single p

theorem as_sum (p : MvPolynomialModule σ R M) :
    p = ∑ v in p.support, monomial R v (coeff v p) :=
  (support_sum_monomial_coeff p).symm

variable (σ R)

open Submodule in
lemma span_C_over_poly_eq_span_monomials_over_base (s : Set M) :
    restrictScalars R (span (MvPolynomial σ R) (C R '' s)) =
      ⨆ a : σ →₀ ℕ, map (monomial R a) (span R s) := by
  simp_rw [map_span]
  let K := ⨆ a : σ →₀ ℕ, span R (monomial R a '' s)
  let N := span (MvPolynomial σ R) ((C R : M → MvPolynomialModule σ R M) '' s)
  have H (f : MvPolynomial σ R) : K ≤ comap (Module.toModuleEnd R _ f) K := by
    simp_rw [K, ← map_le_iff_le_comap, Submodule.map_iSup, iSup_le_iff, ← map_span]
    intro a
    induction' f using MvPolynomial.induction_on' with b r _ _ H₁ H₂
    · refine le_iSup_of_le (b + a) ?_
      refine le_trans (le_of_eq ?_) (smul_le_self_of_tower r _)
      refine Eq.trans (map_comp _ _ _).symm <| Eq.trans ?_ (map_comp _ _ _)
      congr 1; ext : 1
      exact Eq.trans (monomial_smul_monomial _ _ _ _) (map_smul _ r _)
    · rw [map_add]
      exact le_trans (Submodule.map_add_le _ _ _) (sup_le H₁ H₂)
  refine le_antisymm (?_ : N ≤ ⟨K.toAddSubmonoid, H⟩) ?_
  · exact span_le.mpr (fun _ h => mem_iSup_of_mem 0 (subset_span h))
  · refine iSup_le fun a => span_le.mpr (image_subset_iff.mpr ?_)
    intro m h
    refine (congrArg (· ∈ span _ _) monomial_eq).mpr ?_
    exact smul_mem _ _ (subset_span (mem_image_of_mem _ h))

variable (M)

lemma top_eq_span_base_monomials :
    (⊤ : Submodule R (MvPolynomialModule σ R M)) =
      ⨆ a : σ →₀ ℕ, LinearMap.range (monomial R a) := by
  conv => enter [2, 1, a]; rw [LinearMap.range_eq_map, ← Submodule.span_univ]
  refine Eq.trans ?_ (span_C_over_poly_eq_span_monomials_over_base σ R _)
  rw [image_univ, eq_comm, Submodule.eq_top_iff']
  intro x
  induction' x using induction_linear with _ _ h₁ h₂
  · exact zero_mem _
  · exact add_mem h₁ h₂
  · rw [monomial_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self _))

variable {σ R M}

@[simp]
theorem coeff_C (a : σ →₀ ℕ) (m : M) :
    coeff a (C R m) = if 0 = a then m else 0 :=
  Finsupp.single_apply

@[simp]
theorem coeff_zero_C (m : M) : coeff (0 : σ →₀ ℕ) (C R m) = m :=
  Finsupp.single_eq_same

@[simp]
theorem coeff_monomial (a b : σ →₀ ℕ) (m : M) :
    coeff a (monomial R b m) = if b = a then m else 0 :=
  Finsupp.single_apply

@[simp]
theorem coeff_monomial_smul (a : σ →₀ ℕ) (r : R) (g : MvPolynomialModule σ R M) (b : σ →₀ ℕ) :
    coeff a (MvPolynomial.monomial b r • g) =
      if b ≤ a then r • coeff (a - b) g else 0 := by
  induction' g using MvPolynomialModule.induction_linear with p q hp hq
  · simp only [smul_zero, map_zero, ite_self]
  · simp only [smul_add, map_add, hp, hq]
    split_ifs
    exacts [rfl, zero_add 0]
  · rw [monomial_smul_monomial, coeff_monomial, coeff_monomial, smul_ite, smul_zero, ← ite_and]
    congr
    rw [eq_iff_iff]
    constructor
    · rintro rfl
      simp
    · rintro ⟨e, rfl⟩
      rw [add_comm, tsub_add_cancel_of_le e]

@[simp]
theorem coeff_smul_monomial (a : σ →₀ ℕ) (f : MvPolynomial σ R) (m : M) (b : σ →₀ ℕ) :
    coeff a (f • monomial R b m) = if b ≤ a then f.coeff (a - b) • m else 0 := by
  induction' f using MvPolynomial.induction_on' with p r p q hp hq
  · split_ifs with h
    <;> simp only [monomial_smul_monomial, coeff_monomial,
      MvPolynomial.coeff_monomial, ite_smul, zero_smul, smul_ite,
      eq_tsub_iff_add_eq_of_le, h, smul_zero, map_smul, ite_eq_right_iff]
    exact (mt (le_of_le_of_eq (self_le_add_left b p)) h).elim
  · rw [add_smul, map_add, hp, hq, coeff_add, add_smul]
    split_ifs
    exacts [rfl, zero_add 0]

theorem coeff_smul (f : MvPolynomial σ R) (g : MvPolynomialModule σ R M) (a : σ →₀ ℕ) :
    coeff a (f • g) = ∑ x in Finset.antidiagonal a, f.coeff x.1 • coeff x.2 g := by
  induction' f using MvPolynomial.induction_on' with b r p q hp hq
  · simp_rw [MvPolynomial.coeff_monomial, ite_smul, zero_smul]
    conv => enter [2, 2, x]; exact if_congr eq_comm rfl rfl
    rw [coeff_monomial_smul, ← Finset.sum_filter,
      Finset.filter_fst_eq_antidiagonal a b, apply_ite (Finset.sum · _),
      Finset.sum_singleton, Finset.sum_empty]
  · simp only [add_smul, map_add, hp, hq, ← Finset.sum_add_distrib, coeff_add]

open Classical in
theorem support_monomial {a : σ →₀ ℕ} {m : M} :
    (monomial R a m).support = if m = 0 then ∅ else {a} := rfl

theorem support_monomial_subset {a : σ →₀ ℕ} {m : M} :
    (monomial R a m).support ⊆ {a} := Finsupp.support_single_subset

theorem support_add {p q : MvPolynomialModule σ R M} :
    (p + q).support ⊆ p.support ∪ q.support := Finsupp.support_add

@[simp]
theorem support_zero : (0 : MvPolynomialModule σ R M).support = ∅ := rfl

theorem support_sum {α} {s : Finset α} {f : α → MvPolynomialModule σ R M} :
    (∑ x in s, f x).support ⊆ s.biUnion fun x => (f x).support :=
  Finsupp.support_finset_sum

/-- `MvPolynomialModule σ R R` is isomorphic to `MvPolynomial σ R` as an
`MvPolynomial σ R`-module. -/
def equivPolynomialSelf :
    MvPolynomialModule σ R R ≃ₗ[MvPolynomial σ R] MvPolynomial σ R where
  __ := AddEquiv.refl ((σ →₀ ℕ) →₀ R)
  map_smul' f x := by
    dsimp
    induction' x using induction_linear with _ _ hp hq a r
    · rw [smul_zero, mul_zero]
    · rw [smul_add, mul_add, hp, hq]
    · ext b
      change coeff b (f • monomial R a r) = _
      rw [coeff_smul_monomial, smul_eq_mul, monomial, ← MvPolynomial.monomial]
      exact Eq.symm <| MvPolynomial.coeff_mul_monomial' b a r f

/-- `MvPolynomialModule σ R S` is isomorphic to `MvPolynomialModule σ S` as an `R`-module. -/
noncomputable def equivPolynomial {S : Type*} [CommSemiring S] [Algebra R S] :
    MvPolynomialModule σ R S ≃ₗ[R] MvPolynomial σ S :=
  { AddEquiv.refl _ with map_smul' := fun _ _ => rfl }

variable (R' : Type*) {M' : Type*} [CommSemiring R'] [AddCommMonoid M']
    [Module R' M'] [Algebra R R'] [Module R M'] [IsScalarTower R R' M']

-- This should probably be bilinear in `f`
/-- The image of a polynomial under a linear map. -/
noncomputable def map (f : M →ₗ[R] M') :
    MvPolynomialModule σ R M →ₗ[R] MvPolynomialModule σ R' M' :=
  Finsupp.mapRange.linearMap f

@[simp]
theorem map_monomial (f : M →ₗ[R] M') (a : σ →₀ ℕ) (m : M) :
    map R' f (monomial R a m) = monomial R' a (f m) :=
  Finsupp.mapRange_single (hf := f.map_zero)

theorem map_smul (f : M →ₗ[R] M') (p : MvPolynomial σ R)
    (q : MvPolynomialModule σ R M) :
    map R' f (p • q) = MvPolynomial.map (algebraMap R R') p • map R' f q := by
  apply induction_linear q
  · rw [smul_zero, map_zero, smul_zero]
  · intro f g e₁ e₂
    rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  · intro i m
    induction' p using MvPolynomial.induction_on' with _ _ _ _ e₁ e₂
    · simp only [monomial_smul_monomial, map_monomial, f.map_smul,
        MvPolynomial.map_monomial, algebraMap_smul]
    · rw [add_smul, map_add, e₁, e₂, map_add, add_smul]

variable {R'}

-- Should this have `R` as an explicit argument?
-- Or should it be called `aeval` and `eval` is a special case?
/-- Evaluate a polynomial `p : PolynomialModule R M` at `r : R`. -/
@[simps! (config := .lemmasOnly)]
def eval (T : σ → R') : MvPolynomialModule σ R M' →ₗ[R'] M' where
  toFun p := ∑ a in p.support, (∏ i in a.support, T i ^ a i) • coeff a p
  map_add' _ _ := by
    refine Finsupp.sum_add_index' ?_ ?_ <;> intros
    <;> simp only [smul_zero, Finsupp.sum_zero, smul_add, Finsupp.sum_add]
  map_smul' r p := by
    refine (Finsupp.sum_smul_index' (fun _ => smul_zero _)).trans ?_
    simp_rw [Finset.smul_sum, ← smul_comm r]; rfl

open MvPolynomial renaming eval → eval', monomial → monomial' in
lemma eval_apply' (T : σ → R') (p : MvPolynomialModule σ R M') :
    eval T p = ∑ a in p.support, eval' T (monomial' a 1) • coeff a p := by
  simp_rw [eval_apply, eval_monomial, one_mul]; rfl

@[simp]
theorem eval_monomial (T : σ → R') (a : σ →₀ ℕ) (m : M') :
    eval T (monomial R a m) = (∏ i in a.support, T i ^ a i) • m := by
  refine Finsupp.sum_single_index ?_
  simp only [smul_zero, Finsupp.sum_zero]

@[simp]
lemma eval_C (T : σ → R') (m : M') : eval T (C R m) = m := by
  rw [C, eval_monomial, Finsupp.support_zero, Finset.prod_empty, one_smul]

theorem eval_smul (p : MvPolynomial σ R) (q : MvPolynomialModule σ R M)
    (T : σ → R) : eval T (p • q) = MvPolynomial.eval T p • eval T q := by
  induction' q using induction_linear with f g e₁ e₂ i m
  · rw [smul_zero, map_zero, smul_zero]
  · rw [smul_add, map_add, e₁, e₂, map_add, smul_add]
  · induction' p using MvPolynomial.induction_on' with _ _ _ _ e₁ e₂
    · rw [monomial_smul_monomial, eval_monomial, MvPolynomial.eval_monomial,
        eval_monomial, smul_comm, ← Finsupp.prod, Finsupp.prod_add_index',
        mul_smul, mul_smul, ← Finsupp.prod]
      · exact fun _ => pow_zero _
      · exact fun _ => pow_add _
    · rw [add_smul, map_add, MvPolynomial.eval_add, e₁, e₂, add_smul]

@[simp]
theorem eval_map (f : M →ₗ[R] M') (q : MvPolynomialModule σ R M) (T : σ → R) :
    eval (algebraMap R R' ∘ T) (map R' f q) = f (eval T q) := by
  induction' q using induction_linear with _ _ e₁ e₂
  <;> simp only [map_zero, map_add, map_monomial, eval_monomial, f.map_smul,
    comp_apply, ← map_pow, ← map_prod, algebraMap_smul]
  rw [e₁, e₂]

@[simp]
theorem eval_map' (f : M →ₗ[R] M) (q : MvPolynomialModule σ R M) (T : σ → R) :
    eval T (map R f q) = f (eval T q) :=
  eval_map f q T

variable {τ} [DecidableEq τ]

/-- `comp P q` is the plethystic action of a family
`P (i : σ) : MvPolynomial τ R` on `q : MvPolynomialModule σ R M` as `q(X i ↦ P i)`.
See `MvPolynomial.bind₁` -/
@[simps!]
noncomputable def comp (P : σ → MvPolynomial τ R) :
    MvPolynomialModule σ R M →ₗ[R] MvPolynomialModule τ R M :=
  (eval P).restrictScalars R ∘ₗ map (MvPolynomial τ R) (C R)

theorem comp_monomial (P : σ → MvPolynomial τ R) (a : σ →₀ ℕ) (m : M) :
    comp P (monomial R a m) =
      (∏ i in a.support, P i ^ a i : MvPolynomial τ R) • C R m := by
  rw [comp_apply, map_monomial, eval_monomial]

theorem comp_eval (P : σ → MvPolynomial τ R) (q : MvPolynomialModule σ R M)
    (T : τ → R) : eval T (comp P q) = eval (MvPolynomial.eval T ∘ P) q := by
  induction' q using induction_linear
  <;> simp only [map_zero, map_add, comp_apply, map_monomial, eval_monomial,
    eval_smul, map_prod, map_pow, eval_C, Function.comp_apply]
  congr

theorem comp_smul (P : σ → MvPolynomial τ R) (p' : MvPolynomial σ R)
    (q : MvPolynomialModule σ R M) :
    comp P (p' • q) = MvPolynomial.bind₁ P p' • comp P q := by
  rw [comp_apply, map_smul, eval_smul, MvPolynomial.bind₁, aeval_def,
    MvPolynomial.eval_map, comp_apply]

end MvPolynomialModule
