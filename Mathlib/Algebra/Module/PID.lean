/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathlib.Algebra.Module.DedekindDomain
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.Biproducts

#align_import algebra.module.pid from "leanprover-community/mathlib"@"cdc34484a07418af43daf8198beaf5c00324bca8"

/-!
# Structure of finitely generated modules over a PID

## Main statements

* `Module.equiv_directSum_of_isTorsion` : A finitely generated torsion module over a PID is
  isomorphic to a direct sum of some `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
* `Module.equiv_free_prod_directSum` : A finitely generated module over a PID is isomorphic to the
  product of a free module (its torsion free part) and a direct sum of the form above (its torsion
  submodule).

## Notation

* `R` is a PID and `M` is a (finitely generated for main statements) `R`-module, with additional
  torsion hypotheses in the intermediate lemmas.
* `N` is an `R`-module lying over a higher type universe than `R`. This assumption is needed on the
  final statement for technical reasons.
* `p` is an irreducible element of `R` or a tuple of these.

## Implementation details

We first prove (`Submodule.isInternal_prime_power_torsion_of_pid`) that a finitely generated
torsion module is the internal direct sum of its `p i ^ e i`-torsion submodules for some
(finitely many) prime powers `p i ^ e i`. This is proved in more generality for a Dedekind domain
at `Submodule.isInternal_prime_power_torsion`.

Then we treat the case of a `p ^ ∞`-torsion module (that is, a module where all elements are
cancelled by scalar multiplication by some power of `p`) and apply it to the `p i ^ e i`-torsion
submodules (that are `p i ^ ∞`-torsion) to get the result for torsion modules.

Then we get the general result using that a torsion free module is free (which has been proved at
`Module.free_of_finite_type_torsion_free'` at `LinearAlgebra.FreeModule.PID`.)

## Tags

Finitely generated module, principal ideal domain, classification, structure theorem
-/


universe u v

open scoped BigOperators Classical

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

variable {M : Type v} [AddCommGroup M] [Module R M]

variable {N : Type max u v} [AddCommGroup N] [Module R N]

open scoped DirectSum

open Submodule

open UniqueFactorizationMonoid

/-- A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`.-/
theorem Submodule.isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBy R M
        (IsPrincipal.generator (p : Ideal R) ^
          (factors (⊤ : Submodule R M).annihilator).count ↑p) := by
  convert isInternal_prime_power_torsion hM
  -- ⊢ torsionBy R M (IsPrincipal.generator ↑x✝ ^ Multiset.count (↑x✝) (factors (an …
  ext p : 1
  -- ⊢ p ∈ torsionBy R M (IsPrincipal.generator ↑x✝ ^ Multiset.count (↑x✝) (factors …
  rw [← torsionBySet_span_singleton_eq, Ideal.submodule_span_eq, ← Ideal.span_singleton_pow,
    Ideal.span_singleton_generator]
#align submodule.is_internal_prime_power_torsion_of_pid Submodule.isInternal_prime_power_torsion_of_pid

/-- A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`.-/
theorem Submodule.exists_isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i)
        (e : ι → ℕ), DirectSum.IsInternal fun i => torsionBy R M <| p i ^ e i := by
  refine' ⟨_, _, _, _, _, _, Submodule.isInternal_prime_power_torsion_of_pid hM⟩
  -- ⊢ Fintype { x // x ∈ Multiset.toFinset (factors (annihilator ⊤)) }
  exact Finset.fintypeCoeSort _
  -- ⊢ ∀ (i : { x // x ∈ Multiset.toFinset (factors (annihilator ⊤)) }), Irreducibl …
  · rintro ⟨p, hp⟩
    -- ⊢ Irreducible (IsPrincipal.generator ↑{ val := p, property := hp })
    have hP := prime_of_factor p (Multiset.mem_toFinset.mp hp)
    -- ⊢ Irreducible (IsPrincipal.generator ↑{ val := p, property := hp })
    haveI := Ideal.isPrime_of_prime hP
    -- ⊢ Irreducible (IsPrincipal.generator ↑{ val := p, property := hp })
    exact (IsPrincipal.prime_generator_of_isPrime p hP.ne_zero).irreducible
    -- 🎉 no goals
#align submodule.exists_is_internal_prime_power_torsion_of_pid Submodule.exists_isInternal_prime_power_torsion_of_pid

namespace Module

section PTorsion

variable {p : R} (hp : Irreducible p) (hM : Module.IsTorsion' M (Submonoid.powers p))

variable [dec : ∀ x : M, Decidable (x = 0)]

open Ideal Submodule.IsPrincipal

theorem _root_.Ideal.torsionOf_eq_span_pow_pOrder (x : M) :
    torsionOf R M x = span {p ^ pOrder hM x} := by
  dsimp only [pOrder]
  -- ⊢ torsionOf R M x = Ideal.span {p ^ Nat.find (_ : ∃ n, p ^ n • x = 0)}
  rw [← (torsionOf R M x).span_singleton_generator, Ideal.span_singleton_eq_span_singleton, ←
    Associates.mk_eq_mk_iff_associated, Associates.mk_pow]
  have prop :
    (fun n : ℕ => p ^ n • x = 0) = fun n : ℕ =>
      (Associates.mk <| generator <| torsionOf R M x) ∣ Associates.mk p ^ n :=
    by ext n; rw [← Associates.mk_pow, Associates.mk_dvd_mk, ← mem_iff_generator_dvd]; rfl
  have := (isTorsion'_powers_iff p).mp hM x; rw [prop] at this
  -- ⊢ Associates.mk (generator (torsionOf R M x)) = Associates.mk p ^ Nat.find (_  …
                                             -- ⊢ Associates.mk (generator (torsionOf R M x)) = Associates.mk p ^ Nat.find (_  …
  classical
  convert
    Associates.eq_pow_find_of_dvd_irreducible_pow ((Associates.irreducible_mk p).mpr hp)
      this.choose_spec
#align ideal.torsion_of_eq_span_pow_p_order Ideal.torsionOf_eq_span_pow_pOrder

theorem p_pow_smul_lift {x y : M} {k : ℕ} (hM' : Module.IsTorsionBy R M (p ^ pOrder hM y))
    (h : p ^ k • x ∈ R ∙ y) : ∃ a : R, p ^ k • x = p ^ k • a • y := by
  -- Porting note: needed to make `smul_smul` work below.
  letI : MulAction R M := MulActionWithZero.toMulAction
  -- ⊢ ∃ a, p ^ k • x = p ^ k • a • y
  by_cases hk : k ≤ pOrder hM y
  -- ⊢ ∃ a, p ^ k • x = p ^ k • a • y
  · let f :=
      ((R ∙ p ^ (pOrder hM y - k) * p ^ k).quotEquivOfEq _ ?_).trans
        (quotTorsionOfEquivSpanSingleton R M y)
    have : f.symm ⟨p ^ k • x, h⟩ ∈
        R ∙ Ideal.Quotient.mk (R ∙ p ^ (pOrder hM y - k) * p ^ k) (p ^ k) := by
      rw [← Quotient.torsionBy_eq_span_singleton, mem_torsionBy_iff, ← f.symm.map_smul]
      convert f.symm.map_zero; ext
      rw [coe_smul_of_tower, coe_mk, coe_zero, smul_smul, ← pow_add, Nat.sub_add_cancel hk, @hM' x]
      · exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hp.ne_zero)
    rw [Submodule.mem_span_singleton] at this; obtain ⟨a, ha⟩ := this; use a
    -- ⊢ ∃ a, p ^ k • x = p ^ k • a • y
                                               -- ⊢ ∃ a, p ^ k • x = p ^ k • a • y
                                                                       -- ⊢ p ^ k • x = p ^ k • a • y
    rw [f.eq_symm_apply, ← Ideal.Quotient.mk_eq_mk, ← Quotient.mk_smul] at ha
    -- ⊢ p ^ k • x = p ^ k • a • y
    dsimp only [smul_eq_mul, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      quotTorsionOfEquivSpanSingleton_apply_mk] at ha
    rw [smul_smul, mul_comm]; exact congr_arg ((↑) : _ → M) ha.symm
    -- ⊢ p ^ k • x = (a * p ^ k) • y
                              -- ⊢ Submodule.span R {p ^ (pOrder hM y - k) * p ^ k} = torsionOf R M y
    · symm; convert Ideal.torsionOf_eq_span_pow_pOrder hp hM y
      -- ⊢ torsionOf R M y = Submodule.span R {p ^ (pOrder hM y - k) * p ^ k}
            -- ⊢ p ^ (pOrder hM y - k) * p ^ k = p ^ pOrder hM y
      rw [← pow_add, Nat.sub_add_cancel hk]
      -- 🎉 no goals
  · use 0
    -- ⊢ p ^ k • x = p ^ k • 0 • y
    rw [zero_smul, smul_zero, ← Nat.sub_add_cancel (le_of_not_le hk), pow_add, mul_smul, hM',
      smul_zero]
#align module.p_pow_smul_lift Module.p_pow_smul_lift

open Submodule.Quotient

theorem exists_smul_eq_zero_and_mk_eq {z : M} (hz : Module.IsTorsionBy R M (p ^ pOrder hM z))
    {k : ℕ} (f : (R ⧸ R ∙ p ^ k) →ₗ[R] M ⧸ R ∙ z) :
    ∃ x : M, p ^ k • x = 0 ∧ Submodule.Quotient.mk (p := span R {z}) x = f 1 := by
  have f1 := mk_surjective (R ∙ z) (f 1)
  -- ⊢ ∃ x, p ^ k • x = 0 ∧ Submodule.Quotient.mk x = ↑f 1
  have : p ^ k • f1.choose ∈ R ∙ z := by
    rw [← Quotient.mk_eq_zero, mk_smul, f1.choose_spec, ← f.map_smul]
    convert f.map_zero; change _ • Submodule.Quotient.mk _ = _
    rw [← mk_smul, Quotient.mk_eq_zero, Algebra.id.smul_eq_mul, mul_one]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := p_pow_smul_lift hp hM hz this
  -- ⊢ ∃ x, p ^ k • x = 0 ∧ Submodule.Quotient.mk x = ↑f 1
  refine' ⟨f1.choose - a • z, by rw [smul_sub, sub_eq_zero, ha], _⟩
  -- ⊢ Submodule.Quotient.mk (Exists.choose f1 - a • z) = ↑f 1
  rw [mk_sub, mk_smul, (Quotient.mk_eq_zero _).mpr <| Submodule.mem_span_singleton_self _,
    smul_zero, sub_zero, f1.choose_spec]
#align module.exists_smul_eq_zero_and_mk_eq Module.exists_smul_eq_zero_and_mk_eq

open Finset Multiset

set_option maxHeartbeats 800000 in
/-- A finitely generated `p ^ ∞`-torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p ^ e i)` for some `e i`.-/
theorem torsion_by_prime_power_decomposition (hN : Module.IsTorsion' N (Submonoid.powers p))
    [h' : Module.Finite R N] :
    ∃ (d : ℕ) (k : Fin d → ℕ), Nonempty <| N ≃ₗ[R] ⨁ i : Fin d, R ⧸ R ∙ p ^ (k i : ℕ) := by
  obtain ⟨d, s, hs⟩ := @Module.Finite.exists_fin _ _ _ _ _ h'; use d; clear h'
  -- ⊢ ∃ d k, Nonempty (N ≃ₗ[R] ⨁ (i : Fin d), R ⧸ Submodule.span R {p ^ k i})
                                                               -- ⊢ ∃ k, Nonempty (N ≃ₗ[R] ⨁ (i : Fin d), R ⧸ Submodule.span R {p ^ k i})
                                                                      -- ⊢ ∃ k, Nonempty (N ≃ₗ[R] ⨁ (i : Fin d), R ⧸ Submodule.span R {p ^ k i})
  induction' d with d IH generalizing N
  -- ⊢ ∃ k, Nonempty (N ≃ₗ[R] ⨁ (i : Fin Nat.zero), R ⧸ Submodule.span R {p ^ k i})
  · simp only [Nat.zero_eq] at *
    -- ⊢ ∃ k, Nonempty (N ≃ₗ[R] ⨁ (i : Fin Nat.zero), R ⧸ Submodule.span R {p ^ k i})
    -- Porting note: was `use fun i => finZeroElim i`
    use finZeroElim
    -- ⊢ Nonempty (N ≃ₗ[R] ⨁ (i : Fin Nat.zero), R ⧸ Submodule.span R {p ^ finZeroEli …
    rw [Set.range_eq_empty, Submodule.span_empty] at hs
    -- ⊢ Nonempty (N ≃ₗ[R] ⨁ (i : Fin Nat.zero), R ⧸ Submodule.span R {p ^ finZeroEli …
    haveI : Unique N :=
      ⟨⟨0⟩, fun x => by dsimp; rw [← Submodule.mem_bot R, hs]; exact Submodule.mem_top⟩
    haveI : IsEmpty (Fin Nat.zero) := inferInstanceAs (IsEmpty (Fin 0))
    -- ⊢ Nonempty (N ≃ₗ[R] ⨁ (i : Fin Nat.zero), R ⧸ Submodule.span R {p ^ finZeroEli …
    exact ⟨0⟩
    -- 🎉 no goals
  · have : ∀ x : N, Decidable (x = 0) := fun _ => by classical infer_instance
    -- ⊢ ∃ k, Nonempty (N ≃ₗ[R] ⨁ (i : Fin (Nat.succ d)), R ⧸ Submodule.span R {p ^ k …
    obtain ⟨j, hj⟩ := exists_isTorsionBy hN d.succ d.succ_ne_zero s hs
    -- ⊢ ∃ k, Nonempty (N ≃ₗ[R] ⨁ (i : Fin (Nat.succ d)), R ⧸ Submodule.span R {p ^ k …
    let s' : Fin d → N ⧸ R ∙ s j := Submodule.Quotient.mk ∘ s ∘ j.succAbove
    -- ⊢ ∃ k, Nonempty (N ≃ₗ[R] ⨁ (i : Fin (Nat.succ d)), R ⧸ Submodule.span R {p ^ k …
    -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5732):
    -- `obtain` doesn't work with placeholders.
    have := IH ?_ s' ?_
    obtain ⟨k, ⟨f⟩⟩ := this
    clear IH
    · have : ∀ i : Fin d,
          ∃ x : N, p ^ k i • x = 0 ∧ f (Submodule.Quotient.mk x) = DirectSum.lof R _ _ i 1 := by
        intro i
        let fi := f.symm.toLinearMap.comp (DirectSum.lof _ _ _ i)
        obtain ⟨x, h0, h1⟩ := exists_smul_eq_zero_and_mk_eq hp hN hj fi; refine' ⟨x, h0, _⟩; rw [h1]
        simp only [LinearMap.coe_comp, f.symm.coe_toLinearMap, f.apply_symm_apply,
          Function.comp_apply]
      refine ⟨?_, ⟨?_⟩⟩
      -- ⊢ Fin (Nat.succ d) → ℕ
      · exact fun a => (fun i => (Option.rec (pOrder hN (s j)) k i : ℕ)) (finSuccEquiv d a)
        -- 🎉 no goals
      · refine (((@lequivProdOfRightSplitExact _ _ _ _ _ _ _ _ _ _ _ _
          ((f.trans ULift.moduleEquiv.{u, u, v}.symm).toLinearMap.comp <| mkQ _)
          ((DirectSum.toModule _ _ _ fun i => (liftQSpanSingleton (p ^ k i)
              (LinearMap.toSpanSingleton _ _ _) (this i).choose_spec.left : R ⧸ _ →ₗ[R] _)).comp
            ULift.moduleEquiv.toLinearMap) (R ∙ s j).injective_subtype ?_ ?_).symm.trans
          (((quotTorsionOfEquivSpanSingleton R N (s j)).symm.trans
          (quotEquivOfEq (torsionOf R N (s j)) _
          (Ideal.torsionOf_eq_span_pow_pOrder hp hN (s j)))).prod
          (ULift.moduleEquiv))).trans
          (@DirectSum.lequivProdDirectSum R _ _ _
          (fun i => R ⧸ R ∙ p ^ @Option.rec _ (fun _ => ℕ) (pOrder hN <| s j) k i) _ _).symm).trans
          (DirectSum.lequivCongrLeft R (finSuccEquiv d).symm)
        · rw [range_subtype, LinearEquiv.ker_comp, ker_mkQ]
          -- 🎉 no goals
        · rw [← f.comp_coe, LinearMap.comp_assoc, LinearMap.comp_assoc,
            LinearEquiv.toLinearMap_symm_comp_eq, LinearMap.comp_id, ← LinearMap.comp_assoc,
            ← LinearMap.comp_assoc]
          suffices (f.toLinearMap.comp (R ∙ s j).mkQ).comp _ = LinearMap.id by
            rw [this, LinearMap.id_comp]
          ext i : 3
          -- ⊢ ↑(LinearMap.comp (LinearMap.comp (LinearMap.comp (LinearMap.comp (↑f) (mkQ ( …
          simp only [LinearMap.coe_comp, Function.comp_apply, mkQ_apply]
          -- ⊢ ↑↑f (Submodule.Quotient.mk (↑(DirectSum.toModule R (Fin d) N fun i => liftQS …
          rw [LinearEquiv.coe_toLinearMap, LinearMap.id_apply, DirectSum.toModule_lof,
            liftQSpanSingleton_apply, LinearMap.toSpanSingleton_one, Ideal.Quotient.mk_eq_mk,
            map_one, (this i).choose_spec.right]
    · exact (mk_surjective _).forall.mpr fun x =>
        ⟨(@hN x).choose, by rw [← Quotient.mk_smul, (@hN x).choose_spec, Quotient.mk_zero]⟩
    · have hs' := congr_arg (Submodule.map <| mkQ <| R ∙ s j) hs
      -- ⊢ Submodule.span R (Set.range s') = ⊤
      rw [Submodule.map_span, Submodule.map_top, range_mkQ] at hs'; simp only [mkQ_apply] at hs'
      -- ⊢ Submodule.span R (Set.range s') = ⊤
                                                                    -- ⊢ Submodule.span R (Set.range s') = ⊤
      simp only; rw [← Function.comp.assoc, Set.range_comp (_ ∘ s), Fin.range_succAbove]
      -- ⊢ Submodule.span R (Set.range (Submodule.Quotient.mk ∘ s ∘ Fin.succAbove j)) = ⊤
                 -- ⊢ Submodule.span R (Submodule.Quotient.mk ∘ s '' {j}ᶜ) = ⊤
      rw [← Set.range_comp, ← Set.insert_image_compl_eq_range _ j, Function.comp_apply,
        (Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _), span_insert_zero] at hs'
      exact hs'
      -- 🎉 no goals
#align module.torsion_by_prime_power_decomposition Module.torsion_by_prime_power_decomposition

end PTorsion

/-- A finitely generated torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.-/
theorem equiv_directSum_of_isTorsion [h' : Module.Finite R N] (hN : Module.IsTorsion R N) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| N ≃ₗ[R] ⨁ i : ι, R ⧸ R ∙ p i ^ e i := by
  obtain ⟨I, fI, _, p, hp, e, h⟩ := Submodule.exists_isInternal_prime_power_torsion_of_pid hN
  -- ⊢ ∃ ι x p x e, Nonempty (N ≃ₗ[R] ⨁ (i : ι), R ⧸ span R {p i ^ e i})
  haveI := fI
  -- ⊢ ∃ ι x p x e, Nonempty (N ≃ₗ[R] ⨁ (i : ι), R ⧸ span R {p i ^ e i})
  have :
    ∀ i,
      ∃ (d : ℕ) (k : Fin d → ℕ),
        Nonempty <| torsionBy R N (p i ^ e i) ≃ₗ[R] ⨁ j, R ⧸ R ∙ p i ^ k j := by
    have := isNoetherian_of_isNoetherianRing_of_finite R N
    haveI := fun i => isNoetherian_submodule' (torsionBy R N <| p i ^ e i)
    exact fun i =>
      torsion_by_prime_power_decomposition.{u, v} (hp i)
        ((isTorsion'_powers_iff <| p i).mpr fun x => ⟨e i, smul_torsionBy _ _⟩)
  classical
  refine'
    ⟨Σ i, Fin (this i).choose, inferInstance, fun ⟨i, _⟩ => p i, fun ⟨i, _⟩ => hp i, fun ⟨i, j⟩ =>
      (this i).choose_spec.choose j,
      ⟨(LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h).symm.trans <|
          (DFinsupp.mapRange.linearEquiv fun i => (this i).choose_spec.choose_spec.some).trans <|
            (DirectSum.sigmaLcurryEquiv R).symm.trans
              (DFinsupp.mapRange.linearEquiv fun i => quotEquivOfEq _ _ _)⟩⟩
  cases' i with i j
  simp only
#align module.equiv_direct_sum_of_is_torsion Module.equiv_directSum_of_isTorsion

/-- **Structure theorem of finitely generated modules over a PID** : A finitely generated
  module over a PID is isomorphic to the product of a free module and a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.-/
theorem equiv_free_prod_directSum [h' : Module.Finite R N] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| N ≃ₗ[R] (Fin n →₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i := by
  have := isNoetherian_of_isNoetherianRing_of_finite R N
  -- ⊢ ∃ n ι x p x e, Nonempty (N ≃ₗ[R] (Fin n →₀ R) × ⨁ (i : ι), R ⧸ span R {p i ^ …
  haveI := isNoetherian_submodule' (torsion R N)
  -- ⊢ ∃ n ι x p x e, Nonempty (N ≃ₗ[R] (Fin n →₀ R) × ⨁ (i : ι), R ⧸ span R {p i ^ …
  haveI := Module.Finite.of_surjective _ (torsion R N).mkQ_surjective
  -- ⊢ ∃ n ι x p x e, Nonempty (N ≃ₗ[R] (Fin n →₀ R) × ⨁ (i : ι), R ⧸ span R {p i ^ …
  obtain ⟨I, fI, p, hp, e, ⟨h⟩⟩ :=
    equiv_directSum_of_isTorsion.{u, v} (@torsion_isTorsion R N _ _ _)
  obtain ⟨n, ⟨g⟩⟩ := @Module.basisOfFiniteTypeTorsionFree' R _ _ _ (N ⧸ torsion R N) _ _ _ _
  -- ⊢ ∃ n ι x p x e, Nonempty (N ≃ₗ[R] (Fin n →₀ R) × ⨁ (i : ι), R ⧸ span R {p i ^ …
  haveI : Module.Projective R (N ⧸ torsion R N) := Module.Projective.of_basis ⟨g⟩
  -- ⊢ ∃ n ι x p x e, Nonempty (N ≃ₗ[R] (Fin n →₀ R) × ⨁ (i : ι), R ⧸ span R {p i ^ …
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id (torsion R N).mkQ_surjective
  -- ⊢ ∃ n ι x p x e, Nonempty (N ≃ₗ[R] (Fin n →₀ R) × ⨁ (i : ι), R ⧸ span R {p i ^ …
  refine'
    ⟨n, I, fI, p, hp, e,
      ⟨(lequivProdOfRightSplitExact (torsion R N).injective_subtype _ hf).symm.trans <|
          (h.prod g).trans <| LinearEquiv.prodComm.{u, u} R _ (Fin n →₀ R) ⟩⟩
  rw [range_subtype, ker_mkQ]
  -- 🎉 no goals
#align module.equiv_free_prod_direct_sum Module.equiv_free_prod_directSum

end Module
