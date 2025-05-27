/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Nailin Guan
-/
import Mathlib

/-!
# Weakly regular seqence is stable under flat base change

-/

universe v' v u' u

variable {R : Type u} [CommRing R]

abbrev SemiLinearMapAlgebraMapOfLinearMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) : M →ₛₗ[algebraMap R A] N where
  __ := f
  map_smul' m r := by simp

abbrev LinearMapOfSemiLinearMapAlgebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₛₗ[algebraMap R A] N) : M →ₗ[R] N where
  __ := f
  map_smul' m r := by simp

open RingTheory.Sequence IsLocalRing ModuleCat



section IsLocalization

variable [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R)

lemma ENat.add_right_cancel_iff (a b c : ℕ∞) (netop : c ≠ ⊤) : a + c = b + c ↔ a = b :=
  ⟨fun h ↦ ENat.add_left_injective_of_ne_top netop h, fun h ↦ by rw [h]⟩

lemma withBotENat_add_coe_cancel (a b : WithBot ℕ∞) (c : ℕ) : a + c = b + c ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  by_cases eqbot : a = ⊥
  · simp [eqbot, WithBot.bot_add] at h
    rw [WithBot.add_coe_eq_bot_iff.mp h.symm, eqbot]
  · by_cases eqbot' : b = ⊥
    · absurd eqbot
      simpa [eqbot'] using h
    · have : a.unbot eqbot + c = b.unbot eqbot' + c := by
        apply WithBot.coe_inj.mp
        convert h
        repeat simp;rfl
      rw [← WithBot.coe_unbot a eqbot, ← WithBot.coe_unbot b eqbot', WithBot.coe_inj]
      simpa [ENat.add_right_cancel_iff _ _ _ (ENat.coe_ne_top c)] using this

variable [p.IsPrime] {Rₚ : Type u'} [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
  [IsLocalRing Rₚ]
  -- This can be deduced from `IsLocalization.AtPrime Rₚ p`, but cannot be an
  -- `instance`, so we need to manually add this condition.

variable (Rₚ) in
open Pointwise in
omit [IsLocalRing R] [IsNoetherianRing R] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] in
lemma isLocaliation_map_isSMulRegular_of_isSMulRegular (r : R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    (reg : IsSMulRegular M r) : IsSMulRegular Mₚ (algebraMap R Rₚ r) := by
  rw [isSMulRegular_algebraMap_iff r, isSMulRegular_iff_ker_lsmul_eq_bot Mₚ r,
    LinearMap.ker_eq_bot']
  intro m hm
  rcases IsLocalizedModule.mk'_surjective p.primeCompl f m with ⟨a, ha⟩
  simp only [← ha, LinearMap.lsmul_apply] at hm ⊢
  have : r • IsLocalizedModule.mk' f a.1 a.2 = 0 := hm
  rw [← IsLocalizedModule.mk'_smul, IsLocalizedModule.mk'_eq_zero'] at this
  simp only [Subtype.exists, Submonoid.mk_smul, exists_prop] at this
  rcases this with ⟨s, mem, hs⟩
  rw [smul_smul, mul_comm, ← smul_smul] at hs
  apply (IsLocalizedModule.mk'_eq_zero' f a.2).mpr ⟨⟨s, mem⟩, ?_⟩
  simp only [Submonoid.mk_smul, ← Submodule.mem_bot (R := R),
    ← (isSMulRegular_iff_ker_lsmul_eq_bot M r).mp reg]
  exact hs

variable (Rₚ) in
abbrev quotSMulTop_isLocalizedModule_map (x : R) (M : Type*) [AddCommGroup M] [Module R M]
    (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ] [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ]
    (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] :
    QuotSMulTop x M →ₗ[R] QuotSMulTop ((algebraMap R Rₚ) x) Mₚ :=
  LinearMapOfSemiLinearMapAlgebraMap (Submodule.mapQ _ _
    (SemiLinearMapAlgebraMapOfLinearMap f)
    (fun m hm ↦ by
      rw [← Submodule.ideal_span_singleton_smul] at hm
      simp only [Submodule.mem_comap, LinearMap.coe_mk, LinearMap.coe_toAddHom]
      refine Submodule.smul_induction_on hm (fun r hr m hm ↦ ?_)
        (fun m1 m2 hm1 hm2 ↦ by simpa using Submodule.add_mem _ hm1 hm2)
      rcases Ideal.mem_span_singleton'.mp hr with ⟨r', hr'⟩
      simpa only [← hr', map_smul, mul_comm r' x, ← smul_smul,
        algebra_compatible_smul Rₚ x (r' • f m)]
        using Submodule.smul_mem_pointwise_smul (r' • f m) ((algebraMap R Rₚ) x) ⊤ hm))

variable (Rₚ) in
omit [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing Rₚ] in
lemma isLocalizedModule_quotSMulTop_isLocalizedModule_map (x : R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f] :
    IsLocalizedModule.AtPrime p (quotSMulTop_isLocalizedModule_map p Rₚ x M Mₚ f) where
  map_units r := by
    let alg := (Algebra.algHom R Rₚ (Module.End Rₚ (QuotSMulTop ((algebraMap R Rₚ) x) Mₚ)))
    rcases isUnit_iff_exists.mp (IsUnit.algebraMap_of_algebraMap (r := r.1) alg.toLinearMap
      (map_one alg) (IsLocalization.map_units Rₚ r)) with ⟨s, hs1, hs2⟩
    exact isUnit_iff_exists.mpr ⟨LinearMap.restrictScalars R s,
      ⟨LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs1 (Eq.refl x)),
        LinearMap.ext (fun x ↦ by simpa using DFunLike.congr hs2 (Eq.refl x))⟩⟩
  surj' y := by
    induction' y using Submodule.Quotient.induction_on with y
    rcases IsLocalizedModule.surj' (S := p.primeCompl) (f := f) y with ⟨z, hz⟩
    use (Submodule.Quotient.mk z.1, z.2)
    simp [← hz]
  exists_of_eq {y1 y2} h := by
    induction' y1 using Submodule.Quotient.induction_on with y1
    induction' y2 using Submodule.Quotient.induction_on with y2
    simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, Submodule.mapQ_apply] at h
    have h := (Submodule.Quotient.mk_eq_zero _).mp (sub_eq_zero_of_eq h)
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h with ⟨m, _, hm⟩
    rcases IsLocalizedModule.surj p.primeCompl f m with ⟨⟨z, s⟩, hz⟩
    have eq : f (s • (y1 - y2)) = f (x • z) := by simp [← hm, ← hz, smul_comm s x m]
    rcases IsLocalizedModule.exists_of_eq (S := p.primeCompl) eq with ⟨c, hc⟩
    use c * s
    apply sub_eq_zero.mp
    have h : (0 : QuotSMulTop x M) = Submodule.Quotient.mk (c • s • (y1 - y2)) := by
      simpa [hc] using (smul_eq_zero_of_right c <| (Submodule.Quotient.mk_eq_zero _).mpr <|
        Submodule.smul_mem_pointwise_smul z x ⊤ Submodule.mem_top).symm
    simp [h, smul_sub, mul_smul]

variable (Rₚ) in
omit [IsLocalRing R] [IsNoetherianRing R] [IsLocalRing Rₚ] in
open Pointwise in
lemma isLocaliation_map_is_weakly_regular_of_is_weakly_regular (rs : List R)
    (M : Type*) [AddCommGroup M] [Module R M] (Mₚ : Type*) [AddCommGroup Mₚ] [Module R Mₚ]
    [Module Rₚ Mₚ] [IsScalarTower R Rₚ Mₚ] (f : M →ₗ[R] Mₚ) [IsLocalizedModule.AtPrime p f]
    (reg : IsWeaklyRegular M rs) : IsWeaklyRegular Mₚ (rs.map (algebraMap R Rₚ)) := by
  generalize len : rs.length = n
  induction' n with n ih generalizing M Mₚ rs
  · simp [List.length_eq_zero_iff.mp len]
  · match rs with
    | [] => simp at len
    | x :: rs' =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [isWeaklyRegular_cons_iff, List.map_cons] at reg ⊢
      refine ⟨isLocaliation_map_isSMulRegular_of_isSMulRegular p Rₚ x M Mₚ f reg.1, ?_⟩
      let g := quotSMulTop_isLocalizedModule_map p Rₚ x M Mₚ f
      have := isLocalizedModule_quotSMulTop_isLocalizedModule_map p Rₚ x M Mₚ f
      exact ih rs' (QuotSMulTop x M) (QuotSMulTop ((algebraMap R Rₚ) x) Mₚ) g reg.2 len

end IsLocalization
