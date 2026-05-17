/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Finiteness.Small

/-!
# Modules admitting finite free resolutions

## Main definitions
* `Module.HasFiniteFreeResolutionOfLength` : We say that an `R`-module `M` has a finite free
  resolution of length `n` if there exists an exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ M ⟶ 0` such
  that `Eᵢ` are finite free `R`-modules.
* `Module.HasFiniteFreeResolution` : We say that an `R`-module `M` has a finite free resolution
  if it has a finite free resolution of some finite length.
-/

public section

universe w v v' u u'

namespace Module

variable (R : Type u) [Ring R] [Small.{v} R]

/-- We say that an `R`-module `M` has a finite free resolution of length `n` if there exists an
exact sequence `0 ⟶ Eₙ ⟶ ⋯ ⟶ E₀ ⟶ M ⟶ 0` such that `Eᵢ` are finite free `R`-modules. -/
inductive HasFiniteFreeResolutionOfLength (R : Type u) [Ring R] [Small.{v} R] :
    ∀ (M : Type v), [AddCommGroup M] → [Module R M] → ℕ → Prop
  | zero (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Free R M] :
      HasFiniteFreeResolutionOfLength R M 0
  | succ (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
      (F : Type v) [AddCommGroup F] [Module R F] [Module.Finite R F] [Free R F]
      (K : Type v) [AddCommGroup K] [Module R K] [Module.Finite R K]
      (f : K →ₗ[R] F) (g : F →ₗ[R] M) (hf : Function.Injective f) (hg : Function.Surjective g)
      (he : Function.Exact f g) (hk : HasFiniteFreeResolutionOfLength R K n) :
      HasFiniteFreeResolutionOfLength R M (n + 1)

namespace HasFiniteFreeResolutionOfLength

variable {R} {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}

theorem module_finite (hM : HasFiniteFreeResolutionOfLength R M n) : Module.Finite R M := by
  cases hM with
  | zero => infer_instance
  | succ _ _ _ _ _ g _ hg _ _ => exact Module.Finite.of_surjective g hg

theorem succ_of_hasFiniteFreeResolutionOfLength (hM : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength R M (n + 1) := by
  induction hM with
  | zero M =>
      exact (HasFiniteFreeResolutionOfLength.zero PUnit).succ M 0 M PUnit 0 LinearMap.id
        (Function.injective_of_subsingleton _) (fun x ↦ ⟨x, rfl⟩)
          (Function.Exact.of_comp_of_mem_range rfl (fun _ hy ↦ ⟨0, hy.symm⟩))
  | succ M n F K f g hf hg he _ ih => exact ih.succ M (n + 1) F K f g hf hg he

theorem of_ge {m : ℕ} (hM : HasFiniteFreeResolutionOfLength R M n) (h : n ≤ m) :
    HasFiniteFreeResolutionOfLength R M m :=
  Nat.le.rec hM (fun _ ↦ succ_of_hasFiniteFreeResolutionOfLength) h

theorem of_semilinearEquiv {S : Type u'} [Ring S] [Small.{v'} S]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R M n)
    {N : Type v'} [AddCommGroup N] [Module S N] (e : M ≃ₛₗ[σ] N) :
    HasFiniteFreeResolutionOfLength S N n := by
  induction hn generalizing N with
  | zero _ =>
      have : Module.Finite S N := Module.Finite.of_surjective e.toLinearMap e.surjective
      have : Free S N := Free.of_equiv e
      exact HasFiniteFreeResolutionOfLength.zero N
  | succ _ n F K f g hf hg he hk ih =>
      let : Module S F := compHom F σ'
      let : Module S K := compHom K σ'
      let eF : F ≃ₛₗ[σ] F := compHom.self_equiv σ σ' F
      let eK : K ≃ₛₗ[σ] K := compHom.self_equiv σ σ' K
      let fS : K →ₗ[S] F := (eF.toLinearMap ∘ₛₗ f) ∘ₛₗ eK.symm.toLinearMap
      let gS : F →ₗ[S] N := (e.toLinearMap ∘ₛₗ g) ∘ₛₗ eF.symm.toLinearMap
      have : Free S F := Free.of_equiv eF
      have : Module.Finite S F := Module.Finite.of_surjective eF.toLinearMap eF.surjective
      have : Module.Finite S K := Module.Finite.of_surjective eK.toLinearMap eK.surjective
      have : Small.{v'} F := Module.Finite.small S F
      have : Small.{v'} K := Module.Finite.small S K
      let +nondep eFv : Shrink.{v'} F ≃ₗ[S] F := Shrink.linearEquiv S F
      let +nondep eKv : Shrink.{v'} K ≃ₗ[S] K := Shrink.linearEquiv S K
      refine (ih (eK.trans eKv.symm)).succ N n (Shrink.{v'} F) (Shrink.{v'} K)
        (eFv.symm ∘ₗ fS ∘ₗ eKv) (gS ∘ₗ eFv) ?_ ((e.surjective.comp hg).comp eFv.surjective) ?_
      · exact eFv.symm.injective.comp (hf.comp eKv.injective)
      · exact (LinearEquiv.conj_exact_iff_exact (fS ∘ₗ eKv.toLinearMap) gS eFv.symm).2 <|
          fun x ↦ by simpa [gS, fS] using he (eF.symm x)

variable [Small.{w} R]

theorem of_linearEquiv {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (e : M ≃ₗ[R] N) {n : ℕ} (hn : HasFiniteFreeResolutionOfLength R M n) :
    HasFiniteFreeResolutionOfLength R N n :=
  hn.of_semilinearEquiv e

theorem succ' {F : Type*} {K : Type w} [AddCommGroup F] [Module R F] [Module.Finite R F] [Free R F]
    [AddCommGroup K] [Module R K] (f : K →ₗ[R] F) (g : F →ₗ[R] M) (hf : Function.Injective f)
    (hg : Function.Surjective g) (he : Function.Exact f g) {n : ℕ}
    (hk : HasFiniteFreeResolutionOfLength R K n) : HasFiniteFreeResolutionOfLength R M (n + 1) := by
  have : Module.Finite R K := hk.module_finite
  have : Small.{v} F := Module.Finite.small.{v} R F
  have : Small.{v} K := Module.Finite.small.{v} R K
  let +nondep eF : Shrink.{v} F ≃ₗ[R] F := Shrink.linearEquiv R F
  let +nondep eK : Shrink.{v} K ≃ₗ[R] K := Shrink.linearEquiv R K
  let fv : Shrink.{v} K →ₗ[R] Shrink.{v} F := eF.symm ∘ₗ f ∘ₗ eK.toLinearMap
  exact (hk.of_linearEquiv eK.symm).succ M n (Shrink.{v} F) (Shrink.{v} K) fv (g ∘ₗ eF.toLinearMap)
    (eF.symm.injective.comp (hf.comp eK.injective)) (hg.comp eF.surjective) <|
      (LinearEquiv.conj_symm_exact_iff_exact (f ∘ₗ eK.toLinearMap) g eF).2 <|
        (Function.Surjective.comp_exact_iff_exact eK.surjective).2 he

end HasFiniteFreeResolutionOfLength

/-- An `R`-module `M` has a finite free resolution if it has a finite free resolution of some finite
length. -/
class HasFiniteFreeResolution (R : Type u) [Ring R] [Small.{v} R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop where
  out (R M) : ∃ (n : ℕ),  HasFiniteFreeResolutionOfLength R M n

namespace HasFiniteFreeResolution

variable (M : Type v) [AddCommGroup M] [Module R M]

instance of_finite_of_free [Module.Finite R M] [Free R M] : HasFiniteFreeResolution R M :=
  ⟨0, HasFiniteFreeResolutionOfLength.zero M⟩

instance (priority := low) module_finite [HasFiniteFreeResolution R M] : Module.Finite R M :=
  (HasFiniteFreeResolution.out R M).choose_spec.module_finite

theorem of_semilinearEquiv (S : Type u') [Ring S] [Small.{v'} S] {σ : R →+* S} {σ' : S →+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [HasFiniteFreeResolution R M]
    (N : Type v') [AddCommGroup N] [Module S N] (e : M ≃ₛₗ[σ] N) :
    HasFiniteFreeResolution S N := by
  obtain ⟨n, hn⟩ := HasFiniteFreeResolution.out R M
  exact ⟨n, hn.of_semilinearEquiv e⟩

variable {R M} [Small.{w} R]

theorem of_linearEquiv {N : Type w} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    [HasFiniteFreeResolution R M] : HasFiniteFreeResolution R N :=
  of_semilinearEquiv R M R N e

theorem of_ker_hasFiniteFreeResolution {F : Type*} [AddCommGroup F] [Module R F] [Module.Finite R F]
    [Free R F] {K : Type w} [AddCommGroup K] [Module R K] (f : K →ₗ[R] F) (g : F →ₗ[R] M)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    [HasFiniteFreeResolution R K] : HasFiniteFreeResolution R M := by
  obtain ⟨n, hk⟩ := HasFiniteFreeResolution.out R K
  exact ⟨n + 1, hk.succ' f g hf hg he⟩

variable (R M)

instance [Small.{max w v} R] [HasFiniteFreeResolution R M] :
    HasFiniteFreeResolution R (ULift.{w} M) :=
  of_linearEquiv ULift.moduleEquiv.symm

omit [Small.{w} R] in
theorem of_ulift [Small.{max w v} R] [HasFiniteFreeResolution R (ULift.{w} M)] :
    HasFiniteFreeResolution R M :=
  of_linearEquiv ULift.moduleEquiv

instance [Small.{w} M] [HasFiniteFreeResolution R M] : HasFiniteFreeResolution R (Shrink.{w} M) :=
  of_linearEquiv (Shrink.linearEquiv R M).symm

theorem of_shrink [Small.{w, v} M] [HasFiniteFreeResolution R (Shrink.{w} M)] :
    HasFiniteFreeResolution R M :=
  of_linearEquiv (Shrink.linearEquiv R M)

end Module.HasFiniteFreeResolution
