/-
Copyright (c) 2024 Judith Ludwig, Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Florent Schaffhauser, Yunzhou Xie, Jujian Zhang
-/

import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Faithfully flat modules

A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and `IM ≠ M` whenever
`I` is a maximal ideal of `R`.

## Main declaration

- `Module.FaithfullyFlat`: the predicate asserting that an `R`-module `M` is faithfully flat.

## Main theorems

- `Module.FaithfullyFlat.iff_flat_and_proper_ideal`: an `R`-module `M` is faithfully flat iff it is
  flat and for all proper ideals `I` of `R`, `I • M ≠ M`.
- `Module.FaithfullyFlat.iff_flat_and_rTensor_faithful`: an `R`-module `M` is faithfully flat iff it
  is flat and tensoring with `M` is faithful, i.e. `N ≠ 0` implies `N ⊗ M ≠ 0`.
- `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful`: an `R`-module `M` is faithfully flat iff it
  is flat and tensoring with `M` is faithful, i.e. `N ≠ 0` implies `M ⊗ N ≠ 0`.

- `Module.FaithfullyFlat.self`: the `R`-module `R` is faithfully flat.

-/

universe u v

open TensorProduct

namespace Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/--
A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and,
for all `R`-module homomorphism `f : N → N'` such that `id ⊗ f = 0`, we have `f = 0`.
-/
@[mk_iff] class FaithfullyFlat extends Module.Flat R M : Prop where
  submodule_ne_top : ∀ ⦃m : Ideal R⦄ (_ : Ideal.IsMaximal m), m • (⊤ : Submodule R M) ≠ ⊤

namespace FaithfullyFlat
instance self : FaithfullyFlat R R where
  submodule_ne_top m h r := Ideal.eq_top_iff_one _ |>.not.1 h.ne_top <| by
    simpa using show 1 ∈ (m • ⊤ : Ideal R) from r.symm ▸ ⟨⟩

section proper_ideal

lemma iff_flat_and_proper_ideal :
    FaithfullyFlat R M ↔
    (Flat R M ∧ ∀ (I : Ideal R), I ≠ ⊤ → I • (⊤ : Submodule R M) ≠ ⊤) := by
  rw [faithfullyFlat_iff]
  refine ⟨fun ⟨flat, h⟩ => ⟨flat, fun I hI r => ?_⟩, fun h => ⟨h.1, fun m hm => h.2 _ hm.ne_top⟩⟩
  obtain ⟨m, hm, le⟩ := I.exists_le_maximal hI
  exact h hm <| eq_top_iff.2 <| show ⊤ ≤ m • ⊤ from r ▸ Submodule.smul_mono le (by simp [r])

lemma iff_flat_and_ideal_smul_eq_top :
    FaithfullyFlat R M ↔
    (Flat R M ∧ ∀ (I : Ideal R), I • (⊤ : Submodule R M) = ⊤ → I = ⊤) :=
  iff_flat_and_proper_ideal R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun I => eq_iff_iff.2 <| by tauto

end proper_ideal

section faithful

instance rTensor_nontrivial
    [fl: FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
    Nontrivial (N ⊗[R] M) := by
  obtain ⟨n, hn⟩ := nontrivial_iff_exists_ne (0 : N) |>.1 inferInstance
  let I := (Submodule.span R {n}).annihilator
  by_cases I_ne_top : I = ⊤
  · rw [Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul] at I_ne_top
    contradiction
  let inc : R ⧸ I →ₗ[R] N := Submodule.liftQ _ ((LinearMap.lsmul R N).flip n) <| fun r hr => by
    simpa only [LinearMap.mem_ker, LinearMap.flip_apply, LinearMap.lsmul_apply,
      Submodule.mem_annihilator_span_singleton, I] using hr
  have injective_inc : Function.Injective inc := LinearMap.ker_eq_bot.1 <| eq_bot_iff.2 <| by
    intro r hr
    induction r using Quotient.inductionOn' with | h r =>
    simpa only [Submodule.Quotient.mk''_eq_mk, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_annihilator_span_singleton, LinearMap.mem_ker, Submodule.liftQ_apply,
      LinearMap.flip_apply, LinearMap.lsmul_apply, I, inc] using hr
  have ne_top := iff_flat_and_proper_ideal R M |>.1 fl |>.2 I I_ne_top
  refine subsingleton_or_nontrivial _ |>.resolve_left fun rid => ?_
  exact False.elim <| ne_top <| Submodule.subsingleton_quotient_iff_eq_top.1 <|
    Function.Injective.comp (g := LinearMap.rTensor M inc)
      (fl.toFlat.rTensor_preserves_injective_linearMap inc injective_inc)
      ((quotTensorEquivQuotSMul M I).symm.injective) |>.subsingleton

instance lTensor_nontrivial
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
    Nontrivial (M ⊗[R] N) :=
  TensorProduct.comm R M N |>.toEquiv.nontrivial

lemma rTensor_reflects_triviality
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N]
    [h : Subsingleton (N ⊗[R] M)] : Subsingleton N := by
  revert h; change _ → _; contrapose
  simp only [not_subsingleton_iff_nontrivial]
  intro h
  infer_instance

lemma lTensor_reflects_triviality
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N]
    [Subsingleton (M ⊗[R] N)] :
    Subsingleton N := by
  haveI : Subsingleton (N ⊗[R] M) := (TensorProduct.comm R N M).toEquiv.injective.subsingleton
  apply rTensor_reflects_triviality R M

attribute [-simp] Ideal.Quotient.mk_eq_mk in
lemma iff_flat_and_rTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Nontrivial N → Nontrivial (N ⊗[R] M)) := by
  refine ⟨fun fl => ⟨inferInstance, rTensor_nontrivial R M⟩, fun ⟨flat, faithful⟩ => ⟨?_⟩⟩
  intro m hm rid
  specialize faithful (ULift (R ⧸ m)) inferInstance
  haveI : Nontrivial ((R ⧸ m) ⊗[R] M) :=
    (congr (ULift.moduleEquiv : ULift (R ⧸ m) ≃ₗ[R] R ⧸ m)
      (LinearEquiv.refl R M)).symm.toEquiv.nontrivial
  have := (quotTensorEquivQuotSMul M m).toEquiv.symm.nontrivial
  haveI H : Subsingleton (M ⧸ m • (⊤ : Submodule R M)) := by
    rwa [Submodule.subsingleton_quotient_iff_eq_top]
  rw [← not_nontrivial_iff_subsingleton] at H
  contradiction

lemma iff_flat_and_rTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Subsingleton (N ⊗[R] M) → Subsingleton N) :=
  iff_flat_and_rTensor_faithful R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 <| by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

lemma iff_flat_and_lTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Nontrivial N → Nontrivial (M ⊗[R] N)) :=
  iff_flat_and_rTensor_faithful R M |>.trans
  ⟨fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).toEquiv.nontrivial⟩,
    fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).symm.toEquiv.nontrivial⟩⟩

lemma iff_flat_and_lTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type max u v) [AddCommGroup N] [Module R N],
        Subsingleton (M ⊗[R] N) → Subsingleton N) :=
  iff_flat_and_lTensor_faithful R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 <| by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

end faithful

end FaithfullyFlat

end Module
