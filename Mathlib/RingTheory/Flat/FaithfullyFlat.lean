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
- `Module.FaithfullyFlat.iff_iff_rTensor_exact`: an `R`-module `M` is faithfully flat iff tensoring
  with `M` preserves and reflects exact sequences, i.e. the sequence `N₁ → N₂ → N₃` is exact *iff*
  the sequence `N₁ ⊗ M → N₂ ⊗ M → N₃ ⊗ M` is exact.
- `Module.FaithfullyFlat.iff_iff_lTensor_exact`: an `R`-module `M` is faithfully flat iff tensoring
  with `M` preserves and reflects exact sequences, i.e. the sequence `N₁ → N₂ → N₃` is exact *iff*
  the sequence `M ⊗ N₁ → M ⊗ N₂ → M ⊗ N₃` is exact.

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

section complex

private lemma range_le_ker_of_exact_rTensor [fl : FaithfullyFlat R M]
    ⦃N1 N2 N3 : Type*⦄
    [AddCommGroup N1] [Module R N1]
    [AddCommGroup N2] [Module R N2]
    [AddCommGroup N3] [Module R N3]
    (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3)
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    LinearMap.range l12 ≤ LinearMap.ker l23 := by
  intro x hx
  simp only [LinearMap.mem_ker]
  obtain ⟨y, rfl⟩ := hx
  have : ∀ (n1 : N1) (m : M), l23 (l12 n1) ⊗ₜ[R] m = 0 := fun n1 m ↦
    ex.apply_apply_eq_zero (n1 ⊗ₜ[R] m)
  have eq1 := this y
  by_contra! hxx
  let E : Submodule R N3 := Submodule.span R {l23 (l12 y)}
  have hE : Nontrivial E :=
    ⟨0, ⟨⟨l23 (l12 y), Submodule.mem_span_singleton_self _⟩, Subtype.coe_ne_coe.1 hxx.symm⟩⟩
  have eq0: (⊤ : Submodule R (E ⊗[R] M)) = ⊥ := by
    ext x
    simp only [Submodule.mem_top, Submodule.mem_bot, true_iff]
    have mem : x ∈ (⊤ : Submodule R _) := ⟨⟩
    rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem
    obtain ⟨c, hc, rfl⟩ := mem
    choose b a hy using hc
    let r :  ⦃a : E ⊗[R] M⦄ → a ∈ ↑c.support → R := fun a ha =>
      Submodule.mem_span_singleton.1 (b ha).2 |>.choose
    have hr : ∀ ⦃i : E ⊗[R] M⦄ (hi : i ∈ c.support), b hi =
        r hi • ⟨l23 (l12 y), Submodule.mem_span_singleton_self _⟩ := by
      intro i hi
      ext
      exact Submodule.mem_span_singleton.1 (b hi).2 |>.choose_spec.symm

    simp only [Finsupp.sum]
    calc ∑ x ∈ c.support, c x • x
      _ = ∑ i ∈ c.support.attach, c i.1 • i.1 := by rw [← Finset.sum_attach]
      _ = ∑ i ∈ c.support.attach, c i.1 • (b i.2 ⊗ₜ a i.2) :=
        Finset.sum_congr rfl fun i _ => by rw [hy i.2]
      _ = ∑ i ∈ c.support.attach,
          (c i.1 • ((r i.2) • ⟨l23 (l12 y), Submodule.mem_span_singleton_self _⟩)) ⊗ₜ a i.2 :=
        Finset.sum_congr rfl fun i _ => by simp only [smul_tmul, tmul_smul, ← hr]
      _ = ∑ i ∈ c.support.attach, 0 :=
        Finset.sum_congr rfl fun r _ => by
          apply_fun (LinearMap.rTensor (M := M) E.subtype) using
            (Module.Flat.rTensor_preserves_injective_linearMap (M := M) E.subtype <|
              Submodule.injective_subtype E)
          simp only [SetLike.mk_smul_mk, LinearMap.rTensor_tmul, Submodule.coe_subtype, map_zero,
            ← smul_tmul', eq1, smul_zero]
    exact Finset.sum_const_zero
  exact Submodule.nontrivial_iff_ne_bot.1 (by aesop) eq0

lemma rTensor_reflects_exact [fl : FaithfullyFlat R M]
    (N1 N2 N3 : Type*)
    [AddCommGroup N1] [Module R N1]
    [AddCommGroup N2] [Module R N2]
    [AddCommGroup N3] [Module R N3]
    (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3)
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    Function.Exact l12 l23 := LinearMap.exact_iff.2 <| by
  have complex : LinearMap.range l12 ≤ LinearMap.ker l23 := range_le_ker_of_exact_rTensor R M _ _ ex

  refine le_antisymm ?_ complex
  rintro x (hx : l23 x = 0)
  let H := LinearMap.ker l23 ⧸ LinearMap.range (Submodule.inclusion complex)
  suffices triv_coh : Subsingleton H by
    have eq0 : (Submodule.mkQ _ ⟨x, hx⟩ : H) = 0 := triv_coh.elim _ _
    obtain ⟨⟨y, hy⟩, eq0⟩ := Submodule.Quotient.mk_eq_zero _ |>.1 eq0
    simp only [Subtype.ext_iff, Submodule.coe_inclusion] at eq0
    subst eq0
    assumption
  have triv_tensor : Subsingleton (H ⊗[R] M) := by
    let e : H ⊗[R] M ≃ₗ[R] ((LinearMap.ker l23 ⊗[R] M) ⧸ _) :=
      TensorProduct.quotientTensorEquiv _ _
    haveI : Subsingleton
        ((LinearMap.ker l23 ⊗[R] M) ⧸
          LinearMap.range (map (LinearMap.range (Submodule.inclusion complex)).subtype
            (LinearMap.id : M →ₗ[R] M))) := by
      rw [Submodule.subsingleton_quotient_iff_eq_top, eq_top_iff]
      let ι : (LinearMap.ker l23) ⊗[R] M →ₗ[R] N2 ⊗[R] M := (Submodule.subtype _).rTensor M
      rw [← Submodule.map_le_map_iff_of_injective (f := ι)
        (hf := Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective),
        Submodule.map_top]

      rintro _ ⟨z, rfl⟩
      have mem : ι z ∈ LinearMap.ker (LinearMap.rTensor M l23) := by
        simp only [LinearMap.mem_ker, ι]
        rw [← LinearMap.comp_apply, LinearMap.rTensor, LinearMap.rTensor, ← map_comp,
          show l23 ∘ₗ (LinearMap.ker l23).subtype = 0 by ext; simp]
        simp only [LinearMap.comp_id, map_zero_left, LinearMap.zero_apply]
      rw [LinearMap.exact_iff.1 ex] at mem
      obtain ⟨W, hW⟩ := mem
      rw [← hW]
      clear hW z
      induction W using TensorProduct.induction_on with
      | zero => exact Submodule.zero_mem _
      | tmul x y =>
        simp only [LinearMap.rTensor_tmul, Submodule.mem_map, LinearMap.mem_range,
          exists_exists_eq_and, ι]
        refine ⟨⟨⟨l12 x, complex <| by simp⟩, ⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩⟩ ⊗ₜ y, ?_⟩
        simp only [map_tmul, Submodule.coe_subtype, LinearMap.id_coe, id_eq, LinearMap.rTensor_tmul]
      | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    exact e.injective.subsingleton

  refine subsingleton_or_nontrivial H |>.resolve_right fun h => ?_
  haveI : Nontrivial (H ⊗[R] M) := inferInstance
  rw [← not_subsingleton_iff_nontrivial] at this
  contradiction

lemma lTensor_reflects_exact [fl : FaithfullyFlat R M]
    (N1 N2 N3 : Type*)
    [AddCommGroup N1] [Module R N1]
    [AddCommGroup N2] [Module R N2]
    [AddCommGroup N3] [Module R N3]
    (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3)
    (ex : Function.Exact (l12.lTensor M) (l23.lTensor M)) :
    Function.Exact l12 l23 :=
  rTensor_reflects_exact R M _ _ _ _ _ <| ex.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.comm _ _ _) (e₂ := TensorProduct.comm _ _ _)
    (e₃ := TensorProduct.comm _ _ _) (by ext; rfl) (by ext; rfl)

lemma implies_iff_exact [fl : FaithfullyFlat R M]
    (N1 N2 N3 : Type max u v)
    [AddCommGroup N1] [Module R N1]
    [AddCommGroup N2] [Module R N2]
    [AddCommGroup N3] [Module R N3]
    (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3) :
    Function.Exact l12 l23 ↔ Function.Exact (l12.rTensor M) (l23.rTensor M) :=
  ⟨fun e => Module.Flat.iff_rTensor_exact.1 fl.toFlat e,
    fun ex => rTensor_reflects_exact R M N1 N2 N3 l12 l23 ex⟩

lemma iff_iff_rTensor_exact :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N1 N2 N3 : Type max u v)
        [AddCommGroup N1] [Module R N1]
        [AddCommGroup N2] [Module R N2]
        [AddCommGroup N3] [Module R N3]
        (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.rTensor M) (l23.rTensor M)) :=
  ⟨fun fl => ⟨inferInstance, implies_iff_exact R M⟩, fun ⟨flat, iff_exact⟩ =>
    iff_flat_and_rTensor_reflects_triviality _ _ |>.2 ⟨flat, fun N _ _ h => by
    have ex := iff_exact PUnit N PUnit 0 0 |>.2 fun x => by
      simpa using Subsingleton.elim _ _
    rw [subsingleton_iff_forall_eq 0]
    intro y
    specialize ex y
    simpa [eq_comm] using ex⟩⟩

lemma iff_iff_lTensor_exact :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N1 N2 N3 : Type max u v)
        [AddCommGroup N1] [Module R N1]
        [AddCommGroup N2] [Module R N2]
        [AddCommGroup N3] [Module R N3]
        (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.lTensor M) (l23.lTensor M)) :=
  iff_iff_rTensor_exact _ _ |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr <| fun N1 => forall_congr fun N2 => forall_congr fun N3 =>
    forall_congr fun _ => forall_congr fun _ => forall_congr fun _ => forall_congr fun _ =>
    forall_congr fun _ => forall_congr fun _ => forall_congr fun l12 => forall_congr fun l23 =>
    iff_iff_eq.1 <| iff_congr (by rfl) (Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := TensorProduct.comm _ _ _) (e₂ := TensorProduct.comm _ _ _)
      (e₃ := TensorProduct.comm _ _ _) (by ext; simp) (by ext; simp))

end complex

end FaithfullyFlat

end Module
