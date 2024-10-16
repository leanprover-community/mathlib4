/-
Copyright (c) 2024 Judith Ludwig, Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Florent Schaffhauser
-/

import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RingTheory.Finiteness
import Mathlib.Algebra.Module.Defs

/-!
# Faithfully flat modules

A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and,
for all `R`-module homomorphism `f : N → N'` such that `id ⊗ f = 0`, we have `f = 0`.

In the Stacks project, the definition of faithfully flat is different but tag
<https://stacks.math.columbia.edu/tag/00TN> proves that their definition is equivalent to this.

## Main declaration

- `Module.FaithfullyFlat`: the predicate asserting that an `R`-module `M` is faithfully flat.

## Main theorems

- `Module.FaithfullyFlat.of_linearEquiv`: modules linearly equivalent to a flat modules are flat
- `Module.FaithfullyFlat.comp`: https://stacks.math.columbia.edu/tag/00HC
-/

universe u

open TensorProduct

namespace Module

variable (R : Type u) (M : Type u) [CommRing R] [AddCommGroup M] [Module R M]

/--
A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and,
for all `R`-module homomorphism `f : N → N'` such that `id ⊗ f = 0`, we have `f = 0`.
-/

@[mk_iff] class FaithfullyFlat : Prop where
  flat : Module.Flat R M := by infer_instance
  submodule_ne_top :  ∀ ⦃m : Ideal R⦄ (_ : Ideal.IsMaximal m), m • (⊤ : Submodule R M) ≠ ⊤

namespace FaithfullyFlat

attribute [instance] FaithfullyFlat.flat

instance self (R : Type u) [CommRing R] : FaithfullyFlat R R where
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

end proper_ideal

section faithful

attribute [-simp] Ideal.Quotient.mk_eq_mk in
lemma iff_flat_and_rTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type u) [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (N ⊗[R] M)) := by
  refine ⟨fun fl => ⟨inferInstance, ?_⟩, fun ⟨flat, faithful⟩ => ⟨flat, ?_⟩⟩
  · intro N _ _ _
    obtain ⟨n, hn⟩ := nontrivial_iff_exists_ne (0 : N) |>.1 inferInstance
    let I := (Submodule.span R {n}).annihilator
    by_cases I_ne_top : I = ⊤
    · rw [Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul] at I_ne_top
      contradiction
    let inc : R ⧸ I →ₗ[R] N := Submodule.liftQ _ ((LinearMap.lsmul R N).flip n) <| fun r hr => by
      simpa only [LinearMap.mem_ker, LinearMap.flip_apply, LinearMap.lsmul_apply,
        Submodule.mem_annihilator_span_singleton, I] using hr
    have injective_inc : Function.Injective inc := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro r hr
      induction r using Quotient.inductionOn' with | h r =>
      simpa only [Submodule.Quotient.mk''_eq_mk, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_annihilator_span_singleton, LinearMap.mem_ker, Submodule.liftQ_apply,
        LinearMap.flip_apply, LinearMap.lsmul_apply, I, inc] using hr
    have ne_top := iff_flat_and_proper_ideal R M |>.1 fl |>.2 I I_ne_top
    refine subsingleton_or_nontrivial _ |>.resolve_left fun rid => ?_
    have : Function.Injective
      (LinearMap.rTensor M inc ∘ₗ (TensorProduct.quotientRingTensorEquiv M I).symm.toLinearMap) :=
      Function.Injective.comp
        (g := LinearMap.rTensor M inc)
        (f := (TensorProduct.quotientRingTensorEquiv M I).symm.toLinearMap)
        (Module.Flat.rTensor_preserves_injective_linearMap (h := fl.flat) inc injective_inc)
        (LinearEquiv.injective _)
    have := this.subsingleton
    rw [Submodule.subsingleton_quotient_iff_eq_top] at this
    contradiction
  · intro m hm rid
    specialize faithful (R ⧸ m) inferInstance
    have := (TensorProduct.quotientRingTensorEquiv M m).toEquiv.symm.nontrivial
    haveI H : Subsingleton (M ⧸ m • (⊤ : Submodule R M)) := by
      rwa [Submodule.subsingleton_quotient_iff_eq_top]
    rw [← not_nontrivial_iff_subsingleton] at H
    contradiction

lemma iff_flat_and_rTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type u) [AddCommGroup N] [Module R N], Subsingleton (N ⊗[R] M) → Subsingleton N) :=
  iff_flat_and_rTensor_faithful R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 <| by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

lemma iff_flat_and_lTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type u) [AddCommGroup N] [Module R N], Nontrivial N → Nontrivial (M ⊗[R] N)) :=
  iff_flat_and_rTensor_faithful R M |>.trans
  ⟨fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).toEquiv.nontrivial⟩,
    fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).symm.toEquiv.nontrivial⟩⟩

lemma iff_flat_and_lTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N : Type u) [AddCommGroup N] [Module R N], Subsingleton (M ⊗[R] N) → Subsingleton N) :=
  iff_flat_and_lTensor_faithful R M |>.trans <| and_congr_right_iff.2 fun _ => iff_of_eq <|
    forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 <| by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

end faithful

lemma range_le_ker_of_exact_rTensor [fl : FaithfullyFlat R M]
    ⦃N1 N2 N3 : Type u⦄
    [AddCommGroup N1] [Module R N1]
    [AddCommGroup N2] [Module R N2]
    [AddCommGroup N3] [Module R N3]
    (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3)
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    LinearMap.range l12 ≤ LinearMap.ker l23 := by
  have faithful := iff_flat_and_rTensor_faithful R M |>.1 fl |>.2
  intro x hx
  simp only [LinearMap.mem_ker]
  obtain ⟨y, hy⟩ := hx
  have : ∀ (n1 : N1) (m : M), l23.rTensor M (l12.rTensor M (n1 ⊗ₜ m)) = 0 := fun n1 m ↦ by
    exact Function.Exact.apply_apply_eq_zero ex (n1 ⊗ₜ[R] m)
  simp only [LinearMap.rTensor_tmul] at this
  have eq1 := this y
  by_contra! hxx
  let E : Submodule R N3 := Submodule.span R {l23 x}
  have hE : Nontrivial E := ⟨0, ⟨⟨l23 x, Submodule.mem_span_singleton_self _⟩,
    Subtype.coe_ne_coe.1 hxx.symm⟩⟩
  haveI : Nontrivial (E ⊗[R] M) := faithful E hE
  rw [hy] at eq1
  have eq0: (⊤ : Submodule R (E ⊗[R] M)) = 0 := by
    ext xx
    simp only [Submodule.mem_top, Submodule.zero_eq_bot, Submodule.mem_bot, true_iff]
    have mem : xx ∈ (⊤ : Submodule R _) := ⟨⟩
    rw [← TensorProduct.span_tmul_eq_top, mem_span_set] at mem
    obtain ⟨c, hc, rfl⟩ := mem
    choose b a hy using hc
    let r :  ⦃a : E ⊗[R] M⦄ → a ∈ ↑c.support → R := fun a ha =>
      Submodule.mem_span_singleton.1 (b ha).2 |>.choose
    have hr : ∀ ⦃i : E ⊗[R] M⦄ (hi : i ∈ c.support), b hi =
        r hi • ⟨l23 x, Submodule.mem_span_singleton_self _⟩ := by
      intro i hi
      ext
      exact Submodule.mem_span_singleton.1 (b hi).2 |>.choose_spec.symm

    simp only [Finsupp.sum]
    calc ∑ x ∈ c.support, c x • x
      _ = ∑ i ∈ c.support.attach, c i.1 • i.1 := by rw [← Finset.sum_attach]
      _ = ∑ i ∈ c.support.attach, c i.1 • (b i.2 ⊗ₜ a i.2) :=
        Finset.sum_congr rfl fun i _ => by rw [hy i.2]
      _ = ∑ i ∈ c.support.attach,
          (c i.1 • ((r i.2) • ⟨l23 x, Submodule.mem_span_singleton_self _⟩)) ⊗ₜ a i.2 :=
        Finset.sum_congr rfl fun i _ => by simp only [smul_tmul, tmul_smul, ← hr]
      _ = ∑ i ∈ c.support.attach, 0 :=
        Finset.sum_congr rfl fun r _ => by
          apply_fun (LinearMap.rTensor (M := M) E.subtype) using
            (Module.Flat.rTensor_preserves_injective_linearMap (M := M) E.subtype <|
              Submodule.injective_subtype E)
          simp only [SetLike.mk_smul_mk, LinearMap.rTensor_tmul, Submodule.coe_subtype, map_zero,
            ← smul_tmul', eq1, smul_zero]
    exact Finset.sum_const_zero
  have hEEE : (⊤ : Submodule R (E ⊗[R] M)) ≠ 0 := Submodule.nontrivial_iff_ne_bot.1 (by aesop)
  tauto

section complex

lemma implies_iff_exact [fl : FaithfullyFlat R M] :
    ∀ (N1 N2 N3 : Type u)
        [AddCommGroup N1] [Module R N1]
        [AddCommGroup N2] [Module R N2]
        [AddCommGroup N3] [Module R N3]
        (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.rTensor M) (l23.rTensor M) := by
  classical
  intro N1 N2 N3 _ _ _ _ _ _ l12 l23
  refine ⟨fun e => Module.Flat.iff_rTensor_exact.1 inferInstance e,
    fun ex => LinearMap.exact_iff.2 <| ?_⟩
  have faithful := iff_flat_and_rTensor_faithful R M |>.1 fl |>.2
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
  have := faithful H inferInstance
  rw [← not_subsingleton_iff_nontrivial] at this
  contradiction

lemma iff_iff_rTensor_exact :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      ∀ (N1 N2 N3 : Type u)
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
      ∀ (N1 N2 N3 : Type u)
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

section linearMap

variable {N : Type u} [AddCommGroup N] [Module R N]

/--
If `M` is a faithfully flat module, then for all linear maps `f`, the map `id ⊗ f = 0`, if and only
if  `f = 0`. -/
lemma implies_zero_iff_lTensor_zero {N' : Type u} [AddCommGroup N'] [Module R N']
    [h: FaithfullyFlat R M] (f : N →ₗ[R] N') :
    f = 0 ↔  LinearMap.lTensor M f = 0 :=
  ⟨fun hf => hf.symm ▸ LinearMap.lTensor_zero M, fun hf => by
    rw [iff_iff_lTensor_exact] at h
    have := h.1
    have := hf.symm ▸ h.2 N N' N' f LinearMap.id |>.2 (by
      rw [LinearMap.exact_iff, LinearMap.range_zero, LinearMap.ker_eq_bot]
      apply Module.Flat.lTensor_preserves_injective_linearMap
      exact fun _ _ h => h)
    ext x
    simpa using this (f x)⟩


/--
If `M` is a faithfully flat module, then for all linear maps `f`, the map `f ⊗ id = 0`, if and only
if  `f = 0`. -/
lemma implies_zero_iff_rTensor_zero {N' : Type u} [AddCommGroup N'] [Module R N']
    [h: FaithfullyFlat R M] (f : N →ₗ[R] N') :
    f = 0 ↔  LinearMap.rTensor M f = 0 :=
  implies_zero_iff_lTensor_zero R M f |>.trans
  ⟨fun h => by ext n m; exact (TensorProduct.comm R N' M).injective <|
    (by simpa using congr($h (m ⊗ₜ n))), fun h => by
    ext m n; exact (TensorProduct.comm R M N').injective <| (by simpa using congr($h (n ⊗ₜ m)))⟩


/--
An `R`-module `M` is faithfully flat iff it is flat and for all linear maps `f`, the map
`id ⊗ f = 0`, if and only if `f = 0`. -/
lemma iff_zero_iff_lTensor_zero :
    FaithfullyFlat R M ↔
    (Module.Flat R M ∧
      (∀ ⦃N N': Type u⦄ [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
      (f : N →ₗ[R] N'), f.lTensor M = 0 ↔ f = 0)):=
  ⟨fun fl => ⟨inferInstance, fun N N' _ _ _ _ f => implies_zero_iff_lTensor_zero R M f |>.symm⟩,
    fun ⟨flat, Z⟩ => iff_flat_and_lTensor_reflects_triviality R M |>.2 ⟨flat, fun N _ _ _ => by
      have := Z (LinearMap.id : N →ₗ[R] N) |>.1 (by ext; exact Subsingleton.elim _ _)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y => congr($this y)⟩⟩

/--
An `R`-module `M` is faithfully flat iff it is flat and for all linear maps `f`, the map
`id ⊗ f = 0`, if and only if `f = 0`. -/
lemma iff_zero_iff_rTensor_zero :
    FaithfullyFlat R M ↔
    (Module.Flat R M ∧
      (∀ ⦃N N': Type u⦄ [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
      (f : N →ₗ[R] N'), f.rTensor M = 0 ↔ (f = 0))):=
  ⟨fun fl => ⟨inferInstance, fun N N' _ _ _ _ f => implies_zero_iff_rTensor_zero R M f |>.symm⟩,
    fun ⟨flat, Z⟩ => iff_flat_and_rTensor_reflects_triviality R M |>.2 ⟨flat, fun N _ _ _ => by
      have := Z (LinearMap.id : N →ₗ[R] N) |>.1 (by ext; exact Subsingleton.elim _ _)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y => congr($this y)⟩⟩

end linearMap


/-- An `R`-module linearly equivalent to a faithfully flat `R`-module is faithfully flat. -/
lemma of_linearEquiv [f : FaithfullyFlat R M]
    (M' : Type u) [AddCommGroup M'] [Module R M'] (e : M' ≃ₗ[R] M) :
    FaithfullyFlat R M' := by
  rw [iff_zero_iff_lTensor_zero] at f ⊢
  refine ⟨f.1.of_linearEquiv _ _ _ e, fun N N' _ _ _ _ g => f.2 g |>.symm.trans ?_ |>.symm⟩
  have eq : LinearMap.lTensor M' g =
      e.symm.toLinearMap.rTensor _ ∘ₗ LinearMap.lTensor M g ∘ₗ
      e.toLinearMap.rTensor _ := by ext; simp
  rw [eq]

  refine ⟨fun h => h ▸ by simp, fun h => ?_⟩
  ext m n
  simpa using congr(e.toLinearMap.rTensor _ ($h (e.symm m ⊗ₜ[R] n)))

open TensorProduct LinearMap

variable (R : Type u) (S : Type u) (M : Type u)
  [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- If `S` is a faithfully flat `R`-algebra, then any faithfully flat `S`-Module is faithfully flat
as an `R`-module. -/
theorem comp [Module.FaithfullyFlat R S] [Module.FaithfullyFlat S M] :
    FaithfullyFlat R M := by
  rw [iff_zero_iff_lTensor_zero]
  refine ⟨Module.Flat.comp R S M, fun N N' _ _ _ _ f => ⟨fun aux => ?_, fun eq => eq ▸ by simp⟩⟩
    -- where
    -- flat := Module.Flat.comp R S M
    -- zero_if_lTensor_zero := by

    --  intro aux
  letI e1 : M ⊗[S] (S ⊗[R] N') →ₗ[S] (M ⊗[R] N') :=
  AlgebraTensorModule.cancelBaseChange R S S M N'
  letI e1.symm := (AlgebraTensorModule.cancelBaseChange R S S M N').symm
  letI e2 : (M ⊗[R] N) →ₗ[S] M ⊗[S] (S ⊗[R] N) :=
  (AlgebraTensorModule.cancelBaseChange R S S M N).symm
  letI e2.symm := (AlgebraTensorModule.cancelBaseChange R S S M N)
  letI fS :  M ⊗[S] (S ⊗[R] N) →ₗ[S] M ⊗[S] (S ⊗[R] N') :=
  lTensor M (TensorProduct.AlgebraTensorModule.map LinearMap.id f)
  have h : restrictScalars (R:= R) (S:= S) (e1 ∘ₗ fS ∘ₗ e2) = lTensor M f := by
    ext n
    simp [e1, e2, fS]
  have h1 : fS = e1.symm ∘ₗ (e1 ∘ₗ fS ∘ₗ e2) ∘ₗ e2.symm := by
    ext m n
    simp [e1, e1.symm, e2, e2.symm]
  have g : e1 ∘ₗ fS ∘ₗ e2 = 0 := by
    rw [aux] at h
    rwa [← DFunLike.coe_fn_eq] at h ⊢
  have g1: fS = 0 := by
    rw [aux] at h
    rw [g] at h1
    simp only [h1, zero_comp, comp_zero]
  rw [implies_zero_iff_lTensor_zero (R:= R) (M := S) f]
  have h3: lTensor S f = 0 ↔
  TensorProduct.AlgebraTensorModule.map (R:= R) (A:= S) (M:= S) LinearMap.id f = 0 := by
    have res : restrictScalars (R:= R) (S:= S) (TensorProduct.AlgebraTensorModule.map
    (R:= R) (A:= S) (M:= S) LinearMap.id f) = LinearMap.lTensor S f := by
        ext s n
        simp only [AlgebraTensorModule.curry_apply, curry_apply, coe_restrictScalars,
          AlgebraTensorModule.map_tmul, id_coe, id_eq, lTensor_tmul]
    constructor
    · rw [← res]
      intro h
      ext n
      simp only [AlgebraTensorModule.curry_apply, h, curry_apply, zero_apply,
        coe_restrictScalars]
    · intro h
      rw [← res]
      ext s n
      simp only [h, AlgebraTensorModule.curry_apply, curry_apply, coe_restrictScalars,
      zero_apply, restrictScalars_zero]
  rw [h3]
  rw [implies_zero_iff_lTensor_zero (R:= S) (M := M) (N:= S ⊗ N) (N':= S ⊗ N')
    (AlgebraTensorModule.map LinearMap.id f)]
  exact g1

end FaithfullyFlat

end Module
