/-
Copyright (c) 2024 Judith Ludwig, Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Florent Schaffhauser, Yunzhou Xie, Jujian Zhang
-/
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Stability

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
- `Module.FaithfullyFlat.iff_exact_iff_rTensor_exact`: an `R`-module `M` is faithfully flat iff
  tensoring with `M` preserves and reflects exact sequences, i.e. the sequence `N₁ → N₂ → N₃` is
  exact *iff* the sequence `N₁ ⊗ M → N₂ ⊗ M → N₃ ⊗ M` is exact.
- `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`: an `R`-module `M` is faithfully flat iff
  tensoring with `M` preserves and reflects exact sequences, i.e. the sequence `N₁ → N₂ → N₃` is
  exact *iff* the sequence `M ⊗ N₁ → M ⊗ N₂ → M ⊗ N₃` is exact.
- `Module.FaithfullyFlat.iff_zero_iff_lTensor_zero`: an `R`-module `M` is faithfully flat iff for
  all linear maps `f : N → N'`, `f = 0` iff `M ⊗ f = 0`.
- `Module.FaithfullyFlat.iff_zero_iff_rTensor_zero`: an `R`-module `M` is faithfully flat iff for
  all linear maps `f : N → N'`, `f = 0` iff `f ⊗ M = 0`.

- `Module.FaithfullyFlat.of_linearEquiv`: modules linearly equivalent to a flat modules are flat
- `Module.FaithfullyFlat.trans`: if `S` is `R`-faithfully flat and `M` is `S`-faithfully flat, then
  `M` is `R`-faithfully flat.

- `Module.FaithfullyFlat.self`: the `R`-module `R` is faithfully flat.

-/

universe u v

open TensorProduct DirectSum

namespace Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/--
A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and,
for all `R`-linear maps `f : N → N'` such that `id ⊗ f = 0`, we have `f = 0`.
-/
@[mk_iff] class FaithfullyFlat : Prop extends Module.Flat R M where
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
    [fl : FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
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

/-- If `M` is a faithfully flat `R`-module and `N` is `R`-linearly isomorphic to `M`, then
`N` is faithfully flat. -/
lemma of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] [FaithfullyFlat R M]
    (e : N ≃ₗ[R] M) : FaithfullyFlat R N := by
  rw [iff_flat_and_lTensor_faithful]
  exact ⟨Flat.of_linearEquiv e,
    fun P _ _ hP ↦ (TensorProduct.congr e (LinearEquiv.refl R P)).toEquiv.nontrivial⟩

section

/-- A direct sum of faithfully flat `R`-modules is faithfully flat. -/
instance directSum {ι : Type*} [Nonempty ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] [∀ i, FaithfullyFlat R (M i)] : FaithfullyFlat R (⨁ i, M i) := by
  classical
  rw [iff_flat_and_lTensor_faithful]
  refine ⟨inferInstance, fun N _ _ hN ↦ ?_⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := M i ⊗[R] N)
  haveI : Nontrivial (⨁ (i : ι), M i ⊗[R] N) :=
    ⟨DirectSum.of _ i x, DirectSum.of _ i y, fun h ↦ hxy (DirectSum.of_injective i h)⟩
  apply (TensorProduct.directSumLeft R M N).toEquiv.nontrivial

/-- Free `R`-modules over discrete types are flat. -/
instance finsupp (ι : Type v) [Nonempty ι] : FaithfullyFlat R (ι →₀ R) := by
  classical exact of_linearEquiv _ _ (finsuppLEquivDirectSum R R ι)

end

/-- Any free, nontrivial `R`-module is flat. -/
instance [Nontrivial M] [Module.Free R M] : FaithfullyFlat R M :=
  of_linearEquiv _ _ (Free.chooseBasis R M).repr

section

variable {N : Type*} [AddCommGroup N] [Module R N]

@[simp]
lemma subsingleton_tensorProduct_iff_right [Module.FaithfullyFlat R M] :
    Subsingleton (M ⊗[R] N) ↔ Subsingleton N :=
  ⟨fun _ ↦ lTensor_reflects_triviality R M N, fun _ ↦ inferInstance⟩

@[simp]
lemma subsingleton_tensorProduct_iff_left [Module.FaithfullyFlat R N] :
    Subsingleton (M ⊗[R] N) ↔ Subsingleton M :=
  ⟨fun _ ↦ rTensor_reflects_triviality R N M, fun _ ↦ inferInstance⟩

@[simp]
lemma nontrivial_tensorProduct_iff_right [Module.FaithfullyFlat R M] :
    Nontrivial (M ⊗[R] N) ↔ Nontrivial N := by
  simp [← not_iff_not, not_nontrivial_iff_subsingleton]

@[simp]
lemma nontrivial_tensorProduct_iff_left [Module.FaithfullyFlat R N] :
    Nontrivial (M ⊗[R] N) ↔ Nontrivial M := by
  simp [← not_iff_not, not_nontrivial_iff_subsingleton]

end

section exact

/-!
### Faithfully flat modules and exact sequences

In this section we prove that an `R`-module `M` is faithfully flat iff tensoring with `M`
preserves and reflects exact sequences.

Let `N₁ -l₁₂-> N₂ -l₂₃-> N₃` be two linear maps.
- We first show that if `N₁ ⊗ M -> N₂ ⊗ M -> N₃ ⊗ M` is exact, then `N₁ -l₁₂-> N₂ -l₂₃-> N₃` is a
  complex, i.e. `range l₁₂ ≤ ker l₂₃`.
  This is `range_le_ker_of_exact_rTensor`.
- Then in `rTensor_reflects_exact`, we show `ker l₂₃ = range l₁₂` by considering the cohomology
  `ker l₂₃ ⧸ range l₁₂`.
This shows that when `M` is faithfully flat, `- ⊗ M` reflects exact sequences. For details, see
comments in the proof. Since `M` is flat, `- ⊗ M` preserves exact sequences.

On the other hand, if `- ⊗ M` preserves and reflects exact sequences, then `M` is faithfully flat.
- `M` is flat because `- ⊗ M` preserves exact sequences.
- We need to show that if `N ⊗ M = 0` then `N = 0`. Consider the sequence `N -0-> N -0-> 0`. After
  tensoring with `M`, we get `N ⊗ M -0-> N ⊗ M -0-> 0` which is exact because `N ⊗ M = 0`.
  Since `- ⊗ M` reflects exact sequences, `N = 0`.
-/

section arbitrary_universe

variable {N1 : Type*} [AddCommGroup N1] [Module R N1]
variable {N2 : Type*} [AddCommGroup N2] [Module R N2]
variable {N3 : Type*} [AddCommGroup N3] [Module R N3]
variable (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3)

/--
If `M` is faithfully flat, then exactness of `N₁ ⊗ M -> N₂ ⊗ M -> N₃ ⊗ M` implies that the
composition `N₁ -> N₂ -> N₃` is `0`.

Implementation detail, please use `rTensor_reflects_exact` instead.
-/
lemma range_le_ker_of_exact_rTensor [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    LinearMap.range l12 ≤ LinearMap.ker l23 := by
  -- let `n1 ∈ N1`. We need to show `l23 (l12 n1) = 0`. Suppose this is not the case.
  rintro _ ⟨n1, rfl⟩
  rw [LinearMap.mem_ker]
  by_contra! hn1
  -- Let `E` be the submodule spanned by `l23 (l12 n1)`. Then because `l23 (l12 n1) ≠ 0`, we have
  -- `E ≠ 0`.
  let E : Submodule R N3 := Submodule.span R {l23 (l12 n1)}
  have hE : Nontrivial E :=
    ⟨0, ⟨⟨l23 (l12 n1), Submodule.mem_span_singleton_self _⟩, Subtype.coe_ne_coe.1 hn1.symm⟩⟩
  -- Since `N1 ⊗ M -> N2 ⊗ M -> N3 ⊗ M` is exact, we have `l23 (l12 n1) ⊗ₜ m = 0` for all `m : M`.
  have eq1 : ∀ (m : M), l23 (l12 n1) ⊗ₜ[R] m = 0 := fun m ↦
    ex.apply_apply_eq_zero (n1 ⊗ₜ[R] m)
  -- Then `E ⊗ M = 0`. Indeed,
  have eq0 : (⊤ : Submodule R (E ⊗[R] M)) = ⊥ := by
    -- suppose `x ∈ E ⊗ M`. We will show `x = 0`.
    ext x
    simp only [Submodule.mem_top, Submodule.mem_bot, true_iff]
    have mem : x ∈ (⊤ : Submodule R _) := ⟨⟩
    rw [← TensorProduct.span_tmul_eq_top, Submodule.mem_span_set] at mem
    obtain ⟨c, hc, rfl⟩ := mem
    choose b a hy using hc
    let r :  ⦃a : E ⊗[R] M⦄ → a ∈ ↑c.support → R := fun a ha =>
      Submodule.mem_span_singleton.1 (b ha).2 |>.choose
    have hr : ∀ ⦃i : E ⊗[R] M⦄ (hi : i ∈ c.support), b hi =
        r hi • ⟨l23 (l12 n1), Submodule.mem_span_singleton_self _⟩ := fun a ha =>
      Subtype.ext <| Submodule.mem_span_singleton.1 (b ha).2 |>.choose_spec.symm
    -- Since `M` is flat and `E -> N1` is injective, we only need to check that x = 0
    -- in `N1 ⊗ M`. We write `x = ∑ μᵢ • (l23 (l12 n1)) ⊗ mᵢ = ∑ μᵢ • 0 = 0`
    -- (remember `E = span {l23 (l12 n1)}` and `eq1`)
    refine Finset.sum_eq_zero fun i hi => show c i • i = 0 from
      (Module.Flat.rTensor_preserves_injective_linearMap (M := M) E.subtype <|
              Submodule.injective_subtype E) ?_
    rw [← hy hi, hr hi, smul_tmul, map_smul, LinearMap.rTensor_tmul, Submodule.subtype_apply, eq1,
      smul_zero, map_zero]
  have : Subsingleton (E ⊗[R] M) := subsingleton_iff_forall_eq 0 |>.2 fun x =>
    show x ∈ (⊥ : Submodule R _) from eq0 ▸ ⟨⟩
  -- but `E ⊗ M = 0` implies `E = 0` because `M` is faithfully flat and this is a contradiction.
  exact not_subsingleton_iff_nontrivial.2 inferInstance <| fl.rTensor_reflects_triviality R M E

lemma rTensor_reflects_exact [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    Function.Exact l12 l23 := LinearMap.exact_iff.2 <| by
  have complex : LinearMap.range l12 ≤ LinearMap.ker l23 := range_le_ker_of_exact_rTensor R M _ _ ex
  -- By the previous lemma we have that range l12 ≤ ker l23 and hence the quotient
  -- H := ker l23 ⧸ range l12 makes sense.
  -- Hence our goal ker l23 = range l12 follows from the claim that H = 0.
  let H := LinearMap.ker l23 ⧸ LinearMap.range (Submodule.inclusion complex)
  suffices triv_coh : Subsingleton H by
    rw [Submodule.subsingleton_quotient_iff_eq_top, Submodule.range_inclusion,
      Submodule.comap_subtype_eq_top] at triv_coh
    exact le_antisymm triv_coh complex
  -- Since `M` is faithfully flat, we need only to show that `H ⊗ M` is trivial.
  suffices Subsingleton (H ⊗[R] M) from rTensor_reflects_triviality R M H
  let e : H ⊗[R] M ≃ₗ[R] _ := TensorProduct.quotientTensorEquiv _ _
  -- Note that `H ⊗ M` is isomorphic to `ker l12 ⊗ M ⧸ range ((range l12 ⊗ M) -> (ker l23 ⊗ M))`.
  -- So the problem is reduced to proving surjectivity of `range l12 ⊗ M → ker l23 ⊗ M`.
  rw [e.toEquiv.subsingleton_congr, Submodule.subsingleton_quotient_iff_eq_top,
    LinearMap.range_eq_top]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  -- let `x ⊗ m` be an element in `ker l23 ⊗ M`, then `x ⊗ m` is in the kernel of `l23 ⊗ 𝟙M`.
  -- Since `N1 ⊗ M -l12 ⊗ M-> N2 ⊗ M -l23 ⊗ M-> N3 ⊗ M` is exact, we have that `x ⊗ m` is in
  -- the range of `l12 ⊗ 𝟙M`, i.e. `x ⊗ m = (l12 ⊗ 𝟙M) y` for some `y ∈ N1 ⊗ M` as elements of
  -- `N2 ⊗ M`. We need to prove that `x ⊗ m = (l12 ⊗ 𝟙M) y` still holds in `(ker l23) ⊗ M`.
  -- This is okay because `M` is flat and `ker l23 -> N2` is injective.
  | tmul x m =>
    rcases x with ⟨x, (hx : l23 x = 0)⟩
    have mem : x ⊗ₜ[R] m ∈ LinearMap.ker (l23.rTensor M) := by simp [hx]
    rw [LinearMap.exact_iff.1 ex] at mem
    obtain ⟨y, hy⟩ := mem
    refine ⟨LinearMap.rTensor M (LinearMap.rangeRestrict _ ∘ₗ LinearMap.rangeRestrict l12) y,
      Module.Flat.rTensor_preserves_injective_linearMap (LinearMap.ker l23).subtype
      Subtype.val_injective ?_⟩
    simp only [LinearMap.comp_codRestrict, LinearMap.rTensor_tmul, Submodule.coe_subtype, ← hy]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_def, ← LinearMap.rTensor_comp,
      ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.comp_assoc,
      LinearMap.subtype_comp_codRestrict, ← LinearMap.comp_assoc, Submodule.subtype_comp_inclusion,
      LinearMap.subtype_comp_codRestrict]
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, by simp⟩

lemma lTensor_reflects_exact [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.lTensor M) (l23.lTensor M)) :
    Function.Exact l12 l23 :=
  rTensor_reflects_exact R M _ _ <| ex.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.comm _ _ _) (e₂ := TensorProduct.comm _ _ _)
    (e₃ := TensorProduct.comm _ _ _) (by ext; rfl) (by ext; rfl)

@[simp]
lemma rTensor_exact_iff_exact [FaithfullyFlat R M] :
    Function.Exact (l12.rTensor M) (l23.rTensor M) ↔ Function.Exact l12 l23 :=
  ⟨fun ex ↦ rTensor_reflects_exact R M l12 l23 ex, fun e ↦ Module.Flat.rTensor_exact _ e⟩

@[simp]
lemma lTensor_exact_iff_exact [FaithfullyFlat R M] :
    Function.Exact (l12.lTensor M) (l23.lTensor M) ↔ Function.Exact l12 l23 :=
  ⟨fun ex ↦ lTensor_reflects_exact R M l12 l23 ex, fun e ↦ Module.Flat.lTensor_exact _ e⟩

section

variable {N N' : Type*} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
  (f : N →ₗ[R] N')

@[simp]
lemma lTensor_injective_iff_injective [Module.FaithfullyFlat R M] :
    Function.Injective (f.lTensor M) ↔ Function.Injective f := by
  rw [← LinearMap.exact_zero_iff_injective (M ⊗[R] Unit), ← LinearMap.exact_zero_iff_injective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

@[simp]
lemma lTensor_surjective_iff_surjective [Module.FaithfullyFlat R M] :
    Function.Surjective (f.lTensor M) ↔ Function.Surjective f := by
  rw [← LinearMap.exact_zero_iff_surjective (M ⊗[R] Unit),
    ← LinearMap.exact_zero_iff_surjective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

end

end arbitrary_universe

section fixed_universe

lemma iff_exact_iff_rTensor_exact :
    FaithfullyFlat R M ↔
    (∀ {N1 : Type max u v} [AddCommGroup N1] [Module R N1]
      {N2 : Type max u v} [AddCommGroup N2] [Module R N2]
      {N3 : Type max u v} [AddCommGroup N3] [Module R N3]
      (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.rTensor M) (l23.rTensor M)) :=
  ⟨fun fl _ _ _ _ _ _ _ _ _ l12 l23 => (rTensor_exact_iff_exact R M l12 l23).symm, fun iff_exact =>
    iff_flat_and_rTensor_reflects_triviality _ _ |>.2
      ⟨Flat.iff_rTensor_exact.2 <| fun _ _ _ => iff_exact .. |>.1,
    fun N _ _ h => subsingleton_iff_forall_eq 0 |>.2 <| fun y => by
      simpa [eq_comm] using (iff_exact (0 : PUnit →ₗ[R] N) (0 : N →ₗ[R] PUnit) |>.2 fun x => by
        simpa using Subsingleton.elim _ _) y⟩⟩

lemma iff_exact_iff_lTensor_exact :
    FaithfullyFlat R M ↔
    (∀ {N1 : Type max u v} [AddCommGroup N1] [Module R N1]
      {N2 : Type max u v} [AddCommGroup N2] [Module R N2]
      {N3 : Type max u v} [AddCommGroup N3] [Module R N3]
      (l12 : N1 →ₗ[R] N2) (l23 : N2 →ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.lTensor M) (l23.lTensor M)) := by
  simp only [iff_exact_iff_rTensor_exact, LinearMap.rTensor_exact_iff_lTensor_exact]

end fixed_universe

end exact

section linearMap

/-!
### Faithfully flat modules and linear maps

In this section we prove that an `R`-module `M` is faithfully flat iff the following holds:

- `M` is flat
- for any `R`-linear map `f : N → N'`, `f` = 0 iff `f ⊗ 𝟙M = 0` iff `𝟙M ⊗ f = 0`

-/

section arbitrary_universe

/--
If `M` is a faithfully flat module, then for all linear maps `f`, the map `id ⊗ f = 0`, if and only
if `f = 0`. -/
lemma zero_iff_lTensor_zero [h : FaithfullyFlat R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N →ₗ[R] N') :
    f = 0 ↔ LinearMap.lTensor M f = 0 :=
  ⟨fun hf => hf.symm ▸ LinearMap.lTensor_zero M, fun hf => by
    have := lTensor_reflects_exact R M f LinearMap.id (by
      rw [LinearMap.exact_iff, hf, LinearMap.range_zero, LinearMap.ker_eq_bot]
      apply Module.Flat.lTensor_preserves_injective_linearMap
      exact fun _ _ h => h)
    ext x; simpa using this (f x)⟩


/--
If `M` is a faithfully flat module, then for all linear maps `f`, the map `f ⊗ id = 0`, if and only
if `f = 0`. -/
lemma zero_iff_rTensor_zero [h: FaithfullyFlat R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {N' : Type*} [AddCommGroup N'] [Module R N']
    (f : N →ₗ[R] N') :
    f = 0 ↔ LinearMap.rTensor M f = 0 :=
  zero_iff_lTensor_zero R M f |>.trans
  ⟨fun h => by ext n m; exact (TensorProduct.comm R N' M).injective <|
    (by simpa using congr($h (m ⊗ₜ n))), fun h => by
    ext m n; exact (TensorProduct.comm R M N').injective <| (by simpa using congr($h (n ⊗ₜ m)))⟩

/-- If `A` is a faithfully flat `R`-algebra, and `m` is a term of an `R`-module `M`,
then `1 ⊗ₜ[R] m = 0` if and only if `m = 0`. -/
@[simp]
theorem one_tmul_eq_zero_iff {A : Type*} [Ring A] [Algebra R A] [FaithfullyFlat R A] (m : M) :
    (1:A) ⊗ₜ[R] m = 0 ↔ m = 0 := by
  constructor; swap
  · rintro rfl; rw [tmul_zero]
  intro h
  let f : R →ₗ[R] M := (LinearMap.lsmul R M).flip m
  suffices f = 0 by simpa [f] using DFunLike.congr_fun this 1
  rw [Module.FaithfullyFlat.zero_iff_lTensor_zero R A]
  ext a
  apply_fun (a • ·) at h
  rw [smul_zero, smul_tmul', smul_eq_mul, mul_one] at h
  simpa [f]

end arbitrary_universe

section fixed_universe

/--
An `R`-module `M` is faithfully flat iff it is flat and for all linear maps `f`, the map
`id ⊗ f = 0`, if and only if `f = 0`. -/
lemma iff_zero_iff_lTensor_zero :
    FaithfullyFlat R M ↔
    (Module.Flat R M ∧
      (∀ {N : Type max u v} [AddCommGroup N] [Module R N]
        {N' : Type max u v} [AddCommGroup N'] [Module R N']
        (f : N →ₗ[R] N'), f.lTensor M = 0 ↔ f = 0)) :=
  ⟨fun fl => ⟨inferInstance, fun f => zero_iff_lTensor_zero R M f |>.symm⟩,
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
      (∀ {N : Type max u v} [AddCommGroup N] [Module R N]
        {N' : Type max u v} [AddCommGroup N'] [Module R N']
        (f : N →ₗ[R] N'), f.rTensor M = 0 ↔ (f = 0))) :=
  ⟨fun fl => ⟨inferInstance, fun f => zero_iff_rTensor_zero R M f |>.symm⟩,
    fun ⟨flat, Z⟩ => iff_flat_and_rTensor_reflects_triviality R M |>.2 ⟨flat, fun N _ _ _ => by
      have := Z (LinearMap.id : N →ₗ[R] N) |>.1 (by ext; exact Subsingleton.elim _ _)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y => congr($this y)⟩⟩

end fixed_universe

end linearMap

section trans

open TensorProduct LinearMap

variable (R : Type*) [CommRing R]
variable (S : Type*) [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [FaithfullyFlat R S] [FaithfullyFlat S M]

include S in
/-- If `S` is a faithfully flat `R`-algebra, then any faithfully flat `S`-Module is faithfully flat
as an `R`-module. -/
theorem trans : FaithfullyFlat R M := by
  rw [iff_zero_iff_lTensor_zero]
  refine ⟨Module.Flat.trans R S M, @fun N _ _ N' _ _ f => ⟨fun aux => ?_, fun eq => eq ▸ by simp⟩⟩
  rw [zero_iff_lTensor_zero (R:= R) (M := S) f,
    show f.lTensor S = (AlgebraTensorModule.map (A:= S) LinearMap.id f).restrictScalars R by aesop,
    show (0 :  S ⊗[R] N →ₗ[R] S ⊗[R] N') = (0 : S ⊗[R] N →ₗ[S] S ⊗[R] N').restrictScalars R by rfl,
    restrictScalars_inj, zero_iff_lTensor_zero (R:= S) (M := M)]
  ext m n
  apply_fun AlgebraTensorModule.cancelBaseChange R S S M N' using LinearEquiv.injective _
  simpa using congr($aux (m ⊗ₜ[R] n))

end trans

/-- Faithful flatness is preserved by arbitrary base change. -/
instance (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R M] :
    Module.FaithfullyFlat S (S ⊗[R] M) := by
  rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
  refine ⟨inferInstance, fun N _ _ hN ↦ ?_⟩
  let _ : Module R N := Module.compHom N (algebraMap R S)
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r ↦ congrFun rfl
  have := (AlgebraTensorModule.cancelBaseChange R S S N M).symm.subsingleton
  exact FaithfullyFlat.rTensor_reflects_triviality R M N

end FaithfullyFlat

/-- Flat descends along faithfully flat ring maps. -/
lemma Flat.of_flat_tensorProduct (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Module.Flat S (S ⊗[R] M)] : Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  have : Flat R (S ⊗[R] M) := Flat.trans _ S _
  rw [← FaithfullyFlat.lTensor_injective_iff_injective R S]
  have : LinearMap.lTensor S (LinearMap.lTensor M f) =
      (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ LinearMap.lTensor (S ⊗[R] M) f ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap := by
    ext
    simp
  simpa [this] using Flat.lTensor_preserves_injective_linearMap f hf

lemma Flat.iff_flat_tensorProduct (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : Module.Flat S (S ⊗[R] M) ↔ Module.Flat R M :=
  ⟨fun _ ↦ .of_flat_tensorProduct R M S, fun _ ↦ inferInstance⟩

end Module
