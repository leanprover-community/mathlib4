/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.LightProfinite.Limits
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
/-!

# Effective epimorphisms in `LightProfinite`

This file proves that `EffectiveEpi`, `Epi` and `Surjective` are all equivalent in `LightProfinite`.
As a consequence we prove that `LightProfinite` is `Preregular`. It follows from the constructions
in `LightProfinite/Limits.lean` that `LightProfinite` is `FinitaryExtensive`. Together this implies
that it is `Precoherent`.

-/

universe u

/-
Previously, this had accidentally been made a global instance,
and we now turn it on locally when convenient.
-/
attribute [local instance] CategoryTheory.ConcreteCategory.instFunLike

open CategoryTheory Limits

namespace LightProfinite

/--
Implementation: if `π` is a surjective morphism in `LightProfinite`, then it is an effective epi.
The theorem `LightProfinite.effectiveEpi_iff_surjective` should be used instead.
-/
noncomputable
def EffectiveEpi.struct {B X : LightProfinite.{u}} (π : X ⟶ B) (hπ : Function.Surjective π) :
    EffectiveEpiStruct π where
  desc e h := (QuotientMap.of_surjective_continuous hπ π.continuous).lift e fun a b hab ↦
    DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a
  fac e h := ((QuotientMap.of_surjective_continuous hπ π.continuous).lift_comp e
    fun a b hab ↦ DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
    (by ext; exact hab)) a)
  uniq e h g hm := by
    suffices g = (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv ⟨e,
      fun a b hab ↦
        DFunLike.congr_fun (h ⟨fun _ ↦ a, continuous_const⟩ ⟨fun _ ↦ b, continuous_const⟩
        (by ext; exact hab)) a⟩ by assumption
    rw [← Equiv.symm_apply_eq (QuotientMap.of_surjective_continuous hπ π.continuous).liftEquiv]
    ext
    simp only [QuotientMap.liftEquiv_symm_apply_coe, ContinuousMap.comp_apply, ← hm]
    rfl

theorem epi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.continuous).isClosed
    have hyU : y ∈ Cᶜ := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : Cᶜ ∈ nhds y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
    classical
      let Z := (FintypeCat.of (ULift.{u} <| Fin 2)).toLightProfinite
      let g : Y ⟶ Z := ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        apply ULift.ext
        dsimp [g, LocallyConstant.ofIsClopen]
        erw [comp_apply, ContinuousMap.coe_mk, comp_apply, ContinuousMap.coe_mk,
          Function.comp_apply, if_neg]
        refine mt (fun α => hVU α) ?_
        simp only [C, Set.mem_compl_iff, Set.mem_range, not_exists,
          not_forall, not_not]
        exact ⟨x, rfl⟩
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      erw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget LightProfinite).epi_of_epi_map

theorem effectiveEpi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨EffectiveEpi.struct f h⟩⟩⟩
  rw [← epi_iff_surjective]
  infer_instance

instance : Preregular LightProfinite where
  exists_fac := by
    intro X Y Z f π hπ
    refine ⟨pullback f π, pullback.fst f π, ?_, pullback.snd f π, (pullback.condition _ _).symm⟩
    rw [effectiveEpi_iff_surjective] at hπ ⊢
    intro y
    obtain ⟨z,hz⟩ := hπ (f y)
    exact ⟨⟨(y, z), hz.symm⟩, rfl⟩

instance : FinitaryExtensive LightProfinite :=
  finitaryExtensive_of_preserves_and_reflects lightToProfinite

-- Was an `example`, but that made the linter complain about unused imports
instance : Precoherent LightProfinite := inferInstance

end LightProfinite
