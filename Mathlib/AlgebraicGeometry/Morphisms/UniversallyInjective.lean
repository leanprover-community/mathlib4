/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Topology.LocalAtTarget

/-!
# Universally injective morphism

A morphism of schemes `f : X ⟶ Y` is universally injective if `X ×[Y] Y' ⟶ Y'` is injective
for all base changes `Y' ⟶ Y`. This is equivalent to the diagonal morphism being surjective
(`AlgebraicGeometry.UniversallyInjective.iff_diagonal`).

We show that being universally injective is local at the target, and is stable under
compositions and base changes.

We also prove that universally injective is equivalent to being injective with
purely inseparable residue field extensions (`AlgebraicGeometry.universallyInjective_tfae`,
Stacks tag 01S4).

-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open CategoryTheory.MorphismProperty Function

/--
A morphism of schemes `f : X ⟶ Y` is universally injective if the base change `X ×[Y] Y' ⟶ Y'`
along any morphism `Y' ⟶ Y` is injective (on points).
-/
@[mk_iff]
class UniversallyInjective (f : X ⟶ Y) : Prop where
  universally_injective : universally (topologically (Injective ·)) f

theorem Scheme.Hom.injective (f : X ⟶ Y) [UniversallyInjective f] :
    Function.Injective f :=
  UniversallyInjective.universally_injective _ _ _ .of_id_snd

theorem universallyInjective_eq :
    @UniversallyInjective = universally (topologically (Injective ·)) := by
  ext X Y f; rw [universallyInjective_iff]

theorem universallyInjective_eq_diagonal :
    @UniversallyInjective = diagonal @Surjective := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨fun x ↦ ⟨pullback.fst f f x, hf.1 _ _ _ (IsPullback.of_hasPullback f f) ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, pullback.diagonal_fst]
    rfl
  · rw [← universally_eq_iff.mpr (inferInstance : IsStableUnderBaseChange (diagonal @Surjective)),
      universallyInjective_eq]
    apply universally_mono
    intro X Y f hf x₁ x₂ e
    obtain ⟨t, ht₁, ht₂⟩ := Scheme.Pullback.exists_preimage_pullback _ _ e
    obtain ⟨t, rfl⟩ := hf.1 t
    rw [← ht₁, ← ht₂, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.diagonal_fst,
      pullback.diagonal_snd]

theorem UniversallyInjective.iff_diagonal :
    UniversallyInjective f ↔ Surjective (pullback.diagonal f) := by
  rw [universallyInjective_eq_diagonal]; rfl

instance (priority := 900) [Mono f] : UniversallyInjective f :=
  have := (pullback.isIso_diagonal_iff f).mpr inferInstance
  (UniversallyInjective.iff_diagonal f).mpr inferInstance

theorem UniversallyInjective.respectsIso : RespectsIso @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

instance UniversallyInjective.isStableUnderBaseChange :
    IsStableUnderBaseChange @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

instance universallyInjective_isStableUnderComposition :
    IsStableUnderComposition @UniversallyInjective :=
  universallyInjective_eq ▸ inferInstance

instance : MorphismProperty.IsMultiplicative @UniversallyInjective where
  id_mem _ := inferInstance

instance universallyInjective_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget @UniversallyInjective :=
  universallyInjective_eq_diagonal.symm ▸ inferInstance

@[stacks 01S4]
theorem universallyInjective_tfae :
    List.TFAE [
      UniversallyInjective f,
      ∀ (K : Type u) [Field K], Function.Injective (fun g : Spec (.of K) ⟶ X ↦ g ≫ f),
      Function.Injective f ∧
        ∀ x, letI := (f.residueFieldMap x).hom.toAlgebra
        IsPurelyInseparable (Y.residueField (f x)) (X.residueField x),
      Surjective (pullback.diagonal f) ] := by
  tfae_have 1 ↔ 4 := UniversallyInjective.iff_diagonal f
  tfae_have 3 → 2 := by
    intro ⟨h_inj, hf⟩ K _ g₁ g₂ hg
    obtain ⟨e, h⟩ := Scheme.SpecToEquivOfField_eq_iff.mp congr((Y.SpecToEquivOfField K) $(hg))
    apply (X.SpecToEquivOfField K).injective
    simp only [Scheme.SpecToEquivOfField_comp_fst, Scheme.SpecToEquivOfField_comp_snd] at e h
    replace e := h_inj e
    rw [← f.residueFieldMap_congr'_assoc e, CommRingCat.hom_ext_iff] at h
    rw [Scheme.SpecToEquivOfField_eq_iff]
    algebraize [(f.residueFieldMap (g₁ (IsLocalRing.closedPoint K))).hom]
    exact ⟨e, CommRingCat.hom_ext <| @IsPurelyInseparable.injective_comp_algebraMap _ _ _ _ _
      (hf (g₁ (IsLocalRing.closedPoint K))) K _ _ _ _ h⟩
  tfae_have 2 → 4 := fun h ↦ by
    rw [surjective_iff]
    intro z
    let φ := (pullback f f).fromSpecResidueField z
    have hφ₁ : φ ≫ pullback.fst f f = φ ≫ pullback.snd f f :=
      h ((pullback f f).residueField z) (by simp [pullback.condition])
    have hφ₂ : φ = (φ ≫ pullback.fst f f) ≫ pullback.diagonal f :=
      pullback.hom_ext (by simp) (by simp [← hφ₁])
    refine ⟨(φ ≫ pullback.fst f f) (IsLocalRing.closedPoint _), ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hφ₂, Scheme.fromSpecResidueField_apply]
  tfae_have 4 → 3 := fun hf ↦ by
    refine ⟨@f.injective _ _ (tfae_1_iff_4.mpr hf), ?_⟩
    rw [surjective_iff] at hf
    intro x
    algebraize [(f.residueFieldMap x).hom]
    rw [isPurelyInseparable_iff_finSepDegree_eq_one, Field.finSepDegree, Nat.card_eq_one_iff_unique,
      subsingleton_iff]
    refine ⟨?_, inferInstance⟩
    intro σ₁ σ₂
    apply AlgHom.coe_ringHom_injective
    let g₁ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₁.toRingHom⟩
    let g₂ := (X.SpecToEquivOfField _).symm ⟨_, CommRingCat.ofHom σ₂.toRingHom⟩
    suffices X.SpecToEquivOfField _ g₁ = X.SpecToEquivOfField _ g₂ by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
      simpa using congr($(this).2.hom)
    let q := pullback.lift (f := f) (g := f) g₁ g₂ <| by
      simp only [g₁, g₂, Scheme.SpecToEquivOfField_symm_apply, AlgHom.toRingHom_eq_coe,
        Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField x, ← Spec.map_comp_assoc]
      congr 2
      ext a
      simp only [CommRingCat.hom_comp, RingHom.comp_apply]
      exact (AlgHom.commutes σ₁ a).trans (AlgHom.commutes σ₂ a).symm
    have q_fst : q ≫ pullback.fst f f = g₁ := pullback.lift_fst _ _ _
    have q_snd : q ≫ pullback.snd f f = g₂ := pullback.lift_snd _ _ _
    rw [Scheme.SpecToEquivOfField_eq_iff, ← q_fst, ← q_snd]
    obtain ⟨u, hu⟩ := hf (q (IsLocalRing.closedPoint _))
    have hux : u = x := by
      have := congr(pullback.fst f f $(hu))
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply] at this
      simpa [q_fst, g₁] using this
    refine ⟨by simp [g₁, g₂, q_fst, q_snd], ?_⟩
    simp_rw [Scheme.SpecToEquivOfField_comp_snd, Scheme.SpecToEquivOfField_apply_fst,
      Scheme.SpecToEquivOfField_apply_snd, Scheme.Hom.comp_base, TopCat.hom_comp,
      ContinuousMap.comp_apply, ← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.residueFieldCongr (hux ▸ hu).symm).hom]
    have : Mono (Scheme.Hom.residueFieldMap (pullback.diagonal f) x) :=
      ConcreteCategory.mono_of_injective _ (RingHom.injective _)
    simp [← cancel_mono ((pullback.diagonal f).residueFieldMap x), ← Scheme.residueFieldMap_comp,
      (pullback.fst f f).residueFieldMap_congr', (pullback.snd f f).residueFieldMap_congr'_assoc,
      Scheme.Hom.residueFieldMap_congr (pullback.diagonal_snd f),
      Scheme.Hom.residueFieldMap_congr (pullback.diagonal_fst f)]
  tfae_finish

end AlgebraicGeometry
