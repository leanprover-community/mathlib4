/-
Copyright (c) 2026 Dominic Steinitz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominic Steinitz
-/

import Mathlib
import Mathlib.Geometry.Manifold.Algebra.FakeFormIII
import Mathlib.Geometry.Manifold.Algebra.UnitsMFDeriv

/-!
# The Frame Bundle

The frame bundle of a smooth manifold `M` is the principal `GL(E)`-bundle whose fiber
over each point `x ∈ M` consists of all invertible linear maps `E → T_xM`. It is
constructed as an open subset of the Hom bundle `Hom(Trivial M E, TM)`.

## Main definitions

* `FrameBundle I M`: The frame bundle as an open subset of the Hom bundle
* `FrameBundle.isPrincipalBundle`: The frame bundle is a principal `GL(E)`-bundle

## References

* Tu, *Differential Geometry*, §13
-/

open Bundle Set IsManifold OpenPartialHomeomorph ContinuousLinearMap RightActions FiberBundle
open scoped Manifold Topology Bundle ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

omit [CompleteSpace 𝕜] [CompleteSpace E] in
lemma isUnit_comp_iff_of_isUnit {D : E →L[𝕜] E} (hD : IsUnit D) (A : E →L[𝕜] E) :
    IsUnit (D.comp A) ↔ IsUnit A := by
  constructor <;> intro h;
  · obtain ⟨ u, hu ⟩ := h;
    obtain ⟨ v, hv ⟩ := hD;
    refine ⟨v⁻¹ * u, ?_⟩
    simp +decide only [Units.val_mul, hu]
    exact (Units.inv_mul_eq_iff_eq_mul v).mpr
      (congrFun (congrArg ContinuousLinearMap.comp (id (Eq.symm hv))) A)
  · exact hD.mul h

open Bundle FiberBundle

omit [CompleteSpace 𝕜] [CompleteSpace E] in
lemma isUnit_conj_iff (Φ : E ≃L[𝕜] E) (f : E →L[𝕜] E) :
    IsUnit (Φ.toContinuousLinearMap ∘L f ∘L Φ.symm.toContinuousLinearMap) ↔ IsUnit f := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨⟨f, Φ.symm.toContinuousLinearMap ∘L u.inv ∘L Φ.toContinuousLinearMap, ?_, ?_⟩, rfl⟩
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.one_apply]
      have hf : f = Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap := by
        have : Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap =
               Φ.symm.toContinuousLinearMap ∘L
               (Φ.toContinuousLinearMap ∘L f ∘L Φ.symm.toContinuousLinearMap) ∘L
               Φ.toContinuousLinearMap := by
          rw [← hu]
        rw [this]
        ext w
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      rw [hf]
      simp only [Units.inv_eq_val_inv, ContinuousLinearMap.coe_comp',
                 ContinuousLinearEquiv.coe_coe, Function.comp_apply,
                 ContinuousLinearEquiv.apply_symm_apply]
      have : u.val (u.inv (Φ v)) = Φ v := by
        have := congr_fun (congr_arg DFunLike.coe u.val_inv) (Φ v)
        exact this
      have bar : (↑u⁻¹ : E →L[𝕜] E) = u.inv :=
        Eq.symm (Units.inv_eq_val_inv u)
      rw [bar, this]
      exact ContinuousLinearEquiv.symm_apply_apply Φ v
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.one_apply]
      have hf : f = Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap := by
        have : Φ.symm.toContinuousLinearMap ∘L u.val ∘L Φ.toContinuousLinearMap =
               Φ.symm.toContinuousLinearMap ∘L
               (Φ.toContinuousLinearMap ∘L f ∘L Φ.symm.toContinuousLinearMap)
               ∘L Φ.toContinuousLinearMap := by
          rw [← hu]
        rw [this]
        ext w
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      rw [hf]
      simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe,
                 Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
      have : u.inv (u.val (Φ v)) = Φ v := by
        exact congr_fun (congr_arg DFunLike.coe u.inv_val) (Φ v)
      rw [this]
      exact ContinuousLinearEquiv.symm_apply_apply Φ v
  · rintro ⟨u, hu⟩
    refine ⟨⟨Φ.toContinuousLinearMap ∘L u ∘L Φ.symm.toContinuousLinearMap,
             Φ.toContinuousLinearMap ∘L u.inv ∘L Φ.symm.toContinuousLinearMap, ?_, ?_⟩,
            by simp [← hu]⟩
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe]
      have : u.val (u.inv (Φ.symm v)) = Φ.symm v := by
        have := congr_fun (congr_arg DFunLike.coe u.val_inv) (Φ.symm v)
        have foo := this
        exact this
      simp only [Units.inv_eq_val_inv, ContinuousLinearEquiv.symm_apply_apply,
                 ContinuousLinearMap.one_apply]
      have bar : (↑u⁻¹ : E →L[𝕜] E) = u.inv := by
        exact Eq.symm (Units.inv_eq_val_inv u)
      rw [bar, this]
      exact ContinuousLinearEquiv.apply_symm_apply Φ v
    · simp only [← ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
                 ContinuousLinearEquiv.coe_coe]
      have : u.inv (u.val (Φ.symm v)) = Φ.symm v := by
        have := congr_fun (congr_arg DFunLike.coe u.inv_val) (Φ.symm v)
        have foo := this
        exact this
      simp only [Units.inv_eq_val_inv, ContinuousLinearEquiv.symm_apply_apply,
                 ContinuousLinearMap.one_apply]
      have bar : (↑u⁻¹ : E →L[𝕜] E) = u.inv := by
        exact Eq.symm (Units.inv_eq_val_inv u)
      rw [bar]
      rw [this]
      exact ContinuousLinearEquiv.apply_symm_apply Φ v

instance : ∀ (p : TotalSpace (E →L[𝕜] E) fun x ↦ Trivial M E x →L[𝕜] TangentSpace I x),
  Monoid (Trivial M E p.proj →L[𝕜] TangentSpace I p.proj) := by
    intro p
    change Monoid (E →L[𝕜] E)
    haveI : Monoid (E →L[𝕜] E) := inferInstance
    exact ContinuousLinearMap.monoidWithZero.toMonoid

instance : ∀ (p : TotalSpace (E →L[𝕜] E) fun (x : M) ↦ TangentSpace I x →L[𝕜] E),
  Monoid (TangentSpace I p.proj →L[𝕜] E) := by
  intro p
  change Monoid (E →L[𝕜] E)
  haveI : Monoid (E →L[𝕜] E) := inferInstance
  exact ContinuousLinearMap.monoidWithZero.toMonoid

/-- The frame bundle of a smooth manifold `M` is the open subset of the
    Hom bundle `Hom(TM, TM)` consisting of invertible elements. -/
def FrameBundle (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [CompleteSpace E] : TopologicalSpace.Opens
    (TotalSpace (E →L[𝕜] E) (fun x : M => Bundle.Trivial M E x →L[𝕜] TangentSpace I x)) where
  carrier := {p | IsUnit p.2}
  is_open' := by
    apply isOpen_iff_forall_mem_open.mpr
    intro p hp
    set e := trivializationAt (E →L[𝕜] E)
      (fun x : M => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) p.proj
    have hpe : p ∈ e.source := mem_trivializationAt_proj_source
    refine ⟨e.source ∩ e ⁻¹' (e.baseSet ×ˢ {f : E →L[𝕜] E | IsUnit f}),
            fun q ⟨hqs, hq⟩ => ?_,
            e.continuousOn.isOpen_inter_preimage e.open_source (e.open_baseSet.prod Units.isOpen),
            ⟨hpe, ?_⟩⟩
    · simp only [Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq] at hq
      have hb := e.mem_source.mp hqs
      rw [hom_trivializationAt_apply (σ := RingHom.id 𝕜)] at hq
      have hb_triv : q.proj ∈ (trivializationAt E (Bundle.Trivial M E) p.proj).baseSet := by
        simp
      have hb_tan : q.proj ∈ (trivializationAt E (TangentSpace I) p.proj).baseSet := by
        have hbs := hom_trivializationAt_baseSet (F₁ := E) (F₂ := E) (σ := RingHom.id 𝕜)
          (E₁ := Bundle.Trivial M E) (E₂ := TangentSpace I) p.proj
        rw [hbs] at hb; exact hb.2
      rw [ContinuousLinearMap.inCoordinates_eq hb_triv hb_tan] at hq
      have htriv_symm : (Trivialization.continuousLinearEquivAt 𝕜
          (trivializationAt E (Bundle.Trivial M E) p.proj) q.proj hb_triv).symm =
          ContinuousLinearEquiv.refl 𝕜 E := by
        simp [Bundle.Trivial.continuousLinearEquivAt_trivialization,
              ContinuousLinearEquiv.refl_symm]
      simp only [htriv_symm, ContinuousLinearEquiv.coe_refl,
                 ContinuousLinearMap.comp_id] at hq
      have htan_unit : IsUnit
          ((Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).toContinuousLinearMap) :=
        ⟨⟨(Trivialization.continuousLinearEquivAt 𝕜
              (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).toContinuousLinearMap,
          (Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm.toContinuousLinearMap,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan)
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).apply_symm_apply x,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan) x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) q.proj hb_tan).symm_apply_apply x⟩,
          rfl⟩
      letI : NormedAddCommGroup (TangentSpace I q.proj) := inferInstanceAs (NormedAddCommGroup E)
      letI : NormedSpace 𝕜 (TangentSpace I q.proj) := inferInstanceAs (NormedSpace 𝕜 E)
      exact (isUnit_comp_iff_of_isUnit htan_unit q.2).mp hq.2
    · simp only [Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]
      have hb := e.mem_source.mp hpe
      rw [hom_trivializationAt_apply (σ := RingHom.id 𝕜)]
      have hb_triv : p.proj ∈ (trivializationAt E (Bundle.Trivial M E) p.proj).baseSet := by
        simp
      have hb_tan : p.proj ∈ (trivializationAt E (TangentSpace I) p.proj).baseSet := by
        have hbs := hom_trivializationAt_baseSet (F₁ := E) (F₂ := E) (σ := RingHom.id 𝕜)
          (E₁ := Bundle.Trivial M E) (E₂ := TangentSpace I) p.proj
        rw [hbs] at hb; exact hb.2
      refine ⟨hb, ?_⟩
      rw [ContinuousLinearMap.inCoordinates_eq hb_triv hb_tan]
      have htriv_symm : (Trivialization.continuousLinearEquivAt 𝕜
          (trivializationAt E (Bundle.Trivial M E) p.proj) p.proj hb_triv).symm =
          ContinuousLinearEquiv.refl 𝕜 E := by
        simp [Bundle.Trivial.continuousLinearEquivAt_trivialization,
              ContinuousLinearEquiv.refl_symm]
      simp only [htriv_symm, ContinuousLinearEquiv.coe_refl,
                 ContinuousLinearMap.comp_id]
      have htan_unit : IsUnit
          ((Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).toContinuousLinearMap) :=
        ⟨⟨(Trivialization.continuousLinearEquivAt 𝕜
              (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).toContinuousLinearMap,
          (Trivialization.continuousLinearEquivAt 𝕜
            (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm.toContinuousLinearMap,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan)
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).apply_symm_apply x,
           by ext x
              change (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm
                ((Trivialization.continuousLinearEquivAt 𝕜
                  (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan) x) = x
              exact (Trivialization.continuousLinearEquivAt 𝕜
                (trivializationAt E (TangentSpace I) p.proj) p.proj hb_tan).symm_apply_apply x⟩,
          rfl⟩
      letI : NormedAddCommGroup (TangentSpace I p.proj) := inferInstanceAs (NormedAddCommGroup E)
      letI : NormedSpace 𝕜 (TangentSpace I p.proj) := inferInstanceAs (NormedSpace 𝕜 E)
      exact (isUnit_comp_iff_of_isUnit htan_unit p.2).mpr hp

instance [IsManifold I ∞ M] [CompleteSpace E] :
    IsManifold (I.prod 𝓘(𝕜, E →L[𝕜] E)) ∞ ↥(FrameBundle I M) := inferInstance

instance [CompleteSpace E] : LieGroup (modelWithCornersSelf 𝕜 (E →L[𝕜] E)) ∞
    (Units (E →L[𝕜] E)) := inferInstance

omit [CompleteSpace E] [CompleteSpace 𝕜] in
lemma tangentBundleCore_coordChange_isUnit (i j : atlas H M)
    (x : M) (hx : x ∈ i.1.source ∩ j.1.source) :
    IsUnit ((tangentBundleCore I M).coordChange i j x) := by
  have h_inv : (tangentBundleCore I M).coordChange j i x ∘L
    (tangentBundleCore I M).coordChange i j x = ContinuousLinearMap.id 𝕜 E := by
    have := ( tangentBundleCore I M ).coordChange_comp i j i x;
    ext v; exact (by
    convert this ⟨ ⟨ hx.1, hx.2 ⟩, hx.1 ⟩ v using 1;
    exact Eq.symm ( ( tangentBundleCore I M ).coordChange_self i x hx.1 v ))
  have h_inv : (tangentBundleCore I M).coordChange i j x ∘L
  (tangentBundleCore I M).coordChange j i x = ContinuousLinearMap.id 𝕜 E := by
    have := ( tangentBundleCore I M ).coordChange_comp j i j x ⟨ ⟨ hx.2, hx.1 ⟩, hx.2 ⟩;
    exact ContinuousLinearMap.ext fun v => by
     simpa using this v |> Eq.trans <| ( tangentBundleCore I M ).coordChange_self j x hx.2 v
  exact ⟨ ⟨ _, _, h_inv, by assumption ⟩, rfl ⟩

@[reducible, nolint unusedArguments]
def FrameSpace (_I : ModelWithCorners 𝕜 E H) (_M : Type*) [TopologicalSpace _M] [ChartedSpace H _M]
    [IsManifold _I 1 _M] (_ : _M) : Type _ := (E →L[𝕜] E)ˣ

noncomputable def frameBundleFiberBundleCore [CompleteSpace 𝕜] :
    FiberBundleCore (atlas H M) M (E →L[𝕜] E)ˣ where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x g := by
    by_cases hx : x ∈ i.1.source ∩ j.1.source
    · have hunit : IsUnit ((tangentBundleCore I M).coordChange i j x) :=
        tangentBundleCore_coordChange_isUnit i j x hx
      exact (hunit.unit * g)
    · exact g
  coordChange_self i x hx g := by
    simp only [show x ∈ i.1.source ∩ i.1.source from ⟨hx, hx⟩, dif_pos]
    have key := (tangentBundleCore I M).coordChange_self i x hx
    simp only at key
    ext v
    have bar : ((tangentBundleCore I M).coordChange i i x) (g.val v) = g.val v := key (g.val v)
    simp only [tangentBundleCore_coordChange, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, toFun_eq_coe, PartialEquiv.coe_trans_symm, coe_coe_symm,
      ModelWithCorners.toPartialEquiv_coe_symm, Function.comp_apply] at bar
    exact bar
  continuousOn_coordChange i j := by
    rw [(Units.isOpenEmbedding_val (R := E →L[𝕜] E)).isEmbedding.continuousOn_iff]
    apply ContinuousOn.congr
    · change ContinuousOn
        (fun p : M × (E →L[𝕜] E)ˣ => (tangentBundleCore I M).coordChange i j p.1 ∘L p.2.val)
        ((i.1.source ∩ j.1.source) ×ˢ univ)
      apply ContinuousOn.clm_comp
      · apply ((tangentBundleCore I M).continuousOn_coordChange i j).comp
          continuousOn_fst
        intro p hp
        exact hp.1
      · exact Units.continuous_val.comp_continuousOn continuousOn_snd
    · intro p hp
      simp only [Set.mem_prod, Set.mem_univ, and_true] at hp
      simp only [Function.comp, dif_pos hp]
      simp only [Units.val_mul, IsUnit.unit_spec]
      exact mul_def ((tangentBundleCore I M).coordChange i j p.1) ↑p.2
  coordChange_comp i j k x hx g := by
    ext v
    have hjk : x ∈ (j.1).source ∩ (k.1).source := ⟨hx.1.2, hx.2⟩
    have hik : x ∈ (i.1).source ∩ (k.1).source := ⟨hx.1.1, hx.2⟩
    have hij : x ∈ (i.1).source ∩ (j.1).source := ⟨hx.1.1, hx.1.2⟩
    simp only [hij, hjk, hik, dif_pos, IsUnit.unit_spec, Units.val_mul]
    have key := (tangentBundleCore I M).coordChange_comp i j k x
      ⟨⟨hx.1.1, hx.1.2⟩, hx.2⟩ (g.val v)
    exact LinearMap.mem_eqLocus.mp key

noncomputable instance frameBundleTotalSpaceTopology [CompleteSpace 𝕜] :
    TopologicalSpace (Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M)) :=
  (frameBundleFiberBundleCore (I := I) (M := M)).toTopologicalSpace

noncomputable instance frameBundleFiberBundle [CompleteSpace 𝕜] :
    FiberBundle (E →L[𝕜] E)ˣ (FrameSpace I M) :=
  frameBundleFiberBundleCore.fiberBundle

noncomputable def frameBundleProj [IsManifold I ∞ M] :
    ↥(FrameBundle I M) → M :=
  fun p => p.1.proj

noncomputable instance frameBundleMulAction [IsManifold I ∞ M] :
    MulAction (MulOpposite (Units (E →L[𝕜] E))) ↥(FrameBundle I M) where
  smul g p :=
    ⟨⟨p.1.proj, p.1.snd.comp (MulOpposite.unop g).val⟩,
     (show IsUnit p.1.snd from p.2).mul (MulOpposite.unop g).isUnit⟩
  one_smul := fun p => by
    apply Subtype.ext; apply TotalSpace.ext
    · rfl
    · exact heq_of_eq (ContinuousLinearMap.comp_id _)
  mul_smul := fun g h p => by
    apply Subtype.ext; apply TotalSpace.ext
    · rfl
    · exact heq_of_eq (ContinuousLinearMap.comp_assoc _ _ _).symm

omit [CompleteSpace 𝕜] in
omit [IsManifold I 1 M] in
lemma frameBundleAction_respects_fibres [IsManifold I ∞ M]
    (p : ↥(FrameBundle I M)) (g : Units (E →L[𝕜] E)) :
    frameBundleProj (p <• g) = frameBundleProj p := by
  rfl

set_option maxHeartbeats 800000 in
-- who knows
omit [CompleteSpace 𝕜] in
lemma frameBundleAction_free [IsManifold I ∞ M]
    (p : ↥(FrameBundle I M)) :
    MulAction.stabilizer (MulOpposite (Units (E →L[𝕜] E))) p = ⊥ := by
  apply eq_bot_iff.mpr _
  intro g hg
  obtain ⟨g', hg'⟩ : ∃ g' : (E →L[𝕜] E)ˣ, g = MulOpposite.op g' := ⟨_, rfl⟩
  have h_inv : p.1.2 ∘L (g' : E →L[𝕜] E) = p.1.2 := by
    convert congr_arg Subtype.val hg using 1
    constructor <;> intro h <;> ext <;>simp_all +decide only [MulAction.mem_stabilizer_iff]
    · grind +locals
    · convert congr_arg (fun q : ↥(FrameBundle I M) => q.val.2 ‹_›) hg using 1
  have h_inv : (g' : E →L[𝕜] E) = 1 := by
    have h_inj : Function.Injective p.1.2 :=
      p.2.exists_left_inv.elim fun x hx =>
        Function.LeftInverse.injective (fun y => by simpa using congr_arg (fun f => f y) hx)
    exact ContinuousLinearMap.ext fun x => h_inj <| by
      simpa using congr_arg (fun f => f x) ‹p.1.snd ∘L ↑g' = p.1.snd›
  cases g'; aesop

-- Complete replacement for `section Foo` ... `end Foo` in FrameBundle.lean
--
-- Drop the `section Foo` / `end Foo` block entirely and replace with this.
-- This goes AFTER the existing `frameBundleFiberBundle` instance (line ~331)
-- and BEFORE the final `#check` line.

noncomputable section FrameBundlePrincipal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

-- ── Homeomorphism between the two total space representations ────────────────────────────────

def frameBundleEquiv [IsManifold I ∞ M] :
    ↥(FrameBundle I M) ≃ Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M) where
  toFun p := ⟨p.1.proj, p.2.unit⟩
  invFun q := ⟨⟨q.proj, q.snd.val⟩, q.snd.isUnit⟩
  left_inv p := by
    apply Subtype.ext; apply Bundle.TotalSpace.ext
    · rfl
    · simp [IsUnit.unit_spec]
  right_inv q := by
    apply Bundle.TotalSpace.ext
    · rfl
    · simp

lemma frameBundleFiberBundleCore_coordChange_val (i j : atlas H M) (x : M)
    (hx : x ∈ i.1.source ∩ j.1.source) (g : (E →L[𝕜] E)ˣ) :
    ((frameBundleFiberBundleCore (I := I) (M := M)).coordChange i j x g).val =
      (tangentBundleCore I M).coordChange i j x ∘L g.val := by
  unfold frameBundleFiberBundleCore; aesop

omit [CompleteSpace E] [CompleteSpace 𝕜] in
lemma tangentBundleCore_coordChange_comp_inv (i j : atlas H M) (x : M)
    (hx : x ∈ i.1.source ∩ j.1.source) :
    (tangentBundleCore I M).coordChange j i x ∘L (tangentBundleCore I M).coordChange i j x =
      ContinuousLinearMap.id 𝕜 E := by
  have := (tangentBundleCore_coordChange_isUnit (I := I) (M := M) i j x hx)
  obtain ⟨u, hu⟩ := this.exists_left_inv
  have := (tangentBundleCore I M).coordChange_comp j i j x
  simp_all +decide [ContinuousLinearMap.ext_iff]
  have := (tangentBundleCore I M).coordChange_self j x hx.2
  simp_all +decide []
  grind

set_option linter.style.multiGoal false in
lemma intertwining_forward [IsManifold I ∞ M]
    (q : Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M)) :
    let Z := frameBundleFiberBundleCore (I := I) (M := M)
    let i := Z.indexAt q.proj
    let e := Z.localTriv i
    let e' := trivializationAt (E →L[𝕜] E)
      (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) q.proj
    ∀ᶠ p in 𝓝 (e q), (e' ⟨p.1, (Z.coordChange i (Z.indexAt p.1) p.1 p.2).val⟩) =
      (p.1, p.2.val) := by
  apply Filter.eventually_of_mem (IsOpen.mem_nhds _ _) _
  exact (frameBundleFiberBundleCore (I := I) (M := M)).baseSet
    (frameBundleFiberBundleCore (I := I) (M := M) |>.indexAt q.proj) ×ˢ Set.univ
  · exact IsOpen.prod (frameBundleFiberBundleCore (I := I) (M := M) |>.isOpen_baseSet _) isOpen_univ
  · simp +decide []
  · simp +decide only [FiberBundleCore.baseSet_at, FiberBundleCore.proj,
      FiberBundleCore.localTrivAt_def, Set.mem_prod, Set.mem_univ, and_true,
      hom_trivializationAt_apply, Prod.mk.injEq, true_and, Prod.forall]
    intro x y hx
    rw [inCoordinates_eq]
    simp +decide only [Trivial.fiberBundle_trivializationAt',
      Trivial.continuousLinearEquivAt_trivialization, ContinuousLinearEquiv.refl_symm,
      ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.comp_id]
    any_goals first | trivial | exact hx
    rw [frameBundleFiberBundleCore_coordChange_val]
    · convert tangentBundleCore_coordChange_comp_inv
          (frameBundleFiberBundleCore (I := I) (M := M) |>.indexAt q.proj)
          (frameBundleFiberBundleCore (I := I) (M := M) |>.indexAt x) x _ |>
            fun h => congr_arg (fun f => f.comp (y : E →L[𝕜] E)) h using 1
      exact ⟨hx, mem_chart_source H x⟩
    · exact ⟨hx, mem_chart_source H x⟩

lemma continuous_toFrameBundleCore [IsManifold I ∞ M] :
    Continuous (fun q : Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M) =>
      (⟨⟨q.proj, q.snd.val⟩, q.snd.isUnit⟩ : ↥(FrameBundle I M))) := by
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro q
  set Z := frameBundleFiberBundleCore (I := I) (M := M)
  set i := Z.indexAt q.proj
  set e := Z.localTriv i
  set e' := trivializationAt (E →L[𝕜] E)
    (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) q.proj
  have h_cont : ContinuousAt (fun p : M × (E →L[𝕜] E)ˣ =>
      (e' ⟨p.1, (Z.coordChange i (Z.indexAt p.1) p.1 p.2).val⟩)) (e q) := by
    have h_cont : ContinuousAt (fun p : M × (E →L[𝕜] E)ˣ => (p.1, p.2.val)) (e q) :=
      ContinuousAt.prodMk continuousAt_fst
        (Units.continuous_val.continuousAt.comp continuousAt_snd)
    exact h_cont.congr (by filter_upwards [intertwining_forward q] with p hp; aesop)
  convert e.continuousAt_of_comp_right _ (e'.continuousAt_of_comp_left _ _ _) using 1
  · exact Z.mem_baseSet_at q.proj
  · convert continuousAt_fst using 1
  · exact FiberBundle.mem_baseSet_trivializationAt' q.proj
  · convert h_cont using 1

set_option linter.style.multiGoal false in
lemma intertwining_reverse [IsManifold I ∞ M]
    (p : ↥(FrameBundle I M)) :
    let Z := frameBundleFiberBundleCore (I := I) (M := M)
    let i := Z.indexAt p.1.proj
    let e := Z.localTriv i
    let e' := trivializationAt (E →L[𝕜] E)
      (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) p.1.proj
    ∀ᶠ p' in 𝓝 p, Prod.map id Units.val (e ⟨p'.1.proj, p'.2.unit⟩) = e' p'.1 := by
  apply Filter.eventually_of_mem (IsOpen.mem_nhds _ _) _
  exact {x : ↥(FrameBundle I M) | (x : Bundle.TotalSpace (E →L[𝕜] E)
    fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x).proj ∈ (chartAt H p.1.proj).source}
  · have h_proj_cont : Continuous (fun x : Bundle.TotalSpace (E →L[𝕜] E)
      (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) => x.proj) :=
      FiberBundle.continuous_proj (E →L[𝕜] E)
        (fun x : M => Bundle.Trivial M E x →L[𝕜] TangentSpace I x)
    exact h_proj_cont.isOpen_preimage _ (chartAt H p.1.proj |>.open_source) |>
      IsOpen.preimage continuous_subtype_val
  · exact mem_chart_source _ _
  · simp +decide only [Set.mem_setOf_eq, frameBundleFiberBundleCore, Set.mem_inter_iff,
      tangentBundleCore_coordChange, OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
      ModelWithCorners.toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe,
      PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.coe_coe_symm,
      ModelWithCorners.toPartialEquiv_coe_symm, Function.comp_apply,
      FiberBundleCore.proj, Subtype.forall]
    intro a ha ha'
    change (a.proj, ((frameBundleFiberBundleCore (I := I) (M := M)).coordChange
        (achart H a.proj) (achart H p.1.proj) a.proj ha.unit).val)
      = (trivializationAt (E →L[𝕜] E)
          (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) p.1.proj) a
    rw [frameBundleFiberBundleCore_coordChange_val (achart H a.proj) (achart H p.1.proj) a.proj
        ⟨mem_chart_source H a.proj, ha'⟩ ha.unit, ha.unit_spec,
      hom_trivializationAt_apply (σ := RingHom.id 𝕜)]
    rw [inCoordinates_eq]
    all_goals simp_all +decide [trivializationAt]
    congr

lemma continuousAt_of_prodMap_isEmbedding {α β γ δ : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
    {f : α → β × γ} {g : γ → δ} {x : α}
    (hg : Topology.IsEmbedding g) (hf : ContinuousAt (Prod.map id g ∘ f) x) :
    ContinuousAt f x := by
  rw [ContinuousAt] at *
  rw [nhds_prod_eq, Filter.tendsto_prod_iff'] at *
  exact ⟨hf.1, hg.isInducing.tendsto_nhds_iff.mpr hf.2⟩

lemma continuous_fromFrameBundleCore [IsManifold I ∞ M] :
    Continuous (fun p : ↥(FrameBundle I M) =>
      (⟨p.1.proj, p.2.unit⟩ : Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M))) := by
  have h_proj_cont : Continuous (fun p : TotalSpace (E →L[𝕜] E)
    (fun x => Trivial M E x →L[𝕜] TangentSpace I x) ↦ p.proj) :=
    FiberBundle.continuous_proj (E →L[𝕜] E)
      (fun x : M => Bundle.Trivial M E x →L[𝕜] TangentSpace I x)
  apply continuous_iff_continuousAt.mpr
  intro p
  set Z := frameBundleFiberBundleCore (I := I) (M := M)
  set e := Z.localTriv (Z.indexAt p.1.proj)
  set e' := trivializationAt (E →L[𝕜] E)
    (fun x => Bundle.Trivial M E x →L[𝕜] TangentSpace I x) p.1.proj
  apply e.continuousAt_of_comp_left
  · convert h_proj_cont.continuousAt.comp (continuous_subtype_val.continuousAt) using 1
  · exact mem_chart_source H _
  · have h_intertwining : ∀ᶠ p' in 𝓝 p,
        Prod.map id Units.val (e ⟨p'.1.proj, p'.2.unit⟩) = e' p'.1 :=
      intertwining_reverse p
    have h_cont : ContinuousAt (Prod.map id Units.val ∘
        (e ∘ fun p : ↥(FrameBundle I M) => ⟨p.1.proj, p.2.unit⟩)) p := by
      apply ContinuousAt.congr_of_eventuallyEq _ h_intertwining
      exact e'.continuousAt (FiberBundle.mem_trivializationAt_proj_source) |>.comp
        continuous_subtype_val.continuousAt
    convert continuousAt_of_prodMap_isEmbedding Units.isOpenEmbedding_val.isEmbedding h_cont
      using 1

/-- The homeomorphism between the FiberBundleCore total space and the FrameBundle Opens subtype. -/
def frameBundleCoreHomeomorph [IsManifold I ∞ M] :
    Bundle.TotalSpace (E →L[𝕜] E)ˣ (FrameSpace I M) ≃ₜ ↥(FrameBundle I M) where
  toEquiv := frameBundleEquiv.symm
  continuous_toFun := continuous_toFrameBundleCore
  continuous_invFun := continuous_fromFrameBundleCore

-- ── IsPrincipalBundle instance ───────────────────────────────────────────────────────────────

omit [CompleteSpace 𝕜] in
omit [IsManifold I 1 M] in
private lemma smul_unit_eq_mul [IsManifold I ∞ M]
    (p : ↥(FrameBundle I M)) (g : (E →L[𝕜] E)ˣ) :
    (p <• g).2.unit.val = p.2.unit.val ∘L (g : E →L[𝕜] E) := by
  simp [HSMul.hSMul, SMul.smul, IsUnit.unit_spec]

end FrameBundlePrincipal

-- Everything up through frameBundleCoreHomeomorph stays in the general 𝕜 variable block
-- (frameBundleEquiv, the intertwining lemmas, frameBundleCoreHomeomorph, etc.)

section FrameBundleRL  -- restricted to ℝ for IsPrincipalBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

noncomputable instance FrameBundle.isPrincipalBundle [IsManifold I ∞ M] :
    IsPrincipalBundle
      I
      (Units (E →L[ℝ] E))
      (modelWithCornersSelf ℝ (E →L[ℝ] E))
      ↥(FrameBundle I M)
      (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (frameBundleProj (I := I) (M := M)) where
  is_free := frameBundleAction_free
  respects_fibres := frameBundleAction_respects_fibres
  smooth_proj := by
    apply ContMDiff.comp (I' := I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E)))
    · exact contMDiff_proj (fun x : M => Bundle.Trivial M E x →L[ℝ] TangentSpace I x)
    · exact contMDiff_subtype_val
  localTriv := fun p =>
    (trivializationAt (E →L[ℝ] E)ˣ (FrameSpace I M) p.1.proj).compHomeomorph
      frameBundleCoreHomeomorph.symm
  mem_baseSet_localTriv := fun p =>
    mem_baseSet_trivializationAt (E →L[ℝ] E)ˣ (FrameSpace I M) p.1.proj
  equivariant_localTriv := fun p g => by
    apply Prod.ext
    · simp only [frameBundleProj, HSMul.hSMul, SMul.smul]
      exact rfl
    · apply Units.ext
      have key : ∀ (q : ↥(FrameBundle I M)),
          ((trivializationAt (E →L[ℝ] E)ˣ (FrameSpace I M) p.1.proj).compHomeomorph
            frameBundleCoreHomeomorph.symm q).2.val =
          ((frameBundleFiberBundleCore (I := I) (M := M)).coordChange
            (achart H q.1.proj) (achart H p.1.proj) q.1.proj q.2.unit).val := by
        intro q
        simp only [Trivialization.compHomeomorph, frameBundleCoreHomeomorph, frameBundleEquiv]
        exact rfl
      change ((trivializationAt (E →L[ℝ] E)ˣ (FrameSpace I M) p.1.proj).compHomeomorph
                frameBundleCoreHomeomorph.symm (p <• g)).2.val =
             ((trivializationAt (E →L[ℝ] E)ˣ (FrameSpace I M) p.1.proj).compHomeomorph
                frameBundleCoreHomeomorph.symm p).2.val * (g : E →L[ℝ] E)
      rw [key (p <• g), key p]
      simp only [HSMul.hSMul, SMul.smul]
      rw [frameBundleFiberBundleCore_coordChange_val _ _ p.1.proj
            ⟨mem_chart_source H p.1.proj, mem_chart_source H p.1.proj⟩,
          frameBundleFiberBundleCore_coordChange_val _ _ p.1.proj
            ⟨mem_chart_source H p.1.proj, mem_chart_source H p.1.proj⟩]
      exact rfl

end FrameBundleRL

section FrameBundleYangMills

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `maurerCartan` for `(E →L[ℝ] E)ˣ` is left-multiplication by `g⁻¹`. -/
lemma maurerCartan_units_eq
    (g : (E →L[ℝ] E)ˣ) (v : E →L[ℝ] E) :
    maurerCartan (IG := modelWithCornersSelf ℝ (E →L[ℝ] E)) g v =
      (g⁻¹ : (E →L[ℝ] E)ˣ).val ∘L v := by
  simp only [maurerCartan]
  exact mfderiv_units_mulLeft g⁻¹ g v

/-- `Ad_{g⁻¹}` for `(E →L[ℝ] E)ˣ` is conjugation. -/
lemma Ad_units_eq
    (g : (E →L[ℝ] E)ˣ) (A : E →L[ℝ] E) :
    Ad (IG := modelWithCornersSelf ℝ (E →L[ℝ] E)) g⁻¹ A =
      (g⁻¹ : (E →L[ℝ] E)ˣ).val ∘L A ∘L g.val := by
  simp only [Ad]
  refine (mfderiv_units_mul_mul g⁻¹ g⁻¹⁻¹ A).trans ?_
  simp only [inv_inv]
  rw [mul_assoc]
  rfl

variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The Yang-Mills connection transformation law for the frame bundle, in coordinates.
This is the coordinate form of the abstract `yangMills_transformation`: for the frame bundle
the group is `(E →L[ℝ] E)ˣ`, the adjoint action `Ad_{g⁻¹}` is conjugation and the Maurer-Cartan
form `maurerCartan g` is left multiplication by `g⁻¹`. -/
theorem frameBundleYangMills_transformation
    [SmoothRightGAction ∞ (modelWithCornersSelf ℝ (E →L[ℝ] E))
      (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E))) (E →L[ℝ] E)ˣ ↑(FrameBundle I M)]
    (τ : ConnectionForm (G := (E →L[ℝ] E)ˣ) (IG := modelWithCornersSelf ℝ (E →L[ℝ] E))
      (IB := I) (P := ↑(FrameBundle I M)))
    (σ₁ σ₂ : M → ↑(FrameBundle I M)) (U₁ U₂ : Set M)
    (hσ₁ : IsLocalSection (IB := I) (IG := modelWithCornersSelf ℝ (E →L[ℝ] E))
      (proj := frameBundleProj) σ₁ U₁)
    (hσ₂ : IsLocalSection (IB := I) (IG := modelWithCornersSelf ℝ (E →L[ℝ] E))
      (proj := frameBundleProj) σ₂ U₂)
    (Ω : M → (E →L[ℝ] E)ˣ) (hΩ : ∀ m ∈ U₁ ∩ U₂, σ₁ m <• Ω m = σ₂ m)
    (m : M) (hm : m ∈ U₁ ∩ U₂) (v : TangentSpace I m) :
    yangMillsField τ σ₂ m v =
      (Ω m)⁻¹.val ∘L (yangMillsField τ σ₁ m v) ∘L (Ω m).val +
      (Ω m)⁻¹.val ∘L (mfderiv I (modelWithCornersSelf ℝ (E →L[ℝ] E)) Ω m v) := by
  rw [yangMills_transformation τ σ₁ σ₂ U₁ U₂ hσ₁ hσ₂ Ω hΩ m hm v, Ad_units_eq,
      maurerCartan_units_eq]
  exact rfl
end FrameBundleYangMills
