/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Pointwise colimits of coherent sheaves
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C A I : Type*} [Category C] [Category A] [Category I]
    [Preregular C] [FinitaryExtensive C] [HasPullbacks C]
    [HasColimitsOfShape I A]
    [PreservesFiniteLimits (colim : (I ⥤ A) ⥤ A)]

/-- If colimits of shape `I` preserve finite limits in `A`, a pointwise colimit of
coherent sheaves is a sheaf. -/
lemma isSheaf_pointwiseColimit_of_preservesFiniteLimits
    (F : I ⥤ Sheaf (coherentTopology C) A) :
    Presheaf.IsSheaf (coherentTopology C)
      ((F ⋙ sheafToPresheaf (coherentTopology C) A).flip ⋙ colim) := by
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
  constructor
  · apply +allowSynthFailures comp_preservesFiniteProducts
    have : ∀ (i : I), PreservesFiniteProducts ((F ⋙ sheafToPresheaf _ _).obj i) := fun i => by
      exact inferInstanceAs (PreservesFiniteProducts (F.obj i).obj)
    exact ⟨fun _ ↦ preservesLimitsOfShape_of_evaluation _ _ fun d ↦
      inferInstanceAs (PreservesLimitsOfShape _ ((F ⋙ sheafToPresheaf _ _).obj d))⟩
  · intro X B π hπ pb hpb
    let Fp := F ⋙ sheafToPresheaf (coherentTopology C) A
    let G : WalkingParallelPair ⥤ I ⥤ A :=
      parallelPair
        (Functor.whiskerLeft Fp
          ((evaluation Cᵒᵖ A).map pb.fst.op))
        (Functor.whiskerLeft Fp
          ((evaluation Cᵒᵖ A).map pb.snd.op))
    let K : Cone G := Fork.ofι
      (Functor.whiskerLeft Fp ((evaluation Cᵒᵖ A).map π.op))
      (by
        ext i
        exact regularTopology.equalizerCondition_w (F.obj i).obj pb)
    have hK : IsLimit K := by
      apply evaluationJointlyReflectsLimits
      intro i
      let ii : G ⋙ (evaluation I A).obj i ≅
          parallelPair ((F.obj i).obj.map pb.fst.op) ((F.obj i).obj.map pb.snd.op) :=
        parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp [G, Fp]) (by simp [G, Fp])
      let e : (Cone.postcompose ii.hom).obj (((evaluation I A).obj i).mapCone K) ≅
          Fork.ofι ((F.obj i).obj.map π.op)
            (regularTopology.equalizerCondition_w (F.obj i).obj pb) := by
        refine Cone.ext (Iso.refl _) ?_
        rintro (_ | _) <;> simp [ii, K, Fp]
      have hsheaf := (F.obj i).property
      rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition] at hsheaf
      exact (IsLimit.equivOfNatIsoOfIso ii _ _ e).symm (hsheaf.2 π pb hpb).some
    have hcolim : IsLimit ((colim (J := I) (C := A)).mapCone K) :=
      isLimitOfPreserves (colim (J := I) (C := A)) hK
    refine ⟨?_⟩
    let i : parallelPair
        ((Fp.flip ⋙ colim).map pb.fst.op)
        ((Fp.flip ⋙ colim).map pb.snd.op) ≅ G ⋙ colim :=
      parallelPair.ext (Iso.refl _) (Iso.refl _)
        (by simp [G, Fp]; rfl) (by simp [G, Fp]; rfl)
    let e : (Cone.postcompose i.hom).obj
        (Fork.ofι ((Fp.flip ⋙ colim).map π.op)
          (regularTopology.equalizerCondition_w (Fp.flip ⋙ colim) pb)) ≅
        (colim (J := I) (C := A)).mapCone K := by
      refine Cone.ext (Iso.refl _) ?_
      rintro (_ | _) <;>
        dsimp [i, K, parallelPair.ext] <;> simp only [Category.id_comp, Category.comp_id]
      · rfl
      · change (Fp.flip ⋙ colim).map π.op ≫ (Fp.flip ⋙ colim).map pb.fst.op =
          colimMap (Functor.whiskerLeft Fp ((evaluation Cᵒᵖ A).map π.op) ≫
            Functor.whiskerLeft Fp ((evaluation Cᵒᵖ A).map pb.fst.op))
        rw [← Functor.map_comp, ← Functor.whiskerLeft_comp, ← Functor.map_comp]
        rfl
    exact (IsLimit.equivOfNatIsoOfIso i _ _ e).symm hcolim

/-- A presheaf colimit of coherent sheaves is a sheaf when colimits of that shape preserve
finite limits in the category of values. -/
lemma isSheaf_colimit_of_preservesFiniteLimits
    (F : I ⥤ Sheaf (coherentTopology C) A)
    (c : Cocone (F ⋙ sheafToPresheaf (coherentTopology C) A))
    (hc : IsColimit c) :
    Presheaf.IsSheaf (coherentTopology C) c.pt := by
  let i : c.pt ≅ (pointwiseCocone (F ⋙ sheafToPresheaf
      (coherentTopology C) A)).pt :=
    hc.coconePointUniqueUpToIso (pointwiseIsColimit _)
  rw [Presheaf.isSheaf_of_iso_iff i]
  exact isSheaf_pointwiseColimit_of_preservesFiniteLimits F

/-- Colimits commuting with finite limits are created by the inclusion of coherent sheaves
into presheaves. -/
@[implicit_reducible]
noncomputable def createsColimitsOfShapeOfPreservesFiniteLimits
 :
    CreatesColimitsOfShape I
      (sheafToPresheaf (coherentTopology C) A) :=
  CategoryTheory.Sheaf.createsColimitsOfShapeOfIsSheaf (isSheaf_colimit_of_preservesFiniteLimits)

end CategoryTheory.Sheaf
