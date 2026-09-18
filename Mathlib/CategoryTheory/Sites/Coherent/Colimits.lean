/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison

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
  -- Postcomposition with `colim` preserves coherent sheaves.
  apply Presheaf.isSheaf_coherent_of_hasPullbacks_comp
  -- The diagram is a sheaf valued in `I ⥤ A`, since its evaluations are sheaves.
  rw [Presheaf.isSheaf_iff_isLimit]
  intro X S hS
  refine ⟨evaluationJointlyReflectsLimits _ fun i ↦ ?_⟩
  exact ((Presheaf.isSheaf_iff_isLimit _ _).1 (F.obj i).property S hS).some

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
noncomputable def createsColimitsOfShapeOfPreservesFiniteLimits :
    CreatesColimitsOfShape I
      (sheafToPresheaf (coherentTopology C) A) :=
  CategoryTheory.Sheaf.createsColimitsOfShapeOfIsSheaf (isSheaf_colimit_of_preservesFiniteLimits)

end CategoryTheory.Sheaf
