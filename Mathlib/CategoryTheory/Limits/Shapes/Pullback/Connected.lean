/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!

# Pullbacks commute with connected limits

-/

universe v u

namespace CategoryTheory.Limits

/--
Let `F` and `G` be two diagrams indexed by a connected `I`, and `X` and `Y` be two cones over
`F` and `G` respectively, with maps `α : F ⟶ G` and `f : X ⟶ Y` that commutes with the cone maps.
Suppose `X = Y x[G i] F i` for all `i` and `Y = lim G`, then `X = lim F`.
-/
noncomputable
def isLimitOfIsPullbackOfIsConnected
    {I C : Type*} [Category I] [IsConnected I] [Category C] {F G : I ⥤ C}
    (α : F ⟶ G) (cF : Cone F) (cG : Cone G)
    (f : (Cones.postcompose α).obj cF ⟶ cG)
    (hf : ∀ i, IsPullback (cF.π.app i) f.hom (α.app i) (cG.π.app i))
    (hcG : IsLimit cG) : IsLimit cF where
  lift s := (hf (Classical.arbitrary _)).lift
    (s.π.app (Classical.arbitrary _)) (hcG.lift ((Cones.postcompose α).obj s)) (by simp)
  fac s j := by
    let f (i : _) : s.pt ⟶ cF.pt :=
      (hf i).lift (s.π.app i) (hcG.lift ((Cones.postcompose α).obj s)) (by simp)
    have (i j : _) : f i = f j := by
      refine constant_of_preserves_morphisms f (fun j₁ j₂ g ↦ ?_) i j
      refine (hf j₂).hom_ext ?_ (by simp [f])
      rw [IsPullback.lift_fst, ← cF.w g, IsPullback.lift_fst_assoc, Cone.w]
    change f _ ≫ _ = _
    rw [this _ j]
    simp [f]
  uniq s g hg := (hf (Classical.arbitrary _)).hom_ext (by simp [hg])
    (hcG.hom_ext <| by simp [reassoc_of% hg])

/--
Let `F` and `G` be two diagrams indexed by a connected `I`, and `X` and `Y` be two cocones over
`F` and `G` respectively, with maps `α : F ⟶ G` and `f : X ⟶ Y` that commutes with the cocone maps.
Suppose `Y = X ⨿[F i] G i` for all `i` and `Y = colim G`, then `X = colim F`.
-/
noncomputable
def isColimitOfIsPushoutOfIsConnected
    {I C : Type*} [Category I] [IsConnected I] [Category C] {F G : I ⥤ C}
    (α : F ⟶ G) (cF : Cocone F) (cG : Cocone G)
    (f : cF ⟶ (Cocones.precompose α).obj cG)
    (hf : ∀ i, IsPushout (cF.ι.app i) (α.app i) f.hom (cG.ι.app i))
    (hcF : IsColimit cF) : IsColimit cG where
  desc s := (hf (Classical.arbitrary _)).desc
    (hcF.desc ((Cocones.precompose α).obj s)) (s.ι.app (Classical.arbitrary _)) (by simp)
  fac s j := by
    let f (i : _) : cG.pt ⟶ s.pt :=
      (hf i).desc (hcF.desc ((Cocones.precompose α).obj s)) (s.ι.app i) (by simp)
    have (i j : _) : f i = f j := by
      refine constant_of_preserves_morphisms f (fun j₁ j₂ g ↦ ?_) i j
      refine (hf j₁).hom_ext (by simp [f]) ?_
      rw [IsPushout.inr_desc, ← cG.w g, Category.assoc, IsPushout.inr_desc, Cocone.w]
    change _ ≫ f _ = _
    rw [this _ j]
    simp [f]
  uniq s g hg := (hf (Classical.arbitrary _)).hom_ext (hcF.hom_ext <| by simp [hg]) (by simp [hg])

end CategoryTheory.Limits
