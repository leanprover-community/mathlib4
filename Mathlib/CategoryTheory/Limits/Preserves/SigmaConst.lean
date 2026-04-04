/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# `sigmaConst.obj` preserves colimits

Given an object `R` in a category `C` with coproducts of size `w`,
the functor `sigmaConst.obj R : Type w ⥤ C` which sends
a type `T` to the coproduct of copies of `R` indexed by `T`
preserves all colimits.

-/

public section

universe w v' v u' u

namespace CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/- If the morphisms in `C` were in `Type w`, the functor
`sigmaConst.{w}`
would be a left adjoint (see `sigmaConstAdj`). In general, we cannot
expect this functor to be a left adjoint, but the commutation
with colimits always holds. -/
instance {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] (R : C) :
    PreservesColimitsOfSize.{v', u'} (sigmaConst.{w}.obj R) where
  preservesColimitsOfShape {J _} := ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨by
    replace hc := (Types.isColimit_iff_coconeTypesIsColimit ..).1 ⟨hc⟩
    let coconeTypes (s : Cocone (K ⋙ sigmaConst.obj R)) : K.CoconeTypes :=
      { pt := R ⟶ s.pt
        ι j k := Sigma.ι (fun _ ↦ R) k ≫ s.ι.app j
        ι_naturality g := by ext; simp [← s.w g] }
    exact {
      desc s := Sigma.desc (hc.desc (coconeTypes s))
      fac s j := by
        dsimp
        ext k
        simpa using congr_fun (hc.fac (coconeTypes s) j) k
      uniq s m hm := by
        dsimp
        ext x
        obtain ⟨j, k, rfl⟩ := Functor.CoconeTypes.IsColimit.ι_jointly_surjective hc x
        simpa [coconeTypes, ← hm] using congr_fun (hc.fac (coconeTypes s) j).symm k }⟩⟩⟩

end CategoryTheory.Limits
