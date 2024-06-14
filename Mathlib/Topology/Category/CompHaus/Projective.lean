/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.StoneCech
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

#align_import topology.category.CompHaus.projective from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# CompHaus has enough projectives

In this file we show that `CompHaus` has enough projectives.

## Main results

Let `X` be a compact Hausdorff space.

* `CompHaus.projective_ultrafilter`: the space `Ultrafilter X` is a projective object
* `CompHaus.projectivePresentation`: the natural map `Ultrafilter X → X`
  is a projective presentation

## Reference

See [miraglia2006introduction] Chapter 21 for a proof that `CompHaus` has enough projectives.

-/


noncomputable section

open CategoryTheory Function

namespace CompHaus

attribute [local instance] ConcreteCategory.instFunLike

instance projective_ultrafilter (X : Type*) : Projective (of <| Ultrafilter X) where
  factors {Y Z} f g hg := by
    rw [epi_iff_surjective] at hg
    obtain ⟨g', hg'⟩ := hg.hasRightInverse
    let t : X → Y := g' ∘ f ∘ (pure : X → Ultrafilter X)
    let h : Ultrafilter X → Y := Ultrafilter.extend t
    have hh : Continuous h := continuous_ultrafilter_extend _
    use ⟨h, hh⟩
    apply (forget CompHaus).map_injective
    simp only [Functor.map_comp, ContinuousMap.coe_mk, coe_comp]
    convert denseRange_pure.equalizer (g.continuous.comp hh) f.continuous _
    -- Porting note: We need to get the coercions to functions under control.
    -- The next two lines should not be needed.
    let g'' : ContinuousMap Y Z := g
    have : g'' ∘ g' = id := hg'.comp_eq_id
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
    erw [comp.assoc, ultrafilter_extend_extends, ← comp.assoc, this, id_comp]
set_option linter.uppercaseLean3 false in
#align CompHaus.projective_ultrafilter CompHaus.projective_ultrafilter

/-- For any compact Hausdorff space `X`,
  the natural map `Ultrafilter X → X` is a projective presentation. -/
def projectivePresentation (X : CompHaus) : ProjectivePresentation X where
  p := of <| Ultrafilter X
  f := ⟨_, continuous_ultrafilter_extend id⟩
  projective := CompHaus.projective_ultrafilter X
  epi :=
    ConcreteCategory.epi_of_surjective _ fun x =>
      ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩
set_option linter.uppercaseLean3 false in
#align CompHaus.projective_presentation CompHaus.projectivePresentation

instance : EnoughProjectives CompHaus where presentation X := ⟨projectivePresentation X⟩

end CompHaus
