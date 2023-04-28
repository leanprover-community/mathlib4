/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module topology.category.CompHaus.projective
! leanprover-community/mathlib commit 829895f162a1f29d0133f4b3538f4cd1fb5bffd3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.CompHaus.Basic
import Mathbin.Topology.StoneCech
import Mathbin.CategoryTheory.Preadditive.Projective

/-!
# CompHaus has enough projectives

In this file we show that `CompHaus` has enough projectives.

## Main results

Let `X` be a compact Hausdorff space.

* `CompHaus.projective_ultrafilter`: the space `ultrafilter X` is a projective object
* `CompHaus.projective_presentation`: the natural map `ultrafilter X → X`
  is a projective presentation

## Reference

See [miraglia2006introduction] Chapter 21 for a proof that `CompHaus` has enough projectives.

-/


noncomputable section

open CategoryTheory Function

namespace CompHaus

instance projective_ultrafilter (X : Type _) : Projective (of <| Ultrafilter X)
    where Factors Y Z f g hg := by
    rw [epi_iff_surjective] at hg
    obtain ⟨g', hg'⟩ := hg.has_right_inverse
    let t : X → Y := g' ∘ f ∘ (pure : X → Ultrafilter X)
    let h : Ultrafilter X → Y := Ultrafilter.extend t
    have hh : Continuous h := continuous_ultrafilter_extend _
    use ⟨h, hh⟩
    apply faithful.map_injective (forget CompHaus)
    simp only [forget_map_eq_coe, ContinuousMap.coe_mk, coe_comp]
    convert dense_range_pure.equalizer (g.continuous.comp hh) f.continuous _
    rw [comp.assoc, ultrafilter_extend_extends, ← comp.assoc, hg'.comp_eq_id, comp.left_id]
#align CompHaus.projective_ultrafilter CompHaus.projective_ultrafilter

/-- For any compact Hausdorff space `X`,
  the natural map `ultrafilter X → X` is a projective presentation. -/
def projectivePresentation (X : CompHaus) : ProjectivePresentation X
    where
  P := of <| Ultrafilter X
  f := ⟨_, continuous_ultrafilter_extend id⟩
  Projective := CompHaus.projective_ultrafilter X
  Epi :=
    ConcreteCategory.epi_of_surjective _ fun x =>
      ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩
#align CompHaus.projective_presentation CompHaus.projectivePresentation

instance : EnoughProjectives CompHaus where presentation X := ⟨projectivePresentation X⟩

end CompHaus

