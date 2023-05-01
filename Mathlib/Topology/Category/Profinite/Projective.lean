/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module topology.category.Profinite.projective
! leanprover-community/mathlib commit 829895f162a1f29d0133f4b3538f4cd1fb5bffd3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Category.Profinite.Basic
import Mathbin.Topology.StoneCech
import Mathbin.CategoryTheory.Preadditive.Projective

/-!
# Profinite sets have enough projectives

In this file we show that `Profinite` has enough projectives.

## Main results

Let `X` be a profinite set.

* `Profinite.projective_ultrafilter`: the space `ultrafilter X` is a projective object
* `Profinite.projective_presentation`: the natural map `ultrafilter X → X`
  is a projective presentation

-/


noncomputable section

universe u v w

open CategoryTheory Function

namespace Profinite

instance projective_ultrafilter (X : Type u) : Projective (of <| Ultrafilter X)
    where Factors Y Z f g hg := by
    rw [epi_iff_surjective] at hg
    obtain ⟨g', hg'⟩ := hg.has_right_inverse
    let t : X → Y := g' ∘ f ∘ (pure : X → Ultrafilter X)
    let h : Ultrafilter X → Y := Ultrafilter.extend t
    have hh : Continuous h := continuous_ultrafilter_extend _
    use ⟨h, hh⟩
    apply faithful.map_injective (forget Profinite)
    simp only [forget_map_eq_coe, ContinuousMap.coe_mk, coe_comp]
    refine' dense_range_pure.equalizer (g.continuous.comp hh) f.continuous _
    rw [comp.assoc, ultrafilter_extend_extends, ← comp.assoc, hg'.comp_eq_id, comp.left_id]
#align Profinite.projective_ultrafilter Profinite.projective_ultrafilter

/-- For any profinite `X`, the natural map `ultrafilter X → X` is a projective presentation. -/
def projectivePresentation (X : Profinite.{u}) : ProjectivePresentation X
    where
  P := of <| Ultrafilter X
  f := ⟨_, continuous_ultrafilter_extend id⟩
  Projective := Profinite.projective_ultrafilter X
  Epi :=
    ConcreteCategory.epi_of_surjective _ fun x =>
      ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩
#align Profinite.projective_presentation Profinite.projectivePresentation

instance : EnoughProjectives Profinite.{u} where presentation X := ⟨projectivePresentation X⟩

end Profinite

