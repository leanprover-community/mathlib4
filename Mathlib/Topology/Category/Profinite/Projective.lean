/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.StoneCech
import Mathlib.CategoryTheory.Preadditive.Projective

#align_import topology.category.Profinite.projective from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# Profinite sets have enough projectives

In this file we show that `Profinite` has enough projectives.

## Main results

Let `X` be a profinite set.

* `Profinite.projective_ultrafilter`: the space `Ultrafilter X` is a projective object
* `Profinite.projectivePresentation`: the natural map `Ultrafilter X → X`
  is a projective presentation

-/


noncomputable section

universe u v w

open CategoryTheory Function

namespace Profinite

set_option linter.uppercaseLean3 false

instance projective_ultrafilter (X : Type u) : Projective (of <| Ultrafilter X) where
  factors {Y Z} f g hg := by
    rw [epi_iff_surjective] at hg
    -- ⊢ ∃ f', f' ≫ g = f
    obtain ⟨g', hg'⟩ := hg.hasRightInverse
    -- ⊢ ∃ f', f' ≫ g = f
    let t : X → Y := g' ∘ f ∘ (pure : X → Ultrafilter X)
    -- ⊢ ∃ f', f' ≫ g = f
    let h : Ultrafilter X → Y := Ultrafilter.extend t
    -- ⊢ ∃ f', f' ≫ g = f
    have hh : Continuous h := continuous_ultrafilter_extend _
    -- ⊢ ∃ f', f' ≫ g = f
    use ⟨h, hh⟩
    -- ⊢ ContinuousMap.mk h ≫ g = f
    apply Faithful.map_injective (F := forget Profinite)
    -- ⊢ (forget Profinite).map (ContinuousMap.mk h ≫ g) = (forget Profinite).map f
    simp only [ContinuousMap.coe_mk, coe_comp]
    -- ⊢ (forget Profinite).map (ContinuousMap.mk (Ultrafilter.extend (g' ∘ ↑f ∘ pure …
    convert denseRange_pure.equalizer (g.continuous.comp hh) f.continuous _
    -- ⊢ (↑g ∘ h) ∘ pure = ↑f ∘ pure
     -- Porting note: same fix as in `Topology.Category.CompHaus.Projective`
    let g'' : ContinuousMap Y Z := g
    -- ⊢ (↑g ∘ h) ∘ pure = ↑f ∘ pure
    have : g'' ∘ g' = id := hg'.comp_eq_id
    -- ⊢ (↑g ∘ h) ∘ pure = ↑f ∘ pure
    rw [comp.assoc, ultrafilter_extend_extends, ← comp.assoc, this, comp.left_id]
    -- 🎉 no goals
#align Profinite.projective_ultrafilter Profinite.projective_ultrafilter

/-- For any profinite `X`, the natural map `Ultrafilter X → X` is a projective presentation. -/
def projectivePresentation (X : Profinite.{u}) : ProjectivePresentation X where
  p := of <| Ultrafilter X
  f := ⟨_, continuous_ultrafilter_extend id⟩
  projective := Profinite.projective_ultrafilter X
  epi := ConcreteCategory.epi_of_surjective _ fun x =>
    ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩
#align Profinite.projective_presentation Profinite.projectivePresentation

instance : EnoughProjectives Profinite.{u} where presentation X := ⟨projectivePresentation X⟩

end Profinite
