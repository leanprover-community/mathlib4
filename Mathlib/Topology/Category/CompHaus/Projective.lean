/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Topology.Category.CompHaus.Basic
import Mathlib.Topology.StoneCech
import Mathlib.CategoryTheory.Preadditive.Projective

#align_import topology.category.CompHaus.projective from "leanprover-community/mathlib"@"829895f162a1f29d0133f4b3538f4cd1fb5bffd3"

/-!
# CompHaus has enough projectives

In this file we show that `CompHaus` has enough projectives.

## Main results

Let `X` be a compact Hausdorff space.

* `CompHaus.projective_ultrafilter`: the space `Ultrafilter X` is a projective object
* `CompHaus.projective_presentation`: the natural map `Ultrafilter X → X`
  is a projective presentation

## Reference

See [miraglia2006introduction] Chapter 21 for a proof that `CompHaus` has enough projectives.

-/


noncomputable section

open CategoryTheory Function

namespace CompHaus

attribute [local instance] ConcreteCategory.funLike

instance projective_ultrafilter (X : Type*) : Projective (of <| Ultrafilter X)
    where
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
    apply Faithful.map_injective (F := forget CompHaus)
    -- ⊢ (forget CompHaus).map (ContinuousMap.mk h ≫ g) = (forget CompHaus).map f
    simp only [Functor.map_comp, ContinuousMap.coe_mk, coe_comp]
    -- ⊢ (forget CompHaus).map (ContinuousMap.mk (Ultrafilter.extend (g' ∘ ↑f ∘ pure) …
    convert denseRange_pure.equalizer (g.continuous.comp hh) f.continuous _
    -- ⊢ (↑g ∘ h) ∘ pure = ↑f ∘ pure
    -- Porting note: We need to get the coercions to functions under control.
    -- The next two lines should not be needed.
    let g'' : ContinuousMap Y Z := g
    -- ⊢ (↑g ∘ h) ∘ pure = ↑f ∘ pure
    have : g'' ∘ g' = id := hg'.comp_eq_id
    -- ⊢ (↑g ∘ h) ∘ pure = ↑f ∘ pure
    rw [comp.assoc, ultrafilter_extend_extends, ← comp.assoc, this, comp.left_id]
    -- 🎉 no goals
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
