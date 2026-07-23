/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.MorphismProperty.TrivialBundles

/-!
# Gluing of trivial bundles


-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory

variable {C : Type*} [Category* C]

namespace MorphismProperty.TrivialBundleWithFiber


-- to be moved
section

variable {F E B : C} {p : E ⟶ B} (hp : TrivialBundleWithFiber F p)
  {c : BinaryFan B F} (hc : IsLimit c)

def isoOfIsLimit : E ≅ c.pt := hp.isLimit.conePointUniqueUpToIso hc

@[reassoc (attr := simp)]
lemma isoOfIsLimit_hom_fst : (hp.isoOfIsLimit hc).hom ≫ c.fst = p :=
  hp.isLimit.conePointUniqueUpToIso_hom_comp hc ⟨.left⟩

@[reassoc (attr := simp)]
lemma isoOfIsLimit_hom_snd : (hp.isoOfIsLimit hc).hom ≫ c.snd = hp.r :=
  hp.isLimit.conePointUniqueUpToIso_hom_comp hc ⟨.right⟩

end


variable [CartesianMonoidalCategory C]

open CartesianMonoidalCategory

section

variable {F E B : C} {p : E ⟶ B} (hp : TrivialBundleWithFiber F p)

def isoTensor : E ≅ B ⊗ F :=
  hp.isoOfIsLimit (tensorProductIsBinaryProduct B F)

@[reassoc (attr := simp)]
lemma isoTensor_hom_fst : hp.isoTensor.hom ≫ fst _ _ = p :=
  isoOfIsLimit_hom_fst _ _

@[reassoc (attr := simp)]
lemma isoTensor_hom_snd : hp.isoTensor.hom ≫ snd _ _ = hp.r :=
  isoOfIsLimit_hom_snd _ _

end

variable {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ F : C}
  {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
  {t' : Y₁ ⟶ Y₂} {l' : Y₁ ⟶ Y₃} {r' : Y₂ ⟶ Y₄} {b' : Y₃ ⟶ Y₄}
  (sq : IsPushout t l r b) (sq' : IsPushout t' l' r' b')
  {p₁ : Y₁ ⟶ X₁} {p₂ : Y₂ ⟶ X₂} {p₃ : Y₃ ⟶ X₃} {p₄ : Y₄ ⟶ X₄}
  (sq₁₂ : IsPullback t' p₁ p₂ t) (sq₂₄ : IsPullback r' p₂ p₄ r)
  (sq₁₃ : IsPullback l' p₁ p₃ l) (sq₃₄ : IsPullback b' p₃ p₄ b)
  (h₂ : TrivialBundleWithFiber F p₂) (h₃ : TrivialBundleWithFiber F p₃)
  [PreservesColimit (span t l) (tensorRight F)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include sq sq' in
/-- Assume we have a pushout square
```
   t
X₁ ⟶ X₂
l|   |r
 v   v
X₃ ⟶ X₄
   b
```
which is the bottom face of a cube, where the top face
(involving objects `Y₁`, `Y₂`, `Y₃`, and `Y₄`, and morphisms
`t'`, `l'`, `r'`, and `b'`) is also a pushout square, while
the four vertical faces are pullback squares.
Denote `pᵢ : Yᵢ ⟶ Xᵢ` the vertical morphisms.
If we assume that both `p₂ : Y₂ ⟶ X₂` and `p₄ : Y₃ ⟶ X₃`
are trivial bundles with fiber `F`, that
both trivializations of `p₁ : Y₁ ⟶ X₁` obtained after
pulling back coincide, and that the pushout of the bottom
face commutes with the product with `F`, then there exists
(a unique) structure `TrivialBundleWithFiber F p₄` which
restricts the given ones over `X₂` and `X₃`. -/
lemma exists_gluing (h₁ : h₂.pullback sq₁₂ = h₃.pullback sq₁₃) :
    ∃ (h₄ : TrivialBundleWithFiber F p₄),
      h₄.pullback sq₂₄ = h₂ ∧ h₄.pullback sq₃₄ = h₃ := by
  simp only [ext_iff, pullback_r] at h₁
  obtain ⟨f, hf₂, hf₃⟩ := sq'.exists_desc h₂.r h₃.r h₁
  obtain ⟨e₄, comm₁, comm₂⟩ :=
    IsPushout.exists_iso_of_isos sq' (sq.map (tensorRight F))
      (h₂.pullback sq₁₂).isoTensor h₂.isoTensor h₃.isoTensor
        (by dsimp; ext <;> simp [sq₁₂.w])
        (by dsimp; ext <;> simp [sq₁₃.w, h₁])
  refine ⟨⟨f, IsLimit.ofIsoLimit (tensorProductIsBinaryProduct X₄ F)
      ((BinaryFan.ext e₄ ?_ ?_).symm)⟩,
    by ext; assumption, by ext; assumption⟩
  · apply sq'.hom_ext <;> dsimp [Fan.proj]
    · simpa [reassoc_of% comm₁] using sq₂₄.w
    · simpa [reassoc_of% comm₂] using sq₃₄.w
  · apply sq'.hom_ext <;> dsimp [Fan.proj]
    · simpa [reassoc_of% comm₁]
    · simpa [reassoc_of% comm₂]

end MorphismProperty.TrivialBundleWithFiber

end CategoryTheory
