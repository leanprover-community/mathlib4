/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Geometry.Manifold.VectorBundle.Pullback

universe u u'

variable {M M' H H' EM EM' 𝕜 : Type*} (F F' : Type*)

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace H] (I : ModelWithCorners 𝕜 EM H)
  [NormedAddCommGroup EM'] [NormedSpace 𝕜 EM'] [TopologicalSpace H']
    (I' : ModelWithCorners 𝕜 EM' H')

variable [TopologicalSpace M] [ChartedSpace H M] --[SmoothManifoldWithCorners I M]
variable [TopologicalSpace M'] [ChartedSpace H' M'] --[SmoothManifoldWithCorners I' M']

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (E : M → Type u) [(x : M) → AddCommMonoid (E x)] [(x : M) → Module 𝕜 (E x)]
  [TopologicalSpace (Bundle.TotalSpace F E)] [(x : M) → TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E] [SmoothVectorBundle F E I]

variable [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  (E' : M' → Type u') [(x : M') → AddCommMonoid (E' x)] [(x : M') → Module 𝕜 (E' x)]
  [TopologicalSpace (Bundle.TotalSpace F' E')] [(x : M') → TopologicalSpace (E' x)]
  [FiberBundle F' E'] [VectorBundle 𝕜 F' E']
  [SmoothVectorBundle F' E' I']

noncomputable section

open Bundle
open scoped Manifold

variable (M M') in
/-- The projection from a product of two manifolds onto the first factor, as a bundled smooth map.
-/
@[simps] def SmoothMap.fst : SmoothMap (I.prod I') I (M × M') M where
  val := Prod.fst
  property := smooth_fst

variable (M M') in
/-- The projection from a product of two manifolds onto the second factor, as a bundled smooth map.
-/
@[simps] def SmoothMap.snd : SmoothMap (I.prod I') I' (M × M') M' where
  val := Prod.snd
  property := smooth_snd

-- FIXME at the moment `Prod.fst *ᵖ E` and `SmoothMap.fst M M' I I' *ᵖ E` are different types and
-- only the latter carries a vector bundle instance.  Maybe the pullback smooth vector bundle
-- instance should not take a bundled smooth map, just a bare one?

/-- For vector bundles `E` and `E'`, the construction `E ⊞ E'`. -/
abbrev BoxProd := (SmoothMap.fst M M' I I' *ᵖ E) ×ᵇ (SmoothMap.snd M M' I I' *ᵖ E')

/-- For vector bundles `E` and `E'`, the total space of `E ⊞ E'` is canonically isomorphic to the
product of the total spaces of `E` and `E'` -/
@[simps] def equivProd :
    TotalSpace (F × F') (BoxProd I I' E E') ≃ TotalSpace F E × TotalSpace F' E' where
  toFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), (p.1.2, p.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- For vector bundles `E` and `E'`, the canonical isomorphism from the total space of `E ⊞ E'` to
the product of the total spaces of `E` and `E'` is smooth. -/
theorem equivProd_smooth :
    Smooth ((I.prod I').prod 𝓘(𝕜, F × F')) ((I.prod 𝓘(𝕜, F)).prod (I'.prod 𝓘(𝕜, F')))
      (equivProd F F' I I' E E') := by
  apply Smooth.prod_mk
  · have h₁ := Bundle.Prod.smooth_fst (I.prod I') F (SmoothMap.fst M M' I I' *ᵖ E) F'
      (SmoothMap.snd M M' I I' *ᵖ E')
    have h₂ := Bundle.Pullback.smooth_lift F E I (I.prod I') (SmoothMap.fst M M' I I')
    exact h₂.comp h₁
  · have h₁ := Bundle.Prod.smooth_snd (I.prod I') F (SmoothMap.fst M M' I I' *ᵖ E) F'
      (SmoothMap.snd M M' I I' *ᵖ E')
    have h₂ := Bundle.Pullback.smooth_lift F' E' I' (I.prod I') (SmoothMap.snd M M' I I')
    exact h₂.comp h₁

omit [(x : M) → Module 𝕜 (E x)] [VectorBundle 𝕜 F E] [SmoothVectorBundle F E I]
  [(x : M') → Module 𝕜 (E' x)] [VectorBundle 𝕜 F' E'] [SmoothVectorBundle F' E' I'] in
/-- For vector bundles `E` and `E'`, the canonical isomorphism from the product of the total spaces
of `E` and `E'` to the total space of `E ⊞ E'` is smooth. -/
theorem equivProd_symm_smooth :
    Smooth ((I.prod 𝓘(𝕜, F)).prod (I'.prod 𝓘(𝕜, F'))) ((I.prod I').prod 𝓘(𝕜, F × F'))
      (equivProd F F' I I' E E').symm := by
  apply Bundle.Prod.smooth_of_smooth_fst_comp_of_smooth_snd_comp
  · apply Bundle.Pullback.smooth_of_smooth_proj_comp_of_smooth_lift_comp
    · apply Smooth.prod_map
      · apply smooth_proj
      · apply smooth_proj
    · apply smooth_fst
  · apply Bundle.Pullback.smooth_of_smooth_proj_comp_of_smooth_lift_comp
    · apply Smooth.prod_map
      · apply smooth_proj
      · apply smooth_proj
    · apply smooth_snd
