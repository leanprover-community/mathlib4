/-
Copyright (c) 2024 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus

open Set

-- TODO : this is a terrible name...
class CFCDomain (X : Type*) [TopologicalSpace X] (i : outParam (X → ℂ)) extends Embedding i : Prop

instance : CFCDomain ℂ id where toEmbedding := embedding_id
instance {s : Set ℂ} : CFCDomain s (↑) where toEmbedding := embedding_subtype_val
instance {s : Submonoid ℂ} : CFCDomain s (↑) where toEmbedding := embedding_subtype_val
instance : CFCDomain ℝ (↑) where toEmbedding := Complex.isometry_ofReal.embedding

abbrev CFCDomain.incl (X : Type*) [TopologicalSpace X] {i : X → ℂ} [hi : CFCDomain X i] : C(X, ℂ) :=
  ⟨i, hi.continuous⟩

variable {A : Type*} (X Y : Type*) [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
  [CstarRing A] [StarModule ℂ A] [CompleteSpace A]
  [TopologicalSpace X] [TopologicalSpace Y] {i : X → ℂ} {j : Y → ℂ}

-- TODO : this is a terrible name...
class CFCElement [TopologicalSpace X] {i : X → ℂ} [CFCDomain X i] (a : A) : Prop where
  isStarNormal : IsStarNormal a
  spectrum_subset : spectrum ℂ a ⊆ range i

instance {a : A} [IsStarNormal a] : CFCElement ℂ a where
  isStarNormal := inferInstance
  spectrum_subset := range_id ▸ subset_univ _

lemma IsSelfAdjoint.cfcElement {a : A} (ha : IsSelfAdjoint a) : CFCElement ℝ a where
  isStarNormal := ha.isStarNormal
  spectrum_subset z hz := ⟨z.re, .symm <| ha.mem_spectrum_eq_re hz⟩

instance {a : selfAdjoint A} : CFCElement ℝ (a : A) :=
  a.2.cfcElement

lemma cfcElement_of_unitary {a : A} (ha : a ∈ unitary A) : CFCElement circle a where
  isStarNormal := ⟨ha.1.trans ha.2.symm⟩ -- TODO: we should have a name for this
  spectrum_subset := Subtype.range_val ▸ spectrum.subset_circle_of_unitary ha

instance {a : unitary A} : CFCElement circle (a : A) :=
  cfcElement_of_unitary a.2

-- TODO: develop general `Embedding.lift`
noncomputable def CFCElement.spectrumMap [Nonempty X] [hi : CFCDomain X i] (a : A)
    [CFCElement X a] : C(spectrum ℂ a, X) :=
  ⟨i.invFun ∘ (↑), hi.continuous_iff.mpr <| continuous_subtype_val.congr fun x ↦
    .symm <| i.invFun_eq <| spectrum_subset x.2⟩

lemma CFCElement.apply_spectrum_map [Nonempty X] [CFCDomain X i] (a : A) [CFCElement X a]
    (x : spectrum ℂ a) : i (spectrumMap X a x) = x :=
  i.invFun_eq <| spectrum_subset x.2

lemma CFCElement.range_spectrum_map [Nonempty X] [hi : CFCDomain X i] (a : A) [CFCElement X a] :
    range (spectrumMap X a) = i ⁻¹' spectrum ℂ a :=
  -- ugly
  subset_antisymm (range_subset_iff.mpr fun x ↦ by simp [apply_spectrum_map X a])
    (fun x hx ↦ ⟨⟨i x, hx⟩, hi.inj i.apply_invFun_apply⟩)

variable {X Y} [CstarRing A] [StarModule ℂ A] [CompleteSpace A] [Nonempty X]

noncomputable def cfc [CFCDomain X i] [CFCDomain Y j] (f : C(X, Y)) (a : A) [CFCElement X a] : A :=
  haveI : IsStarNormal a := CFCElement.isStarNormal i
  ↑(continuousFunctionalCalculus a <| (CFCDomain.incl Y).comp <| f.comp <|
    CFCElement.spectrumMap X a)

lemma cfc_eq_cfc' [CFCDomain X i] [CFCDomain Y j] (f : C(X, Y)) (a : A) [CFCElement X a] :
    cfc f a = cfc (CFCDomain.incl Y |>.comp f) a :=
  rfl -- unbelievable...

lemma cfc'_add [CFCDomain X i] (f g : C(X, ℂ)) (a : A) [CFCElement X a] :
    cfc (f + g) a = cfc f a + cfc g a := by
  rw [cfc, cfc, cfc, ← AddMemClass.coe_add (elementalStarAlgebra ℂ a), ← map_add]

lemma cfc_add [CFCDomain X i] [CFCDomain Y j] [AddMonoid Y] [ContinuousAdd Y]
    (hj : ∀ y₁ y₂, j (y₁ + y₂) = j y₁ + j y₂) (f g : C(X, Y)) (a : A) [CFCElement X a] :
    cfc (f + g) a = cfc f a + cfc g a :=
  rw []

lemma spectrum_cfc_eq [CFCDomain X i] [hj : CFCDomain Y j] (f : C(X, Y)) (a : A)
    [CFCElement X a] : spectrum ℂ (cfc f a) = (j ∘ f) '' (i ⁻¹' spectrum ℂ a) := by
  have : IsStarNormal a := CFCElement.isStarNormal i
  rw [cfc, ← StarSubalgebra.spectrum_eq, AlgEquiv.spectrum_eq (continuousFunctionalCalculus a),
      ContinuousMap.spectrum_eq_range, ← ContinuousMap.comp_assoc, ContinuousMap.coe_comp,
      ContinuousMap.coe_comp, range_comp, CFCElement.range_spectrum_map, ContinuousMap.coe_mk]
  exact elementalStarAlgebra.isClosed ℂ a

instance [CFCDomain X i] [hj : CFCDomain Y j] (f : C(X, Y)) (a : A) [CFCElement X a] :
    CFCElement Y (cfc f a) where
  isStarNormal := sorry
