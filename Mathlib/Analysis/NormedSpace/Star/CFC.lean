/-
Copyright (c) 2024 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus

open Set

variable {A X Y : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
  [CstarRing A] [StarModule ℂ A] [CompleteSpace A]
  [TopologicalSpace X] [TopologicalSpace Y] {i : X → ℂ} {j : Y → ℂ}

class CFCDomain (i : X → ℂ) (a : A) : Prop where
  isStarNormal : IsStarNormal a
  spectrum_subset : spectrum ℂ a ⊆ range i

instance {a : A} [IsStarNormal a] : CFCDomain id a where
  isStarNormal := inferInstance
  spectrum_subset := range_id ▸ subset_univ _

lemma IsSelfAdjoint.cfcDomain {a : A} (ha : IsSelfAdjoint a) : CFCDomain ((↑) : ℝ → ℂ) a where
  isStarNormal := ha.isStarNormal
  spectrum_subset z hz := ⟨z.re, .symm <| ha.mem_spectrum_eq_re hz⟩

instance {a : selfAdjoint A} : CFCDomain ((↑) : ℝ → ℂ) (a : A) :=
  a.2.cfcDomain

lemma cfcDomain_of_unitary {a : A} (ha : a ∈ unitary A) : CFCDomain ((↑) : circle → ℂ) a where
  isStarNormal := ⟨ha.1.trans ha.2.symm⟩ -- TODO: we should have a name for this
  spectrum_subset := Subtype.range_val ▸ spectrum.subset_circle_of_unitary ha

instance {a : unitary A} : CFCDomain ((↑) : circle → ℂ) (a : A) :=
  cfcDomain_of_unitary a.2

-- TODO: develop general `Embedding.lift`
noncomputable def CFCDomain.spectrumMap [Nonempty X] (hi : Embedding i) (a : A) [CFCDomain i a] :
    C(spectrum ℂ a, X) :=
  ⟨i.invFun ∘ (↑), hi.continuous_iff.mpr <| continuous_subtype_val.congr fun x ↦
    .symm <| i.invFun_eq <| spectrum_subset x.2⟩

lemma CFCDomain.apply_spectrum_map [Nonempty X] (hi : Embedding i) (a : A) [CFCDomain i a]
    (x : spectrum ℂ a) : i (spectrumMap hi a x) = x :=
  i.invFun_eq <| spectrum_subset x.2

lemma CFCDomain.range_spectrum_map [Nonempty X] (hi : Embedding i) (a : A) [CFCDomain i a] :
    range (spectrumMap hi a) = i ⁻¹' spectrum ℂ a :=
  subset_antisymm (range_subset_iff.mpr fun x ↦ by simp [apply_spectrum_map hi a])
    (fun x hx ↦ ⟨⟨i x, hx⟩, hi.inj i.apply_invFun_apply⟩)

variable [CstarRing A] [StarModule ℂ A] [CompleteSpace A] [Nonempty X]

noncomputable def cfc (hi : Embedding i) (hj : Embedding j) (f : C(X, Y)) (a : A)
    [CFCDomain i a] : A :=
  haveI : IsStarNormal a := CFCDomain.isStarNormal i
  ↑(continuousFunctionalCalculus a <| (⟨j, hj.continuous⟩ : C(Y, ℂ)).comp <| f.comp <|
    CFCDomain.spectrumMap hi a)

lemma spectrum_cfc_eq (hi : Embedding i) (hj : Embedding j) (f : C(X, Y)) (a : A)
    [CFCDomain i a] : spectrum ℂ (cfc hi hj f a) = (j ∘ f) '' (i ⁻¹' spectrum ℂ a) := by
  have : IsStarNormal a := CFCDomain.isStarNormal i
  rw [cfc, ← StarSubalgebra.spectrum_eq, AlgEquiv.spectrum_eq (continuousFunctionalCalculus a),
      ContinuousMap.spectrum_eq_range, ← ContinuousMap.comp_assoc, ContinuousMap.coe_comp,
      ContinuousMap.coe_comp, range_comp, CFCDomain.range_spectrum_map, ContinuousMap.coe_mk]
  exact elementalStarAlgebra.isClosed ℂ a
