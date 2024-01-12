/-
Copyright (c) 2024 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus

open Set

-- TODO : this is a terrible name...
class CFCEmb (S : Type*) [TopologicalSpace S] (i : outParam (S → ℂ)) extends Embedding i : Prop

instance : CFCEmb ℂ id where toEmbedding := embedding_id
instance {s : Set ℂ} : CFCEmb s (↑) where toEmbedding := embedding_subtype_val
instance {s : Submonoid ℂ} : CFCEmb s (↑) where toEmbedding := embedding_subtype_val
instance : CFCEmb ℝ (↑) where toEmbedding := Complex.isometry_ofReal.embedding

abbrev CFC.X (S : Type*) [TopologicalSpace S] {i : S → ℂ} [hi : CFCEmb S i] : C(S, ℂ) :=
  ⟨i, hi.continuous⟩

variable {A : Type*} (S T U : Type*) [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
  [CstarRing A] [StarModule ℂ A] [CompleteSpace A]
  [TopologicalSpace S] [TopologicalSpace T] [TopologicalSpace U] {i : S → ℂ} {j : T → ℂ} {k : U → ℂ}

-- TODO : this is a terrible name...
class CFCCompatible [TopologicalSpace S] {i : S → ℂ} [CFCEmb S i] (a : A) : Prop where
  isStarNormal : IsStarNormal a
  spectrum_subset : spectrum ℂ a ⊆ range i

instance {a : A} [IsStarNormal a] : CFCCompatible ℂ a where
  isStarNormal := inferInstance
  spectrum_subset := range_id ▸ subset_univ _

lemma IsSelfAdjoint.cfcCompatible {a : A} (ha : IsSelfAdjoint a) : CFCCompatible ℝ a where
  isStarNormal := ha.isStarNormal
  spectrum_subset z hz := ⟨z.re, .symm <| ha.mem_spectrum_eq_re hz⟩

instance {a : selfAdjoint A} : CFCCompatible ℝ (a : A) :=
  a.2.cfcCompatible

lemma cfcCompatible_of_unitary {a : A} (ha : a ∈ unitary A) : CFCCompatible circle a where
  isStarNormal := ⟨ha.1.trans ha.2.symm⟩ -- TODO: we should have a name for this
  spectrum_subset := Subtype.range_val ▸ spectrum.subset_circle_of_unitary ha

instance {a : unitary A} : CFCCompatible circle (a : A) :=
  cfcCompatible_of_unitary a.2

-- TODO: develop general `Embedding.lift`
noncomputable def CFCCompatible.spectrumMap [Nonempty S] [hi : CFCEmb S i] (a : A)
    [CFCCompatible S a] : C(spectrum ℂ a, S) :=
  ⟨i.invFun ∘ (↑), hi.continuous_iff.mpr <| continuous_subtype_val.congr fun x ↦
    .symm <| i.invFun_eq <| spectrum_subset x.2⟩

lemma CFCCompatible.apply_spectrum_map [Nonempty S] [CFCEmb S i] (a : A) [CFCCompatible S a]
    (x : spectrum ℂ a) : i (spectrumMap S a x) = x :=
  i.invFun_eq <| spectrum_subset x.2

lemma CFCCompatible.range_spectrum_map [Nonempty S] [hi : CFCEmb S i] (a : A) [CFCCompatible S a] :
    range (spectrumMap S a) = i ⁻¹' spectrum ℂ a :=
  -- ugly
  subset_antisymm (range_subset_iff.mpr fun x ↦ by simp [apply_spectrum_map S a])
    (fun x hx ↦ ⟨⟨i x, hx⟩, hi.inj i.apply_invFun_apply⟩)

variable {S T} [CstarRing A] [StarModule ℂ A] [CompleteSpace A] [Nonempty S] [Nonempty T]

noncomputable def cfc [CFCEmb S i] [CFCEmb T j] (f : C(S, T)) (a : A) [CFCCompatible S a] : A :=
  haveI : IsStarNormal a := CFCCompatible.isStarNormal i
  ↑(continuousFunctionalCalculus a <| (CFC.X T).comp <| f.comp <|
    CFCCompatible.spectrumMap S a)

lemma cfc_comp_emb [CFCEmb S i] [CFCEmb T j] (f : C(S, T)) (a : A) [CFCCompatible S a] :
    cfc f a = cfc (CFC.X T |>.comp f) a :=
  rfl -- unbelievable...

lemma cfc_ext [CFCEmb S i] [hj : CFCEmb T j] (f g : C(S, T)) (a : A)
    [CFCCompatible S a] (H : ∀ x ∈ (CFC.X S) ⁻¹' spectrum ℂ a, f x = g x) :
    cfc f a = cfc g a := by
  rw [cfc, cfc]
  congr 3
  ext x
  exact H _ <| by simp [CFCCompatible.apply_spectrum_map S a x]

lemma spectrum_cfc_eq [CFCEmb S i] [hj : CFCEmb T j] (f : C(S, T)) (a : A)
    [CFCCompatible S a] : spectrum ℂ (cfc f a) = (j ∘ f) '' (i ⁻¹' spectrum ℂ a) := by
  have : IsStarNormal a := CFCCompatible.isStarNormal i
  rw [cfc, ← StarSubalgebra.spectrum_eq, AlgEquiv.spectrum_eq (continuousFunctionalCalculus a),
      ContinuousMap.spectrum_eq_range, ← ContinuousMap.comp_assoc, ContinuousMap.coe_comp,
      ContinuousMap.coe_comp, range_comp, CFCCompatible.range_spectrum_map, ContinuousMap.coe_mk]
  exact elementalStarAlgebra.isClosed ℂ a

instance [CFCEmb S i] [hj : CFCEmb T j] (f : C(S, T)) (a : A) [CFCCompatible S a] :
    CFCCompatible T (cfc f a) where
  isStarNormal := sorry
  spectrum_subset := by
    rw [spectrum_cfc_eq, image_comp]
    exact image_subset_range _ _

lemma cfc_unique [CFCEmb S i] (a : A) [CFCCompatible S a] (Φ : C(S, ℂ) →⋆ₐ[ℂ] A)
    (hΦa : Φ (CFC.X S) = a)
    (hΦspec : ∀ (f g : C(S, ℂ)), (CFC.X S ⁻¹' spectrum ℂ a).EqOn f g → Φ f = Φ g)
    (f : C(S, ℂ)) :
    Φ f = cfc f a :=
  sorry

lemma cfc_comp [CFCEmb S i] [CFCEmb T j] [CFCEmb U k] (a : A) [CFCCompatible S a] (f : C(S, T))
    (g : C(T, U)) :
    cfc (g.comp f) a = cfc g (cfc f a) := by
  rw [cfc_comp_emb (f := g.comp f), cfc_comp_emb (f := g), ← ContinuousMap.comp_assoc]
  let Φ : C(T, ℂ) →⋆ₐ[ℂ] A :=
  { toFun := fun h ↦ cfc (h.comp f) a,
    map_one' := sorry,
    map_mul' := sorry
    map_zero' := sorry,
    map_add' := sorry,
    map_star' := sorry,
    commutes' := sorry }
  refine cfc_unique (cfc f a) Φ rfl (fun h₁ h₂ H ↦ cfc_ext _ _ a fun x hx ↦ H ?_)
    ((CFC.X U).comp g)
  sorry -- annoying but true, there's probably a better route

/-! Examples -/
