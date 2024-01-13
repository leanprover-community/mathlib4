/-
Copyright (c) 2024 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Analysis.NormedSpace.Star.ContinuousFunctionalCalculus

open Set
open scoped NNReal

/-!
### `CFC.Domain`

A typeclass for types used as domains and codomains for functional calculus
-/

-- TODO : this is a terrible name...
class CFC.Domain (S : Type*) [TopologicalSpace S] (i : outParam (S → ℂ)) extends Embedding i : Prop

instance : CFC.Domain ℂ id where toEmbedding := embedding_id
instance {s : Set ℂ} : CFC.Domain s (↑) where toEmbedding := embedding_subtype_val
instance {s : Submonoid ℂ} : CFC.Domain s (↑) where toEmbedding := embedding_subtype_val
instance : CFC.Domain ℝ (↑) where toEmbedding := Complex.isometry_ofReal.embedding
instance : CFC.Domain ℝ≥0 (↑) where toEmbedding :=
  Complex.isometry_ofReal.embedding.comp embedding_subtype_val

abbrev CFC.X (S : Type*) [TopologicalSpace S] {i : S → ℂ} [hi : CFC.Domain S i] : C(S, ℂ) :=
  ⟨i, hi.continuous⟩

variable {A : Type*} (S T U : Type*) [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
  [CstarRing A] [StarModule ℂ A] [CompleteSpace A]
  [TopologicalSpace S] [TopologicalSpace T] [TopologicalSpace U] {i : S → ℂ} {j : T → ℂ} {k : U → ℂ}

/-!
### `CFC.Compatible`

An element `a` is compatible with a domain `S` if the spectrum of `a` lies in `S`
-/

-- TODO : this is a terrible name...
class CFC.Compatible [TopologicalSpace S] {i : S → ℂ} [CFC.Domain S i] (a : A) : Prop where
  isStarNormal : IsStarNormal a
  spectrum_subset : spectrum ℂ a ⊆ range i

instance {a : A} [IsStarNormal a] : CFC.Compatible ℂ a where
  isStarNormal := inferInstance
  spectrum_subset := range_id ▸ subset_univ _

lemma IsSelfAdjoint.cfcCompatible {a : A} (ha : IsSelfAdjoint a) : CFC.Compatible ℝ a where
  isStarNormal := ha.isStarNormal
  spectrum_subset z hz := ⟨z.re, .symm <| ha.mem_spectrum_eq_re hz⟩

instance {a : selfAdjoint A} : CFC.Compatible ℝ (a : A) :=
  a.2.cfcCompatible

lemma cfcCompatible_of_unitary {a : A} (ha : a ∈ unitary A) : CFC.Compatible circle a where
  isStarNormal := ⟨ha.1.trans ha.2.symm⟩ -- TODO: we should have a name for this
  spectrum_subset := Subtype.range_val ▸ spectrum.subset_circle_of_unitary ha

instance {a : unitary A} : CFC.Compatible circle (a : A) :=
  cfcCompatible_of_unitary a.2

/-!
### Construction of continuous functional calculus + basic properties
-/

-- TODO: develop general `Embedding.lift`
noncomputable def CFC.Compatible.spectrumMap [Nonempty S] [hi : CFC.Domain S i] (a : A)
    [CFC.Compatible S a] : C(spectrum ℂ a, S) :=
  ⟨i.invFun ∘ (↑), hi.continuous_iff.mpr <| continuous_subtype_val.congr fun x ↦
    .symm <| i.invFun_eq <| spectrum_subset x.2⟩

lemma CFC.Compatible.apply_spectrumMap [Nonempty S] [CFC.Domain S i] (a : A) [CFC.Compatible S a]
    (x : spectrum ℂ a) : i (spectrumMap S a x) = x :=
  i.invFun_eq <| spectrum_subset x.2

lemma CFC.Compatible.X_comp_spectrumMap [Nonempty S] [CFC.Domain S i] (a : A) [CFC.Compatible S a] :
    (CFC.X S).comp (spectrumMap S a) = ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) := by
  ext x
  exact CFC.Compatible.apply_spectrumMap S a x

lemma CFC.Compatible.range_spectrum_map [Nonempty S] [hi : CFC.Domain S i] (a : A)
    [CFC.Compatible S a] : range (spectrumMap S a) = i ⁻¹' spectrum ℂ a :=
  -- ugly
  subset_antisymm (range_subset_iff.mpr fun x ↦ by simp [apply_spectrumMap S a])
    (fun x hx ↦ ⟨⟨i x, hx⟩, hi.inj i.apply_invFun_apply⟩)

variable {S T U} [Nonempty S] [Nonempty T]

noncomputable def cfc [CFC.Domain S i] [CFC.Domain T j] (f : C(S, T)) (a : A)
    [CFC.Compatible S a] : A :=
  haveI : IsStarNormal a := CFC.Compatible.isStarNormal i
  ↑(continuousFunctionalCalculus a <| (CFC.X T).comp <| f.comp <|
    CFC.Compatible.spectrumMap S a)

lemma cfc_X [CFC.Domain S i] (a : A) [ha : CFC.Compatible S a] :
    cfc (CFC.X S) a = a := by
  have := ha.isStarNormal
  rw [cfc, CFC.Compatible.X_comp_spectrumMap]
  exact congrArg _ (continuousFunctionalCalculus_map_id a)

lemma cfc_X_comp [CFC.Domain S i] [CFC.Domain T j] (f : C(S, T)) (a : A) [CFC.Compatible S a] :
    cfc f a = cfc (CFC.X T |>.comp f) a :=
  rfl -- unbelievable...

lemma cfc_ext' [CFC.Domain S i] [CFC.Domain T j] [hj : CFC.Domain U k] (f : C(S, T))
    (g : C(S, U)) (a : A) [CFC.Compatible S a]
    (H : ∀ x ∈ (CFC.X S) ⁻¹' spectrum ℂ a, CFC.X T (f x) = CFC.X U (g x)) :
    cfc f a = cfc g a := by
  rw [cfc, cfc]
  congr 3
  ext x
  exact H _ <| by simp [CFC.Compatible.apply_spectrumMap S a x]

lemma cfc_ext [CFC.Domain S i] [CFC.Domain T j] (f g : C(S, T)) (a : A)
    [CFC.Compatible S a] (H : ∀ x ∈ (CFC.X S) ⁻¹' spectrum ℂ a, f x = g x) :
    cfc f a = cfc g a :=
  cfc_ext' f g a (fun x hx ↦ congrArg _ (H x hx))

lemma cfc_mem [Star T] [ContinuousStar T] [CFC.Domain S i] [CFC.Domain T j]
    (f : C(S, T)) (a : A) [CFC.Compatible S a] :
    cfc f a ∈ elementalStarAlgebra ℂ a :=
  SetLike.coe_mem _

lemma spectrum_cfc_eq [CFC.Domain S i] [hj : CFC.Domain T j] (f : C(S, T)) (a : A)
    [CFC.Compatible S a] : spectrum ℂ (cfc f a) = (j ∘ f) '' (i ⁻¹' spectrum ℂ a) := by
  have : IsStarNormal a := CFC.Compatible.isStarNormal i
  rw [cfc, ← StarSubalgebra.spectrum_eq, AlgEquiv.spectrum_eq (continuousFunctionalCalculus a),
      ContinuousMap.spectrum_eq_range, ← ContinuousMap.comp_assoc, ContinuousMap.coe_comp,
      ContinuousMap.coe_comp, range_comp, CFC.Compatible.range_spectrum_map, ContinuousMap.coe_mk]
  exact elementalStarAlgebra.isClosed ℂ a

/-!
### Algebraic properties

TODO : write a tactic to try filling the algebra fields
-/

lemma cfc_zero [Zero T] [CFC.Domain S i] [hj : CFC.Domain T j] (j_zero : j 0 = 0)
    (a : A) [ha : CFC.Compatible S a] :
    cfc (0 : C(S, T)) a = 0 := by
  have := ha.isStarNormal
  have : ((CFC.X T).comp <| (0 : C(S, T)).comp <| CFC.Compatible.spectrumMap S a) = 0 := by
    ext _x
    exact j_zero
  rw [cfc, ← ZeroMemClass.coe_zero (elementalStarAlgebra ℂ a), this]
  congr
  exact map_zero (continuousFunctionalCalculus a)

lemma cfc_add [Add T] [ContinuousAdd T] [CFC.Domain S i] [hj : CFC.Domain T j]
    (j_add : ∀ x y, j (x + y) = j x + j y) (f g : C(S, T)) (a : A)
    [CFC.Compatible S a] :
    cfc (f + g) a = cfc f a + cfc g a := by
  rw [cfc, cfc, cfc, ← AddMemClass.coe_add, ← AddEquivClass.map_add]
  congr
  ext x
  exact j_add _ _

lemma cfc_one [One T] [CFC.Domain S i] [hj : CFC.Domain T j] (j_one : j 1 = 1)
    (a : A) [ha : CFC.Compatible S a] :
    cfc (1 : C(S, T)) a = 1 := by
  have := ha.isStarNormal
  have : ((CFC.X T).comp <| (1 : C(S, T)).comp <| CFC.Compatible.spectrumMap S a) = 1 := by
    ext _x
    exact j_one
  rw [cfc, ← OneMemClass.coe_one (elementalStarAlgebra ℂ a), this]
  congr
  exact map_one (continuousFunctionalCalculus a)

lemma cfc_mul [Mul T] [ContinuousMul T] [CFC.Domain S i] [hj : CFC.Domain T j]
    (j_mul : ∀ x y, j (x * y) = j x * j y) (f g : C(S, T)) (a : A)
    [CFC.Compatible S a] :
    cfc (f * g) a = cfc f a * cfc g a := by
  rw [cfc, cfc, cfc, ← MulMemClass.coe_mul, ← MulEquivClass.map_mul]
  congr
  ext x
  exact j_mul _ _

lemma cfc_smul {R : Type*} [TopologicalSpace R] [SMul R T] [SMul R ℂ] [SMul R A]
    [IsScalarTower R ℂ A] [ContinuousSMul R T] [CFC.Domain S i]
    [CFC.Domain T j] (j_smul : ∀ (r : R) x, j (r • x) = r • j x) (r : R) (f : C(S, T)) (a : A)
    [CFC.Compatible S a] :
    cfc (r • f) a = r • (cfc f a) := by
  sorry -- lacking lemma

lemma cfc_algebraMap {R : Type*} [CommSemiring R] [Semiring T] [TopologicalSemiring T]
    [Algebra R T] [Algebra R ℂ] [Algebra R A]
    [CFC.Domain S i] [CFC.Domain T j]
    (j_algMap : ∀ r : R, j (algebraMap R T r) = algebraMap R ℂ r)
    (r : R) (a : A)
    [CFC.Compatible S a] :
    cfc (algebraMap R C(S, T) r) a = algebraMap R A r := by
  sorry -- lacking lemma

lemma cfc_star [Star T] [ContinuousStar T] [CFC.Domain S i] [hj : CFC.Domain T j]
    (j_star : ∀ x, j (star x) = star (j x)) (f : C(S, T)) (a : A) [ha : CFC.Compatible S a] :
    cfc (star f) a = star (cfc f a) := by
  sorry -- lacking lemma

lemma cfc_isSelfAdjoint [Star T] [TrivialStar T] [ContinuousStar T] [CFC.Domain S i]
    [hj : CFC.Domain T j] (j_star : ∀ x, j (star x) = star (j x)) (f : C(S, T)) (a : A)
    [ha : CFC.Compatible S a] : IsSelfAdjoint (cfc f a) := by
  rw [IsSelfAdjoint, ← cfc_star j_star, star_trivial]

lemma cfc_commute [CFC.Domain S i] [CFC.Domain T j]
    (f g : C(S, T)) (a : A) [ha : CFC.Compatible S a] :
    Commute (cfc f a) (cfc g a) :=
  have := ha.isStarNormal
  congrArg ((↑) : elementalStarAlgebra ℂ a → A) <|
    (Commute.all _ _).map (continuousFunctionalCalculus a)

instance cfc_isStarNormal [CFC.Domain S i] [CFC.Domain T j] (f : C(S, T)) (a : A)
    [ha : CFC.Compatible S a] : IsStarNormal (cfc f a) := .mk <| by
  rw [cfc_X_comp, ← cfc_star (by intro; rfl)]
  exact cfc_commute _ _ a

/-!
### Composition
-/

instance [CFC.Domain S i] [hj : CFC.Domain T j] (f : C(S, T)) (a : A) [CFC.Compatible S a] :
    CFC.Compatible T (cfc f a) where
  isStarNormal := inferInstance
  spectrum_subset := by
    rw [spectrum_cfc_eq, image_comp]
    exact image_subset_range _ _

lemma cfc_unique [CFC.Domain S i] (a : A) [CFC.Compatible S a] (Φ : C(S, ℂ) →⋆ₐ[ℂ] A)
    (hΦa : Φ (CFC.X S) = a)
    (hΦspec : ∀ (f g : C(S, ℂ)), (CFC.X S ⁻¹' spectrum ℂ a).EqOn f g → Φ f = Φ g)
    (f : C(S, ℂ)) :
    Φ f = cfc f a :=
  sorry

lemma cfc_comp [CFC.Domain S i] [CFC.Domain T j] [CFC.Domain U k] (a : A) [CFC.Compatible S a]
    (f : C(S, T)) (g : C(T, U)) :
    cfc (g.comp f) a = cfc g (cfc f a) := by
  rw [cfc_X_comp (f := g.comp f), cfc_X_comp (f := g), ← ContinuousMap.comp_assoc]
  let Φ : C(T, ℂ) →⋆ₐ[ℂ] A :=
  { toFun := fun h ↦ cfc (h.comp f) a,
    map_one' := cfc_one rfl _,
    map_mul' := fun h₁ h₂ ↦ cfc_mul (fun _ _ ↦ rfl) (h₁.comp f) (h₂.comp f) a,
    map_zero' := cfc_zero rfl (T := ℂ) a,
    map_add' := fun h₁ h₂ ↦ cfc_add (fun _ _ ↦ rfl) (h₁.comp f) (h₂.comp f) a,
    map_star' := fun h ↦ cfc_star (fun _ ↦ by rfl) (h.comp f) a,
    commutes' := fun r ↦ cfc_algebraMap (fun _ ↦ rfl) r a }
  refine cfc_unique (cfc f a) Φ rfl (fun h₁ h₂ H ↦ cfc_ext _ _ a fun x hx ↦ H ?_)
    ((CFC.X U).comp g)
  sorry -- easy with better API

lemma cfc_eq_self_of_X_commutes [CFC.Domain S i] [CFC.Domain T j] (f : C(S, T)) (a : A)
    [CFC.Compatible S a] (H : (CFC.X T).comp f = CFC.X S) :
    cfc f a = a := by
  rw [cfc_X_comp, H, cfc_X]

/-!
### Examples
-/

noncomputable instance selfAdjoint.hasPosPart : PosPart (selfAdjoint A) where
  pos a := ⟨cfc (ContinuousMap.id ℝ ⊔ 0) a,
    cfc_isSelfAdjoint (fun _ ↦ by simp [Complex.conj_ofReal]) _ _⟩
