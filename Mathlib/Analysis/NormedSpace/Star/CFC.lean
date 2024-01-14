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

section defs

variable (S : Type*) [TopologicalSpace S] (i : outParam (S → ℂ))

class CFC.Domain extends Embedding i : Prop

class CFC.ZeroDomain [Zero S] [CFC.Domain S i] : Prop where
  map_zero' : i 0 = 0

class CFC.NegDomain [Neg S] [CFC.Domain S i] : Prop where
  map_neg' : ∀ x, i (-x) = -(i x)

class CFC.AddDomain [Add S] [CFC.Domain S i] : Prop where
  map_add' : ∀ x y, i (x + y) = i x + i y

class CFC.OneDomain [One S] [CFC.Domain S i] : Prop where
  map_one' : i 1 = 1

class CFC.MulDomain [Mul S] [CFC.Domain S i] : Prop where
  map_mul' : ∀ x y, i (x * y) = i x * i y

class CFC.StarDomain [Star S] [CFC.Domain S i] : Prop where
  map_star' : ∀ x, i (star x) = star (i x)

class CFC.SMulDomain (R : Type*) [SMul R S] [SMul R ℂ] [CFC.Domain S i] : Prop where
  map_smul' : ∀ (r : R) x, i (r • x) = r • (i x)

-- attribute [simp] CFC.ZeroDomain.map_zero'
-- attribute [simp] CFC.AddDomain.map_add'
-- attribute [simp] CFC.NegDomain.map_neg'
-- attribute [simp] CFC.MulDomain.map_mul'
-- attribute [simp] CFC.OneDomain.map_one'
-- attribute [simp] CFC.StarDomain.map_star'
-- attribute [simp] CFC.SMulDomain.map_smul'

end defs

section instances

instance : CFC.Domain ℂ id where toEmbedding := embedding_id
instance : CFC.ZeroDomain ℂ id where map_zero' := rfl
instance : CFC.NegDomain ℂ id where map_neg' _ := rfl
instance : CFC.AddDomain ℂ id where map_add' _ _ := rfl
instance : CFC.OneDomain ℂ id where map_one' := rfl
instance : CFC.MulDomain ℂ id where map_mul' _ _ := rfl
instance : CFC.StarDomain ℂ id where map_star' _ := rfl
instance : CFC.SMulDomain ℂ id ℂ where map_smul' _ _ := rfl
instance : CFC.SMulDomain ℂ id ℝ where map_smul' _ _ := rfl

instance {s : Set ℂ} : CFC.Domain s (↑) where toEmbedding := embedding_subtype_val

instance {s : Submonoid ℂ} : CFC.Domain s (↑) where toEmbedding := embedding_subtype_val
instance {s : Submonoid ℂ} : CFC.OneDomain s (↑) where map_one' := rfl
instance {s : Submonoid ℂ} : CFC.MulDomain s (↑) where map_mul' _ _ := rfl

instance : CFC.Domain ℝ (↑) where toEmbedding := Complex.isometry_ofReal.embedding
instance : CFC.ZeroDomain ℝ (↑) where map_zero' := rfl
instance : CFC.NegDomain ℝ (↑) where map_neg' := Complex.ofReal_neg
instance : CFC.AddDomain ℝ (↑) where map_add' := Complex.ofReal_add
instance : CFC.OneDomain ℝ (↑) where map_one' := rfl
instance : CFC.MulDomain ℝ (↑) where map_mul' := Complex.ofReal_mul
instance : CFC.StarDomain ℝ (↑) where map_star' _ := by simp [Complex.conj_ofReal]
instance : CFC.SMulDomain ℝ (↑) ℝ where map_smul' _ _ := by simp

instance : CFC.Domain ℝ≥0 (↑) where toEmbedding :=
  Complex.isometry_ofReal.embedding.comp embedding_subtype_val
instance : CFC.ZeroDomain ℝ≥0 (↑) where map_zero' := rfl
instance : CFC.AddDomain ℝ≥0 (↑) where map_add' := by simp
instance : CFC.OneDomain ℝ≥0 (↑) where map_one' := rfl
instance : CFC.MulDomain ℝ≥0 (↑) where map_mul' := by simp
instance : CFC.StarDomain ℝ≥0 (↑) where map_star' _ := by simp [Complex.conj_ofReal]

end instances

abbrev CFC.X (S : Type*) [TopologicalSpace S] {i : S → ℂ} [hi : CFC.Domain S i] : C(S, ℂ) :=
  ⟨i, hi.continuous⟩

lemma CFC.X_injective {S : Type*} [TopologicalSpace S] {i : S → ℂ} [CFC.Domain S i] :
    Function.Injective (CFC.X S) :=
  CFC.Domain.toEmbedding.inj

variable {A : Type*} (S T U V : Type*) [NormedRing A] [StarRing A] [NormedAlgebra ℂ A]
  [CstarRing A] [StarModule ℂ A] [CompleteSpace A]
  [TopologicalSpace S] [TopologicalSpace T] [TopologicalSpace U] [TopologicalSpace V]
  {i : S → ℂ} {j : T → ℂ} {k : U → ℂ} {l : V → ℂ}

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

variable {S T U V} [Nonempty S] [Nonempty T] [Nonempty U] [Nonempty V]

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

lemma cfc_ext' [CFC.Domain S i] [CFC.Domain T j] [hj : CFC.Domain U k] [CFC.Domain V l]
    (f : C(S, T)) (g : C(U, V)) (a : A) [CFC.Compatible S a] [CFC.Compatible U a]
    (H : ∀ x y, CFC.X S x ∈ spectrum ℂ a → CFC.X U y = CFC.X S x → CFC.X T (f x) = CFC.X V (g y)) :
    cfc f a = cfc g a := by
  rw [cfc, cfc]
  congr
  ext x
  refine H _ _ ?_ ?_ <;> simp [CFC.Compatible.apply_spectrumMap _ a x]

lemma cfc_ext [CFC.Domain S i] [CFC.Domain T j] (f g : C(S, T)) (a : A)
    [CFC.Compatible S a] (H : ∀ x ∈ (CFC.X S) ⁻¹' spectrum ℂ a, f x = g x) :
    cfc f a = cfc g a :=
  cfc_ext' f g a (fun x _y hx hxy ↦ (CFC.X_injective hxy).symm ▸ congrArg _ (H x hx))

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
-/

section

variable [CFC.Domain S i] [CFC.Domain T j]

lemma cfc_zero [Zero T] [hj : CFC.ZeroDomain T j] (a : A)
    [ha : CFC.Compatible S a] :
    cfc (0 : C(S, T)) a = 0 := by
  have := ha.isStarNormal
  have : ((CFC.X T).comp <| (0 : C(S, T)).comp <| CFC.Compatible.spectrumMap S a) = 0 := by
    ext _x
    exact hj.map_zero'
  rw [cfc, ← ZeroMemClass.coe_zero (elementalStarAlgebra ℂ a), this]
  congr
  exact map_zero (continuousFunctionalCalculus a)

lemma cfc_add [Add T] [ContinuousAdd T] [hj : CFC.AddDomain T j]
    (f g : C(S, T)) (a : A) [CFC.Compatible S a] :
    cfc (f + g) a = cfc f a + cfc g a := by
  rw [cfc, cfc, cfc, ← AddMemClass.coe_add, ← AddEquivClass.map_add]
  congr
  ext x
  exact hj.map_add' _ _

-- `[AddGroup T] [TopologicalAddGroup T]` because of too strong requirements for neg on `C(S, T)`
lemma cfc_neg [AddGroup T] [TopologicalAddGroup T] [hj : CFC.NegDomain T j]
    (f : C(S, T)) (a : A) [CFC.Compatible S a] :
    cfc (-f) a = -(cfc f a) := by
  sorry -- lacking lemma

lemma cfc_one [One T] [hj : CFC.OneDomain T j]
    (a : A) [ha : CFC.Compatible S a] :
    cfc (1 : C(S, T)) a = 1 := by
  have := ha.isStarNormal
  have : ((CFC.X T).comp <| (1 : C(S, T)).comp <| CFC.Compatible.spectrumMap S a) = 1 := by
    ext _x
    exact hj.map_one'
  rw [cfc, ← OneMemClass.coe_one (elementalStarAlgebra ℂ a), this]
  congr
  exact map_one (continuousFunctionalCalculus a)

lemma cfc_mul [Mul T] [ContinuousMul T] [hj : CFC.MulDomain T j]
    (f g : C(S, T)) (a : A)
    [CFC.Compatible S a] :
    cfc (f * g) a = cfc f a * cfc g a := by
  rw [cfc, cfc, cfc, ← MulMemClass.coe_mul, ← MulEquivClass.map_mul]
  congr
  ext x
  exact hj.map_mul' _ _

--lemma cfc_smul {R : Type*} [TopologicalSpace R] [SMul R T] [SMul R ℂ] [SMul R A]
--    [IsScalarTower R ℂ A] [ContinuousSMul R T] [CFC.Domain S i]
--    [CFC.Domain T j] (j_smul : ∀ (r : R) x, j (r • x) = r • j x) (r : R) (f : C(S, T)) (a : A)
--    [CFC.Compatible S a] :
--    cfc (r • f) a = r • (cfc f a) := by
--  sorry -- lacking lemma

--lemma cfc_algebraMap {R : Type*} [CommSemiring R] [Semiring T] [TopologicalSemiring T]
--    [Algebra R T] [Algebra R ℂ] [Algebra R A]
--    [CFC.Domain S i] [CFC.Domain T j]
--    (j_algMap : ∀ r : R, j (algebraMap R T r) = algebraMap R ℂ r)
--    (r : R) (a : A)
--    [CFC.Compatible S a] :
--    cfc (algebraMap R C(S, T) r) a = algebraMap R A r := by
--  sorry -- lacking lemma

lemma cfc_star [Star T] [ContinuousStar T] [hj : CFC.StarDomain T j]
    (f : C(S, T)) (a : A) [ha : CFC.Compatible S a] :
    cfc (star f) a = star (cfc f a) := by
  sorry -- lacking lemma

lemma cfc_isSelfAdjoint [Star T] [TrivialStar T] [ContinuousStar T]
    [hj : CFC.StarDomain T j] (f : C(S, T)) (a : A)
    [ha : CFC.Compatible S a] : IsSelfAdjoint (cfc f a) := by
  rw [IsSelfAdjoint, ← cfc_star, star_trivial]

lemma cfc_commute
    (f g : C(S, T)) (a : A) [ha : CFC.Compatible S a] :
    Commute (cfc f a) (cfc g a) :=
  have := ha.isStarNormal
  congrArg ((↑) : elementalStarAlgebra ℂ a → A) <|
    (Commute.all _ _).map (continuousFunctionalCalculus a)

instance cfc_isStarNormal (f : C(S, T)) (a : A)
    [ha : CFC.Compatible S a] : IsStarNormal (cfc f a) := .mk <| by
  rw [cfc_X_comp, ← cfc_star]
  exact cfc_commute _ _ a

end

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
    map_one' := cfc_one _,
    map_mul' := fun h₁ h₂ ↦ cfc_mul (h₁.comp f) (h₂.comp f) a,
    map_zero' := cfc_zero (T := ℂ) a,
    map_add' := fun h₁ h₂ ↦ cfc_add (h₁.comp f) (h₂.comp f) a,
    map_star' := fun h ↦ cfc_star (h.comp f) a,
    commutes' := sorry }
  refine cfc_unique (cfc f a) Φ rfl (fun h₁ h₂ H ↦ cfc_ext _ _ a fun x hx ↦ H ?_)
    ((CFC.X U).comp g)
  sorry -- easy with better API

lemma cfc_eq_self_of_X_commutes [CFC.Domain S i] [CFC.Domain T j] (f : C(S, T)) (a : A)
    [CFC.Compatible S a] (H : (CFC.X T).comp f = CFC.X S) :
    cfc f a = a := by
  rw [cfc_X_comp, H, cfc_X]

lemma cfc_id [CFC.Domain S i] (a : A) [CFC.Compatible S a] :
    cfc (.id S) a = a :=
  cfc_eq_self_of_X_commutes _ _ rfl

/-!
### Algebraic properties following from composition
-/

section

variable [CFC.Domain S i] [CFC.Domain T j]

variable (S) in
lemma neg_eq_cfc [AddGroup S] [TopologicalAddGroup S] [CFC.NegDomain S i] (a : A)
    [CFC.Compatible S a] : -a = cfc (- .id S) a := calc
  -a = -(cfc (.id S) a) := by rw [cfc_id]
  _  = cfc (- .id S) a := .symm <| cfc_neg _ _

-- TODO add IsStarNormal.neg even though not needed
instance CFC.Compatible.neg [AddGroup S] [TopologicalAddGroup S] [CFC.NegDomain S i] (a : A)
    [CFC.Compatible S a] : CFC.Compatible S (-a) := neg_eq_cfc S a ▸ inferInstance

lemma cfc_neg_comm [AddGroup S] [TopologicalAddGroup S] [CFC.NegDomain S i] [CFC.Domain T j]
    (f : C(S, T)) (a : A) [CFC.Compatible S a] : cfc f (-a) = cfc (f.comp (- .id S)) a := by
  simp_rw [neg_eq_cfc S a, cfc_comp]

end

/-!
### Examples
-/

noncomputable def CstarRing.abs (a : A) [IsStarNormal a] : selfAdjoint A :=
  ⟨cfc ⟨(‖·‖ : ℂ → ℝ), continuous_norm⟩ a, cfc_isSelfAdjoint _ _⟩

theorem CstarRing.coe_abs (a : A) [IsStarNormal a] :
    (↑(CstarRing.abs a) : A) = cfc ⟨(‖·‖ : ℂ → ℝ), continuous_norm⟩ a :=
  rfl

noncomputable instance selfAdjoint.hasPosPart : PosPart (selfAdjoint A) where
  pos a := ⟨cfc (PosPart.pos (.id ℝ)) a, cfc_isSelfAdjoint _ _⟩

theorem selfAdjoint.coe_pos_part (a : selfAdjoint A) :
    (↑(a⁺) : A) = cfc (PosPart.pos (.id ℝ)) (a : A) :=
  rfl

noncomputable instance selfAdjoint.hasNegPart : NegPart (selfAdjoint A) where
  neg a := ⟨cfc (NegPart.neg (.id ℝ)) a, cfc_isSelfAdjoint _ _⟩

theorem selfAdjoint.coe_neg_part (a : selfAdjoint A) :
    (↑(a⁻) : A) = cfc (NegPart.neg (.id ℝ)) (a : A) :=
  rfl

theorem selfAdjoint.coe_abs (a : selfAdjoint A) :
    (↑(CstarRing.abs (a : A)) : A) = cfc (|.id ℝ|) (a : A) :=
  cfc_ext' _ _ (a : A) fun x y _ (hxy : ↑y = x) ↦ hxy.symm ▸ by simp

-- TODO: move
lemma ContinuousMap.pos_part_comp (f : C(S, ℝ)) (g : C(T, S)) : f⁺.comp g = (f.comp g)⁺ := by
  sorry

lemma ContinuousMap.neg_part_comp (f : C(S, ℝ)) (g : C(T, S)) : f⁻.comp g = (f.comp g)⁻ := by
  sorry

theorem selfAdjoint.neg_part_neg (a : selfAdjoint A) : (-a)⁻ = a⁺ := by
  ext
  simp_rw [selfAdjoint.coe_neg_part, selfAdjoint.coe_pos_part, AddSubgroupClass.coe_neg a,
    cfc_neg_comm, ContinuousMap.neg_part_comp, ContinuousMap.id_comp,
    ← LatticeOrderedGroup.pos_eq_neg_neg]

theorem selfAdjoint.pos_part_neg (a : selfAdjoint A) : (-a)⁺ = a⁻ := by
  simpa only [neg_neg] using (selfAdjoint.neg_part_neg (-a)).symm

theorem selfAdjoint.pos_part_sub_neg_part (a : selfAdjoint A) : a⁺ - a⁻ = a := by
  ext
  rw [AddSubgroupClass.coe_sub, selfAdjoint.coe_neg_part, selfAdjoint.coe_pos_part,
      sub_eq_add_neg, ← cfc_neg, ← cfc_add, ← sub_eq_add_neg, LatticeOrderedGroup.pos_sub_neg,
      cfc_id]

theorem CstarRing.pos_part_add_neg_part (a : selfAdjoint A) : a⁺ + a⁻ = CstarRing.abs (a : A) := by
  ext
  rw [AddMemClass.coe_add, selfAdjoint.coe_neg_part, selfAdjoint.coe_pos_part,
      ← cfc_add, ← LatticeOrderedGroup.pos_add_neg, selfAdjoint.coe_abs]

theorem selfAdjoint.pos_part_mul_neg_part (a : selfAdjoint A) : (↑(a⁺) : A) * ↑(a⁻) = 0 := by
  rw [selfAdjoint.coe_pos_part, selfAdjoint.coe_neg_part, ← cfc_mul]
  convert cfc_zero (a : A)
  ext x
  simp only [LatticeOrderedGroup.pos_part_def, LatticeOrderedGroup.neg_part_def,
    ContinuousMap.mul_apply, ContinuousMap.sup_apply, ContinuousMap.id_apply,
    ContinuousMap.zero_apply, ContinuousMap.neg_apply]
  rcases (le_total x 0) with (hx|hx) <;> simp [hx] <;> rfl
  all_goals infer_instance

-- it is essential to use coercions here because `self_adjoint A` can't have a `has_mul` instance
theorem selfAdjoint.neg_part_mul_pos_part (a : selfAdjoint A) : (↑(a⁻) : A) * ↑(a⁺) = 0 := by
  convert selfAdjoint.pos_part_mul_neg_part a using 1
  exact cfc_commute _ _ _
