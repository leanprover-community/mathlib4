/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.Analysis.Normed.Field.WithAbs

/-!
# Dimensions of completions at infinite places

Let `L/K` and `w` be an infinite place of `L` lying above the infinite place `v` of `K`.
In this file, we prove:
- the sum of the ramification indices of all such places `w` is the same as `[L : K]`;
- the `v.Completion` dimension of `w.Completion` is equal to the ramification index.
-/

open scoped Classical

noncomputable section

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L]
variable [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}

theorem comap_embedding_eq_of_isReal (h : (w.comap (algebraMap K L)).IsReal) :
    (w.comap (algebraMap K L)).embedding = w.embedding.comp (algebraMap K L) := by
  rw [← mk_embedding w, comap_mk, mk_embedding, embedding_mk_eq_of_isReal
    (by rwa [← isReal_mk_iff, ← comap_mk, mk_embedding])]

theorem comap_mk_of_isExtension {ψ : L →+* ℂ} (hψ : IsExtension v.embedding ψ) :
    (mk ψ).comap (algebraMap K L) = v := by
  rw [comap_mk, hψ, mk_embedding]

variable (w)

namespace RamifiedExtension

open Extension

variable (w : v.RamifiedExtension L)

theorem isExtension_embedding : IsExtension v.embedding w.1.embedding := by
  rw [IsExtension, ← congrArg embedding w.comap_eq,
    ← comap_embedding_eq_of_isReal w.isReal_comap]

instance : IsLift L v w := ⟨w.isExtension_embedding⟩

theorem isExtension_conjugate_embedding : IsExtension v.embedding (conjugate w.1.embedding) := by
  rw [IsExtension, ← ComplexEmbedding.isReal_iff.1 <| isReal_iff.1 w.isReal,
    ← congrArg InfinitePlace.embedding w.comap_eq]
  simp [comap_embedding_eq_of_isReal w.isReal_comap]

instance : IsConjugateLift L v w := ⟨w.isExtension_conjugate_embedding⟩

theorem isMixedExtension : IsMixedExtension v.embedding w.1.embedding :=
  ⟨w.isExtension_embedding, isReal_iff.1 w.isReal, isComplex_iff.1 w.isComplex⟩

theorem isMixedExtension_conjugate : IsMixedExtension v.embedding (conjugate w.1.embedding) :=
  ⟨w.isExtension_conjugate_embedding, isReal_iff.1 w.isReal,
    mt ComplexEmbedding.isReal_conjugate_iff.1 <| isComplex_iff.1 w.isComplex⟩

/-- A mixed extension `ψ : L →+* ℂ` determines a ramified infinite place `w` lying above `v`. -/
def ofIsMixedExtension {ψ : L →+* ℂ} (h : IsMixedExtension v.embedding ψ) :
    RamifiedExtension L v := by
  refine ⟨mk ψ, comap_mk_of_isExtension h.1, ?_⟩
  rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, h.1, embedding_mk_eq_of_isReal h.2.1]
  refine ⟨?_, h.2.1⟩
  cases embedding_mk_eq ψ with
  | inl hψ =>
    rw [hψ]; exact h.2.2
  | inr hψ =>
    rw [hψ, ComplexEmbedding.isReal_conjugate_iff]
    exact h.2.2

/-- The conjugate of a mixed extension `ψ : L →+* ℂ` determines a ramified infinite place
`w` lying above `v`. -/
def ofIsMixedExtension_conjugate {ψ : L →+* ℂ} (h : IsMixedExtension v.embedding ψ) :
    RamifiedExtension L v := by
  refine ⟨mk ψ, comap_mk_of_isExtension h.1, ?_⟩
  rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, h.1, embedding_mk_eq_of_isReal h.2.1]
  refine ⟨?_, h.2.1⟩
  cases embedding_mk_eq ψ with
  | inl hψ =>
    rw [hψ]; exact h.2.2
  | inr hψ =>
    rw [hψ, ComplexEmbedding.isReal_conjugate_iff]
    exact h.2.2

theorem ofIsMixedExtension_embedding {ψ : L →+* ℂ} (h : IsMixedExtension v.embedding ψ) :
    (ofIsMixedExtension h).1.embedding = ψ ∨ conjugate (ofIsMixedExtension h).1.embedding = ψ := by
  cases embedding_mk_eq ψ with
  | inl hl => exact Or.inl hl
  | inr hr => right; simp_rw [star_eq_iff_star_eq, ← hr]; rfl

variable (L v)

/-- If `w` is a ramified place above `v` then `w.embedding` and `conjugate w.embedding`
are distinct mixed extensions of `v.embedding`, giving a two-fold map from `RamifiedExtension`
to the type of all mixed extensions of `v.embedding`. -/
def toIsMixedExtension (w : v.RamifiedExtension L ⊕ v.RamifiedExtension L) :
    { ψ : L →+* ℂ // IsMixedExtension v.embedding ψ } :=
  let f : v.RamifiedExtension L → { ψ : L →+* ℂ // IsMixedExtension v.embedding ψ } :=
    Subtype.map (fun w => w.embedding) (fun w h => isMixedExtension ⟨w, h⟩)
  let g : v.RamifiedExtension L → { ψ : L →+* ℂ // IsMixedExtension v.embedding ψ } :=
    Subtype.map (fun w => conjugate w.embedding) (fun w h => isMixedExtension_conjugate ⟨w, h⟩)
  Sum.elim f g w

theorem toIsMixedExtension_injective : (toIsMixedExtension L v).Injective := by
  apply Subtype.map_injective _ (embedding_injective _) |>.sumElim
    (Subtype.map_injective _ (conjugate_embedding_injective _))
  exact Subtype.map_ne _ _ (fun w h => isMixedExtension ⟨w, h⟩)
    (fun w h => isMixedExtension_conjugate ⟨w, h⟩)
    (fun _ _ _ h => h.2.ne_conjugate)

theorem toIsMixedExtension_surjective : (toIsMixedExtension L v).Surjective := by
  intro ⟨ψ, h⟩
  cases ofIsMixedExtension_embedding h with
  | inl hl =>
    use Sum.inl (ofIsMixedExtension h)
    simp [toIsMixedExtension, Subtype.map_def, hl]
  | inr hr =>
    use Sum.inr (ofIsMixedExtension h)
    simp [toIsMixedExtension, Subtype.map_def, hr]

/-- The equivalence between two copies of ramified places `w` over `v` and the type of all
mixed extensions of `v.embedding`. -/
def sumEquivIsMixedExtension :
    v.RamifiedExtension L ⊕ v.RamifiedExtension L ≃
      { ψ : L →+* ℂ // IsMixedExtension v.embedding ψ } :=
  Equiv.ofBijective _ ⟨toIsMixedExtension_injective L v, toIsMixedExtension_surjective L v⟩

theorem two_mul_card_eq [NumberField L] :
    2 * Fintype.card (v.RamifiedExtension L) =
      Fintype.card { ψ : L →+* ℂ // IsMixedExtension v.embedding ψ } := by
  simp [← Fintype.card_eq.2 ⟨sumEquivIsMixedExtension L v⟩]
  ring

end RamifiedExtension

namespace IsUnramified

variable {w}

theorem not_isMixedExtension (h : w.IsUnramified K) (hw : w.comap (algebraMap K L) = v):
    ¬IsMixedExtension v.embedding w.embedding := by
  contrapose! h
  rw [not_isUnramified_iff, isComplex_iff, isReal_iff]
  aesop

theorem not_isMixedExtension_conjugate (h : w.IsUnramified K) (hw : w.comap (algebraMap K L) = v):
    ¬IsMixedExtension v.embedding (conjugate w.embedding) := by
  contrapose! h
  rw [not_isUnramified_iff, isComplex_iff, isReal_iff]
  aesop

end IsUnramified

namespace UnramifiedExtension

open Extension

variable {w : v.UnramifiedExtension L}

theorem isUnmixedExtension (h : IsExtension v.embedding w.1.embedding) :
    IsUnmixedExtension v.embedding w.1.embedding :=
  ⟨h, w.isUnramified.not_isMixedExtension w.comap_eq⟩

instance : Coe (v.UnramifiedExtension L) (v.Extension L) where
  coe w := ⟨w.1, w.comap_eq⟩

theorem isUnmixedExtension_conjugate (h : ¬IsExtension v.embedding w.1.embedding) :
    IsUnmixedExtension v.embedding (conjugate w.1.embedding) :=
  ⟨isExtension_conjugate_of_not_isExtension (w : v.Extension L) h,
    w.isUnramified.not_isMixedExtension_conjugate w.comap_eq⟩

theorem isReal_of_isReal (w : UnramifiedExtension L v) (hv : v.IsReal) : w.1.IsReal :=
  (InfinitePlace.isUnramified_iff.1 w.isUnramified).resolve_right
    (by simpa [w.comap_eq] using not_isComplex_iff_isReal.2 hv)

theorem isComplex_base {w : UnramifiedExtension L v} (hw : w.1.IsComplex) :
    v.IsComplex :=
  not_isReal_iff_isComplex.1 <| mt w.isReal_of_isReal <| not_isReal_iff_isComplex.2 hw

theorem not_isExtension_iff_isExtension_conj (w : UnramifiedExtension L v)
    (hw : w.1.IsComplex) :
    ¬IsExtension v.embedding (w.1.embedding) ↔
      IsExtension v.embedding (conjugate w.1.embedding) := by
  refine ⟨isExtension_conjugate_of_not_isExtension (w : v.Extension L), ?_⟩
  intro hc h
  have hv_isComplex : v.IsComplex := w.isComplex_base hw
  rw [isComplex_iff, ComplexEmbedding.isReal_iff, RingHom.ext_iff, not_forall] at hv_isComplex
  let ⟨x, hx⟩ := hv_isComplex
  exact hx <| RingHom.congr_fun hc x ▸ ComplexEmbedding.conjugate_comp _ (algebraMap K L) ▸
    RingHom.congr_fun (congrArg conjugate h) x |>.symm

/-- An unmixed extension `ψ : L →+* ℂ` determines an unramified infinite place `w`
lying above `v`. -/
def ofIsUnmixedExtension {ψ : L →+* ℂ}
    (h : IsUnmixedExtension v.embedding ψ) :
    UnramifiedExtension L v := by
  refine ⟨mk ψ, comap_mk_of_isExtension h.1, ?_⟩
  rw [isUnramified_iff, isReal_iff]
  by_cases hv : ComplexEmbedding.IsReal v.embedding
  · simpa [embedding_mk_eq_of_isReal <| h.isReal_of_isReal hv] using Or.inl (h.isReal_of_isReal hv)
  · simpa [comap_mk, h.1, mk_embedding, isComplex_iff] using Or.inr hv

@[simp]
theorem ofIsUnmixedExtension_embedding {ψ : L →+* ℂ}
    (h : IsUnmixedExtension v.embedding ψ) :
    (ofIsUnmixedExtension h).1.embedding = (mk ψ).embedding :=
  rfl

theorem ofIsUnmixedExtension_embedding_isExtension {ψ : L →+* ℂ}
    (h : IsUnmixedExtension v.embedding ψ) :
    letI w := ofIsUnmixedExtension h
    ((IsExtension v.embedding w.1.embedding ∧ w.1.embedding = ψ) ∨
      (¬IsExtension v.embedding w.1.embedding ∧ conjugate w.1.embedding = ψ)) := by
  by_cases hv : ComplexEmbedding.IsReal v.embedding
  · simpa [embedding_mk_eq_of_isReal <| h.isReal_of_isReal hv] using Or.inl h.1
  · cases embedding_mk_eq ψ with
    | inl hl => simpa [hl] using Or.inl h.1
    | inr hr =>
      rw [not_isExtension_iff_isExtension_conj _
        (isComplex_mk_iff.2 <| h.1.not_isReal_of_not_isReal hv)]
      simpa [ofIsUnmixedExtension_embedding, hr] using Or.inr h.1

variable (L v)

/-- If `w` is an unramified place above `v` then there are the following two cases:
- `v` and `w` are both real;
- `v` and `w` are both complex.
In the first case `w.embedding` and `conjugate w.embedding` coincide. In the second case
only one of `w.embedding` and `conjugate w.embedding` can extend `v.embedding`. In both cases
then, there is a unique unmixed extension of `v.embedding` associated to the unramified
place `w` over `v`. -/
def toIsUnmixedExtension (w : UnramifiedExtension L v) :
    { ψ : L →+* ℂ // IsUnmixedExtension v.embedding ψ } :=
  let f := Subtype.map (fun w => w.1.embedding) (fun w h => w.isUnmixedExtension h)
  let g := Subtype.map (fun w => conjugate w.1.embedding)
    (fun w h => w.isUnmixedExtension_conjugate h)
  if h : IsExtension v.embedding w.1.embedding then f ⟨w, h⟩ else g ⟨w, h⟩

variable {L v} in
theorem toIsUnmixedExtension_ofIsUnmixedExtension {ψ : L →+* ℂ}
    (h : IsUnmixedExtension v.embedding ψ) :
    toIsUnmixedExtension L v (ofIsUnmixedExtension h) = ⟨ψ, h⟩ := by
  cases ofIsUnmixedExtension_embedding_isExtension h with
  | inl hl =>
    simp_rw [toIsUnmixedExtension, dif_pos hl.1, Subtype.map_def, ofIsUnmixedExtension_embedding,
      Subtype.mk.injEq]
    rw [← hl.2, ofIsUnmixedExtension_embedding, mk_embedding]
  | inr hr =>
    simp_rw [toIsUnmixedExtension, dif_neg hr.1, Subtype.map_def, ofIsUnmixedExtension_embedding,
      Subtype.mk.injEq]
    rw [← hr.2, ofIsUnmixedExtension_embedding, mk_conjugate_eq, mk_embedding]

theorem toIsUnmixedExtension_injective : (toIsUnmixedExtension L v).Injective := by
  apply Function.Injective.dite _
    (Subtype.map_injective _ <|
      Function.Injective.comp (embedding_injective _) Subtype.val_injective)
    (Subtype.map_injective _ <|
        Function.Injective.comp (conjugate_embedding_injective _) Subtype.val_injective)
    (@fun _ _ hw₁ hw₂ => by
      simpa [Subtype.map_def] using mt (eq_of_embedding_eq_conjugate L)
        (embedding_injective L |>.ne_iff.1 (hw₁.ne hw₂)))

theorem toIsUnmixedExtension_surjective : (toIsUnmixedExtension L v).Surjective :=
  fun ⟨_, h⟩ => ⟨ofIsUnmixedExtension h, toIsUnmixedExtension_ofIsUnmixedExtension h⟩

/-- The equivalence between the unramified places `w` over `v` and the type of all
unmixed extensions of `v.embedding`. -/
def equivIsUnmixedExtension :
    UnramifiedExtension L v ≃ { ψ : L →+* ℂ // IsUnmixedExtension v.embedding ψ } :=
  Equiv.ofBijective _ ⟨toIsUnmixedExtension_injective L v, toIsUnmixedExtension_surjective L v⟩

theorem card_eq [NumberField L] :
    Fintype.card (UnramifiedExtension L v) =
      Fintype.card { ψ : L →+* ℂ // IsUnmixedExtension v.embedding ψ } := by
  rw [← Fintype.card_eq.2 ⟨equivIsUnmixedExtension L v⟩]

instance (w : v.UnramifiedExtension L) [h : Fact v.IsReal] :
    IsLift L v w where
  isExtension' := by
    rw [← congrArg embedding w.comap_eq,
      comap_embedding_eq_of_isReal <| by apply w.comap_eq ▸ h.elim]

end UnramifiedExtension

namespace Extension

--variable {K}

instance : Algebra (WithAbs v.1) ℂ := v.embedding.toAlgebra

theorem isExtension_algHom (φ : L →ₐ[WithAbs v.1] ℂ) : IsExtension v.embedding φ.toRingHom := by
  have := v.embedding.algebraMap_toAlgebra ▸ funext_iff.2 φ.commutes'
  simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.commutes,
    DFunLike.coe_fn_eq] at this
  show φ.toRingHom.comp (algebraMap (WithAbs v.1) L) = v.embedding
  rwa [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]

variable (L v)

/-- For any infinite place `v` of `K`, the `K`-algebra maps from `L` to `ℂ` are equivalent to
the embeddings `L →+* ℂ` that extend `v.embedding`. -/
def algHomEquivIsExtension :
    (L →ₐ[WithAbs v.1] ℂ) ≃ { ψ : L →+* ℂ // IsExtension v.embedding ψ } :=
  Equiv.ofBijective (fun φ => ⟨φ.toRingHom, isExtension_algHom φ⟩)
    ⟨fun _ _ h => AlgHom.coe_ringHom_injective (by simpa using h),
      fun ⟨σ, h⟩ => ⟨⟨σ, fun _ => by simp [RingHom.algebraMap_toAlgebra, ← h]; rfl⟩, rfl⟩⟩

theorem card_isUnramified_add_two_mul_card_isRamified [NumberField K] [NumberField L] :
    Fintype.card (v.UnramifiedExtension L) + 2 * Fintype.card (v.RamifiedExtension L) =
      Module.finrank K L := by
  show _ = Module.finrank (WithAbs v.1) L
  rw [← AlgHom.card (WithAbs v.1) L ℂ, Fintype.card_eq.2 ⟨algHomEquivIsExtension L v⟩,
    Fintype.card_eq.2 ⟨isExtensionEquivSum v.embedding⟩, Fintype.card_sum,
    RamifiedExtension.two_mul_card_eq, UnramifiedExtension.card_eq]
  ring

theorem sum_ramificationIdx_eq [NumberField K] [NumberField L] :
    ∑ w : v.Extension L, w.1.ramificationIdx K = Module.finrank K L := by
  let e : v.Extension L ≃ v.UnramifiedExtension L ⊕ v.RamifiedExtension L :=
    (Equiv.sumCompl _).symm.trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).sumCongr
        (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun w => ¬IsUnramified K w))
  rw [Fintype.sum_equiv e _ ((fun w => w.1.ramificationIdx K) ∘ e.symm)
    (fun _ => by simp only [Function.comp_apply, Equiv.symm_apply_apply])]
  simp only [Function.comp_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Fintype.sum_sum_type, Sum.map_inl, Equiv.sumCompl_apply_inl, e,
    Equiv.subtypeSubtypeEquivSubtypeInter_symm_apply_coe_coe, Sum.map_inr, Equiv.sumCompl_apply_inr]
  rw [Finset.sum_congr rfl (fun x _ => ramificationIdx_eq_one K x.2.2),
    Finset.sum_congr rfl (fun x _ => ramificationIdx_eq_two K x.2.2),
    Finset.sum_const, Finset.sum_const, ← Fintype.card, ← Fintype.card, smul_eq_mul, mul_one,
    smul_eq_mul, mul_comm, ← card_isUnramified_add_two_mul_card_isRamified L v]

end Extension

namespace Completion

open AbsoluteValue.Completion NumberField.ComplexEmbedding

variable {K : Type*} [Field K] {v : InfinitePlace K}
variable {L : Type*} [Field L] [Algebra K L]

open UniformSpace.Completion in
theorem coe_extensionEmbeddingOfIsReal [hv : Fact v.IsReal] (x : v.Completion) :
    extensionEmbeddingOfIsReal hv.elim x = extensionEmbedding v x := by
  induction x using induction_on
  · exact isClosed_eq (Continuous.comp' (by fun_prop) continuous_extension) continuous_extension
  · simp only [extensionEmbedding_of_isReal_coe, embedding_of_isReal_apply, extensionEmbedding_coe]

instance algebraReal [hv : Fact v.IsReal] : Algebra v.Completion ℝ :=
  (extensionEmbeddingOfIsReal hv.elim).toAlgebra

/-- There are two choices for embedding `v.Completion` into `ℂ`, and therefore two choices
for giving `ℂ` a `v.Completion` algebra. The canonical algebra is the one that aligns
with the choice made for `extensionEmbedding`. -/
instance : Algebra v.Completion ℂ := (extensionEmbedding v).toAlgebra

variable (v) in
/-- There are two choices for embedding `v.Completion` into `ℂ`, and therefore two choices
for giving `ℂ` a `v.Completion` algebra. `algebraComplexStar` is the alternative algebra
defined by the conjugate of `extensionEmbedding`. -/
def algebraComplexStar : Algebra v.Completion ℂ :=
  conjugate (extensionEmbedding v) |>.toAlgebra

variable (v) in
/-- If `v` is a real infinite place, then `v.Completion` is isomorphic to `ℝ` as `v.Completion`
algebras. -/
def algEquivRealOfReal [Fact v.IsReal] :
    v.Completion ≃ₐ[v.Completion] ℝ :=
  AlgEquiv.ofRingEquiv (f := ringEquivRealOfIsReal _) (fun _ => rfl)

variable (v) in
/-- If `v` is a complex infinite place, then `v.Completion` is isomorphic to `ℂ` as `v.Completion`
algebras, using the canonical `v.Completion` algebra for `ℂ`. -/
def algEquivComplexOfComplex [hv : Fact v.IsComplex] :
    v.Completion ≃ₐ[v.Completion] ℂ :=
  AlgEquiv.ofRingEquiv (f := ringEquivComplexOfIsComplex hv.elim) (fun _ => rfl)

variable (v) in
/-- If `v` is a complex infinite place, then `v.Completion` is isomorphic to `ℂ` as `v.Completion`
algebras, using the conjugate `v.Completion` algebra for `ℂ`. -/
def algEquivComplexOfComplexStar [hv : Fact v.IsComplex] :
    letI := algebraComplexStar v
    v.Completion ≃ₐ[v.Completion] ℂ :=
  letI := algebraComplexStar v
  AlgEquiv.ofRingEquiv (f := (ringEquivComplexOfIsComplex hv.elim).trans starRingAut)
    (fun _ => rfl)

instance {L : Type*} [Field L] [Algebra K L] (w : v.Extension L) :
    Algebra v.Completion w.1.Completion := by
  exact mapOfComp (L := WithAbs w.1.1) (comp_of_comap_eq w.2) |>.toAlgebra

namespace RamifiedExtension

variable (w : v.RamifiedExtension L)

instance : Algebra v.Completion w.1.Completion :=
  inferInstanceAs (Algebra v.Completion (w : v.Extension L).1.Completion)

open UniformSpace.Completion in
theorem extensionEmbedding_algebraMap (x : v.Completion) :
    extensionEmbedding w.1 (algebraMap v.Completion w.1.Completion x) =
      extensionEmbedding v x := by
  induction x using induction_on
  · exact isClosed_eq (Continuous.comp continuous_extension continuous_map) continuous_extension
  · rw [RingHom.algebraMap_toAlgebra, mapOfComp_coe]
    simp only [extensionEmbedding_coe, ← congrArg InfinitePlace.embedding w.comap_eq,
      comap_embedding_eq_of_isReal w.isReal_comap]
    rfl

instance : IsScalarTower v.Completion w.1.Completion ℂ :=
  .of_algebraMap_smul fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      extensionEmbedding_algebraMap, RingHom.algebraMap_toAlgebra]

instance [Fact v.IsReal] : IsScalarTower v.Completion ℝ ℂ :=
  .of_algebraMap_smul fun r x => by
    simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, coe_extensionEmbeddingOfIsReal]

instance (w : v.RamifiedExtension L) : Fact w.1.IsComplex := ⟨w.isComplex⟩

/-- If `w` is a ramified extension of `v`, then `w.Completion` is isomorphic to `ℂ` as
`v.Completion` algebras. -/
def algEquivComplex : w.1.Completion ≃ₐ[v.Completion] ℂ :=
  algEquivComplexOfComplex w.1 |>.restrictScalars v.Completion

/-- If `w` is a ramified extension of `v`, then the `v.Completion`-dimension of `w.Completion`
is `2`. -/
theorem finrank_eq_two [Fact v.IsReal] : Module.finrank v.Completion w.1.Completion = 2 := by
  rw [algEquivComplex w |>.toLinearEquiv.finrank_eq, ← Module.finrank_mul_finrank v.Completion ℝ ℂ,
    ← algEquivRealOfReal v |>.toLinearEquiv.finrank_eq, Module.finrank_self,
    Complex.finrank_real_complex, one_mul]

end RamifiedExtension

namespace UnramifiedExtension

open NumberField.ComplexEmbedding Extension

variable {L : Type*} [Field L] [Algebra K L] (w : v.UnramifiedExtension L)

instance : Algebra v.Completion w.1.Completion :=
  inferInstanceAs (Algebra v.Completion (w : v.Extension L).1.Completion)

open UniformSpace.Completion in
theorem extensionEmbedding_algebraMap [IsLift L v w] (x : v.Completion) :
    extensionEmbedding w.1 (algebraMap v.Completion w.1.Completion x) =
      extensionEmbedding v x := by
  induction x using induction_on
  · exact isClosed_eq (Continuous.comp continuous_extension continuous_map) continuous_extension
  · rw [RingHom.algebraMap_toAlgebra, mapOfComp_coe]
    simp only [extensionEmbedding_coe, embedding_of_isReal_apply, ← IsLift.isExtension L v w]
    rfl

open UniformSpace.Completion in
theorem extensionEmbeddingOfIsReal_algebraMap
    [hv : Fact v.IsReal] [hw : Fact w.1.IsReal] (x : v.Completion) :
    extensionEmbeddingOfIsReal hw.elim (algebraMap v.Completion w.1.Completion x) =
      extensionEmbeddingOfIsReal hv.elim x := by
  apply_fun Complex.ofReal using Complex.ofReal_injective
  simp only [coe_extensionEmbeddingOfIsReal, extensionEmbedding_algebraMap]

instance [Fact v.IsReal] [Fact w.1.IsReal] : IsScalarTower v.Completion w.1.Completion ℝ :=
  .of_algebraMap_smul fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      extensionEmbeddingOfIsReal_algebraMap, RingHom.algebraMap_toAlgebra]

/-- If `w` is an unramified extension of `v`, and both infinite places are real, then
`w.Completion` is isomorphic to `ℝ` as `v.Completion` algebras. -/
def algEquivReal [Fact v.IsReal] [Fact w.1.IsReal] : w.1.Completion ≃ₐ[v.Completion] ℝ :=
  algEquivRealOfReal w.1 |>.restrictScalars v.Completion

instance [IsLift L v w] : IsScalarTower v.Completion w.1.Completion ℂ :=
  .of_algebraMap_smul fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      extensionEmbedding_algebraMap, RingHom.algebraMap_toAlgebra]

open UniformSpace.Completion in
theorem extensionEmbedding_algebraMap_star [IsConjugateLift L v w] (x : v.Completion) :
   conjugate (extensionEmbedding w.1) (algebraMap v.Completion w.1.Completion x) =
      (extensionEmbedding v) x := by
  induction x using induction_on
  · exact isClosed_eq (Continuous.comp (by
        show Continuous (starRingEnd ℂ ∘ extensionEmbedding w.1);
        exact Continuous.comp Complex.continuous_conj continuous_extension) continuous_map)
      continuous_extension
  · rw [RingHom.algebraMap_toAlgebra, mapOfComp_coe]
    simp only [extensionEmbedding_coe, conjugate_coe_eq, embedding_of_isReal_apply,
      ← IsConjugateLift.isExtension L v w]
    rfl

/-- If `w` is an unramified extension of `v` such that both infinite places are complex
and `w.embedding` extends `v.embedding` then `w.Completion` is isomorphic to `ℂ` as
`v.Completion` algebras. This uses the canonical `w.Completion` algebra for `ℂ`. -/
def algEquivComplex [Fact w.1.IsComplex] [IsLift L v w] :
  w.1.Completion ≃ₐ[v.Completion] ℂ :=
  algEquivComplexOfComplex w.1 |>.restrictScalars v.Completion

@[nolint unusedArguments]
instance [IsConjugateLift L v w] : Algebra w.1.Completion ℂ :=
  algebraComplexStar w.1

instance [IsConjugateLift L v w] : IsScalarTower v.Completion w.1.Completion ℂ :=
  .of_algebraMap_smul fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      extensionEmbedding_algebraMap_star, RingHom.algebraMap_toAlgebra]

/-- If `w` is an unramified extension of `v` such that both infinite places are complex
and `conjugate w.embedding` extends `v.embedding` then `w.Completion` is isomorphic to `ℂ` as
`v.Completion` algebras. This uses the conjugate `w.Completion` algebra for `ℂ`. -/
def algEquivComplexStar [Fact w.1.IsComplex] [IsConjugateLift L v w] :
    w.1.Completion ≃ₐ[v.Completion] ℂ :=
  algEquivComplexOfComplexStar w.1 |>.restrictScalars v.Completion

instance [hv : Fact v.IsReal] : Fact w.1.IsReal := ⟨w.isReal_of_isReal hv.elim⟩

instance [hv : Fact v.IsComplex] : Fact w.1.IsComplex :=
  ⟨Extension.isComplex_of_isComplex (w : v.Extension L) hv.elim⟩

/-- If `w` is an unramified extension of `v` and both infinite places are complex then
the `v.Completion`-dimension of `w.Completion` is `1`. -/
theorem finrank_eq_one : Module.finrank v.Completion w.1.Completion = 1 := by
  by_cases hv : v.IsReal
  · have : Fact v.IsReal := ⟨hv⟩
    rw [algEquivReal w |>.toLinearEquiv.finrank_eq,
      ← algEquivRealOfReal v |>.toLinearEquiv.finrank_eq, Module.finrank_self]
  · have : Fact v.IsComplex := ⟨not_isReal_iff_isComplex.1 hv⟩
    cases isLift_or_isConjugateLift L v w with
    | inl hl =>
      rw [algEquivComplex w |>.toLinearEquiv.finrank_eq,
        ← algEquivComplexOfComplex v |>.toLinearEquiv.finrank_eq, Module.finrank_self]
    | inr hr =>
      rw [algEquivComplexStar w |>.toLinearEquiv.finrank_eq,
       ← algEquivComplexOfComplex v |>.toLinearEquiv.finrank_eq, Module.finrank_self]

end UnramifiedExtension

variable (w : v.Extension L)

theorem finrank_eq_ramificationIdx :
    Module.finrank v.Completion w.1.Completion = ramificationIdx K w.1 := by
  by_cases h : w.1.IsRamified K
  · let w := w.toRamifiedExtension h
    have : Fact v.IsReal := ⟨w.isReal⟩
    show Module.finrank v.Completion w.1.Completion = ramificationIdx K w.1
    simp [ramificationIdx, w.isRamified, RamifiedExtension.finrank_eq_two]
  · let w := w.toUnramifiedExtension (by simpa using h)
    show Module.finrank v.Completion w.1.Completion = ramificationIdx K w.1
    simp [ramificationIdx, w.isUnramified, UnramifiedExtension.finrank_eq_one]

end NumberField.InfinitePlace.Completion
