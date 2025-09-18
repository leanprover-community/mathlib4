/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.NumberTheory.NumberField.Completion
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Dimensions of completions at infinite places

Let `L/K` and `w` be an infinite place of `L` lying above the infinite place `v` of `K`.
In this file, we prove:
- the sum of the ramification indices of all such places `w` is the same as `[L : K]`;
- the `v.Completion` dimension of `w.Completion` is equal to the ramification index.
-/

noncomputable section

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L]
variable [Algebra K L] {v : InfinitePlace K} {w : InfinitePlace L}

theorem comap_embedding_eq_of_isReal (h : (w.comap (algebraMap K L)).IsReal) :
    (w.comap (algebraMap K L)).embedding = w.embedding.comp (algebraMap K L) := by
  rw [← mk_embedding w, comap_mk, mk_embedding, embedding_mk_eq_of_isReal
    (by rwa [← isReal_mk_iff, ← comap_mk, mk_embedding])]

theorem comap_mk_of_isExtension (ψ : Extension L v.embedding) :
    (mk ψ).comap (algebraMap K L) = v := by
  rw [comap_mk, ψ.2, mk_embedding]

variable (w)

namespace RamifiedExtension

open Extension

variable (w : v.Extension L)

theorem isExtension_embedding (h : w.1.IsRamified K) :
    w.1.embedding.comp (algebraMap K L) = v.embedding := by
  rw [← congrArg embedding w.2,
    ← comap_embedding_eq_of_isReal (isRamified_iff.1 h).2]

instance l [Fact (w.1.IsRamified K)] : IsLift L v w := ⟨isExtension_embedding _ Fact.out⟩

theorem isExtension_conjugate_embedding (h : w.1.IsRamified K) :
    (conjugate w.1.embedding).comp (algebraMap K L) = v.embedding := by
  have := (w.2 ▸ (isRamified_iff.1 h).2)
  rw [← ComplexEmbedding.isReal_iff.1 <| isReal_iff.1 this,
    ← congrArg InfinitePlace.embedding w.2]
  simp [comap_embedding_eq_of_isReal ((isRamified_iff.1 h).2)]

instance [Fact (w.1.IsRamified K)] : IsConjugateLift L v w :=
  ⟨isExtension_conjugate_embedding _ Fact.out⟩

theorem isMixedExtension (h : w.1.IsRamified K) :
    Extension.IsMixed ⟨_, isExtension_embedding _ h⟩  :=
  ⟨isReal_iff.1 (w.2 ▸ isRamified_iff.1 h).2, isComplex_iff.1 (isRamified_iff.1 h).1⟩

theorem isMixedExtension_conjugate (h : w.1.IsRamified K) :
    Extension.IsMixed ⟨_, isExtension_conjugate_embedding _ h⟩ :=
  ⟨isReal_iff.1 (w.2 ▸ isRamified_iff.1 h).2,
    mt ComplexEmbedding.isReal_conjugate_iff.1 <| isComplex_iff.1 (isRamified_iff.1 h).1⟩

variable (L v) in
def toIsExtension :
    { w : v.Extension L // w.1.IsRamified K } → Extension L v.embedding :=
  fun ⟨w, h⟩ ↦ ⟨w.1.embedding, isExtension_embedding _ h⟩

variable (L v) in
theorem toIsExtension_injective :
    Function.Injective (toIsExtension L v) := by
  intro ψ₁ ψ₂ hψ
  aesop (add simp [toIsExtension])

variable (L v) in
def toIsExtension_conjugate :
    { w : v.Extension L // w.1.IsRamified K } → Extension L v.embedding :=
  fun ⟨_, h⟩ ↦ ⟨_, isExtension_conjugate_embedding _ h⟩

variable (L v) in
theorem toIsExtension_conjugate_injective :
    Function.Injective (toIsExtension_conjugate L v) := by
  intro ψ₁ ψ₂ hψ
  aesop (add simp [toIsExtension_conjugate])

/-- A mixed extension `ψ : L →+* ℂ` determines a ramified infinite place `w` lying above `v`. -/
def ofIsMixedExtension {ψ : Extension L v.embedding} (h : ψ.IsMixed) :
    { w : v.Extension L // w.1.IsRamified K } := by
  refine ⟨⟨mk ψ, comap_mk_of_isExtension ψ⟩, ?_⟩
  rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, ψ.2, embedding_mk_eq_of_isReal h.1]
  refine ⟨?_, h.1⟩
  cases embedding_mk_eq ψ.1 with
  | inl hψ =>
    rw [hψ]; exact h.2
  | inr hψ =>
    rw [hψ, ComplexEmbedding.isReal_conjugate_iff]
    exact h.2

/-- The conjugate of a mixed extension `ψ : L →+* ℂ` determines a ramified infinite place
`w` lying above `v`. -/
def ofIsMixedExtension_conjugate {ψ : Extension L v.embedding} (h : ψ.IsMixed) :
    { w : v.Extension L // w.1.IsRamified K } := by
  refine ⟨⟨mk ψ, comap_mk_of_isExtension ψ⟩, ?_⟩
  rw [isRamified_iff, isComplex_iff, comap_mk, isReal_iff, ψ.2, embedding_mk_eq_of_isReal h.1]
  refine ⟨?_, h.1⟩
  cases embedding_mk_eq ψ.1 with
  | inl hψ =>
    rw [hψ]; exact h.2
  | inr hψ =>
    rw [hψ, ComplexEmbedding.isReal_conjugate_iff]
    exact h.2

theorem ofIsMixedExtension_embedding {ψ : Extension L v.embedding} (h : ψ.IsMixed) :
    (ofIsMixedExtension h).1.1.embedding = ψ ∨
      conjugate (ofIsMixedExtension h).1.1.embedding = ψ := by
  cases embedding_mk_eq ψ.1 with
  | inl hl => exact Or.inl hl
  | inr hr => right; simp_rw [star_eq_iff_star_eq, ← hr]; rfl

variable (L v)

/-- If `w` is a ramified place above `v` then `w.embedding` and `conjugate w.embedding`
are distinct mixed extensions of `v.embedding`, giving a two-fold map from `RamifiedExtension`
to the type of all mixed extensions of `v.embedding`. -/
def toIsMixedExtension
    (w : { w : v.Extension L // w.1.IsRamified K } ⊕ { w : v.Extension L // w.1.IsRamified K }) :
    { ψ : Extension L v.embedding // ψ.IsMixed } :=
  let f := Subtype.coind (toIsExtension L v)
    fun ⟨_, hr⟩ => isMixedExtension _ hr
  let g := Subtype.coind (fun ⟨_, he⟩ ↦ ⟨_, isExtension_conjugate_embedding _ he⟩)
    fun ⟨_, hr⟩ => isMixedExtension_conjugate _ hr
  Sum.elim f g w

theorem toIsMixedExtension_injective : (toIsMixedExtension L v).Injective :=
  (Subtype.coind_injective _ (toIsExtension_injective L v)).sumElim
    (Subtype.coind_injective _ (toIsExtension_conjugate_injective L v)) <|
      fun a b ↦ by simpa [toIsExtension, Subtype.coind] using b.2.ne_conjugate

theorem toIsMixedExtension_surjective : (toIsMixedExtension L v).Surjective := by
  intro ⟨ψ, h⟩
  cases ofIsMixedExtension_embedding h with
  | inl hl =>
    use .inl (ofIsMixedExtension h)
    simp [toIsMixedExtension, Subtype.coind, toIsExtension, hl]
  | inr hr =>
    use .inr (ofIsMixedExtension h)
    simp [toIsMixedExtension, Subtype.coind, hr]

/-- The equivalence between two copies of ramified places `w` over `v` and the type of all
mixed extensions of `v.embedding`. -/
def sumEquivIsMixedExtension :
    { w : v.Extension L // w.1.IsRamified K } ⊕ { w : v.Extension L // w.1.IsRamified K } ≃
      { ψ : Extension L v.embedding // ψ.IsMixed } :=
  Equiv.ofBijective _ ⟨toIsMixedExtension_injective L v, toIsMixedExtension_surjective L v⟩

open scoped Classical in
theorem two_mul_card_eq [NumberField L] :
    2 * Fintype.card ({ w : v.Extension L // w.1.IsRamified K }) =
      Fintype.card { ψ : Extension L v.embedding // ψ.IsMixed } := by
  simp [← Fintype.card_eq.2 ⟨sumEquivIsMixedExtension L v⟩]
  ring

end RamifiedExtension

namespace IsUnramified

variable {w}

end IsUnramified

namespace UnramifiedExtension

open Extension

variable {w : v.Extension L}

theorem isUnmixedExtension (hw : w.1.IsUnramified K)
    (he : w.1.embedding.comp (algebraMap K L) = v.embedding) :
    Extension.IsUnmixed ⟨_, he⟩ := by
  aesop (add simp [isUnramified_iff])

--instance : Coe (v.UnramifiedExtension L) (v.Extension L) where
  --coe w := ⟨w.1, w.comap_eq⟩

theorem isUnmixedExtension_conjugate (hw : w.1.IsUnramified K)
    (he : w.1.embedding.comp (algebraMap K L) ≠ v.embedding) :
    Extension.IsUnmixed ⟨_, isExtension_conjugate_of_not_isExtension _ he⟩ := by
  aesop (add simp [isUnramified_iff])

theorem isReal_of_isReal (hw : w.1.IsUnramified K) (hv : v.IsReal) : w.1.IsReal :=
  (InfinitePlace.isUnramified_iff.1 hw).resolve_right
    (by simpa [w.2] using not_isComplex_iff_isReal.2 hv)

theorem isComplex_base (h : w.1.IsUnramified K) (hw : w.1.IsComplex) :
    v.IsComplex :=
  not_isReal_iff_isComplex.1 <| mt (isReal_of_isReal h) <| not_isReal_iff_isComplex.2 hw

theorem not_isExtension_iff_isExtension_conj (hw₀ : w.1.IsUnramified K)
    (hw : w.1.IsComplex) :
    w.1.embedding.comp (algebraMap K L) ≠ v.embedding ↔
      (conjugate w.1.embedding).comp (algebraMap K L) = v.embedding := by
  refine ⟨isExtension_conjugate_of_not_isExtension (w : v.Extension L), ?_⟩
  intro hc h
  have hv_isComplex : v.IsComplex := isComplex_base hw₀ hw
  rw [isComplex_iff, ComplexEmbedding.isReal_iff, RingHom.ext_iff, not_forall] at hv_isComplex
  let ⟨x, hx⟩ := hv_isComplex
  exact hx <| RingHom.congr_fun hc x ▸ ComplexEmbedding.conjugate_comp _ (algebraMap K L) ▸
    RingHom.congr_fun (congrArg conjugate h) x |>.symm

/-- An unmixed extension `ψ : L →+* ℂ` determines an unramified infinite place `w`
lying above `v`. -/
def ofIsUnmixedExtension {ψ : Extension L v.embedding} (h : ψ.IsUnmixed) :
    { w : v.Extension L // w.1.IsUnramified K } := by
  refine ⟨⟨mk ψ, comap_mk_of_isExtension ψ⟩, ?_⟩
  rw [isUnramified_iff, isReal_iff]
  by_cases hv : ComplexEmbedding.IsReal v.embedding
  · simpa [embedding_mk_eq_of_isReal <| h.isReal_of_isReal hv] using Or.inl (h.isReal_of_isReal hv)
  · simpa [comap_mk, ψ.2, mk_embedding, isComplex_iff] using Or.inr hv

theorem isUnramified_of_isUnmixed {ψ : Extension L v.embedding} (h : ψ.IsUnmixed) :
    (mk ψ.1).IsUnramified K := by
  rw [isUnramified_iff, isReal_iff]
  by_cases hv : ComplexEmbedding.IsReal v.embedding
  · simpa [embedding_mk_eq_of_isReal <| h.isReal_of_isReal hv] using Or.inl (h.isReal_of_isReal hv)
  · simpa [comap_mk, ψ.2, mk_embedding, isComplex_iff] using Or.inr hv

@[simp]
theorem ofIsUnmixedExtension_embedding {ψ : Extension L v.embedding} (h : ψ.IsUnmixed) :
    embedding (ofIsUnmixedExtension h).1.1 = (mk ψ).embedding :=
  rfl

theorem ofIsUnmixedExtension_embedding_isExtension {ψ : Extension L v.embedding} (h : ψ.IsUnmixed) :
    letI w := ofIsUnmixedExtension h
    ((w.1.1.embedding.comp (algebraMap K L) = v.embedding ∧ w.1.1.embedding = ψ) ∨
      (w.1.1.embedding.comp (algebraMap K L) ≠ v.embedding ∧ conjugate w.1.1.embedding = ψ)) := by
  by_cases hv : ComplexEmbedding.IsReal v.embedding
  · simpa [embedding_mk_eq_of_isReal <| h.isReal_of_isReal hv] using Or.inl ψ.2
  · cases embedding_mk_eq ψ.1 with
    | inl hl => simpa [hl] using Or.inl ψ.2
    | inr hr =>
      rw [not_isExtension_iff_isExtension_conj (ofIsUnmixedExtension h).2
        (isComplex_mk_iff.2 <| ψ.not_isReal_of_not_isReal hv)]
      simpa [ofIsUnmixedExtension_embedding, hr] using Or.inr ψ.2

variable (L v)

open scoped Classical in
/-- If `w` is an unramified place above `v` then there are the following two cases:
- `v` and `w` are both real;
- `v` and `w` are both complex.
In the first case `w.embedding` and `conjugate w.embedding` coincide. In the second case
only one of `w.embedding` and `conjugate w.embedding` can extend `v.embedding`. In both cases
then, there is a unique unmixed extension of `v.embedding` associated to the unramified
place `w` over `v`. -/
def toIsUnmixedExtension (w : {w : v.Extension L // w.1.IsUnramified K }) :
    { ψ : Extension L v.embedding // ψ.IsUnmixed } := by
  by_cases hw : w.1.1.embedding.comp (algebraMap K L) = v.embedding
  · exact ⟨⟨w.1.1.embedding, hw⟩, isUnmixedExtension w.2 hw⟩
  · exact ⟨⟨conjugate w.1.1.embedding,
      isExtension_conjugate_of_not_isExtension _ hw⟩,
        isUnmixedExtension_conjugate w.2 hw⟩
  --let f := Subtype.restrict (IsExtension v.embedding) (fun ⟨_, hr⟩ => isUnmixedExtension _ hr)

  --let f : Subtype.coind (fun w ↦ ⟨w.1, w.2⟩(fun w h => w.isUnmixedExtension h)
  --let g := Subtype.map (fun w => conjugate w.1.embedding)
    --(fun w h => w.isUnmixedExtension_conjugate h)
  --if h : IsExtension v.embedding w.1.embedding then S ⟨w, h⟩ else g ⟨w, h⟩


variable {L v} in
theorem toIsUnmixedExtension_ofIsUnmixedExtension {ψ : Extension L v.embedding}
    (h : ψ.IsUnmixed) :
    toIsUnmixedExtension L v (ofIsUnmixedExtension h) = ⟨ψ, h⟩ := by
  cases ofIsUnmixedExtension_embedding_isExtension h with
  | inl hl => aesop (add simp [ofIsUnmixedExtension_embedding, toIsUnmixedExtension])
  | inr hr => aesop (add simp [ofIsUnmixedExtension_embedding, toIsUnmixedExtension])

theorem toIsUnmixedExtension_injective : (toIsUnmixedExtension L v).Injective := by
  classical
  unfold toIsUnmixedExtension
  intro _ _ _
  aesop
  · exact eq_of_embedding_eq_conjugate L a
  · exact (eq_of_embedding_eq_conjugate L a.symm).symm
  /-rintro
  simp [Subtype.mk.injEq]
  apply Function.Injective.dite

  apply Function.Injective.dite _
    (Subtype.map_injective _ <|
      Function.Injective.comp (embedding_injective _) Subtype.val_injective)
    (Subtype.map_injective _ <|
        Function.Injective.comp (conjugate_embedding_injective _) Subtype.val_injective)
    (@fun _ _ hw₁ hw₂ => by
      simpa [Subtype.map_def] using mt (eq_of_embedding_eq_conjugate L)
        (embedding_injective L |>.ne_iff.1 fun h ↦ by aesop))-/

theorem toIsUnmixedExtension_surjective : (toIsUnmixedExtension L v).Surjective :=
  fun ⟨_, h⟩ => ⟨ofIsUnmixedExtension h, toIsUnmixedExtension_ofIsUnmixedExtension h⟩

/-- The equivalence between the unramified places `w` over `v` and the type of all
unmixed extensions of `v.embedding`. -/
def equivIsUnmixedExtension :
    {w : v.Extension L // w.1.IsUnramified K } ≃ { ψ : Extension L v.embedding // ψ.IsUnmixed } :=
  Equiv.ofBijective _ ⟨toIsUnmixedExtension_injective L v, toIsUnmixedExtension_surjective L v⟩

open scoped Classical in
theorem card_eq [NumberField L] :
    Fintype.card ({w : v.Extension L // w.1.IsUnramified K }) =
      Fintype.card { ψ : Extension L v.embedding // ψ.IsUnmixed } := by
  rw [← Fintype.card_eq.2 ⟨equivIsUnmixedExtension L v⟩]

instance [Fact (w.1.IsUnramified K)] [h : Fact v.IsReal] :
    IsLift L v w where
  isExtension' := by
    rw [← congrArg embedding w.comap_eq,
      comap_embedding_eq_of_isReal <| by apply w.comap_eq ▸ h.elim]

end UnramifiedExtension

namespace Extension

instance : Algebra (WithAbs v.1) ℂ := v.embedding.toAlgebra

theorem isExtension_algHom (φ : L →ₐ[WithAbs v.1] ℂ) :
    φ.toRingHom.comp (algebraMap K L) = v.embedding := by
  have := v.embedding.algebraMap_toAlgebra ▸ funext_iff.2 φ.commutes'
  simp only [AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_coe, AlgHom.commutes,
    DFunLike.coe_fn_eq] at this
  change φ.toRingHom.comp (algebraMap (WithAbs v.1) L) = v.embedding
  rwa [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower]

variable (L v)

/-- For any infinite place `v` of `K`, the `K`-algebra maps from `L` to `ℂ` are equivalent to
the embeddings `L →+* ℂ` that extend `v.embedding`. -/
def algHomEquivIsExtension :
    (L →ₐ[WithAbs v.1] ℂ) ≃ { ψ : L →+* ℂ // ψ.comp (algebraMap K L) = v.embedding } :=
  Equiv.ofBijective (fun φ => ⟨φ.toRingHom, isExtension_algHom φ⟩)
    ⟨fun _ _ h => AlgHom.coe_ringHom_injective (by simpa using h),
      fun ⟨σ, h⟩ => ⟨⟨σ, fun _ => by simp [RingHom.algebraMap_toAlgebra, ← h]; rfl⟩, rfl⟩⟩

open scoped Classical in
theorem card_isUnramified_add_two_mul_card_isRamified [NumberField K] [NumberField L] :
    Fintype.card ({w : v.Extension L // w.1.IsUnramified K }) +
      2 * Fintype.card ({w : v.Extension L // w.1.IsRamified K }) =
      Module.finrank K L := by
  change _ = Module.finrank (WithAbs v.1) L
  rw [← AlgHom.card (WithAbs v.1) L ℂ, Fintype.card_eq.2 ⟨algHomEquivIsExtension L v⟩,
    Fintype.card_eq.2 ⟨(Equiv.sumCompl Extension.IsMixed).symm⟩, Fintype.card_sum,
    RamifiedExtension.two_mul_card_eq, UnramifiedExtension.card_eq]
  ring

open scoped Classical in
theorem sum_ramificationIdx_eq [NumberField K] [NumberField L] :
    ∑ w : v.Extension L, w.1.ramificationIdx K = Module.finrank K L := by
  rw [Fintype.sum_equiv (Equiv.sumCompl fun w ↦ w.1.IsUnramified K).symm _
    ((fun w ↦ w.1.ramificationIdx K) ∘ (Equiv.sumCompl fun w : v.Extension L ↦ w.1.IsUnramified K))
    (fun _ => by simp)]
  simp only [Function.comp_apply, Fintype.sum_sum_type, Equiv.sumCompl_apply_inl,
    Equiv.sumCompl_apply_inr]
  rw [Finset.sum_congr rfl (fun x _ => ramificationIdx_eq_one K x.2),
    Finset.sum_congr rfl (fun x _ => ramificationIdx_eq_two K x.2),
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

variable {w : v.Extension L}

instance : Algebra v.Completion w.1.Completion :=
  inferInstanceAs (Algebra v.Completion (w : v.Extension L).1.Completion)

open UniformSpace.Completion in
theorem extensionEmbedding_algebraMap (h : w.1.IsRamified K) (x : v.Completion) :
    extensionEmbedding w.1 (algebraMap v.Completion w.1.Completion x) =
      extensionEmbedding v x := by
  induction x using induction_on
  · exact isClosed_eq (Continuous.comp continuous_extension continuous_map) continuous_extension
  · rw [RingHom.algebraMap_toAlgebra, mapOfComp_coe]
    simp only [extensionEmbedding_coe, ← congrArg InfinitePlace.embedding w.comap_eq,
      comap_embedding_eq_of_isReal <| (isRamified_iff.1 h).2]
    rfl

instance [Fact (w.1.IsRamified K)] : IsScalarTower v.Completion w.1.Completion ℂ :=
  .of_algebraMap_smul fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
      extensionEmbedding_algebraMap Fact.out, RingHom.algebraMap_toAlgebra]

instance [Fact v.IsReal] : IsScalarTower v.Completion ℝ ℂ :=
  .of_algebraMap_smul fun r x => by
    simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, coe_extensionEmbeddingOfIsReal]

instance [i : Fact (w.1.IsRamified K)] : Fact w.1.IsComplex := ⟨by
    exact ((isRamified_iff).1 <| i.out).1
  ⟩

variable (w) in
/-- If `w` is a ramified extension of `v`, then `w.Completion` is isomorphic to `ℂ` as
`v.Completion` algebras. -/
def algEquivComplex [Fact (w.1.IsRamified K)] : w.1.Completion ≃ₐ[v.Completion] ℂ :=
  algEquivComplexOfComplex w.1 |>.restrictScalars v.Completion

variable (w) in
/-- If `w` is a ramified extension of `v`, then the `v.Completion`-dimension of `w.Completion`
is `2`. -/
theorem finrank_eq_two [Fact v.IsReal] [Fact (w.1.IsRamified K)] :
    Module.finrank v.Completion w.1.Completion = 2 := by
  rw [algEquivComplex w |>.toLinearEquiv.finrank_eq, ← Module.finrank_mul_finrank v.Completion ℝ ℂ,
    ← algEquivRealOfReal v |>.toLinearEquiv.finrank_eq, Module.finrank_self,
    Complex.finrank_real_complex, one_mul]

end RamifiedExtension

namespace UnramifiedExtension

open NumberField.ComplexEmbedding Extension

variable {L : Type*} [Field L] [Algebra K L] (w : v.Extension L)

instance : Algebra v.Completion w.1.Completion :=
  inferInstanceAs (Algebra v.Completion (w : v.Extension L).1.Completion)

open UniformSpace.Completion in
theorem extensionEmbedding_algebraMap [IsLift L v w] (x : v.Completion) :
    extensionEmbedding w.1 (algebraMap v.Completion w.1.Completion x) =
      extensionEmbedding v x := by
  induction x using induction_on
  · exact isClosed_eq (Continuous.comp continuous_extension continuous_map) continuous_extension
  · rw [RingHom.algebraMap_toAlgebra, mapOfComp_coe]
    simp only [extensionEmbedding_coe, ← IsLift.isExtension L v w]
    rfl

open UniformSpace.Completion RamifiedExtension in
theorem extensionEmbeddingOfIsReal_algebraMap [Fact (w.1.IsUnramified K)]
    [hv : Fact v.IsReal] [hw : Fact w.1.IsReal] (x : v.Completion) :
    extensionEmbeddingOfIsReal hw.elim (algebraMap v.Completion w.1.Completion x) =
      extensionEmbeddingOfIsReal hv.elim x := by
  apply_fun Complex.ofReal using Complex.ofReal_injective
  simp only [coe_extensionEmbeddingOfIsReal, extensionEmbedding_algebraMap]

instance [Fact (w.1.IsUnramified K)] [Fact v.IsReal] [Fact w.1.IsReal] :
  IsScalarTower v.Completion w.1.Completion ℝ :=
    .of_algebraMap_smul fun r x => by
      rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra,
        extensionEmbeddingOfIsReal_algebraMap, RingHom.algebraMap_toAlgebra]

/-- If `w` is an unramified extension of `v`, and both infinite places are real, then
`w.Completion` is isomorphic to `ℝ` as `v.Completion` algebras. -/
def algEquivReal [Fact (w.1.IsUnramified K)] [Fact v.IsReal] [Fact w.1.IsReal] :
    w.1.Completion ≃ₐ[v.Completion] ℝ :=
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
        change Continuous (starRingEnd ℂ ∘ extensionEmbedding w.1);
        exact Continuous.comp Complex.continuous_conj continuous_extension) continuous_map)
      continuous_extension
  · rw [RingHom.algebraMap_toAlgebra, mapOfComp_coe]
    simp only [extensionEmbedding_coe, conjugate_coe_eq, ← IsConjugateLift.isExtension L v w]
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

instance [Fact (w.1.IsUnramified K)] [hv : Fact v.IsReal] : Fact w.1.IsReal :=
    ⟨UnramifiedExtension.isReal_of_isReal Fact.out hv.elim⟩

instance [hv : Fact v.IsComplex] : Fact w.1.IsComplex :=
  ⟨Extension.isComplex_of_isComplex (w : v.Extension L) hv.elim⟩

/-- If `w` is an unramified extension of `v` and both infinite places are complex then
the `v.Completion`-dimension of `w.Completion` is `1`. -/
theorem finrank_eq_one [Fact (w.1.IsUnramified K)] :
    Module.finrank v.Completion w.1.Completion = 1 := by
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
  · --et w := w.toRamifiedExtension h
    --have : Fact v.IsReal := ⟨w.isReal⟩
    have : Fact v.IsReal := ⟨w.2 ▸ (isRamified_iff.1 h).2⟩
    have : Fact (w.1.IsRamified K) := ⟨by simpa using h⟩
    --change Module.finrank v.Completion w.1.Completion = ramificationIdx K w.1
    simp [ramificationIdx, RamifiedExtension.finrank_eq_two w, Fact.out]
  · have : Fact (w.1.IsUnramified K) := ⟨by simpa using h⟩
    simp [ramificationIdx, Fact.out, UnramifiedExtension.finrank_eq_one w]

end NumberField.InfinitePlace.Completion
