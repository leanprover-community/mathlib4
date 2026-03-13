/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Factorizations.CM5b
public import Mathlib.Algebra.Homology.HomologicalComplexLimitsEventuallyConstant
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Category.Factorisation
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Factorization lemma

In this file, we shall show that if `f : K ⟶ L` is a morphism between bounded below
cochain complexes in an abelian category with enough injectives,
there exists a factorization `ι ≫ π = f` with `ι : K ⟶ K'` a monomorphism that is also
a quasimorphism and `π : K' ⟶ L` a morphism which degreewise is an epimorphism with
an injective kernel, while `K'` is also bounded below (with precise bounds depending
on the available bounds for `K` and `L`): this is
`CochainComplex.Plus.modelCategoryQuillen.cm5a` (TODO). Using the factorization
obtained in the file `Mathlib/Algebra/Homology/Factorizations/CM5b.lean`,
we may assume `f : K ⇨ L` is a monomorphism (a case which appears as
the lemma `CochainComplex.Plus.modelCategoryQuillen.cm5a_cof` (TODO)).

In the proof, the key (private) lemma shall be
`CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step` which shows that
if `f` is a monomorphism which is a quasi-isomorphism in degrees `≤ n₀` and
`n₀ + 1 = n₁`, then `f` has a factorisation `ι ≫ π = f`
where `ι` is a monomorphism that is a quasi-isomorphism in degrees `≤ n₁`,
and `π` is an isomorphism in degrees `≤ n₀` that is also a degreewise
epimorphism with an injective kernel. The proof of `step` decomposes
a two separate lemmas `step₁` and `step₂` (TODO): we first ensure that `ι`
induces a monomorphism in homology in degree `n₁`, and we proceed further
in `step₂`.

As we assume that both `K` and `L` are bounded below, we may find `n₀ : ℤ`
such that `K` and `L` are striclty `≥ n₀ + 1`: in particular, `f` induces
an isomorphism in degrees `≤ n₀`. Iterating the lemma `step`, we construct
a projective system `ℕᵒᵖ ⥤ CochainComplex C ℤ`
(see `CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.cochainComplexFunctor`).
Degreewise, this projective system is essentially constant, which allows
to take its limit, which shall be the intermediate object in the
lemma `cm5a_cof` (TODO).

-/

open CategoryTheory Limits Opposite Abelian HomologicalComplex Pretriangulated

variable {C : Type*} [Category* C]

namespace HomologicalComplex

instance [HasZeroMorphisms C] [HasZeroObject C]
    {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (i j : ι) (I : C)
    [Injective I] :
    Injective (((single C c i).obj I).X j) := by
  by_cases hij : j = i
  · subst hij
    simp only [single_obj_X_self]
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hij).injective

end HomologicalComplex

variable [Abelian C]

namespace CochainComplex.Plus.modelCategoryQuillen

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace cm5a_cof

/-- Given a morphism `f : K ⟶ L`, this is the property of factorisations
of `f` consisting of a monomorphism followed by a degreewise epimorphism
with injective kernel. -/
public def cofFib : ObjectProperty (Factorisation f) :=
  fun F ↦ Mono F.ι ∧ degreewiseEpiWithInjectiveKernel F.π

instance (F : (cofFib f).FullSubcategory) : Mono F.obj.ι :=
  F.property.1

variable {f} in
/-- The property that the first morphism of the factorisation is
a quasi-isomorphisms in degrees `≤ n`. -/
public def quasiIsoLE (n : ℤ) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F ↦ ∀ i ≤ n, QuasiIsoAt F.obj.ι i

variable {f} in
/-- The property that the second morphism of the factorisation is
an isomorphism in degrees `≤ n`. -/
public def isIsoLE (n : ℤ) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F ↦ ∀ i ≤ n, IsIso (F.obj.π.f i)

namespace step₁

variable [EnoughInjectives C]

/-!
This section provides the material in order to prove the lemma `step₁` below.
Given a monomorphism `f : K ⟶ L` in `CochainComplex C ℤ` which is
a quasi-isomorphism in degrees `≤ n₀` (with `n₀ + 1 = n₁`), we construct
a factorization `ι f n₁ ≫ π K L n₁ = f` where the intermediate object
`mid K L n₁` is `S K n₁ ⊞ L`, with `S K n₁` the single complex in degree `n₁`
given by an injective object containing `K.opcycles n₁` (which is a cokernel of
the differential `K.X n₀ ⟶ K.X n₁`).
We obtain that `ι f n₁` is a quasi-isomorphism in degrees `≤ n₀` and
induces a monomorphism in homology in degree `n₀`,
and that `π K L n₁` is an isomorphism in degrees `≤ n₀` that is
also a degreewise epimorphism with an injective kernel. -/

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)

variable (K) in
/-- The single complex in degree `n₁` that is given by an injective
object containing `K.opcycles n₁`. -/
noncomputable abbrev S : CochainComplex C ℤ :=
    ((single C _ n₁).obj (Injective.under (K.opcycles n₁)))

variable (K L) in
/-- The intermediate object in the factorization. -/
noncomputable abbrev mid := S K n₁ ⊞ L

variable (K) in
/-- The morphim `K ⟶ S K n₁` which in degree `n₁` corresponds to
the composition `K.X n₁ ⟶ K.opcycles n₁ ⟶ Injective.under (K.opcycles n₁)`. -/
noncomputable def i : K ⟶ S K n₁ := mkHomToSingle (K.pOpcycles n₁ ≫ Injective.ι _) (by simp)

/-- The first morphism in the factorization. -/
noncomputable abbrev ι : K ⟶ mid K L n₁ := biprod.lift (i K n₁) f

variable (K L) in
/-- The second morphism in the factorization. -/
noncomputable abbrev π : mid K L n₁ ⟶ L := biprod.snd

variable (K L) in
/-- A section of `π K L n₁` -/
noncomputable abbrev σ : L ⟶ mid K L n₁ := biprod.inr

@[reassoc]
lemma ι_π : ι f n₁ ≫ π K L n₁ = f := by simp

instance [Mono f] : Mono (ι f n₁) := mono_of_mono_fac (ι_π f n₁)

variable (K L) in
lemma degreewiseEpiWithInjectiveKernel_π :
    degreewiseEpiWithInjectiveKernel (π K L n₁) := by
  intro q
  rw [Abelian.epiWithInjectiveKernel_iff]
  exact ⟨(S K n₁).X q, inferInstance, (biprod.inl : _ ⟶ mid K L n₁).f q, by simp,
    ⟨{ r := (biprod.fst : mid K L n₁ ⟶ _).f q, s := (biprod.inr : _ ⟶ mid K L n₁).f q }⟩⟩

variable (K L) in
lemma isIso_π_f (i : ℤ) (hi : i ≠ n₁) :
    IsIso ((π K L n₁).f i) := by
  refine ⟨(biprod.inr : _ ⟶ mid K L n₁).f i, ?_, by simp⟩
  rw [biprodX_ext_to_iff]
  constructor
  · apply (isZero_single_obj_X (.up ℤ) _ _ _ hi).eq_of_tgt
  · simp

include hn₁ in
variable (K L) in
lemma quasiIsoAt_π (i : ℤ) (hi : i ≤ n₀) :
    QuasiIsoAt (π K L n₁) i := by
  obtain (hi | rfl) := hi.lt_or_eq
  · rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    let φ := (shortComplexFunctor' C _ (i - 1) i (i + 1)).map (π K L n₁)
    have : IsIso φ.τ₁ := isIso_π_f _ _ _ _ (by lia)
    have : IsIso φ.τ₂ := isIso_π_f _ _ _ _ (by lia)
    have : IsIso φ.τ₃ := isIso_π_f _ _ _ _ (by lia)
    exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ
  · rw [quasiIsoAt_iff_isIso_homologyMap]
    have : homologyMap (biprod.inl : _ ⟶ mid K L n₁) i = 0 :=
      (ShortComplex.isZero_homology_of_isZero_X₂ _
        (isZero_single_obj_X (.up ℤ) _ _ _ (by lia))).eq_of_src _ _
    refine ⟨homologyMap (σ K L n₁) i, ?_, ?_⟩
    · simp [← homologyMap_id, ← biprod.total, homologyMap_comp, this]
    · simp [← homologyMap_comp, homologyMap_id]

variable (hf : ∀ i ≤ n₀, QuasiIsoAt f i)

include hn₁ hf in
lemma quasiIsoAt_ι (i : ℤ) (hi : i ≤ n₀) :
    QuasiIsoAt (ι f n₁) i := by
  have := quasiIsoAt_π K L n₀ n₁ hn₁ i hi
  rw [← quasiIsoAt_iff_comp_right _ (π K L n₁), ι_π]
  exact hf i hi

instance : Mono (homologyMap (ι f n₁) n₁) := by
  let n₀ := n₁ - 1
  rw [mono_homologyMap_iff_up_to_refinements _ n₀ n₁ (n₁ + 1) (by simp; lia) (by simp)]
  intro A x₁ _ y₀ hy₀
  obtain ⟨y₀, rfl⟩ : ∃ (z₁ : A ⟶ L.X n₀), z₁ ≫ (σ K L n₁).f n₀ = y₀ := by
    refine ⟨y₀ ≫ (π K L n₁).f n₀, Eq.trans ?_ (Category.comp_id _)⟩
    have : (biprod.inl : _ ⟶ mid K L n₁).f n₀ = 0 :=
      (isZero_single_obj_X (.up ℤ) _ _ _ (by lia)).eq_of_src _ _
    simp [this, ← biprod_total_f]
  simp only [Category.assoc, Hom.comm, biprodX_ext_to_iff, biprod_lift_fst_f,
    biprod_inr_fst_f, comp_zero, biprod_lift_snd_f, biprod_inr_snd_f,
    Category.comp_id] at hy₀
  obtain ⟨h₁, h₂⟩ := hy₀
  replace h₁ : x₁ ≫ K.pOpcycles n₁ = 0 := by
    rw [← cancel_mono (Injective.ι _)]
    simpa [i, ← cancel_mono (singleObjXSelf (.up ℤ) n₁ _).hom] using h₁
  obtain ⟨A₁, π, _, x₀, hx₀⟩ :=
    (K.comp_pOpcycles_eq_zero_iff_up_to_refinements x₁ n₀ (by simp; lia)).1 h₁
  exact ⟨A₁, π, inferInstance, x₀, hx₀⟩

end step₁

-- This lemma and a few definitions above are made public only in order to please CI.
-- They will be made private again when the proofs of `cm5a_cof` and `cm5a` are added.
open step₁ in
public lemma step₁ [EnoughInjectives C] [Mono f] (n₀ n₁ : ℤ)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) (hn₁ : n₀ + 1 = n₁ := by lia) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₀ F ∧ isIsoLE n₀ F ∧
      Mono (homologyMap F.obj.ι n₁) :=
  ⟨.mk { mid := mid K L n₁, ι := ι f n₁, π := π K L n₁ }
    ⟨inferInstance, degreewiseEpiWithInjectiveKernel_π K L n₁⟩,
    fun i hi ↦ quasiIsoAt_ι f n₀ n₁ hn₁ hf i hi,
    fun i hi ↦ isIso_π_f K L n₁ i (by lia),
    inferInstance⟩

proof_wanted step₂ [EnoughInjectives C] [Mono f] (n₀ n₁ : ℤ)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) [Mono (homologyMap f n₁)] (hn₁ : n₀ + 1 = n₁ := by lia) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₁ F

proof_wanted step [EnoughInjectives C] [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) (hn₁ : n₀ + 1 = n₁ := by lia) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₀ F

end cm5a_cof

proof_wanted cm5a_cof (n : ℤ) [K.IsStrictlyGE n] [L.IsStrictlyGE n] [Mono f] [EnoughInjectives C] :
    ∃ (K' : CochainComplex C ℤ) (_hK' : K'.IsStrictlyGE n) (ι : K ⟶ K') (π : K' ⟶ L),
      Mono ι ∧ QuasiIso ι ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f

proof_wanted cm5a (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] [EnoughInjectives C] :
    ∃ (K' : CochainComplex C ℤ) (_hK' : K'.IsStrictlyGE n) (ι : K ⟶ K') (π : K' ⟶ L),
      Mono ι ∧ QuasiIso ι ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f

end CochainComplex.Plus.modelCategoryQuillen
