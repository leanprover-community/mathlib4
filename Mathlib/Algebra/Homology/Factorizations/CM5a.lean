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
a two separate lemmas `step₁` and `step₂`: we first ensure that `ι`
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

variable {C : Type*} [Category* C] [Abelian C]

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
/-- The property that the first morphism of a factorisation is
a quasi-isomorphisms in degrees `≤ n`. -/
public def quasiIsoLE (n : ℤ) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F ↦ ∀ i ≤ n, QuasiIsoAt F.obj.ι i

variable {f} in
/-- The property that the second morphism of a factorisation is
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
lemma isIso_π_f (i : ℤ) (hi : i ≠ n₁ := by lia) :
    IsIso ((π K L n₁).f i) := by
  refine ⟨(biprod.inr : _ ⟶ mid K L n₁).f i, ?_, by simp⟩
  rw [biprodX_ext_to_iff]
  constructor
  · apply (isZero_single_obj_X (.up ℤ) _ _ _ hi).eq_of_tgt
  · simp

include hn₁ in
variable (K L) in
lemma quasiIsoAt_π (i : ℤ) (hi : i ≤ n₀ := by lia) :
    QuasiIsoAt (π K L n₁) i := by
  obtain (hi | rfl) := hi.lt_or_eq
  · rw [quasiIsoAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    let φ := (shortComplexFunctor' C _ (i - 1) i (i + 1)).map (π K L n₁)
    have : IsIso φ.τ₁ := isIso_π_f ..
    have : IsIso φ.τ₂ := isIso_π_f ..
    have : IsIso φ.τ₃ := isIso_π_f ..
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

open step₁ in
lemma step₁ [EnoughInjectives C] [Mono f] (n₀ n₁ : ℤ)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) (hn₁ : n₀ + 1 = n₁ := by lia) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₀ F ∧ isIsoLE n₀ F ∧
      Mono (homologyMap F.obj.ι n₁) :=
  ⟨.mk { mid := mid K L n₁, ι := ι f n₁, π := π K L n₁ }
    ⟨inferInstance, degreewiseEpiWithInjectiveKernel_π K L n₁⟩,
    fun i hi ↦ quasiIsoAt_ι f n₀ n₁ hn₁ hf i hi,
    fun i hi ↦ isIso_π_f K L n₁ i (by lia),
    inferInstance⟩

namespace step₂

/-!
This section provides the material in order to prove the lemma `step₂` below.
Given a monomorphism `f : K ⟶ L` that is a quasi-isomorphism in degrees `< n`
and which induces a monomorphism in homology in degree `n`, we construct
a factorisation of `f` as `ι f n ≫ π f n = f` where
`ι f n : K ⟶ mid f n` is a monomorphism which is a quasi-isomorphism
in degrees `≤ n`, `π f n` is a degreewise epimorphism with an injective kernel
which also induces isomorphisms in degrees `≤ n`.
 -/


open HomComplex

variable [EnoughInjectives C] (n : ℤ)

/-- Given a morphism `f : K ⟶ L`, this is the single cochain complex in degree `n`
which is given an injective object which contains `((cokernel f).truncGE n).X n`,
i.e. the object in degree `n` of the canonical truncation `≥ n` of `cokernel f`. -/
noncomputable abbrev S :=
  (single C (.up ℤ) n).obj (Injective.under (((cokernel f).truncGE n).X n))

/-- The morphism `(cokernel f).truncGE n ⟶ S f n` which in degree `n` is
given by `Injective.ι _`. -/
noncomputable def p : (cokernel f).truncGE n ⟶ S f n :=
  mkHomToSingle (Injective.ι _) (fun i hi ↦ by
    simp only [ComplexShape.up_Rel] at hi
    exact (isZero_of_isStrictlyGE _ n _).eq_of_src _ _)

instance : Mono ((p f n).f n) := by
  simp only [p, mkHomToSingle_f, mono_comp_iff_of_mono]
  infer_instance

/-- The obvious morphism `L ⟶ S f n`. -/
noncomputable def α : L ⟶ S f n := cokernel.π f ≫ (cokernel f).πTruncGE n ≫ p f n

@[reassoc (attr := simp)]
lemma comp_α : f ≫ α f n = 0 := by simp [α]

@[reassoc (attr := simp)]
lemma comp_α_f (i : ℤ) : f.f i ≫ (α f n).f i = 0 := by simp [← comp_f]

/-- The intermediate object in the factorisation. -/
noncomputable abbrev mid := mappingCocone (α f n)

/-- The first morphism of the factorisation. -/
noncomputable abbrev ι : K ⟶ mid f n := mappingCocone.lift (α f n) f 0 (by simp)

/-- The second morphism of the factorisation. -/
noncomputable abbrev π : mid f n ⟶ L := mappingCocone.fst (α f n)

@[reassoc]
lemma ι_π : ι f n ≫ π f n = f := by simp

instance [Mono f] : Mono (ι f n) := mono_of_mono_fac (ι_π f n)

lemma degreewiseEpiWithInjectiveKernel_π :
    degreewiseEpiWithInjectiveKernel (π f n) := by
  intro i
  rw [epiWithInjectiveKernel_iff]
  exact ⟨_, inferInstance, (mappingCocone.inr (α f n)).1.v (i - 1) i (by lia), by simp,
    ⟨{r := (mappingCocone.snd (α f n)).v _ _ (by lia)
      s := (mappingCocone.inl (α f n)).v _ _ (by lia)
      id := (add_comm _ _).trans (by simp [mappingCocone.id_X]) }⟩⟩

lemma isIso_π_f (i : ℤ) (hi : i ≤ n) : IsIso ((π f n).f i) := by
  refine ⟨(mappingCocone.inl (α f n)).v i i (add_zero i), ?_, by simp⟩
  simp [← mappingCocone.id_X (α f n) i (i - 1) (by lia),
    (isZero_single_obj_X _ _ _ _ (by lia)).eq_of_src
      ((mappingCocone.inr (α f n)).1.v (i - 1) i (by lia)) 0]

section

attribute [local instance] HasDerivedCategory.standard

lemma mono_homologyMap_π (q : ℤ) (hq : q ≤ n) : Mono (homologyMap (π f n) q) :=
  (CochainComplex.homologyMap_exact₁_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) (q - 1) q (by lia)).mono_g
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_src _ _)

lemma epi_homologyMap_π (q : ℤ) (hq : q < n) : Epi (homologyMap (π f n) q) :=
  (CochainComplex.homologyMap_exact₂_of_distTriang _
    (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) q).epi_f
      ((ExactAt.isZero_homology (exactAt_single_obj _ _ _ _ (by lia))).eq_of_tgt _ _)

end

lemma quasiIsoAt_π (q : ℤ) (hq : q < n) : QuasiIsoAt (π f n) q := by
  have := mono_homologyMap_π f n q (by lia)
  have := epi_homologyMap_π f n q hq
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply Balanced.isIso_of_mono_of_epi

/-- The (exact) short complex `K.homology n ⟶ L.homology n ⟶ (S f n).homology n`. -/
@[simps]
noncomputable def homologyShortComplex : ShortComplex C :=
  ShortComplex.mk (homologyMap f n) (homologyMap (α f n) n) (by
    rw [← homologyMap_comp, comp_α, homologyMap_zero])

instance [Mono (homologyMap f n)] :
    Mono (homologyShortComplex f n).f := by
  assumption

instance : Mono (homologyMap (p f n) n) := by
  have := (S f n).isIso_homologyπ (n - 1) n (by simp) (by simp)
  have : Mono ((truncGE (cokernel f) n).homologyπ n ≫ homologyMap (p f n) n) := by
    rw [homologyπ_naturality (p f n) n]
    infer_instance
  have := (truncGE (cokernel f) n).isIso_homologyπ (n - 1) n (by simp)
    ((isZero_of_isStrictlyGE _ n _ (by lia)).eq_of_src _ _)
  rw [← IsIso.inv_hom_id_assoc ((truncGE (cokernel f) n).homologyπ n) (homologyMap (p f n) n)]
  infer_instance

omit [EnoughInjectives C] in
lemma shortExact [Mono f] : (ShortComplex.mk _ _ (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

lemma exact_homologyShortComplex [Mono f] :
    (homologyShortComplex f n).Exact := by
  let T := ShortComplex.mk (homologyMap f n) (homologyMap (cokernel.π f) n)
    (by rw [← homologyMap_comp, cokernel.condition, homologyMap_zero])
  let φ : T ⟶ homologyShortComplex f n :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := homologyMap ((cokernel f).πTruncGE n ≫ p f n) n
      comm₂₃ := by
        dsimp
        rw [Category.id_comp, ← homologyMap_comp, α] }
  obtain ⟨_, _, _⟩ : Mono φ.τ₃ ∧ IsIso φ.τ₂ ∧ Epi φ.τ₁ := by
    dsimp [φ]
    rw [homologyMap_comp]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact (shortExact f).homology_exact₂ n

variable (hf : ∀ i < n, QuasiIsoAt f i)

include hf

omit [EnoughInjectives C] in
lemma isGE_cokernel [Mono f] [Mono (homologyMap f n)] : (cokernel f).IsGE n := by
  rw [isGE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  refine ((shortExact f).homology_exact₃ i (i + 1) (by simp)).isZero_X₂ ?_ ?_
  · have := hf i hi
    rw [← ((shortExact f).homology_exact₂ i).epi_f_iff]
    infer_instance
  · rw [← ((shortExact f).homology_exact₁ i (i + 1) (by simp)).mono_g_iff]
    by_cases hi' : i + 1 < n
    · have := hf (i + 1) (by lia)
      infer_instance
    · obtain rfl : n = i + 1 := by lia
      infer_instance

omit [EnoughInjectives C] in
lemma quasiIso_truncGEπ [Mono f] [Mono (homologyMap f n)] :
    QuasiIso ((cokernel f).πTruncGE n) := by
  rw [quasiIso_πTruncGE_iff]
  exact isGE_cokernel f n hf

attribute [local instance] HasDerivedCategory.standard in
lemma quasiIsoAt_ι [Mono f] [Mono (homologyMap f n)] (q : ℤ) (hq : q ≤ n) :
    QuasiIsoAt (ι f n) q := by
  obtain hq | rfl := hq.lt_or_eq'
  · have := quasiIsoAt_π f n q hq
    rw [← quasiIsoAt_iff_comp_right _ (π f n), mappingCocone.lift_fst]
    exact hf q hq
  · have := mono_homologyMap_π f n n (by lia)
    have : Mono (homologyMap (mappingCocone.triangle (α f n)).mor₁ n) :=
      by dsimp; infer_instance
    have h₁ := (exact_homologyShortComplex f n).fIsKernel
    have h₂ := (CochainComplex.homologyMap_exact₂_of_distTriang _
      (DerivedCategory.mappingCocone_triangle_distinguished (α f n)) n).fIsKernel
    have : homologyMap (ι f n) n = (IsLimit.conePointUniqueUpToIso h₁ h₂).hom := by
      simp [← cancel_mono (homologyMap (π f n) n),
        dsimp% IsLimit.conePointUniqueUpToIso_hom_comp h₁ h₂ .zero,
        ← homologyMap_comp, mappingCocone.lift_fst]
    rw [quasiIsoAt_iff_isIso_homologyMap, this]
    infer_instance

end step₂

-- This lemma and a few definitions above are made public only in order to please CI.
-- They will be made private again when the proofs of `cm5a_cof` and `cm5a` are added.
open step₂ in
lemma step₂ [EnoughInjectives C] [Mono f] (n₀ n₁ : ℤ)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) [Mono (homologyMap f n₁)] (hn₁ : n₀ + 1 = n₁ := by lia) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₁ F :=
  ⟨.mk { mid := mid f n₁, ι := ι f n₁, π := π f n₁}
    ⟨inferInstance, degreewiseEpiWithInjectiveKernel_π f n₁⟩,
    fun i hi ↦ quasiIsoAt_ι f n₁ (fun j hj ↦ hf j (by lia)) _ hi,
    isIso_π_f f n₁⟩

public lemma step [EnoughInjectives C] [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) (hn₁ : n₀ + 1 = n₁ := by lia) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₀ F := by
  obtain ⟨F₁, h₁, h₂, _⟩ := step₁ f n₀ n₁ hf
  obtain ⟨F₂, h₃, h₄⟩ := step₂ F₁.obj.ι n₀ n₁ h₁
  refine ⟨.mk { mid := F₂.obj.mid, ι := F₂.obj.ι, π := F₂.obj.π ≫ F₁.obj.π }
    ⟨by dsimp; infer_instance, MorphismProperty.comp_mem _ _ _ F₂.property.2 F₁.property.2⟩,
    ⟨h₃, fun i hi ↦ ?_⟩⟩
  have := h₂ i hi
  have := h₄ i (by lia)
  dsimp
  infer_instance

end cm5a_cof

proof_wanted cm5a_cof (n : ℤ) [K.IsStrictlyGE n] [L.IsStrictlyGE n] [Mono f] [EnoughInjectives C] :
    ∃ (K' : CochainComplex C ℤ) (_hK' : K'.IsStrictlyGE n) (ι : K ⟶ K') (π : K' ⟶ L),
      Mono ι ∧ QuasiIso ι ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f

proof_wanted cm5a (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] [EnoughInjectives C] :
    ∃ (K' : CochainComplex C ℤ) (_hK' : K'.IsStrictlyGE n) (ι : K ⟶ K') (π : K' ⟶ L),
      Mono ι ∧ QuasiIso ι ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f

end CochainComplex.Plus.modelCategoryQuillen
