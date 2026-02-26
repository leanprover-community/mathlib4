/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5b
public import Mathlib.Algebra.Homology.HomologicalComplexLimitsEventuallyConstant
public import Mathlib.CategoryTheory.Category.Factorisation
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Factorization lemma

In this file, we show that if `f : K ⟶ L` is a morphism between bounded below
cochain complexes in an abelian category with enough injectives,
there exists a factorization `ι ≫ π = f` with `ι : K ⟶ K'` a monomorphism that is also
a quasimorphism and `π : K' ⟶ L` a morphism which degreewise is an epimorphism with
an injective kernel, while `K'` is also bounded below (with precise bounds depending
on the available bounds for `K` and `L`).

-/

open CategoryTheory Limits Opposite Abelian HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] [EnoughInjectives C]

namespace CochainComplex.Plus.modelCategoryQuillen

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace cm5a_cof

def cofFib : ObjectProperty (Factorisation f) :=
  fun F ↦ Mono F.ι ∧ degreewiseEpiWithInjectiveKernel F.π

instance (F : (cofFib f).FullSubcategory) : Mono F.obj.ι :=
  F.property.1

variable {f} in
def quasiIsoLE (n : ℤ) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F ↦ ∀ i ≤ n, QuasiIsoAt F.obj.ι i

variable {f} in
def isIsoLE (n : ℤ) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F ↦ ∀ i ≤ n, IsIso (F.obj.π.f i)

lemma step₁ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₀ F ∧ isIsoLE n₀ F ∧
      Mono (homologyMap F.obj.ι n₁) := by
  sorry

lemma step₂ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) [Mono (homologyMap f n₁)] :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₁ F := by
  sorry

lemma step [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) :
    ∃ (F : (cofFib f).FullSubcategory), quasiIsoLE n₁ F ∧ isIsoLE n₀ F := by
  obtain ⟨F₁, h₁, h₂, _⟩ := step₁ f n₀ n₁ hn₁ hf
  obtain ⟨F₂, h₃, h₄⟩ := step₂ F₁.obj.ι n₀ n₁ hn₁ h₁
  refine ⟨.mk { mid := _, ι := F₂.obj.ι , π := F₂.obj.π ≫ F₁.obj.π }
    ⟨by dsimp; infer_instance, MorphismProperty.comp_mem _ _ _ F₂.property.2 F₁.property.2⟩,
    ⟨h₃, fun i hi ↦ ?_⟩⟩
  have := h₂ i hi
  have := h₄ i (by lia)
  dsimp
  infer_instance

abbrev CofFibFactorizationQuasiIsoLE (n : ℤ) := (quasiIsoLE (f := f) n).FullSubcategory

namespace CofFibFactorizationQuasiIsoLE

def zero [Mono f] (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE (n + 1)] :
    CofFibFactorizationQuasiIsoLE f (n + (0 : ℕ)) :=
  .mk (.mk { mid := L, ι := f, π := 𝟙 L }
    ⟨by assumption, fun i ↦ epiWithInjectiveKernel_of_iso (𝟙 (L.X i))⟩)
    (fun i hi ↦ by
      dsimp
      rw [quasiIsoAt_iff_isIso_homologyMap]
      apply IsZero.isIso
      all_goals
      · rw [← exactAt_iff_isZero_homology]
        exact exactAt_of_isGE _ (n + 1) i)

variable {f} in
lemma exists_next {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    ∃ (F' : CofFibFactorizationQuasiIsoLE f n₁) (g : F'.1 ⟶ F.1),
      ∀ (i : ℤ) (_ : i ≤ n₀), IsIso (g.hom.h.f i) := by
  obtain ⟨F₁₂, h₁, h₂⟩ := step F.obj.obj.ι n₀ n₁ hn₁ F.property
  exact ⟨.mk (.mk { mid := _, ι := F₁₂.obj.ι, π := F₁₂.obj.π ≫ F.obj.obj.π }
    ⟨by dsimp; infer_instance,
      MorphismProperty.comp_mem _ _ _ F₁₂.property.2 F.obj.property.2⟩) h₁,
      ObjectProperty.homMk { h := F₁₂.obj.π }, h₂⟩

variable {f} in
noncomputable def next {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    CofFibFactorizationQuasiIsoLE f n₁ :=
  (F.exists_next n₁ hn₁).choose

variable {f} in
noncomputable def fromNext {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    (F.next n₁ hn₁).obj ⟶ F.obj :=
  (F.exists_next n₁ hn₁).choose_spec.choose

variable {f} in
lemma isIso_fromNext_hom_h_f {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) (i : ℤ) (hi : i ≤ n₀) :
    IsIso ((F.fromNext n₁ hn₁).hom.h.f i) :=
  (F.exists_next n₁ hn₁).choose_spec.choose_spec i hi

noncomputable def sequence
    [Mono f] (n₀ : ℤ) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)] :
    ∀ (q : ℕ), CofFibFactorizationQuasiIsoLE f (n₀ + q)
  | 0 => zero f n₀
  | q + 1 => (sequence n₀ q).next _ (by lia)

variable [Mono f] (n₀ : ℤ) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)]

noncomputable def toSequenceNext (q : ℕ) :
    (sequence f n₀ (q + 1)).obj ⟶ (sequence f n₀ q).obj :=
  (sequence f n₀ q).fromNext _ (by lia)

end CofFibFactorizationQuasiIsoLE

variable [Mono f] (n₀ : ℤ) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)]

noncomputable def functor : ℕᵒᵖ ⥤ (cofFib f).FullSubcategory :=
  (Functor.ofSequence (fun q ↦ (CofFibFactorizationQuasiIsoLE.toSequenceNext f n₀ q).op)).leftOp

lemma isIso_functor_map_hom_h_f {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) (i : ℤ) (hi : i ≤ n₀ + q₁) :
    IsIso (((functor f n₀).map (homOfLE hq).op).hom.h.f i) := by
  wlog hq' : q₁ + 1 = q₂ generalizing q₁ q₂
  · clear hq'
    obtain ⟨k, hk⟩ := Nat.le.dest hq
    induction k generalizing q₁ q₂ with
    | zero =>
      obtain rfl : q₁ = q₂ := by simpa using hk
      simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
        ObjectProperty.FullSubcategory.id_hom, Factorisation.id_h, id_f]
      infer_instance
    | succ k h =>
      rw [← homOfLE_comp (show q₁ ≤ q₁ + k by lia) (show q₁ + k ≤ q₂ by lia),
        op_comp, Functor.map_comp]
      exact IsIso.comp_isIso' (this _ (by lia) (by lia)) (h _ (by lia) rfl)
  subst hq'
  dsimp [functor]
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact CofFibFactorizationQuasiIsoLE.isIso_fromNext_hom_h_f _ _ _ _ hi

noncomputable abbrev cochainComplexFunctor : ℕᵒᵖ ⥤ CochainComplex C ℤ :=
  functor f n₀ ⋙ ObjectProperty.ι _ ⋙ Factorisation.forget

lemma isEventuallyConstantTo (i : ℤ) (q : ℕ) (h : i ≤ n₀ + q) :
    (cochainComplexFunctor f n₀ ⋙ eval _ _ i).IsEventuallyConstantTo (op q) :=
  fun _ _ ↦ isIso_functor_map_hom_h_f _ _ _ _ (by lia)

instance (i : ℤ) : HasLimit (cochainComplexFunctor f n₀ ⋙ eval _ _ i) :=
  (isEventuallyConstantTo f n₀ i (n₀ - i).natAbs (by lia)).hasLimit

noncomputable abbrev mid : CochainComplex C ℤ := limit (cochainComplexFunctor f n₀)

noncomputable def midπ (q : ℕ) : mid f n₀ ⟶ ((functor f n₀).obj (op q)).obj.mid :=
  limit.π _ (op q)

@[reassoc (attr := simp)]
lemma midπ_w (q₁ q₂ : ℕ) (hq : q₁ ≤ q₂) :
    midπ f n₀ q₂ ≫ ((functor f n₀).map (homOfLE hq).op).hom.h =
      midπ f n₀ q₁ :=
  limit.w _ _

@[reassoc (attr := simp)]
lemma midπ_w_f (q₁ q₂ : ℕ) (hq : q₁ ≤ q₂) (i : ℤ) :
    (midπ f n₀ q₂).f i ≫ ((functor f n₀).map (homOfLE hq).op).hom.h.f i =
      (midπ f n₀ q₁).f i := by
  rw [← midπ_w f n₀ q₁ q₂ hq]
  dsimp

lemma isIso_midπ_f (q : ℕ) (i : ℤ) (h : i ≤ n₀ + q) : IsIso ((midπ f n₀ q).f i) :=
  isIso_π_f_of_isLimit_of_isEventuallyConstantTo _ (limit.isLimit _) _ _
    (isEventuallyConstantTo f n₀ _ _ h)

lemma quasiIsoAt_midπ (q : ℕ) (i : ℤ) (h : i + 1 ≤ n₀ + q) :
    QuasiIsoAt (midπ f n₀ q) i :=
  quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo _ (limit.isLimit _)
    (i - 1) i (i + 1) (by simp) (by simp) _
    (isEventuallyConstantTo f n₀ _ _ (by lia))
    (isEventuallyConstantTo f n₀ _ _ (by lia))
    (isEventuallyConstantTo f n₀ _ _ (by lia))

@[simps]
noncomputable def cone : Cone (cochainComplexFunctor f n₀) where
  pt := K
  π.app q := ((functor f n₀).obj q).obj.ι

noncomputable def ι : K ⟶ mid f n₀ := limit.lift _ (cone f n₀)

@[reassoc (attr := simp)]
lemma ι_midπ (q : ℕ) : ι f n₀ ≫ midπ f n₀ q = ((functor f n₀).obj (op q)).obj.ι := by
  simp [ι, midπ]

@[reassoc (attr := simp)]
lemma ι_midπ_f (q : ℕ) (i : ℤ) : (ι f n₀).f i ≫ (midπ f n₀ q).f i =
    ((functor f n₀).obj (op q)).obj.ι.f i := by
  rw [← ι_midπ]
  dsimp

noncomputable def π : mid f n₀ ⟶ L := midπ f n₀ 0 ≫ ((functor f n₀).obj (op 0)).obj.π

@[reassoc (attr := simp)]
lemma ι_π : ι f n₀ ≫ π f n₀ = f := by
  simp [π]

@[reassoc (attr := simp)]
lemma midπ_π (q : ℕ) : midπ f n₀ q ≫ ((functor f n₀).obj (op q)).obj.π = π f n₀ := by
  simp [π, ← midπ_w_assoc f n₀ 0 q (by lia)]

@[reassoc (attr := simp)]
lemma midπ_π_f (q : ℕ) (i : ℤ) :
    (midπ f n₀ q).f i ≫ ((functor f n₀).obj (op q)).obj.π.f i = (π f n₀).f i := by
  rw [← midπ_π f n₀ q]
  dsimp

instance : (mid f n₀).IsStrictlyGE (n₀ + 1) := by
  rw [isStrictlyGE_iff]
  intro i hi
  have := isIso_midπ_f f n₀ 0 i (by lia)
  exact (L.isZero_of_isStrictlyGE (n₀ + 1) i).of_iso (asIso ((midπ f n₀ 0).f i))

instance : Mono (ι f n₀) :=
  HomologicalComplex.mono_of_mono_f _ (fun i ↦ by
    obtain ⟨q, _⟩ : ∃ (q : ℕ), IsIso ((midπ f n₀ q).f i) :=
      ⟨(i - n₀).natAbs, isIso_midπ_f f n₀ _ i (by lia)⟩
    exact mono_of_mono_fac (ι_midπ_f f n₀ q i))

instance : QuasiIso (ι f n₀) where
  quasiIsoAt i := by
    obtain ⟨q, hq⟩ : ∃ (q : ℕ), i + 1 ≤ n₀ + q := ⟨(i + 1 - n₀).natAbs, by lia⟩
    have := quasiIsoAt_midπ f n₀ q i hq
    rw [← quasiIsoAt_iff_comp_right _ (midπ f n₀ q), ι_midπ]
    exact (CofFibFactorizationQuasiIsoLE.sequence f n₀ q).property i (by lia)

lemma degreewiseEpiWithInjectiveKernel_π : degreewiseEpiWithInjectiveKernel (π f n₀) := by
  intro i
  obtain ⟨q, hq⟩ : ∃ (q : ℕ), i ≤ n₀ + q := ⟨(i - n₀).natAbs, by lia⟩
  rw [← midπ_π_f f n₀ q]
  have := isIso_midπ_f f n₀ q i hq
  exact MorphismProperty.comp_mem _ _ _
    (epiWithInjectiveKernel_of_iso _)
    ((CofFibFactorizationQuasiIsoLE.sequence f n₀ q).obj.property.2 i)

end cm5a_cof

open cm5a_cof in
public lemma cm5a_cof (n : ℤ) [K.IsStrictlyGE n] [L.IsStrictlyGE n] [Mono f] :
    ∃ (K' : CochainComplex C ℤ) (_hK' : K'.IsStrictlyGE n) (ι : K ⟶ K') (π : K' ⟶ L),
      Mono ι ∧ QuasiIso ι ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f := by
  obtain ⟨n, rfl⟩ : ∃ (q : ℤ), n = q + 1 := ⟨n - 1, by simp⟩
  exact ⟨mid f n, inferInstance, ι f n, π f n, inferInstance,
    inferInstance, degreewiseEpiWithInjectiveKernel_π f n, ι_π f n⟩

lemma cm5a (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] :
    ∃ (K' : CochainComplex C ℤ) (_hK' : K'.IsStrictlyGE n) (ι : K ⟶ K') (π : K' ⟶ L),
      Mono ι ∧ QuasiIso ι ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f := by
  have : K.IsStrictlyGE n := K.isStrictlyGE_of_ge n (n + 1) (by lia)
  obtain ⟨L', _, i, p, _, hp, _, rfl⟩ := cm5b f n
  obtain ⟨K', _, ι, π, _, _, hπ, rfl⟩ := cm5a_cof i n
  exact ⟨K', inferInstance, ι, π ≫ p, inferInstance, inferInstance,
    MorphismProperty.comp_mem _ _ _ hπ hp, by simp⟩

end CochainComplex.Plus.modelCategoryQuillen
