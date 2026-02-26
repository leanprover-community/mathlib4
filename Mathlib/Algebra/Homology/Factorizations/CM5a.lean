/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5b
public import Mathlib.CategoryTheory.Category.Factorisation

/-!
# Factorization lemma

In this file, we show that if `f : K ⟶ L` is a morphism of between bounded below
cochain complexes in an abelian category with enough injectives,
there exists a factorization `ι ≫ π = f` with `ι : K ⟶ L'` a monomorphism that is also
a quasimorphism and `π : L' ⟶ L` a morphism which degreewise is an epimorphism with
an injective kernel, while `L'` is also bounded below (with precise bounds depending
on the available bounds for `K` and `L`).

-/

open CategoryTheory Limits Abelian HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace cm5a_cof

def cofFib : ObjectProperty (Factorisation f) :=
  fun F ↦ Mono F.ι ∧ degreewiseEpiWithInjectiveKernel F.π

instance (F : (cofFib f).FullSubcategory) : Mono F.obj.ι :=
  F.property.1

variable {f} in
def isIsoLE (n : ℤ) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F ↦ ∀ i ≤ n, IsIso (F.obj.π.f i)

variable {f} in
def quasiIsoLE (n : ℤ) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F ↦ ∀ i ≤ n, QuasiIsoAt F.obj.ι i

lemma step₁ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) :
    ∃ (F : (cofFib f).FullSubcategory), isIsoLE n₀ F ∧ quasiIsoLE n₀ F ∧
      Mono (homologyMap F.obj.ι n₁) := by
  sorry

lemma step₂ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) [Mono (homologyMap f n₁)] :
    ∃ (F : (cofFib f).FullSubcategory), isIsoLE n₁ F ∧ quasiIsoLE n₁ F := by
  sorry

lemma step₁₂ [Mono f] (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)
    (hf : ∀ i ≤ n₀, QuasiIsoAt f i) :
    ∃ (F : (cofFib f).FullSubcategory), isIsoLE n₀ F ∧ quasiIsoLE n₁ F := by
  obtain ⟨F₁, h₁, h₂, _⟩ := step₁ f n₀ n₁ hn₁ hf
  obtain ⟨F₂, h₃, h₄⟩ := step₂ F₁.obj.ι n₀ n₁ hn₁ h₂
  refine ⟨.mk { mid := _, ι := F₂.obj.ι , π := F₂.obj.π ≫ F₁.obj.π }
    ⟨by dsimp; infer_instance, MorphismProperty.comp_mem _ _ _ F₂.property.2 F₁.property.2⟩,
    ⟨fun i hi ↦ ?_, h₄⟩⟩
  have := h₁ i hi
  have := h₃ i (by lia)
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

variable {f}

lemma exists_next {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    ∃ (F' : CofFibFactorizationQuasiIsoLE f n₁) (g : F'.1 ⟶ F.1),
      ∀ (i : ℤ) (_ : i ≤ n₀), IsIso (g.hom.h.f i) := by
  obtain ⟨F₁₂, h₁, h₂⟩ := step₁₂ F.obj.obj.ι n₀ n₁ hn₁ F.property
  exact ⟨.mk (.mk { mid := _, ι := F₁₂.obj.ι, π := F₁₂.obj.π ≫ F.obj.obj.π }
    ⟨by dsimp; infer_instance,
      MorphismProperty.comp_mem _ _ _ F₁₂.property.2 F.obj.property.2⟩) h₂,
      ObjectProperty.homMk { h := F₁₂.obj.π }, h₁⟩

noncomputable def next {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    CofFibFactorizationQuasiIsoLE f n₁ :=
  (F.exists_next n₁ hn₁).choose

noncomputable def fromNext {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    (F.next n₁ hn₁).obj ⟶ F.obj :=
  (F.exists_next n₁ hn₁).choose_spec.choose

lemma isIso_fromNext_hom_h_f {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) (i : ℤ) (hi : i ≤ n₀) :
    IsIso ((F.fromNext n₁ hn₁).hom.h.f i) :=
  (F.exists_next n₁ hn₁).choose_spec.choose_spec i hi

noncomputable def sequence
    [Mono f] (n₀ : ℤ) [K.IsStrictlyGE (n₀ + 1)] [L.IsStrictlyGE (n₀ + 1)] :
    ∀ (q : ℕ), CofFibFactorizationQuasiIsoLE f (n₀ + q)
  | 0 => zero f n₀
  | q + 1 => (sequence n₀ q).next _ (by lia)

end CofFibFactorizationQuasiIsoLE

end cm5a_cof

public lemma cm5a_cof (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] [Mono f] :
    ∃ (L' : CochainComplex C ℤ) (_hL' : L'.IsStrictlyGE n) (ι : K ⟶ L') (π : L' ⟶ L),
      Mono ι ∧ QuasiIso π ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f := by
  let n₀ := n - 1
  have : K.IsStrictlyGE (n₀ + 1) := K.isStrictlyGE_of_ge (n₀ + 1) (n + 1) (by lia)
  have : L.IsStrictlyGE (n₀ + 1) := L.isStrictlyGE_of_ge (n₀ + 1) n (by lia)
  sorry

end CochainComplex
