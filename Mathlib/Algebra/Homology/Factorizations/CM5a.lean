/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5b
public import Mathlib.CategoryTheory.Category.Factorisation
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

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

variable {f} in
lemma exists_next {n₀ : ℤ} (F : CofFibFactorizationQuasiIsoLE f n₀)
    (n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) :
    ∃ (F' : CofFibFactorizationQuasiIsoLE f n₁) (g : F'.1 ⟶ F.1),
      ∀ (i : ℤ) (_ : i ≤ n₀), IsIso (g.hom.h.f i) := by
  obtain ⟨F₁₂, h₁, h₂⟩ := step₁₂ F.obj.obj.ι n₀ n₁ hn₁ F.property
  exact ⟨.mk (.mk { mid := _, ι := F₁₂.obj.ι, π := F₁₂.obj.π ≫ F.obj.obj.π }
    ⟨by dsimp; infer_instance,
      MorphismProperty.comp_mem _ _ _ F₁₂.property.2 F.obj.property.2⟩) h₂,
      ObjectProperty.homMk { h := F₁₂.obj.π }, h₁⟩

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

noncomputable def toSequenceNext (q : ℕ) : (sequence f n₀ (q + 1)).obj ⟶ (sequence f n₀ q).obj :=
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

def isEventuallyConstantTo (i : ℤ) (q : ℕ) (h : i ≤ n₀ + q) :
    (functor f n₀ ⋙ ObjectProperty.ι _ ⋙ Factorisation.forget ⋙
      eval _ _ i).IsEventuallyConstantTo (op q) :=
  fun _ _ ↦ isIso_functor_map_hom_h_f _ _ _ _ (by lia)

end cm5a_cof

public lemma cm5a_cof (n : ℤ) [K.IsStrictlyGE (n + 1)] [L.IsStrictlyGE n] [Mono f] :
    ∃ (K' : CochainComplex C ℤ) (_hK' : K'.IsStrictlyGE n) (ι : K ⟶ K') (π : K' ⟶ L),
      Mono ι ∧ QuasiIso π ∧ degreewiseEpiWithInjectiveKernel π ∧ ι ≫ π = f := by
  let n₀ := n - 1
  have : K.IsStrictlyGE (n₀ + 1) := K.isStrictlyGE_of_ge (n₀ + 1) (n + 1) (by lia)
  have : L.IsStrictlyGE (n₀ + 1) := L.isStrictlyGE_of_ge (n₀ + 1) n (by lia)
  sorry

end CochainComplex
