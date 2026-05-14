/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.CategoryStar
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Consequences of the homology sequence

Given a morphism `φ : S₁ ⟶ S₂` between two short exact sequences
of homological complexes in an abelian category, we show the naturality
of the homology sequence of `S₁` and `S₂` with respect to `φ`
(see `HomologicalComplex.HomologySequence.δ_naturality`).

Then, we shall show in this file that if two out of the three maps `φ.τ₁`,
`φ.τ₂`, `φ.τ₃` are quasi-isomorphisms, then the third is. We also obtain
more specific separate lemmas which give sufficient conditions for one
of these three morphisms to induce a mono/epi/iso in a given degree
in terms of properties of the other two in the same or neighboring degrees.

So far, we state only four lemmas for `φ.τ₃`. Eight more similar lemmas
for `φ.τ₁` and `φ.τ₂` shall also be obtained (TODO).

-/

@[expose] public section

open CategoryTheory ComposableArrows Abelian

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

namespace HomologicalComplex

namespace HomologySequence

/-- The morphism `snakeInput hS₁ i j hij ⟶ snakeInput hS₂ i j hij` induced by
a morphism `φ : S₁ ⟶ S₂` of short complexes of homological complexes, that
are short exact (`hS₁ : S₁.ShortExact` and `hS₂ : S₁.ShortExact`). -/
@[simps]
noncomputable def mapSnakeInput (i j : ι) (hij : c.Rel i j) :
    snakeInput hS₁ i j hij ⟶ snakeInput hS₂ i j hij where
  f₀ := (homologyFunctor C c i).mapShortComplex.map φ
  f₁ := (opcyclesFunctor C c i).mapShortComplex.map φ
  f₂ := (cyclesFunctor C c j).mapShortComplex.map φ
  f₃ := (homologyFunctor C c j).mapShortComplex.map φ

@[reassoc]
lemma δ_naturality (i j : ι) (hij : c.Rel i j) :
    hS₁.δ i j hij ≫ HomologicalComplex.homologyMap φ.τ₁ _ =
      HomologicalComplex.homologyMap φ.τ₃ _ ≫ hS₂.δ i j hij :=
  ShortComplex.SnakeInput.naturality_δ (mapSnakeInput φ hS₁ hS₂ i j hij)

variable (S)

/-- The (exact) sequence `S.X₁.homology i ⟶ S.X₂.homology i ⟶ S.X₃.homology i` -/
@[simp]
noncomputable def composableArrows₂ (i : ι) : ComposableArrows C 2 :=
  mk₂ (homologyMap S.f i) (homologyMap S.g i)

lemma composableArrows₂_exact (hS₁ : S₁.ShortExact) (i : ι) :
    (composableArrows₂ S₁ i).Exact :=
  (hS₁.homology_exact₂ i).exact_toComposableArrows

/-- The (exact) sequence
`H_i(S.X₁) ⟶ H_i(S.X₂) ⟶ H_i(S.X₃) ⟶ H_j(S.X₁) ⟶ H_j(S.X₂) ⟶ H_j(S.X₃)` when `c.Rel i j`
and `S` is a short exact short complex of homological complexes in an abelian category. -/
@[simp]
noncomputable def composableArrows₅ (i j : ι) (hij : c.Rel i j) : ComposableArrows C 5 :=
  mk₅ (homologyMap S₁.f i) (homologyMap S₁.g i) (hS₁.δ i j hij)
    (homologyMap S₁.f j) (homologyMap S₁.g j)

lemma composableArrows₅_exact (i j : ι) (hij : c.Rel i j) :
    (composableArrows₅ hS₁ i j hij).Exact :=
  exact_of_δ₀ (hS₁.homology_exact₂ i).exact_toComposableArrows
    (exact_of_δ₀ (hS₁.homology_exact₃ i j hij).exact_toComposableArrows
      (exact_of_δ₀ (hS₁.homology_exact₁ i j hij).exact_toComposableArrows
        (hS₁.homology_exact₂ j).exact_toComposableArrows))

set_option backward.isDefEq.respectTransparency false in
/-- The map between the exact sequences `S₁.X₁.homology i ⟶ S₁.X₂.homology i ⟶ S₁.X₃.homology i`
and `S₂.X₁.homology i ⟶ S₂.X₂.homology i ⟶ S₂.X₃.homology i` that is induced by `φ : S₁ ⟶ S₂`. -/
@[simp]
noncomputable def mapComposableArrows₂ (i : ι) : composableArrows₂ S₁ i ⟶ composableArrows₂ S₂ i :=
  homMk₂ (homologyMap φ.τ₁ i) (homologyMap φ.τ₂ i) (homologyMap φ.τ₃ i) (by
    dsimp
    simp only [← homologyMap_comp, φ.comm₁₂]) (by
    dsimp [Precomp.map]
    simp only [← homologyMap_comp, φ.comm₂₃])

/-- The map `composableArrows₅ hS₁ i j hij ⟶ composableArrows₅ hS₂ i j hij` of exact
sequences induced by a morphism `φ : S₁ ⟶ S₂` between short exact short complexes of
homological complexes. -/
@[simp]
noncomputable def mapComposableArrows₅ (i j : ι) (hij : c.Rel i j) :
    composableArrows₅ hS₁ i j hij ⟶ composableArrows₅ hS₂ i j hij :=
  homMk₅ (homologyMap φ.τ₁ i) (homologyMap φ.τ₂ i) (homologyMap φ.τ₃ i)
    (homologyMap φ.τ₁ j) (homologyMap φ.τ₂ j) (homologyMap φ.τ₃ j)
    (naturality' (mapComposableArrows₂ φ i) 0 1)
    (naturality' (mapComposableArrows₂ φ i) 1 2)
    (δ_naturality φ hS₁ hS₂ i j hij)
    (naturality' (mapComposableArrows₂ φ j) 0 1)
    (naturality' (mapComposableArrows₂ φ j) 1 2)

include hS₁ hS₂

lemma mono_homologyMap_τ₃ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : Mono (homologyMap φ.τ₂ i))
    (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Mono (homologyMap φ.τ₃ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply mono_of_epi_of_mono_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δlast.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ _ hij
  · refine mono_of_epi_of_epi_of_mono (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₁ i) (composableArrows₂_exact hS₂ i) ?_ h₁ h₂
    have := hS₁.epi_g
    apply epi_homologyMap_of_epi_of_not_rel
    simpa using hi

lemma epi_homologyMap_τ₃ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₂ i))
    (h₂ : ∀ j, c.Rel i j → Epi (homologyMap φ.τ₁ j))
    (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₂ j)) :
    Epi (homologyMap φ.τ₃ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply epi_of_epi_of_epi_of_mono
      ((δ₀Functor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δlast
    · exact h₁
    · exact h₂ j hij
    · exact h₃ j hij
  · have := hS₂.epi_g
    have eq := (homologyFunctor C _ i).congr_map φ.comm₂₃
    dsimp at eq
    simp only [homologyMap_comp] at eq
    have := epi_homologyMap_of_epi_of_not_rel S₂.g i (by simpa using hi)
    exact epi_of_epi_fac eq.symm

lemma isIso_homologyMap_τ₃ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : IsIso (homologyMap φ.τ₂ i))
    (h₃ : ∀ j, c.Rel i j → IsIso (homologyMap φ.τ₁ j))
    (h₄ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₂ j)) :
    IsIso (homologyMap φ.τ₃ i) := by
  have := mono_homologyMap_τ₃ φ hS₁ hS₂ i h₁ (IsIso.mono_of_iso _) (fun j hij => by
    have := h₃ j hij
    infer_instance)
  have := epi_homologyMap_τ₃ φ hS₁ hS₂ i inferInstance (fun j hij => by
    have := h₃ j hij
    infer_instance) h₄
  apply isIso_of_mono_of_epi

lemma quasiIso_τ₃ (h₁ : QuasiIso φ.τ₁) (h₂ : QuasiIso φ.τ₂) :
    QuasiIso φ.τ₃ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_τ₃ φ hS₁ hS₂
  all_goals infer_instance

end HomologySequence

end HomologicalComplex

namespace CategoryTheory.ShortComplex.ShortExact

open HomologicalComplex Limits

lemma exactAt_X₁ (hS : S.ShortExact) (j : ι)
    (h₁ : Mono (HomologicalComplex.homologyMap S.g j) := by infer_instance)
    (h₂ : ∀ (i : ι), c.Rel i j → Epi (HomologicalComplex.homologyMap S.g i) := by infer_instance) :
    S.X₁.ExactAt j := by
  rw [exactAt_iff_isZero_homology]
  by_cases! hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    have := h₂ i hij
    apply (hS.homology_exact₁ i j hij).isZero_X₂
    · simp [← cancel_epi (HomologicalComplex.homologyMap S.g i)]
    · simp [← cancel_mono (HomologicalComplex.homologyMap S.g j),
        ← HomologicalComplex.homologyMap_comp]
  · have := hS.mono_f
    have := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel S.f j hj
    rw [IsZero.iff_id_eq_zero,
      ← cancel_mono (HomologicalComplex.homologyMap S.f j),
      ← cancel_mono (HomologicalComplex.homologyMap S.g j)]
    simp [← HomologicalComplex.homologyMap_comp]

lemma exactAt_X₂ (hS : S.ShortExact) (i : ι) (h₁ : S.X₁.ExactAt i) (h₃ : S.X₃.ExactAt i) :
    S.X₂.ExactAt i := by
  rw [exactAt_iff_isZero_homology] at h₁ h₃ ⊢
  exact (hS.homology_exact₂ i).isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

lemma exactAt_X₃ (hS : S.ShortExact) (i : ι)
    (h₁ : Epi (HomologicalComplex.homologyMap S.f i) := by infer_instance)
    (h₂ : ∀ (j : ι), c.Rel i j → Mono (HomologicalComplex.homologyMap S.f j) := by infer_instance) :
    S.X₃.ExactAt i := by
  rw [exactAt_iff_isZero_homology]
  by_cases! hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    have := h₂ j hij
    apply (hS.homology_exact₃ i j hij).isZero_X₂
    · simp [← cancel_epi (HomologicalComplex.homologyMap S.f i),
        ← HomologicalComplex.homologyMap_comp]
    · simp [← cancel_mono (HomologicalComplex.homologyMap S.f j)]
  · have := hS.epi_g
    have := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g i hi
    rw [IsZero.iff_id_eq_zero,
      ← cancel_epi (HomologicalComplex.homologyMap S.g i),
      ← cancel_epi (HomologicalComplex.homologyMap S.f i)]
    simp [← HomologicalComplex.homologyMap_comp]

lemma acyclic_X₁ (hS : S.ShortExact) (hg : _root_.QuasiIso S.g) : S.X₁.Acyclic :=
  fun j ↦ hS.exactAt_X₁ j

lemma acyclic_X₂ (hS : S.ShortExact) (h₁ : S.X₁.Acyclic) (h₃ : S.X₃.Acyclic) :
    S.X₂.Acyclic :=
  fun i ↦ hS.exactAt_X₂ i (h₁ _) (h₃ _)

lemma acyclic_X₃ (hS : S.ShortExact) (h : _root_.QuasiIso S.f) : S.X₃.Acyclic :=
  fun i ↦ hS.exactAt_X₃ i

end CategoryTheory.ShortComplex.ShortExact
