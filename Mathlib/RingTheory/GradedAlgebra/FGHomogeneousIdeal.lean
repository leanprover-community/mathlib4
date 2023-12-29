/-
Copyright (c) 2023 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
import Mathlib.RingTheory.Finiteness
import Mathlib.RingTheory.GradedAlgebra.HomogeneousIdeal

/-!
# Finitely generated homogeneous ideals of a graded semiring.

The main contents of this file include:
1. Given a finitely generated homogeneous ideal of a graded semiring, construct a
   spanning set for that ideal which only contains homogeneous elements.
2. Prove that the span of the spanning set we have constructed is indeed the original
   homogeneous ideal.
-/

variable {ι A σ : Type*}
variable [Semiring A]
variable [DecidableEq ι] [AddMonoid ι]
variable [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜] (I : HomogeneousIdeal 𝒜) (hI : Ideal.FG I.toIdeal)

/--
For each `a : A`, `GradedRing.homogeneousComponents 𝒜 a` is the collection of the
homogeneous components of `a`, which is a finite subset of `A`.
-/
def GradedRing.homogeneousComponents [DecidableEq A] (a : A) : Finset A :=
  Finset.image (λ i ↦ (DirectSum.decompose 𝒜 a) i) (DFinsupp.support (DirectSum.decompose 𝒜 a))

lemma GradedRing.homogeneousComponents_def [DecidableEq A] (a : A) :
    GradedRing.homogeneousComponents 𝒜 a = Finset.image (λ i ↦ (DirectSum.decompose 𝒜 a) i)
    (DFinsupp.support (DirectSum.decompose 𝒜 a)) := rfl

lemma GradedRing.ne_zero_of_mem_homogeneousComponents [DecidableEq A] (a c : A) :
    c ∈ GradedRing.homogeneousComponents 𝒜 a → c ≠ 0 := λ hc ↦ by
  rw [homogeneousComponents, Finset.mem_image] at hc; rcases hc with ⟨i, hi1, hi2⟩; subst hi2;
  rw [DFinsupp.mem_support_iff] at hi1; simp only [ne_eq, ZeroMemClass.coe_eq_zero]; exact hi1

lemma GradedRing.exists_of_mem_homogeneousComponents [DecidableEq A] (a c : A) :
    c ∈ GradedRing.homogeneousComponents 𝒜 a → ∃ (i : ι), DirectSum.decompose 𝒜 a i = c :=
  λ hc ↦ by
  rw [GradedRing.homogeneousComponents] at hc;
  simp only [Finset.mem_image, DFinsupp.mem_support_toFun, ne_eq] at *;
  rcases hc with ⟨i, _, _⟩; use i

lemma GradedRing.mem_homogeneousComponents_of_ne_zero_and_exists [DecidableEq A] (a c : A) :
    (c ≠ 0 ∧ ∃ (i : ι), DirectSum.decompose 𝒜 a i = c) →
    c ∈ GradedRing.homogeneousComponents 𝒜 a := λ ⟨hc1, i, hi⟩ ↦ by
  rw [homogeneousComponents, Finset.mem_image]; exact ⟨i, by
  rw [DFinsupp.mem_support_iff]; subst hi; exact Subtype.ne_of_val_ne hc1, hi⟩

lemma GradedRing.mem_homogeneousComponents_iff [DecidableEq A] (a c : A) :
    c ∈ GradedRing.homogeneousComponents 𝒜 a ↔
    c ≠ 0 ∧ ∃ (i : ι), DirectSum.decompose 𝒜 a i = c :=
  ⟨λ hc ↦ ⟨ne_zero_of_mem_homogeneousComponents 𝒜 a c hc, exists_of_mem_homogeneousComponents
  𝒜 a c hc⟩, λ hc ↦ mem_homogeneousComponents_of_ne_zero_and_exists 𝒜 a c hc⟩

lemma GradedRing.mem_homogeneousSubmonoid_of_mem_homogeneousComponents [DecidableEq A]
    (a c : A) (hc : c ∈ GradedRing.homogeneousComponents 𝒜 a) :
    c ∈ SetLike.homogeneousSubmonoid 𝒜 := by
  rw [←(GradedRing.exists_of_mem_homogeneousComponents 𝒜 a c hc).choose_spec]
  dsimp [SetLike.homogeneousSubmonoid]
  simp only [Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_setOf_eq, SetLike.homogeneous_coe]

namespace HomogeneousIdeal

/--
A finite subset of `A` which spans the finitely generated ideal `I.toIdeal`.
-/
noncomputable def FG.spanningSet : Finset A := hI.choose

lemma FG.spanningSet_span_eq : Ideal.span (FG.spanningSet 𝒜 I hI) = I.toIdeal := hI.choose_spec

lemma FG.decompose_mem_toIdeal_of_mem_spanningSet (i : ι) (a : A) : a ∈ FG.spanningSet 𝒜 I hI →
    ((DirectSum.decompose 𝒜 a) i : A) ∈ I.toIdeal :=
  λ ha ↦ I.isHomogeneous i <| show a ∈ I.toIdeal by
  rw [←spanningSet_span_eq]; exact Ideal.subset_span ha

variable [DecidableEq A]

/--
A finite subset of `A` which spans the finitely generated ideal `I.toIdeal` and only
contains homogeneous elements.
-/
noncomputable def FG.homoSpanningSet : Finset A :=
  Finset.sup (FG.spanningSet 𝒜 I hI) (GradedRing.homogeneousComponents 𝒜)

lemma FG.homoSpanningSet_def : FG.homoSpanningSet 𝒜 I hI = Finset.sup
    (FG.spanningSet 𝒜 I hI) (GradedRing.homogeneousComponents 𝒜) := rfl

lemma FG.mem_homogeneousSubmonoid_of_mem_homoSpanningSet (a : A)
    (ha : a ∈ FG.homoSpanningSet 𝒜 I hI) : a ∈ SetLike.homogeneousSubmonoid 𝒜 := by
  rw [homoSpanningSet, Finset.mem_sup] at ha
  exact GradedRing.mem_homogeneousSubmonoid_of_mem_homogeneousComponents 𝒜
    ha.choose a ha.choose_spec.2

lemma FG.ne_zero_of_mem_homoSpanningSet (a : A) (ha : a ∈ FG.homoSpanningSet 𝒜 I hI) :
    a ≠ 0 := by
  rw [homoSpanningSet, Finset.mem_sup] at ha
  rcases ha with ⟨s, _, hsa⟩
  rw [GradedRing.homogeneousComponents, Finset.mem_image] at hsa
  rcases hsa with ⟨i, hi1, hi2⟩
  rw [DFinsupp.mem_support_iff] at hi1
  rw [←hi2]
  simp only [ne_eq, ZeroMemClass.coe_eq_zero]
  exact hi1

lemma FG.exists_of_mem_homoSpanningSet (a : A) (ha : a ∈ FG.homoSpanningSet 𝒜 I hI) :
    ∃ (s : FG.spanningSet 𝒜 I hI) (i : ι), DirectSum.decompose 𝒜 s i = a := by
  rw [homoSpanningSet] at ha
  have : ∃ (s : FG.spanningSet 𝒜 I hI), a ∈ GradedRing.homogeneousComponents 𝒜 (s : A) := by
    rw [Finset.mem_sup] at ha
    exact ⟨⟨ha.choose, ha.choose_spec.1⟩, ha.choose_spec.2⟩
  simp_rw [GradedRing.homogeneousComponents, Finset.mem_image] at this
  rcases this with ⟨s, i, _, hsi⟩
  exact ⟨s, i, hsi⟩

lemma FG.mem_homoSpanningSet_of_ne_zero_and_eq_decompose (a s : A) (i : ι)
    (hs : s ∈ FG.spanningSet 𝒜 I hI) (ha1 : a ≠ 0) (ha2 : a = DirectSum.decompose 𝒜 s i) :
    a ∈ FG.homoSpanningSet 𝒜 I hI := by
  rw [homoSpanningSet, Finset.mem_sup]; exact ⟨s, hs, by
  rw [GradedRing.homogeneousComponents, Finset.mem_image]; exact ⟨i, by
  rw [DFinsupp.mem_support_iff]; exact ⟨by subst ha2; exact Subtype.ne_of_val_ne ha1,
  id ha2.symm⟩⟩⟩

lemma FG.mem_homoSpanningSet_iff (a : A) : a ∈ FG.homoSpanningSet 𝒜 I hI ↔
    a ≠ 0 ∧ ∃ (s : A) (i : ι), s ∈ FG.spanningSet 𝒜 I hI ∧ a = DirectSum.decompose 𝒜 s i :=
  ⟨λ ha ↦ ⟨ne_zero_of_mem_homoSpanningSet 𝒜 I hI a ha, by
  rcases exists_of_mem_homoSpanningSet 𝒜 I hI a ha with ⟨s, i, hasi⟩;
  exact ⟨s, i, Finset.coe_mem s, id hasi.symm⟩⟩, λ ha ↦ by
  rcases ha with ⟨hane0, s, i, hs, hasi⟩;
  exact mem_homoSpanningSet_of_ne_zero_and_eq_decompose 𝒜 I hI a s i hs hane0 hasi⟩

lemma FG.decompose_mem_homoSpanningSet_of_mem_spanningSet (a : A) (i : ι)
    (ha : a ∈ FG.spanningSet 𝒜 I hI) (hi : i ∈ DFinsupp.support (DirectSum.decompose 𝒜 a)):
    (DirectSum.decompose 𝒜 a i : A) ∈ FG.homoSpanningSet 𝒜 I hI := by
  rw [mem_homoSpanningSet_iff]
  rw [DFinsupp.mem_support_iff] at hi
  exact ⟨by simp only [ne_eq, ZeroMemClass.coe_eq_zero]; exact hi, by use a, i⟩

lemma FG.toIdeal_le_homoSpanningSet_span :
    I.toIdeal ≤ Ideal.span (FG.homoSpanningSet 𝒜 I hI) := by
  rw [←spanningSet_span_eq, Ideal.span_le]
  exact (λ s hs ↦ by
    rw [←DirectSum.sum_support_decompose 𝒜 s];
    exact @Ideal.sum_mem A _ (Ideal.span (homoSpanningSet 𝒜 I hI)) ι
      (DFinsupp.support (DirectSum.decompose 𝒜 s)) (fun i ↦ DirectSum.decompose 𝒜 s i) (λ i hi
      ↦ Ideal.subset_span (decompose_mem_homoSpanningSet_of_mem_spanningSet 𝒜 I hI s i hs hi)))

lemma FG.homoSpanningSet_span_le_toIdeal :
    Ideal.span (FG.homoSpanningSet 𝒜 I hI) ≤ I.toIdeal := by
  rw [Ideal.span_le]
  intro x hx
  exact (show ∀ (x : A), x ∈ homoSpanningSet 𝒜 I hI → x ∈ I.toIdeal by
    intro x hx; rw [mem_homoSpanningSet_iff] at hx;
    rcases hx with ⟨_, s, i, hs, hxsi⟩; rw [hxsi];
    exact decompose_mem_toIdeal_of_mem_spanningSet 𝒜 I hI i s hs) x hx

lemma FG.homoSpanningSet_span_eq_toIdeal :
    Ideal.span (FG.homoSpanningSet 𝒜 I hI) = I.toIdeal :=
  le_antisymm (homoSpanningSet_span_le_toIdeal 𝒜 I hI)
  (toIdeal_le_homoSpanningSet_span 𝒜 I hI)

end HomogeneousIdeal
