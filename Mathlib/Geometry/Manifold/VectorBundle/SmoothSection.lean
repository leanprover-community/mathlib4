/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn, Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# `C^n` sections

In this file we define the type `ContMDiffSection` of `n` times continuously differentiable
sections of a vector bundle over a manifold `M` and prove that it's a module over the base field.

In passing, we prove that binary and finite sums, differences and scalar products of `C^n`
sections are `C^n`.

-/


open Bundle Filter Function

open scoped Bundle Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : WithTop ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]

-- Binary and finite sums, negative, differences and scalar products of smooth sections are smooth
section operations

-- Let V be a vector bundle
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

variable {I F n V}

variable {f : M → 𝕜} {a : 𝕜} {s t : Π x : M, V x} {u : Set M} {x₀ : M}

lemma ContMDiffWithinAt.add_section
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (ht : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s + t) x)) u x₀ := by
  rw [contMDiffWithinAt_section] at hs ht ⊢
  set e := trivializationAt F V x₀
  refine (hs.add ht).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).1
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).1

lemma ContMDiffAt.add_section
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (ht : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s + t) x)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.add_section ht

lemma ContMDiffOn.add_section
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (ht : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s + t) x)) u :=
  fun x₀ hx₀ ↦ (hs x₀ hx₀).add_section (ht x₀ hx₀)

lemma ContMDiff.add_section
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)))
    (ht : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s + t) x)) :=
  fun x₀ ↦ (hs x₀).add_section (ht x₀)

lemma ContMDiffWithinAt.neg_section
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (- s x)) u x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine hs.neg.congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).map_neg
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).map_neg

lemma ContMDiffAt.neg_section
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (- s x)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact hs.neg_section

lemma ContMDiffOn.neg_section
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (-s x)) u :=
  fun x₀ hx₀ ↦ (hs x₀ hx₀).neg_section

lemma ContMDiff.neg_section
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (-s x)) :=
  fun x₀ ↦ (hs x₀).neg_section

lemma ContMDiffWithinAt.sub_section
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (ht : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s - t) x)) u x₀ := by
  rw [sub_eq_add_neg]
  exact hs.add_section ht.neg_section

lemma ContMDiffAt.sub_section
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (ht : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s - t) x)) x₀ := by
  rw [sub_eq_add_neg]
  apply hs.add_section ht.neg_section

lemma ContMDiffOn.sub_section
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (ht : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s - t) x)) u :=
  fun x₀ hx₀ ↦ (hs x₀ hx₀).sub_section (ht x₀ hx₀)

lemma ContMDiff.sub_section
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)))
    (ht : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x ((s - t) x)) :=
  fun x₀ ↦ (hs x₀).sub_section (ht x₀)

lemma ContMDiffWithinAt.smul_section (hf : ContMDiffWithinAt I 𝓘(𝕜) n f u x₀)
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (f x • s x)) u x₀ := by
  rw [contMDiffWithinAt_section] at hs ⊢
  set e := trivializationAt F V x₀
  refine (hf.smul hs).congr_of_eventuallyEq ?_ ?_
  · apply eventually_of_mem (U := e.baseSet)
    · exact mem_nhdsWithin_of_mem_nhds <|
        (e.open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x₀)
    · intro x hx
      apply (e.linear 𝕜 hx).2
  · apply (e.linear 𝕜 (FiberBundle.mem_baseSet_trivializationAt' x₀)).2

lemma ContMDiffAt.smul_section (hf : ContMDiffAt I 𝓘(𝕜) n f x₀)
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (f x • s x)) x₀ := by
  rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .smul_section hf hs

lemma ContMDiffOn.smul_section (hf : ContMDiffOn I 𝓘(𝕜) n f u)
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (f x • s x)) u :=
  fun x₀ hx₀ ↦ (hf x₀ hx₀).smul_section (hs x₀ hx₀)

lemma ContMDiff.smul_section (hf : ContMDiff I 𝓘(𝕜) n f)
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (f x • s x)) :=
  fun x₀ ↦ (hf x₀).smul_section (hs x₀)

lemma ContMDiffWithinAt.const_smul_section
    (hs : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (a • s x)) u x₀ :=
  contMDiffWithinAt_const.smul_section hs

lemma ContMDiffAt.const_smul_section
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (a • s x)) x₀ :=
  contMDiffAt_const.smul_section hs

lemma ContMDiffOn.const_smul_section
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (a • s x)) u :=
  contMDiffOn_const.smul_section hs

lemma ContMDiff.const_smul_section
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (a • s x)) :=
  fun x₀ ↦ (hs x₀).const_smul_section

variable {ι : Type*} {t : ι → (x : M) → V x}

lemma ContMDiffWithinAt.sum_section {s : Finset ι}
    (hs : ∀ i ∈ s,
      ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) u x₀ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using contMDiffWithinAt_zeroSection ..
  | insert i s hi h =>
    simp only [Finset.sum_insert hi]
    apply (hs _ (s.mem_insert_self i)).add_section
    exact h fun i a ↦ hs _ (s.mem_insert_of_mem a)

lemma ContMDiffAt.sum_section {s : Finset ι} {x₀ : M}
    (hs : ∀ i ∈ s, ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) x₀ := by
  simp_rw [← contMDiffWithinAt_univ] at hs ⊢
  exact .sum_section hs

lemma ContMDiffOn.sum_section {s : Finset ι}
    (hs : ∀ i ∈ s, ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) u :=
  fun x₀ hx₀ ↦ .sum_section fun i hi ↦ hs i hi x₀ hx₀

lemma ContMDiff.sum_section {s : Finset ι}
    (hs : ∀ i ∈ s, ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) :=
  fun x₀ ↦ .sum_section fun i hi ↦ (hs i hi) x₀

/-- The scalar product `ψ • s` of a `C^k` function `ψ : M → 𝕜` and a section `s` of a vector
bundle `V → M` is `C^k` once `s` is `C^k` on an open set containing `tsupport ψ` .

This is a vector bundle analogue of `contMDiff_of_tsupport`. -/
lemma ContMDiffOn.smul_section_of_tsupport {s : Π (x : M), V x} {ψ : M → 𝕜}
    (hψ : ContMDiffOn I 𝓘(𝕜) n ψ u) (ht : IsOpen u) (ht' : tsupport ψ ⊆ u)
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (ψ x • s x)) := by
  apply contMDiff_of_contMDiffOn_union_of_isOpen (hψ.smul_section hs) ?_ ?_ ht
      (isOpen_compl_iff.mpr <| isClosed_tsupport ψ)
  · apply ((contMDiff_zeroSection _ _).contMDiffOn (s := (tsupport ψ)ᶜ)).congr
    intro y hy
    simp [image_eq_zero_of_notMem_tsupport hy, zeroSection]
  · exact Set.compl_subset_iff_union.mp <| Set.compl_subset_compl.mpr ht'

/-- The sum of a locally finite collection of sections is `C^k` iff each section is.
Version at a point within a set. -/
lemma ContMDiffWithinAt.sum_section_of_locallyFinite
    (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x)) u x₀) :
    ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑' i, (t i x))) u x₀ := by
  obtain ⟨u', hu', hfin⟩ := ht x₀
  -- All sections `t i` but a finite set `s` vanish near `x₀`: choose a neighbourhood `u` of `x₀`
  -- and a finite set `s` of sections which don't vanish.
  let s := {i | ((fun i ↦ {x | t i x ≠ 0}) i ∩ u').Nonempty}
  have := hfin.fintype
  have : ContMDiffWithinAt I (I.prod 𝓘(𝕜, F)) n
      (fun x ↦ TotalSpace.mk' F x (∑ i ∈ s, (t i x))) (u ∩ u') x₀ :=
    ContMDiffWithinAt.sum_section fun i hi ↦ ((ht' i).mono Set.inter_subset_left)
  apply (contMDiffWithinAt_inter hu').mp
  apply this.congr fun y hy ↦ ?_
  · rw [TotalSpace.mk_inj, tsum_eq_sum']
    refine support_subset_iff'.mpr fun i hi ↦ ?_
    by_contra! h
    have : i ∈ s.toFinset := by
      refine Set.mem_toFinset.mpr ?_
      simp only [s, ne_eq, Set.mem_setOf_eq]
      use x₀
      simpa using ⟨h, mem_of_mem_nhds hu'⟩
    exact hi this
  rw [TotalSpace.mk_inj, tsum_eq_sum']
  refine support_subset_iff'.mpr fun i hi ↦ ?_
  by_contra! h
  have : i ∈ s.toFinset := by
    refine Set.mem_toFinset.mpr ?_
    simp only [s, ne_eq, Set.mem_setOf_eq]
    use y
    simpa using ⟨h, Set.mem_of_mem_inter_right hy⟩
  exact hi this

/-- The sum of a locally finite collection of sections is `C^k` at `x` iff each section is. -/
lemma ContMDiffAt.sum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑' i, (t i x))) x₀ := by
  simp_rw [← contMDiffWithinAt_univ] at ht' ⊢
  exact .sum_section_of_locallyFinite ht ht'

/-- The sum of a locally finite collection of sections is `C^k` on a set `u` iff each section is. -/
lemma ContMDiffOn.sum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x)) u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑' i, (t i x))) u :=
  fun x hx ↦ .sum_section_of_locallyFinite ht (ht' · x hx)

/-- The sum of a locally finite collection of sections is `C^k` iff each section is. -/
lemma ContMDiff.sum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑' i, (t i x))) :=
  fun x ↦ .sum_section_of_locallyFinite ht fun i ↦ ht' i x

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {e : PartialHomeomorph M H} {e' : PartialHomeomorph M' H'} {f f₁ : M → M'} {n : WithTop ℕ∞}

theorem ContMDiff.congr (h : ContMDiff I I' n f) (h₁ : ∀ y, f₁ y = f y) :
    ContMDiff I I' n f₁ := by
  rw [← contMDiffOn_univ] at h ⊢
  exact (contMDiffOn_congr fun y a ↦ h₁ y).mpr h

theorem contMDiff_congr (h₁ : ∀ y, f₁ y = f y) :
    ContMDiff I I' n f₁ ↔ ContMDiff I I' n f := by
  simp_rw [← contMDiffOn_univ]
  exact contMDiffOn_congr fun y a ↦ h₁ y

end

-- Future: this lemma can presumably be generalised, but some hypotheses on the supports of
-- the sections `t i` are necessary.
lemma ContMDiff.finsum_section_of_locallyFinite (ht : LocallyFinite fun i ↦ {x : M | t i x ≠ 0})
    (ht' : ∀ i, ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (t i x))) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (∑ᶠ i, (t i x))) := by
  apply (ContMDiff.sum_section_of_locallyFinite ht ht').congr fun y ↦ ?_
  rw [← tsum_eq_finsum]
  choose U hu hfin using ht y
  have : {x | t x y ≠ 0} ⊆ {i | ((fun i ↦ {x | t i x ≠ 0}) i ∩ U).Nonempty} := by
    intro x hx
    rw [Set.mem_setOf] at hx ⊢
    use y
    simpa using ⟨hx, mem_of_mem_nhds hu⟩
  exact Set.Finite.subset hfin this

end operations

/-- Bundled `n` times continuously differentiable sections of a vector bundle.
Denoted as `Cₛ^n⟮I; F, V⟯` within the `Manifold` namespace. -/
structure ContMDiffSection where
  /-- the underlying function of this section -/
  protected toFun : ∀ x, V x
  /-- proof that this section is `C^n` -/
  protected contMDiff_toFun : ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x ↦
    TotalSpace.mk' F x (toFun x)

@[inherit_doc] scoped[Manifold] notation "Cₛ^" n "⟮" I "; " F ", " V "⟯" => ContMDiffSection I F n V

namespace ContMDiffSection

variable {I} {n} {F} {V}

instance : DFunLike Cₛ^n⟮I; F, V⟯ M V where
  coe := ContMDiffSection.toFun
  coe_injective' := by rintro ⟨⟩ ⟨⟩ h; congr

variable {s t : Cₛ^n⟮I; F, V⟯}

@[simp]
theorem coeFn_mk (s : ∀ x, V x)
    (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk x (s x)) :
    (mk s hs : ∀ x, V x) = s :=
  rfl

protected theorem contMDiff (s : Cₛ^n⟮I; F, V⟯) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff_toFun

theorem coe_inj ⦃s t : Cₛ^n⟮I; F, V⟯⦄ (h : (s : ∀ x, V x) = t) : s = t :=
  DFunLike.ext' h

theorem coe_injective : Injective ((↑) : Cₛ^n⟮I; F, V⟯ → ∀ x, V x) :=
  coe_inj

@[ext]
theorem ext (h : ∀ x, s x = t x) : s = t := DFunLike.ext _ _ h

section
variable [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [VectorBundle 𝕜 F V]

instance instAdd : Add Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s t ↦ ⟨s + t, s.contMDiff.add_section t.contMDiff⟩⟩

@[simp]
theorem coe_add (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s + t) = ⇑s + t :=
  rfl

instance instSub : Sub Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s t ↦ ⟨s - t, s.contMDiff.sub_section t.contMDiff⟩⟩

@[simp]
theorem coe_sub (s t : Cₛ^n⟮I; F, V⟯) : ⇑(s - t) = s - t :=
  rfl

instance instZero : Zero Cₛ^n⟮I; F, V⟯ :=
  ⟨⟨fun _ => 0, (contMDiff_zeroSection 𝕜 V).of_le le_top⟩⟩

instance inhabited : Inhabited Cₛ^n⟮I; F, V⟯ :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : Cₛ^n⟮I; F, V⟯) = 0 :=
  rfl

instance instNeg : Neg Cₛ^n⟮I; F, V⟯ :=
  ⟨fun s ↦ ⟨-s, s.contMDiff.neg_section⟩⟩

@[simp]
theorem coe_neg (s : Cₛ^n⟮I; F, V⟯) : ⇑(-s : Cₛ^n⟮I; F, V⟯) = -s :=
  rfl

instance instNSMul : SMul ℕ Cₛ^n⟮I; F, V⟯ :=
  ⟨nsmulRec⟩

@[simp]
theorem coe_nsmul (s : Cₛ^n⟮I; F, V⟯) (k : ℕ) : ⇑(k • s : Cₛ^n⟮I; F, V⟯) = k • ⇑s := by
  induction k with
  | zero => simp_rw [zero_smul]; rfl
  | succ k ih => simp_rw [succ_nsmul, ← ih]; rfl

instance instZSMul : SMul ℤ Cₛ^n⟮I; F, V⟯ :=
  ⟨zsmulRec⟩

@[simp]
theorem coe_zsmul (s : Cₛ^n⟮I; F, V⟯) (z : ℤ) : ⇑(z • s : Cₛ^n⟮I; F, V⟯) = z • ⇑s := by
  rcases z with n | n
  · refine (coe_nsmul s n).trans ?_
    simp only [Int.ofNat_eq_coe, natCast_zsmul]
  · refine (congr_arg Neg.neg (coe_nsmul s (n + 1))).trans ?_
    simp only [negSucc_zsmul]

instance instAddCommGroup : AddCommGroup Cₛ^n⟮I; F, V⟯ :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub coe_nsmul coe_zsmul

instance instSMul : SMul 𝕜 Cₛ^n⟮I; F, V⟯ :=
  ⟨fun c s ↦ ⟨c • ⇑s, s.contMDiff.const_smul_section⟩⟩

@[simp]
theorem coe_smul (r : 𝕜) (s : Cₛ^n⟮I; F, V⟯) : ⇑(r • s : Cₛ^n⟮I; F, V⟯) = r • ⇑s :=
  rfl

variable (I F V n) in
/-- The additive morphism from `C^n` sections to dependent maps. -/
def coeAddHom : Cₛ^n⟮I; F, V⟯ →+ ∀ x, V x where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coeAddHom_apply (s : Cₛ^n⟮I; F, V⟯) : coeAddHom I F n V s = s := rfl

instance instModule : Module 𝕜 Cₛ^n⟮I; F, V⟯ :=
  coe_injective.module 𝕜 (coeAddHom I F n V) coe_smul

end

protected theorem mdifferentiable' (s : Cₛ^n⟮I; F, V⟯) (hn : 1 ≤ n) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff.mdifferentiable hn

protected theorem mdifferentiable (s : Cₛ^∞⟮I; F, V⟯) :
    MDifferentiable I (I.prod 𝓘(𝕜, F)) fun x => TotalSpace.mk' F x (s x : V x) :=
  s.contMDiff.mdifferentiable (mod_cast le_top)

protected theorem mdifferentiableAt (s : Cₛ^∞⟮I; F, V⟯) {x} :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x => TotalSpace.mk' F x (s x : V x)) x :=
  s.mdifferentiable x

end ContMDiffSection
