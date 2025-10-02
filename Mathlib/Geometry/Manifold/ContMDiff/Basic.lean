/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
## Basic properties of `C^n` functions between manifolds

In this file, we show that standard operations on `C^n` maps between manifolds are `C^n` :
* `ContMDiffOn.comp` gives the invariance of the `Cⁿ` property under composition
* `contMDiff_id` gives the smoothness of the identity
* `contMDiff_const` gives the smoothness of constant functions
* `contMDiff_inclusion` shows that the inclusion between open sets of a topological space is `C^n`
* `contMDiff_isOpenEmbedding` shows that if `M` has a `ChartedSpace` structure induced by an open
  embedding `e : M → H`, then `e` is `C^n`.

## Tags
chain rule, manifolds, higher derivative

-/

open Filter Function Set Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare the prerequisites for a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  -- declare the prerequisites for a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M']
  -- declare the prerequisites for a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']

section ChartedSpace
variable [ChartedSpace H M] [ChartedSpace H' M'] [ChartedSpace H'' M'']
  -- declare functions, sets, points and smoothness indices
  {f : M → M'} {s : Set M} {x : M} {n : WithTop ℕ∞}

/-! ### Regularity of the composition of `C^n` functions between manifolds -/

section Composition

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
theorem ContMDiffWithinAt.comp {t : Set M'} {g : M' → M''} (x : M)
    (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x)
    (st : MapsTo f s t) : ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  rw [contMDiffWithinAt_iff] at hg hf ⊢
  refine ⟨hg.1.comp hf.1 st, ?_⟩
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  have : e' (f x) = (writtenInExtChartAt I I' x f) (e x) := by simp only [e, e', mfld_simps]
  rw [this] at hg
  have A : ∀ᶠ y in 𝓝[e.symm ⁻¹' s ∩ range I] e x, f (e.symm y) ∈ t ∧ f (e.symm y) ∈ e'.source := by
    simp only [e, ← map_extChartAt_nhdsWithin, eventually_map]
    filter_upwards [hf.1.tendsto (extChartAt_source_mem_nhds (I := I') (f x)),
      inter_mem_nhdsWithin s (extChartAt_source_mem_nhds (I := I) x)]
    rintro x' (hfx' : f x' ∈ e'.source) ⟨hx's, hx'⟩
    simp only [e, true_and, e.left_inv hx', st hx's, *]
  refine ((hg.2.comp _ (hf.2.mono inter_subset_right)
      ((mapsTo_preimage _ _).mono_left inter_subset_left)).mono_of_mem_nhdsWithin
      (inter_mem ?_ self_mem_nhdsWithin)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [A]
    rintro x' ⟨ht, hfx'⟩
    simp only [*, e, e',mem_preimage, writtenInExtChartAt, (· ∘ ·), mem_inter_iff, e'.left_inv,
      true_and]
    exact mem_range_self _
  · filter_upwards [A]
    rintro x' ⟨-, hfx'⟩
    simp only [*, e, e', (· ∘ ·), writtenInExtChartAt, e'.left_inv]
  · simp only [e, e', writtenInExtChartAt, (· ∘ ·), mem_extChartAt_source,
      e.left_inv, e'.left_inv]

/-- See note [comp_of_eq lemmas] -/
theorem ContMDiffWithinAt.comp_of_eq {t : Set M'} {g : M' → M''} {x : M} {y : M'}
    (hg : ContMDiffWithinAt I' I'' n g t y) (hf : ContMDiffWithinAt I I' n f s x)
    (st : MapsTo f s t) (hx : f x = y) : ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  subst hx; exact hg.comp x hf st

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContMDiffOn.comp {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) (st : s ⊆ f ⁻¹' t) : ContMDiffOn I I'' n (g ∘ f) s := fun x hx =>
  (hg _ (st hx)).comp x (hf x hx) st

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContMDiffOn.comp' {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/-- The composition of `C^n` functions is `C^n`. -/
theorem ContMDiff.comp {g : M' → M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff I I' n f) :
    ContMDiff I I'' n (g ∘ f) := by
  rw [← contMDiffOn_univ] at hf hg ⊢
  exact hg.comp hf subset_preimage_univ

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
theorem ContMDiffWithinAt.comp' {t : Set M'} {g : M' → M''} (x : M)
    (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

/-- `g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`. -/
theorem ContMDiffAt.comp_contMDiffWithinAt {g : M' → M''} (x : M)
    (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)

/-- `g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`. -/
theorem ContMDiffAt.comp_contMDiffWithinAt_of_eq {g : M' → M''} {x : M} {y : M'}
    (hg : ContMDiffAt I' I'' n g y) (hf : ContMDiffWithinAt I I' n f s x) (hx : f x = y) :
    ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  subst hx; exact hg.comp_contMDiffWithinAt x hf

/-- The composition of `C^n` functions at points is `C^n`. -/
nonrec theorem ContMDiffAt.comp {g : M' → M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x))
    (hf : ContMDiffAt I I' n f x) : ContMDiffAt I I'' n (g ∘ f) x :=
  hg.comp x hf (mapsTo_univ _ _)

/-- See note [comp_of_eq lemmas] -/
theorem ContMDiffAt.comp_of_eq {g : M' → M''} {x : M} {y : M'} (hg : ContMDiffAt I' I'' n g y)
    (hf : ContMDiffAt I I' n f x) (hx : f x = y) : ContMDiffAt I I'' n (g ∘ f) x := by
  subst hx; exact hg.comp x hf

theorem ContMDiff.comp_contMDiffOn {f : M → M'} {g : M' → M''} {s : Set M}
    (hg : ContMDiff I' I'' n g) (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) s :=
  hg.contMDiffOn.comp hf Set.subset_preimage_univ

theorem ContMDiffOn.comp_contMDiff {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiff I I' n f) (ht : ∀ x, f x ∈ t) : ContMDiff I I'' n (g ∘ f) :=
  contMDiffOn_univ.mp <| hg.comp hf.contMDiffOn fun x _ => ht x

end Composition

/-! ### The identity is `C^n` -/

section id

theorem contMDiff_id : ContMDiff I I n (id : M → M) :=
  ContMDiff.of_le
    ((contDiffWithinAt_localInvariantProp ⊤).liftProp_id contDiffWithinAtProp_id) le_top

theorem contMDiffOn_id : ContMDiffOn I I n (id : M → M) s :=
  contMDiff_id.contMDiffOn

theorem contMDiffAt_id : ContMDiffAt I I n (id : M → M) x :=
  contMDiff_id.contMDiffAt

theorem contMDiffWithinAt_id : ContMDiffWithinAt I I n (id : M → M) s x :=
  contMDiffAt_id.contMDiffWithinAt

end id

/-! ### Iterated functions -/

section Iterate

/-- The iterates of `C^n` functions on domains are `C^n`. -/
theorem ContMDiffOn.iterate {f : M → M} (hf : ContMDiffOn I I n f s)
    (hmaps : Set.MapsTo f s s) (k : ℕ) :
    ContMDiffOn I I n (f^[k]) s := by
  induction k with
  | zero => simpa using contMDiffOn_id
  | succ k h => simpa using h.comp hf hmaps

/-- The iterates of `C^n` functions are `C^n`. -/
theorem ContMDiff.iterate {f : M → M} (hf : ContMDiff I I n f) (k : ℕ) :
    ContMDiff I I n (f^[k]) :=
  contMDiffOn_univ.mp ((contMDiffOn_univ.mpr hf).iterate (univ.mapsTo_univ f) k)

end Iterate

/-! ### Constants are `C^n` -/

section const
variable {c : M'}

theorem contMDiff_const : ContMDiff I I' n fun _ : M => c := by
  intro x
  refine ⟨continuousWithinAt_const, ?_⟩
  simp only [ContDiffWithinAtProp, Function.comp_def]
  exact contDiffWithinAt_const

@[to_additive]
theorem contMDiff_one [One M'] : ContMDiff I I' n (1 : M → M') := by
  simp only [Pi.one_def, contMDiff_const]

theorem contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => c) s :=
  contMDiff_const.contMDiffOn

@[to_additive]
theorem contMDiffOn_one [One M'] : ContMDiffOn I I' n (1 : M → M') s :=
  contMDiff_one.contMDiffOn

theorem contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => c) x :=
  contMDiff_const.contMDiffAt

@[to_additive]
theorem contMDiffAt_one [One M'] : ContMDiffAt I I' n (1 : M → M') x :=
  contMDiff_one.contMDiffAt

theorem contMDiffWithinAt_const : ContMDiffWithinAt I I' n (fun _ : M => c) s x :=
  contMDiffAt_const.contMDiffWithinAt

@[to_additive]
theorem contMDiffWithinAt_one [One M'] : ContMDiffWithinAt I I' n (1 : M → M') s x :=
  contMDiffAt_const.contMDiffWithinAt

@[nontriviality]
theorem contMDiff_of_subsingleton [Subsingleton M'] : ContMDiff I I' n f := by
  intro x
  rw [Subsingleton.elim f fun _ => (f x)]
  exact contMDiffAt_const

@[nontriviality]
theorem contMDiffAt_of_subsingleton [Subsingleton M'] : ContMDiffAt I I' n f x :=
  contMDiff_of_subsingleton.contMDiffAt

@[nontriviality]
theorem contMDiffWithinAt_of_subsingleton [Subsingleton M'] : ContMDiffWithinAt I I' n f s x :=
  contMDiffAt_of_subsingleton.contMDiffWithinAt

@[nontriviality]
theorem contMDiffOn_of_subsingleton [Subsingleton M'] : ContMDiffOn I I' n f s :=
  contMDiff_of_subsingleton.contMDiffOn

lemma contMDiff_of_discreteTopology [DiscreteTopology M] :
    ContMDiff I I' n f := by
  intro x
  -- f is locally constant, and constant functions are smooth.
  apply contMDiff_const (c := f x).contMDiffAt.congr_of_eventuallyEq
  simp [EventuallyEq]

end const

/-- `f` is continuously differentiable if it is cont. differentiable at
each `x ∈ mulTSupport f`. -/
@[to_additive /-- `f` is continuously differentiable if it is continuously
differentiable at each `x ∈ tsupport f`. See also `contMDiff_section_of_tsupport`
for a similar result for sections of vector bundles. -/]
theorem contMDiff_of_mulTSupport [One M'] {f : M → M'}
    (hf : ∀ x ∈ mulTSupport f, ContMDiffAt I I' n f x) : ContMDiff I I' n f := by
  intro x
  by_cases hx : x ∈ mulTSupport f
  · exact hf x hx
  · exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (notMem_mulTSupport_iff_eventuallyEq.1 hx)

@[to_additive contMDiffWithinAt_of_notMem]
theorem contMDiffWithinAt_of_notMem_mulTSupport {f : M → M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : WithTop ℕ∞) (s : Set M) : ContMDiffWithinAt I I' n f s x := by
  apply contMDiffWithinAt_const.congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds <| notMem_mulTSupport_iff_eventuallyEq.mp hx)
    (image_eq_one_of_notMem_mulTSupport hx)

@[deprecated (since := "2025-05-23")]
alias contMDiffWithinAt_of_not_mem := contMDiffWithinAt_of_notMem

@[to_additive existing contMDiffWithinAt_of_not_mem, deprecated (since := "2025-05-23")]
alias contMDiffWithinAt_of_not_mem_mulTSupport := contMDiffWithinAt_of_notMem_mulTSupport

/-- `f` is continuously differentiable at each point outside of its `mulTSupport`. -/
@[to_additive contMDiffAt_of_notMem]
theorem contMDiffAt_of_notMem_mulTSupport {f : M → M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : WithTop ℕ∞) : ContMDiffAt I I' n f x :=
  contMDiffWithinAt_of_notMem_mulTSupport hx n univ

@[deprecated (since := "2025-05-23")]
alias contMDiffAt_of_not_mem := contMDiffAt_of_notMem

@[to_additive existing contMDiffAt_of_not_mem, deprecated (since := "2025-05-23")]
alias contMDiffAt_of_not_mem_mulTSupport := contMDiffAt_of_notMem_mulTSupport

/-- Given two `C^n` functions `f` and `g` which coincide locally around the frontier of a set `s`,
then the piecewise function defined using `f` on `s` and `g` elsewhere is `C^n`. -/
lemma ContMDiff.piecewise
    {f g : M → M'} {s : Set M} [DecidablePred (· ∈ s)]
    (hf : ContMDiff I I' n f) (hg : ContMDiff I I' n g)
    (hfg : ∀ x ∈ frontier s, f =ᶠ[𝓝 x] g) :
    ContMDiff I I' n (piecewise s f g) := by
  intro x
  by_cases hx : x ∈ interior s
  · apply (hf x).congr_of_eventuallyEq
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [piecewise_eq_of_mem]
    apply interior_subset hy
  by_cases h'x : x ∈ closure s
  · have : x ∈ frontier s := ⟨h'x, hx⟩
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [hfg x this] with y hy
    simp [Set.piecewise, hy]
  · apply (hg x).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds h'x] with y hy
    rw [piecewise_eq_of_notMem]
    contrapose! hy
    simpa using subset_closure hy

/-- Given two `C^n` functions `f` and `g` from `ℝ` to a real manifold which coincide locally
around a point `s`, then the piecewise function using `f` before `t` and `g` after is `C^n`. -/
lemma ContMDiff.piecewise_Iic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f g : ℝ → M} {s : ℝ}
    (hf : ContMDiff 𝓘(ℝ) I n f) (hg : ContMDiff 𝓘(ℝ) I n g) (hfg : f =ᶠ[𝓝 s] g) :
    ContMDiff 𝓘(ℝ) I n (Set.piecewise (Iic s) f g) :=
  hf.piecewise hg (by simpa using hfg)

/-! ### Being `C^k` on a union of open sets can be tested on each set -/
section contMDiff_union

variable {s t : Set M}

/-- If a function is `C^k` on two open sets, it is also `C^n` on their union. -/
lemma ContMDiffOn.union_of_isOpen (hf : ContMDiffOn I I' n f s) (hf' : ContMDiffOn I I' n f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    ContMDiffOn I I' n f (s ∪ t) := by
  intro x hx
  obtain (hx | hx) := hx
  · exact (hf x hx).contMDiffAt (hs.mem_nhds hx) |>.contMDiffWithinAt
  · exact (hf' x hx).contMDiffAt (ht.mem_nhds hx) |>.contMDiffWithinAt

/-- A function is `C^k` on two open sets iff it is `C^k` on their union. -/
lemma contMDiffOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    ContMDiffOn I I' n f (s ∪ t) ↔ ContMDiffOn I I' n f s ∧ ContMDiffOn I I' n f t :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ ↦ ContMDiffOn.union_of_isOpen hfs hft hs ht⟩

lemma contMDiff_of_contMDiffOn_union_of_isOpen (hf : ContMDiffOn I I' n f s)
    (hf' : ContMDiffOn I I' n f t) (hst : s ∪ t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    ContMDiff I I' n f := by
  rw [← contMDiffOn_univ, ← hst]
  exact hf.union_of_isOpen hf' hs ht

/-- If a function is `C^k` on open sets `s i`, it is `C^k` on their union -/
lemma ContMDiffOn.iUnion_of_isOpen {ι : Type*} {s : ι → Set M}
    (hf : ∀ i : ι, ContMDiffOn I I' n f (s i)) (hs : ∀ i, IsOpen (s i)) :
    ContMDiffOn I I' n f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).contMDiffAt ((hs i).mem_nhds hxsi) |>.contMDiffWithinAt

/-- A function is `C^k` on a union of open sets `s i` iff it is `C^k` on each `s i`. -/
lemma contMDiffOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set M}
    (hs : ∀ i, IsOpen (s i)) :
    ContMDiffOn I I' n f (⋃ i, s i) ↔ ∀ i : ι, ContMDiffOn I I' n f (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ ContMDiffOn.iUnion_of_isOpen h hs⟩

lemma contMDiff_of_contMDiffOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set M}
    (hf : ∀ i : ι, ContMDiffOn I I' n f (s i)) (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    ContMDiff I I' n f := by
  rw [← contMDiffOn_univ, ← hs']
  exact ContMDiffOn.iUnion_of_isOpen hf hs

end contMDiff_union


/-! ### The inclusion map from one open set to another is `C^n` -/

section Inclusion

open TopologicalSpace

theorem contMDiffAt_subtype_iff {n : WithTop ℕ∞} {U : Opens M} {f : M → M'} {x : U} :
    ContMDiffAt I I' n (fun x : U ↦ f x) x ↔ ContMDiffAt I I' n f x :=
  ((contDiffWithinAt_localInvariantProp n).liftPropAt_iff_comp_subtype_val _ _).symm

theorem contMDiff_subtype_val {n : WithTop ℕ∞} {U : Opens M} :
    ContMDiff I I n (Subtype.val : U → M) :=
  fun _ ↦ contMDiffAt_subtype_iff.mpr contMDiffAt_id

@[to_additive]
theorem ContMDiff.extend_one [T2Space M] [One M'] {n : WithTop ℕ∞} {U : Opens M} {f : U → M'}
    (supp : HasCompactMulSupport f) (diff : ContMDiff I I' n f) :
    ContMDiff I I' n (Subtype.val.extend f 1) := fun x ↦ by
  refine contMDiff_of_mulTSupport (fun x h ↦ ?_) _
  lift x to U using Subtype.coe_image_subset _ _
    (supp.mulTSupport_extend_one_subset continuous_subtype_val h)
  rw [← contMDiffAt_subtype_iff]
  simp_rw [← comp_def]
  rw [extend_comp Subtype.val_injective]
  exact diff.contMDiffAt

theorem contMDiff_inclusion {n : WithTop ℕ∞} {U V : Opens M} (h : U ≤ V) :
    ContMDiff I I n (Opens.inclusion h : U → V) := by
  rintro ⟨x, hx : x ∈ U⟩
  apply (contDiffWithinAt_localInvariantProp n).liftProp_inclusion
  intro y
  dsimp only [ContDiffWithinAtProp, id_comp, preimage_univ]
  rw [Set.univ_inter]
  exact contDiffWithinAt_id.congr I.rightInvOn (congr_arg I (I.left_inv y))

end Inclusion

end ChartedSpace

/-! ### Open embeddings and their inverses are `C^n` -/

section

variable {e : M → H} (h : IsOpenEmbedding e) {n : WithTop ℕ∞}

/-- If the `ChartedSpace` structure on a manifold `M` is given by an open embedding `e : M → H`,
then `e` is `C^n`. -/
lemma contMDiff_isOpenEmbedding [Nonempty M] :
    haveI := h.singletonChartedSpace; ContMDiff I I n e := by
  haveI := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiff_iff _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace]
  use h.continuous
  intro x y
  -- show the function is actually the identity on the range of I ∘ e
  apply contDiffOn_id.congr
  intro z hz
  -- factorise into the chart `e` and the model `id`
  simp only [mfld_simps]
  rw [h.toOpenPartialHomeomorph_right_inv]
  · rw [I.right_inv]
    apply mem_of_subset_of_mem _ hz.1
    exact letI := h.singletonChartedSpace; extChartAt_target_subset_range (I := I) x
  · -- `hz` implies that `z ∈ range (I ∘ e)`
    have := hz.1
    rw [@extChartAt_target _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace] at this
    have := this.1
    rw [mem_preimage, OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
      h.toOpenPartialHomeomorph_target] at this
    exact this

/-- If the `ChartedSpace` structure on a manifold `M` is given by an open embedding `e : M → H`,
then the inverse of `e` is `C^n`. -/
lemma contMDiffOn_isOpenEmbedding_symm [Nonempty M] :
    haveI := h.singletonChartedSpace; ContMDiffOn I I
      n (IsOpenEmbedding.toOpenPartialHomeomorph e h).symm (range e) := by
  haveI := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiffOn_iff]
  constructor
  · rw [← h.toOpenPartialHomeomorph_target]
    exact (h.toOpenPartialHomeomorph e).continuousOn_symm
  · intro z hz
    -- show the function is actually the identity on the range of I ∘ e
    apply contDiffOn_id.congr
    intro z hz
    -- factorise into the chart `e` and the model `id`
    simp only [mfld_simps]
    have : I.symm z ∈ range e := by
      rw [ModelWithCorners.symm, ← mem_preimage]
      exact hz.2.1
    rw [h.toOpenPartialHomeomorph_right_inv e this]
    apply I.right_inv
    exact mem_of_subset_of_mem (extChartAt_target_subset_range _) hz.1

variable [ChartedSpace H M]
variable [Nonempty M'] {e' : M' → H'} (h' : IsOpenEmbedding e')

/-- Let `M'` be a manifold whose chart structure is given by an open embedding `e'` into its model
space `H'`. If `e' ∘ f : M → H'` is `C^n`, then `f` is `C^n`.

This is useful, for example, when `e' ∘ f = g ∘ e` for smooth maps `e : M → X` and `g : X → H'`. -/
lemma ContMDiff.of_comp_isOpenEmbedding {f : M → M'} (hf : ContMDiff I I' n (e' ∘ f)) :
    haveI := h'.singletonChartedSpace; ContMDiff I I' n f := by
  have : f = (h'.toOpenPartialHomeomorph e').symm ∘ e' ∘ f := by
    ext
    rw [Function.comp_apply, Function.comp_apply, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rw [this]
  apply @ContMDiffOn.comp_contMDiff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h'.singletonChartedSpace _ _ (range e') _ (contMDiffOn_isOpenEmbedding_symm h') hf
  simp

end
