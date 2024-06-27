/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
## Basic properties of smooth functions between manifolds

In this file, we show that standard operations on smooth maps between smooth manifolds are smooth:
* `ContMDiffOn.comp` gives the invariance of the `Cⁿ` property under composition
* `contMDiff_id` gives the smoothness of the identity
* `contMDiff_const` gives the smoothness of constant functions
* `contMDiff_inclusion` shows that the inclusion between open sets of a topological space is smooth
* `contMDiff_openEmbedding` shows that if `M` has a `ChartedSpace` structure induced by an open
embedding `e : M → H`, then `e` is smooth.

## Tags
chain rule, manifolds, higher derivative

-/
open Set Filter Function

open scoped Topology Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [SmoothManifoldWithCorners I' M']
  -- declare a manifold `M''` over the pair `(E'', H'')`.
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare functions, sets, points and smoothness indices
  {e : PartialHomeomorph M H}
  {e' : PartialHomeomorph M' H'} {f f₁ : M → M'} {s s₁ t : Set M} {x : M} {m n : ℕ∞}
variable {I I'}

/-! ### Smoothness of the composition of smooth functions between manifolds -/

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
    filter_upwards [hf.1.tendsto (extChartAt_source_mem_nhds I' (f x)),
      inter_mem_nhdsWithin s (extChartAt_source_mem_nhds I x)]
    rintro x' (hfx' : f x' ∈ e'.source) ⟨hx's, hx'⟩
    simp only [e.map_source hx', true_and_iff, e.left_inv hx', st hx's, *]
  refine ((hg.2.comp _ (hf.2.mono inter_subset_right) inter_subset_left).mono_of_mem
    (inter_mem ?_ self_mem_nhdsWithin)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [A]
    rintro x' ⟨ht, hfx'⟩
    simp only [*, mem_preimage, writtenInExtChartAt, (· ∘ ·), mem_inter_iff, e'.left_inv,
      true_and_iff]
    exact mem_range_self _
  · filter_upwards [A]
    rintro x' ⟨-, hfx'⟩
    simp only [*, (· ∘ ·), writtenInExtChartAt, e'.left_inv]
  · simp only [e, e', writtenInExtChartAt, (· ∘ ·), mem_extChartAt_source, e.left_inv, e'.left_inv]
#align cont_mdiff_within_at.comp ContMDiffWithinAt.comp

/-- See note [comp_of_eq lemmas] -/
theorem ContMDiffWithinAt.comp_of_eq {t : Set M'} {g : M' → M''} {x : M} {y : M'}
    (hg : ContMDiffWithinAt I' I'' n g t y) (hf : ContMDiffWithinAt I I' n f s x)
    (st : MapsTo f s t) (hx : f x = y) : ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  subst hx; exact hg.comp x hf st
#align cont_mdiff_within_at.comp_of_eq ContMDiffWithinAt.comp_of_eq

/-- The composition of `C^∞` functions within domains at points is `C^∞`. -/
nonrec theorem SmoothWithinAt.comp {t : Set M'} {g : M' → M''} (x : M)
    (hg : SmoothWithinAt I' I'' g t (f x)) (hf : SmoothWithinAt I I' f s x) (st : MapsTo f s t) :
    SmoothWithinAt I I'' (g ∘ f) s x :=
  hg.comp x hf st
#align smooth_within_at.comp SmoothWithinAt.comp

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContMDiffOn.comp {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) (st : s ⊆ f ⁻¹' t) : ContMDiffOn I I'' n (g ∘ f) s := fun x hx =>
  (hg _ (st hx)).comp x (hf x hx) st
#align cont_mdiff_on.comp ContMDiffOn.comp

/-- The composition of `C^∞` functions on domains is `C^∞`. -/
nonrec theorem SmoothOn.comp {t : Set M'} {g : M' → M''} (hg : SmoothOn I' I'' g t)
    (hf : SmoothOn I I' f s) (st : s ⊆ f ⁻¹' t) : SmoothOn I I'' (g ∘ f) s :=
  hg.comp hf st
#align smooth_on.comp SmoothOn.comp

/-- The composition of `C^n` functions on domains is `C^n`. -/
theorem ContMDiffOn.comp' {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right
#align cont_mdiff_on.comp' ContMDiffOn.comp'

/-- The composition of `C^∞` functions is `C^∞`. -/
nonrec theorem SmoothOn.comp' {t : Set M'} {g : M' → M''} (hg : SmoothOn I' I'' g t)
    (hf : SmoothOn I I' f s) : SmoothOn I I'' (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp' hf
#align smooth_on.comp' SmoothOn.comp'

/-- The composition of `C^n` functions is `C^n`. -/
theorem ContMDiff.comp {g : M' → M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff I I' n f) :
    ContMDiff I I'' n (g ∘ f) := by
  rw [← contMDiffOn_univ] at hf hg ⊢
  exact hg.comp hf subset_preimage_univ
#align cont_mdiff.comp ContMDiff.comp

/-- The composition of `C^∞` functions is `C^∞`. -/
nonrec theorem Smooth.comp {g : M' → M''} (hg : Smooth I' I'' g) (hf : Smooth I I' f) :
    Smooth I I'' (g ∘ f) :=
  hg.comp hf
#align smooth.comp Smooth.comp

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
theorem ContMDiffWithinAt.comp' {t : Set M'} {g : M' → M''} (x : M)
    (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right
#align cont_mdiff_within_at.comp' ContMDiffWithinAt.comp'

/-- The composition of `C^∞` functions within domains at points is `C^∞`. -/
nonrec theorem SmoothWithinAt.comp' {t : Set M'} {g : M' → M''} (x : M)
    (hg : SmoothWithinAt I' I'' g t (f x)) (hf : SmoothWithinAt I I' f s x) :
    SmoothWithinAt I I'' (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp' x hf
#align smooth_within_at.comp' SmoothWithinAt.comp'

/-- `g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`. -/
theorem ContMDiffAt.comp_contMDiffWithinAt {g : M' → M''} (x : M)
    (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)
#align cont_mdiff_at.comp_cont_mdiff_within_at ContMDiffAt.comp_contMDiffWithinAt

/-- `g ∘ f` is `C^∞` within `s` at `x` if `g` is `C^∞` at `f x` and
`f` is `C^∞` within `s` at `x`. -/
theorem SmoothAt.comp_smoothWithinAt {g : M' → M''} (x : M) (hg : SmoothAt I' I'' g (f x))
    (hf : SmoothWithinAt I I' f s x) : SmoothWithinAt I I'' (g ∘ f) s x :=
  hg.comp_contMDiffWithinAt x hf
#align smooth_at.comp_smooth_within_at SmoothAt.comp_smoothWithinAt

/-- The composition of `C^n` functions at points is `C^n`. -/
nonrec theorem ContMDiffAt.comp {g : M' → M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x))
    (hf : ContMDiffAt I I' n f x) : ContMDiffAt I I'' n (g ∘ f) x :=
  hg.comp x hf (mapsTo_univ _ _)
#align cont_mdiff_at.comp ContMDiffAt.comp

/-- See note [comp_of_eq lemmas] -/
theorem ContMDiffAt.comp_of_eq {g : M' → M''} {x : M} {y : M'} (hg : ContMDiffAt I' I'' n g y)
    (hf : ContMDiffAt I I' n f x) (hx : f x = y) : ContMDiffAt I I'' n (g ∘ f) x := by
  subst hx; exact hg.comp x hf
#align cont_mdiff_at.comp_of_eq ContMDiffAt.comp_of_eq

/-- The composition of `C^∞` functions at points is `C^∞`. -/
nonrec theorem SmoothAt.comp {g : M' → M''} (x : M) (hg : SmoothAt I' I'' g (f x))
    (hf : SmoothAt I I' f x) : SmoothAt I I'' (g ∘ f) x :=
  hg.comp x hf
#align smooth_at.comp SmoothAt.comp

theorem ContMDiff.comp_contMDiffOn {f : M → M'} {g : M' → M''} {s : Set M}
    (hg : ContMDiff I' I'' n g) (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) s :=
  hg.contMDiffOn.comp hf Set.subset_preimage_univ
#align cont_mdiff.comp_cont_mdiff_on ContMDiff.comp_contMDiffOn

theorem Smooth.comp_smoothOn {f : M → M'} {g : M' → M''} {s : Set M} (hg : Smooth I' I'' g)
    (hf : SmoothOn I I' f s) : SmoothOn I I'' (g ∘ f) s :=
  hg.smoothOn.comp hf Set.subset_preimage_univ
#align smooth.comp_smooth_on Smooth.comp_smoothOn

theorem ContMDiffOn.comp_contMDiff {t : Set M'} {g : M' → M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiff I I' n f) (ht : ∀ x, f x ∈ t) : ContMDiff I I'' n (g ∘ f) :=
  contMDiffOn_univ.mp <| hg.comp hf.contMDiffOn fun x _ => ht x
#align cont_mdiff_on.comp_cont_mdiff ContMDiffOn.comp_contMDiff

theorem SmoothOn.comp_smooth {t : Set M'} {g : M' → M''} (hg : SmoothOn I' I'' g t)
    (hf : Smooth I I' f) (ht : ∀ x, f x ∈ t) : Smooth I I'' (g ∘ f) :=
  hg.comp_contMDiff hf ht
#align smooth_on.comp_smooth SmoothOn.comp_smooth

end Composition

/-! ### The identity is smooth -/

section id

theorem contMDiff_id : ContMDiff I I n (id : M → M) :=
  ContMDiff.of_le
    ((contDiffWithinAt_localInvariantProp I I ∞).liftProp_id (contDiffWithinAtProp_id I)) le_top
#align cont_mdiff_id contMDiff_id

theorem smooth_id : Smooth I I (id : M → M) :=
  contMDiff_id
#align smooth_id smooth_id

theorem contMDiffOn_id : ContMDiffOn I I n (id : M → M) s :=
  contMDiff_id.contMDiffOn
#align cont_mdiff_on_id contMDiffOn_id

theorem smoothOn_id : SmoothOn I I (id : M → M) s :=
  contMDiffOn_id
#align smooth_on_id smoothOn_id

theorem contMDiffAt_id : ContMDiffAt I I n (id : M → M) x :=
  contMDiff_id.contMDiffAt
#align cont_mdiff_at_id contMDiffAt_id

theorem smoothAt_id : SmoothAt I I (id : M → M) x :=
  contMDiffAt_id
#align smooth_at_id smoothAt_id

theorem contMDiffWithinAt_id : ContMDiffWithinAt I I n (id : M → M) s x :=
  contMDiffAt_id.contMDiffWithinAt
#align cont_mdiff_within_at_id contMDiffWithinAt_id

theorem smoothWithinAt_id : SmoothWithinAt I I (id : M → M) s x :=
  contMDiffWithinAt_id
#align smooth_within_at_id smoothWithinAt_id

end id

/-! ### Constants are smooth -/

section id
variable {c : M'}

theorem contMDiff_const : ContMDiff I I' n fun _ : M => c := by
  intro x
  refine ⟨continuousWithinAt_const, ?_⟩
  simp only [ContDiffWithinAtProp, (· ∘ ·)]
  exact contDiffWithinAt_const
#align cont_mdiff_const contMDiff_const

@[to_additive]
theorem contMDiff_one [One M'] : ContMDiff I I' n (1 : M → M') := by
  simp only [Pi.one_def, contMDiff_const]
#align cont_mdiff_one contMDiff_one
#align cont_mdiff_zero contMDiff_zero

theorem smooth_const : Smooth I I' fun _ : M => c :=
  contMDiff_const
#align smooth_const smooth_const

@[to_additive]
theorem smooth_one [One M'] : Smooth I I' (1 : M → M') := by simp only [Pi.one_def, smooth_const]
#align smooth_one smooth_one
#align smooth_zero smooth_zero

theorem contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => c) s :=
  contMDiff_const.contMDiffOn
#align cont_mdiff_on_const contMDiffOn_const

@[to_additive]
theorem contMDiffOn_one [One M'] : ContMDiffOn I I' n (1 : M → M') s :=
  contMDiff_one.contMDiffOn
#align cont_mdiff_on_one contMDiffOn_one
#align cont_mdiff_on_zero contMDiffOn_zero

theorem smoothOn_const : SmoothOn I I' (fun _ : M => c) s :=
  contMDiffOn_const
#align smooth_on_const smoothOn_const

@[to_additive]
theorem smoothOn_one [One M'] : SmoothOn I I' (1 : M → M') s :=
  contMDiffOn_one
#align smooth_on_one smoothOn_one
#align smooth_on_zero smoothOn_zero

theorem contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => c) x :=
  contMDiff_const.contMDiffAt
#align cont_mdiff_at_const contMDiffAt_const

@[to_additive]
theorem contMDiffAt_one [One M'] : ContMDiffAt I I' n (1 : M → M') x :=
  contMDiff_one.contMDiffAt
#align cont_mdiff_at_one contMDiffAt_one
#align cont_mdiff_at_zero contMDiffAt_zero

theorem smoothAt_const : SmoothAt I I' (fun _ : M => c) x :=
  contMDiffAt_const
#align smooth_at_const smoothAt_const

@[to_additive]
theorem smoothAt_one [One M'] : SmoothAt I I' (1 : M → M') x :=
  contMDiffAt_one
#align smooth_at_one smoothAt_one
#align smooth_at_zero smoothAt_zero

theorem contMDiffWithinAt_const : ContMDiffWithinAt I I' n (fun _ : M => c) s x :=
  contMDiffAt_const.contMDiffWithinAt
#align cont_mdiff_within_at_const contMDiffWithinAt_const

@[to_additive]
theorem contMDiffWithinAt_one [One M'] : ContMDiffWithinAt I I' n (1 : M → M') s x :=
  contMDiffAt_const.contMDiffWithinAt
#align cont_mdiff_within_at_one contMDiffWithinAt_one
#align cont_mdiff_within_at_zero contMDiffWithinAt_zero

theorem smoothWithinAt_const : SmoothWithinAt I I' (fun _ : M => c) s x :=
  contMDiffWithinAt_const
#align smooth_within_at_const smoothWithinAt_const

@[to_additive]
theorem smoothWithinAt_one [One M'] : SmoothWithinAt I I' (1 : M → M') s x :=
  contMDiffWithinAt_one
#align smooth_within_at_one smoothWithinAt_one
#align smooth_within_at_zero smoothWithinAt_zero

end id

/-- `f` is continuously differentiable if it is cont. differentiable at
each `x ∈ mulTSupport f`. -/
@[to_additive "`f` is continuously differentiable if it is continuously
differentiable at each `x ∈ tsupport f`."]
theorem contMDiff_of_mulTSupport [One M'] {f : M → M'}
    (hf : ∀ x ∈ mulTSupport f, ContMDiffAt I I' n f x) : ContMDiff I I' n f := by
  intro x
  by_cases hx : x ∈ mulTSupport f
  · exact hf x hx
  · exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (not_mem_mulTSupport_iff_eventuallyEq.1 hx)
#align cont_mdiff_of_support contMDiff_of_tsupport

@[deprecated (since := "2024-01-15")] alias contMDiff_of_support := contMDiff_of_tsupport

@[to_additive contMDiffWithinAt_of_not_mem]
theorem contMDiffWithinAt_of_not_mem_mulTSupport {f : M → M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : ℕ∞) (s : Set M) : ContMDiffWithinAt I I' n f s x := by
  apply contMDiffWithinAt_const.congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds <| not_mem_mulTSupport_iff_eventuallyEq.mp hx)
    (image_eq_one_of_nmem_mulTSupport hx)

/-- `f` is continuously differentiable at each point outside of its `mulTSupport`. -/
@[to_additive contMDiffAt_of_not_mem]
theorem contMDiffAt_of_not_mem_mulTSupport {f : M → M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : ℕ∞) : ContMDiffAt I I' n f x :=
  contMDiffWithinAt_of_not_mem_mulTSupport hx n univ


/-! ### The inclusion map from one open set to another is smooth -/

section Inclusion

open TopologicalSpace

theorem contMdiffAt_subtype_iff {n : ℕ∞} {U : Opens M} {f : M → M'} {x : U} :
    ContMDiffAt I I' n (fun x : U ↦ f x) x ↔ ContMDiffAt I I' n f x :=
  ((contDiffWithinAt_localInvariantProp I I' n).liftPropAt_iff_comp_subtype_val _ _).symm

theorem contMDiff_subtype_val {n : ℕ∞} {U : Opens M} : ContMDiff I I n (Subtype.val : U → M) :=
  fun _ ↦ contMdiffAt_subtype_iff.mpr contMDiffAt_id

@[to_additive]
theorem ContMDiff.extend_one [T2Space M] [One M'] {n : ℕ∞} {U : Opens M} {f : U → M'}
    (supp : HasCompactMulSupport f) (diff : ContMDiff I I' n f) :
    ContMDiff I I' n (Subtype.val.extend f 1) := fun x ↦ by
  refine contMDiff_of_mulTSupport (fun x h ↦ ?_) _
  lift x to U using Subtype.coe_image_subset _ _
    (supp.mulTSupport_extend_one_subset continuous_subtype_val h)
  rw [← contMdiffAt_subtype_iff, ← comp_def, extend_comp Subtype.val_injective]
  exact diff.contMDiffAt

theorem contMDiff_inclusion {n : ℕ∞} {U V : Opens M} (h : U ≤ V) :
    ContMDiff I I n (Set.inclusion h : U → V) := by
  rintro ⟨x, hx : x ∈ U⟩
  apply (contDiffWithinAt_localInvariantProp I I n).liftProp_inclusion
  intro y
  dsimp only [ContDiffWithinAtProp, id_comp, preimage_univ]
  rw [Set.univ_inter]
  exact contDiffWithinAt_id.congr I.rightInvOn (congr_arg I (I.left_inv y))
#align cont_mdiff_inclusion contMDiff_inclusion

theorem smooth_subtype_iff {U : Opens M} {f : M → M'} {x : U} :
    SmoothAt I I' (fun x : U ↦ f x) x ↔ SmoothAt I I' f x := contMdiffAt_subtype_iff

theorem smooth_subtype_val {U : Opens M} : Smooth I I (Subtype.val : U → M) := contMDiff_subtype_val

@[to_additive]
theorem Smooth.extend_one [T2Space M] [One M'] {U : Opens M} {f : U → M'}
    (supp : HasCompactMulSupport f) (diff : Smooth I I' f) : Smooth I I' (Subtype.val.extend f 1) :=
  ContMDiff.extend_one supp diff

theorem smooth_inclusion {U V : Opens M} (h : U ≤ V) : Smooth I I (Set.inclusion h : U → V) :=
  contMDiff_inclusion h
#align smooth_inclusion smooth_inclusion

end Inclusion

/-! ### Open embeddings and their inverses are smooth -/

section

variable (I)
  [Nonempty M] {e : M → H} (h : OpenEmbedding e)
  [Nonempty M'] {e' : M' → H'} (h' : OpenEmbedding e')
  {n : WithTop ℕ}

/-- If the `ChartedSpace` structure on a manifold `M` is given by an open embedding `e : M → H`,
then `e` is smooth. -/
lemma contMDiff_openEmbedding :
    haveI := h.singletonChartedSpace; ContMDiff I I n e := by
  haveI := h.singleton_smoothManifoldWithCorners I
  rw [@contMDiff_iff _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace]
  use h.continuous
  intros x y
  -- show the function is actually the identity on the range of I ∘ e
  apply contDiffOn_id.congr
  intros z hz
  -- factorise into the chart `e` and the model `id`
  simp only [mfld_simps]
  rw [h.toPartialHomeomorph_right_inv]
  · rw [I.right_inv]
    apply mem_of_subset_of_mem _ hz.1
    exact haveI := h.singletonChartedSpace; extChartAt_target_subset_range I x
  · -- `hz` implies that `z ∈ range (I ∘ e)`
    have := hz.1
    rw [@extChartAt_target _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace] at this
    have := this.1
    rw [mem_preimage, PartialHomeomorph.singletonChartedSpace_chartAt_eq,
      h.toPartialHomeomorph_target] at this
    exact this

variable {I}
/-- If the `ChartedSpace` structure on a manifold `M` is given by an open embedding `e : M → H`,
then the inverse of `e` is smooth. -/
lemma contMDiffOn_openEmbedding_symm :
    haveI := h.singletonChartedSpace; ContMDiffOn I I
      n (OpenEmbedding.toPartialHomeomorph e h).symm (range e) := by
  haveI := h.singleton_smoothManifoldWithCorners I
  rw [@contMDiffOn_iff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace]
  constructor
  · rw [← h.toPartialHomeomorph_target]
    exact (h.toPartialHomeomorph e).continuousOn_symm
  · intros z hz
    -- show the function is actually the identity on the range of I ∘ e
    apply contDiffOn_id.congr
    intros z hz
    -- factorise into the chart `e` and the model `id`
    simp only [mfld_simps]
    have : I.symm z ∈ range e := by
      rw [ModelWithCorners.symm, ← mem_preimage]
      exact hz.2.1
    rw [h.toPartialHomeomorph_right_inv e this]
    apply I.right_inv
    exact mem_of_subset_of_mem (extChartAt_target_subset_range _ _) hz.1

/-- Let `M'` be a manifold whose chart structure is given by an open embedding `e'` into its model
space `H'`. Then the smoothness of `e' ∘ f : M → H'` implies the smoothness of `f`.

This is useful, for example, when `e' ∘ f = g ∘ e` for smooth maps `e : M → X` and `g : X → H'`. -/
lemma ContMDiff.of_comp_openEmbedding {f : M → M'} (hf : ContMDiff I I' n (e' ∘ f)) :
    haveI := h'.singletonChartedSpace; ContMDiff I I' n f := by
  have : f = (h'.toPartialHomeomorph e').symm ∘ e' ∘ f := by
    ext
    rw [Function.comp_apply, Function.comp_apply, OpenEmbedding.toPartialHomeomorph_left_inv]
  rw [this]
  apply @ContMDiffOn.comp_contMDiff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h'.singletonChartedSpace _ _ (range e') _ (contMDiffOn_openEmbedding_symm h') hf
  simp

end
