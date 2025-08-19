/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Sigma-compactness in topological spaces

## Main definitions
* `IsSigmaCompact`: a set that is the union of countably many compact sets.
* `SigmaCompactSpace X`: `X` is a σ-compact topological space; i.e., is the union
  of a countable collection of compact subspaces.

-/

open Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- A subset `s ⊆ X` is called **σ-compact** if it is the union of countably many compact sets. -/
def IsSigmaCompact (s : Set X) : Prop :=
  ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = s

/-- Compact sets are σ-compact. -/
lemma IsCompact.isSigmaCompact {s : Set X} (hs : IsCompact s) : IsSigmaCompact s :=
  ⟨fun _ ↦ s, fun _ ↦ hs, iUnion_const _⟩

/-- The empty set is σ-compact. -/
@[simp]
lemma isSigmaCompact_empty : IsSigmaCompact (∅ : Set X) :=
  IsCompact.isSigmaCompact isCompact_empty

/-- Countable unions of compact sets are σ-compact. -/
lemma isSigmaCompact_iUnion_of_isCompact [hι : Countable ι] (s : ι → Set X)
    (hcomp : ∀ i, IsCompact (s i)) : IsSigmaCompact (⋃ i, s i) := by
  rcases isEmpty_or_nonempty ι
  · simp only [iUnion_of_empty, isSigmaCompact_empty]
  · -- If ι is non-empty, choose a surjection f : ℕ → ι, this yields a map ℕ → Set X.
    obtain ⟨f, hf⟩ := countable_iff_exists_surjective.mp hι
    exact ⟨s ∘ f, fun n ↦ hcomp (f n), Function.Surjective.iUnion_comp hf _⟩

/-- Countable unions of compact sets are σ-compact. -/
lemma isSigmaCompact_sUnion_of_isCompact {S : Set (Set X)} (hc : Set.Countable S)
    (hcomp : ∀ (s : Set X), s ∈ S → IsCompact s) : IsSigmaCompact (⋃₀ S) := by
  have : Countable S := countable_coe_iff.mpr hc
  rw [sUnion_eq_iUnion]
  apply isSigmaCompact_iUnion_of_isCompact _ (fun ⟨s, hs⟩ ↦ hcomp s hs)

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma isSigmaCompact_iUnion [Countable ι] (s : ι → Set X)
    (hcomp : ∀ i, IsSigmaCompact (s i)) : IsSigmaCompact (⋃ i, s i) := by
  -- Choose a decomposition s_i = ⋃ K_i,j for each i.
  choose K hcomp hcov using fun i ↦ hcomp i
  -- Then, we have a countable union of countable unions of compact sets, i.e. countably many.
  have := calc
    ⋃ i, s i
    _ = ⋃ i, ⋃ n, (K i n) := by simp_rw [hcov]
    _ = ⋃ (i) (n : ℕ), (K.uncurry ⟨i, n⟩) := by rw [Function.uncurry_def]
    _ = ⋃ x, K.uncurry x := by rw [← iUnion_prod']
  rw [this]
  exact isSigmaCompact_iUnion_of_isCompact K.uncurry fun x ↦ (hcomp x.1 x.2)

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma isSigmaCompact_sUnion (S : Set (Set X)) (hc : Set.Countable S)
    (hcomp : ∀ s : S, IsSigmaCompact s (X := X)) : IsSigmaCompact (⋃₀ S) := by
  have : Countable S := countable_coe_iff.mpr hc
  apply sUnion_eq_iUnion.symm ▸ isSigmaCompact_iUnion _ hcomp

/-- Countable unions of σ-compact sets are σ-compact. -/
lemma isSigmaCompact_biUnion {s : Set ι} {S : ι → Set X} (hc : Set.Countable s)
    (hcomp : ∀ (i : ι), i ∈ s → IsSigmaCompact (S i)) :
    IsSigmaCompact (⋃ (i : ι) (_ : i ∈ s), S i) := by
  have : Countable ↑s := countable_coe_iff.mpr hc
  rw [biUnion_eq_iUnion]
  exact isSigmaCompact_iUnion _ (fun ⟨i', hi'⟩ ↦ hcomp i' hi')

/-- A closed subset of a σ-compact set is σ-compact. -/
lemma IsSigmaCompact.of_isClosed_subset {s t : Set X} (ht : IsSigmaCompact t)
    (hs : IsClosed s) (h : s ⊆ t) : IsSigmaCompact s := by
  rcases ht with ⟨K, hcompact, hcov⟩
  refine ⟨(fun n ↦ s ∩ (K n)), fun n ↦ (hcompact n).inter_left hs, ?_⟩
  rw [← inter_iUnion, hcov]
  exact inter_eq_left.mpr h

/-- If `s` is σ-compact and `f` is continuous on `s`, `f(s)` is σ-compact. -/
lemma IsSigmaCompact.image_of_continuousOn {f : X → Y} {s : Set X} (hs : IsSigmaCompact s)
    (hf : ContinuousOn f s) : IsSigmaCompact (f '' s) := by
  rcases hs with ⟨K, hcompact, hcov⟩
  refine ⟨fun n ↦ f '' K n, ?_, hcov.symm ▸ image_iUnion.symm⟩
  exact fun n ↦ (hcompact n).image_of_continuousOn (hf.mono (hcov.symm ▸ subset_iUnion K n))

/-- If `s` is σ-compact and `f` continuous, `f(s)` is σ-compact. -/
lemma IsSigmaCompact.image {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsSigmaCompact s) :
    IsSigmaCompact (f '' s) := hs.image_of_continuousOn hf.continuousOn

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is σ-compact
  if and only `s` is σ-compact. -/
lemma Topology.IsInducing.isSigmaCompact_iff {f : X → Y} {s : Set X}
    (hf : IsInducing f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s) := by
  constructor
  · exact fun h ↦ h.image hf.continuous
  · rintro ⟨L, hcomp, hcov⟩
    -- Suppose f(s) is σ-compact; we want to show s is σ-compact.
    -- Write f(s) as a union of compact sets L n, so s = ⋃ K n with K n := f⁻¹(L n) ∩ s.
    -- Since f is inducing, each K n is compact iff L n is.
    refine ⟨fun n ↦ f ⁻¹' (L n) ∩ s, ?_, ?_⟩
    · intro n
      have : f '' (f ⁻¹' (L n) ∩ s) = L n := by
        rw [image_preimage_inter, inter_eq_left.mpr]
        exact (subset_iUnion _ n).trans hcov.le
      apply hf.isCompact_iff.mpr (this.symm ▸ (hcomp n))
    · calc ⋃ n, f ⁻¹' L n ∩ s
        _ = f ⁻¹' (⋃ n, L n) ∩ s  := by rw [preimage_iUnion, iUnion_inter]
        _ = f ⁻¹' (f '' s) ∩ s := by rw [hcov]
        _ = s := inter_eq_right.mpr (subset_preimage_image _ _)

/-- If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is σ-compact
if and only `s` is σ-compact. -/
lemma Topology.IsEmbedding.isSigmaCompact_iff {f : X → Y} {s : Set X}
    (hf : IsEmbedding f) : IsSigmaCompact s ↔ IsSigmaCompact (f '' s) :=
  hf.isInducing.isSigmaCompact_iff

/-- Sets of subtype are σ-compact iff the image under a coercion is. -/
lemma Subtype.isSigmaCompact_iff {p : X → Prop} {s : Set { a // p a }} :
    IsSigmaCompact s ↔ IsSigmaCompact ((↑) '' s : Set X) :=
  IsEmbedding.subtypeVal.isSigmaCompact_iff

/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `compactCovering`. -/
class SigmaCompactSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- In a σ-compact space, `Set.univ` is a σ-compact set. -/
  isSigmaCompact_univ : IsSigmaCompact (univ : Set X)

/-- A topological space is σ-compact iff `univ` is σ-compact. -/
lemma isSigmaCompact_univ_iff : IsSigmaCompact (univ : Set X) ↔ SigmaCompactSpace X :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.1⟩

/-- In a σ-compact space, `univ` is σ-compact. -/
lemma isSigmaCompact_univ [h : SigmaCompactSpace X] : IsSigmaCompact (univ : Set X) :=
  isSigmaCompact_univ_iff.mpr h

/-- A topological space is σ-compact iff there exists a countable collection of compact
subspaces that cover the entire space. -/
lemma SigmaCompactSpace_iff_exists_compact_covering :
    SigmaCompactSpace X ↔ ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ := by
  rw [← isSigmaCompact_univ_iff, IsSigmaCompact]

lemma SigmaCompactSpace.exists_compact_covering [h : SigmaCompactSpace X] :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ :=
  SigmaCompactSpace_iff_exists_compact_covering.mp h

/-- If `X` is σ-compact, `im f` is σ-compact. -/
lemma isSigmaCompact_range {f : X → Y} (hf : Continuous f) [SigmaCompactSpace X] :
    IsSigmaCompact (range f) :=
  image_univ ▸ isSigmaCompact_univ.image hf

/-- A subset `s` is σ-compact iff `s` (with the subspace topology) is a σ-compact space. -/
lemma isSigmaCompact_iff_isSigmaCompact_univ {s : Set X} :
    IsSigmaCompact s ↔ IsSigmaCompact (univ : Set s) := by
  rw [Subtype.isSigmaCompact_iff, image_univ, Subtype.range_coe]

lemma isSigmaCompact_iff_sigmaCompactSpace {s : Set X} :
    IsSigmaCompact s ↔ SigmaCompactSpace s :=
  isSigmaCompact_iff_isSigmaCompact_univ.trans isSigmaCompact_univ_iff

-- see Note [lower instance priority]
instance (priority := 200) CompactSpace.sigmaCompact [CompactSpace X] : SigmaCompactSpace X :=
  ⟨⟨fun _ ↦ univ, fun _ ↦ isCompact_univ, iUnion_const _⟩⟩

theorem SigmaCompactSpace.of_countable (S : Set (Set X)) (Hc : S.Countable)
    (Hcomp : ∀ s ∈ S, IsCompact s) (HU : ⋃₀ S = univ) : SigmaCompactSpace X :=
  ⟨(exists_seq_cover_iff_countable ⟨_, isCompact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩

-- see Note [lower instance priority]
instance (priority := 100) sigmaCompactSpace_of_locallyCompact_secondCountable
    [LocallyCompactSpace X] [SecondCountableTopology X] : SigmaCompactSpace X := by
  choose K hKc hxK using fun x : X ↦ exists_compact_mem_nhds x
  rcases countable_cover_nhds hxK with ⟨s, hsc, hsU⟩
  refine SigmaCompactSpace.of_countable _ (hsc.image K) (forall_mem_image.2 fun x _ ↦ hKc x) ?_
  rwa [sUnion_image]

section

variable (X)
variable [SigmaCompactSpace X]

open SigmaCompactSpace

/-- A choice of compact covering for a `σ`-compact space, chosen to be monotone. -/
def compactCovering : ℕ → Set X :=
  Accumulate exists_compact_covering.choose

theorem isCompact_compactCovering (n : ℕ) : IsCompact (compactCovering X n) :=
  isCompact_accumulate (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).1 n

theorem iUnion_compactCovering : ⋃ n, compactCovering X n = univ := by
  rw [compactCovering, iUnion_accumulate]
  exact (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).2

theorem iUnion_closure_compactCovering : ⋃ n, closure (compactCovering X n) = univ :=
  eq_top_mono (iUnion_mono fun _ ↦ subset_closure) (iUnion_compactCovering X)

@[mono, gcongr]
theorem compactCovering_subset ⦃m n : ℕ⦄ (h : m ≤ n) : compactCovering X m ⊆ compactCovering X n :=
  monotone_accumulate h

variable {X}

theorem exists_mem_compactCovering (x : X) : ∃ n, x ∈ compactCovering X n :=
  iUnion_eq_univ_iff.mp (iUnion_compactCovering X) x

instance [SigmaCompactSpace Y] : SigmaCompactSpace (X × Y) :=
  ⟨⟨fun n ↦ compactCovering X n ×ˢ compactCovering Y n, fun _ ↦
      (isCompact_compactCovering _ _).prod (isCompact_compactCovering _ _), by
      simp only [iUnion_prod_of_monotone (compactCovering_subset X) (compactCovering_subset Y),
        iUnion_compactCovering, univ_prod_univ]⟩⟩

instance [Finite ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, SigmaCompactSpace (X i)] :
    SigmaCompactSpace (∀ i, X i) := by
  refine ⟨⟨fun n ↦ Set.pi univ fun i ↦ compactCovering (X i) n,
    fun n ↦ isCompact_univ_pi fun i ↦ isCompact_compactCovering (X i) _, ?_⟩⟩
  rw [iUnion_univ_pi_of_monotone]
  · simp only [iUnion_compactCovering, pi_univ]
  · exact fun i ↦ compactCovering_subset (X i)

instance [SigmaCompactSpace Y] : SigmaCompactSpace (X ⊕ Y) :=
  ⟨⟨fun n ↦ Sum.inl '' compactCovering X n ∪ Sum.inr '' compactCovering Y n, fun n ↦
      ((isCompact_compactCovering X n).image continuous_inl).union
        ((isCompact_compactCovering Y n).image continuous_inr),
      by simp only [iUnion_union_distrib, ← image_iUnion, iUnion_compactCovering, image_univ,
        range_inl_union_range_inr]⟩⟩

instance [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, SigmaCompactSpace (X i)] : SigmaCompactSpace (Σ i, X i) := by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · rcases exists_surjective_nat ι with ⟨f, hf⟩
    refine ⟨⟨fun n ↦ ⋃ k ≤ n, Sigma.mk (f k) '' compactCovering (X (f k)) n, fun n ↦ ?_, ?_⟩⟩
    · refine (finite_le_nat _).isCompact_biUnion fun k _ ↦ ?_
      exact (isCompact_compactCovering _ _).image continuous_sigmaMk
    · simp only [iUnion_eq_univ_iff, Sigma.forall, mem_iUnion, hf.forall]
      intro k y
      rcases exists_mem_compactCovering y with ⟨n, hn⟩
      refine ⟨max k n, k, le_max_left _ _, mem_image_of_mem _ ?_⟩
      exact compactCovering_subset _ (le_max_right _ _) hn

protected lemma Topology.IsClosedEmbedding.sigmaCompactSpace {e : Y → X}
    (he : IsClosedEmbedding e) : SigmaCompactSpace Y :=
  ⟨⟨fun n ↦ e ⁻¹' compactCovering X n, fun _ ↦
      he.isCompact_preimage (isCompact_compactCovering _ _), by
      rw [← preimage_iUnion, iUnion_compactCovering, preimage_univ]⟩⟩

theorem IsClosed.sigmaCompactSpace {s : Set X} (hs : IsClosed s) : SigmaCompactSpace s :=
  hs.isClosedEmbedding_subtypeVal.sigmaCompactSpace

instance [SigmaCompactSpace Y] : SigmaCompactSpace (ULift.{u} Y) :=
  IsClosedEmbedding.uliftDown.sigmaCompactSpace

/-- If `X` is a `σ`-compact space, then a locally finite family of nonempty sets of `X` can have
only countably many elements, `Set.Countable` version. -/
protected theorem LocallyFinite.countable_univ {f : ι → Set X} (hf : LocallyFinite f)
    (hne : ∀ i, (f i).Nonempty) : (univ : Set ι).Countable := by
  have := fun n ↦ hf.finite_nonempty_inter_compact (isCompact_compactCovering X n)
  refine (countable_iUnion fun n ↦ (this n).countable).mono fun i _ ↦ ?_
  rcases hne i with ⟨x, hx⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering X) x with ⟨n, hn⟩
  exact mem_iUnion.2 ⟨n, x, hx, hn⟩

/-- If `f : ι → Set X` is a locally finite covering of a σ-compact topological space by nonempty
sets, then the index type `ι` is encodable. -/
protected noncomputable def LocallyFinite.encodable {ι : Type*} {f : ι → Set X}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Encodable ι :=
  @Encodable.ofEquiv _ _ (hf.countable_univ hne).toEncodable (Equiv.Set.univ _).symm

/-- In a topological space with sigma compact topology, if `f` is a function that sends each point
`x` of a closed set `s` to a neighborhood of `x` within `s`, then for some countable set `t ⊆ s`,
the neighborhoods `f x`, `x ∈ t`, cover the whole set `s`. -/
theorem countable_cover_nhdsWithin_of_sigmaCompact {f : X → Set X} {s : Set X} (hs : IsClosed s)
    (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) : ∃ t ⊆ s, t.Countable ∧ s ⊆ ⋃ x ∈ t, f x := by
  simp only [nhdsWithin, mem_inf_principal] at hf
  choose t ht hsub using fun n ↦
    ((isCompact_compactCovering X n).inter_right hs).elim_nhds_subcover _ fun x hx ↦ hf x hx.right
  refine
    ⟨⋃ n, (t n : Set X), iUnion_subset fun n x hx ↦ (ht n x hx).2,
      countable_iUnion fun n ↦ (t n).countable_toSet, fun x hx ↦ mem_iUnion₂.2 ?_⟩
  rcases exists_mem_compactCovering x with ⟨n, hn⟩
  rcases mem_iUnion₂.1 (hsub n ⟨hn, hx⟩) with ⟨y, hyt : y ∈ t n, hyf : x ∈ s → x ∈ f y⟩
  exact ⟨y, mem_iUnion.2 ⟨n, hyt⟩, hyf hx⟩

/-- In a topological space with sigma compact topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
theorem countable_cover_nhds_of_sigmaCompact {f : X → Set X} (hf : ∀ x, f x ∈ 𝓝 x) :
    ∃ s : Set X, s.Countable ∧ ⋃ x ∈ s, f x = univ := by
  simp only [← nhdsWithin_univ] at hf
  rcases countable_cover_nhdsWithin_of_sigmaCompact isClosed_univ fun x _ ↦ hf x with
    ⟨s, -, hsc, hsU⟩
  exact ⟨s, hsc, univ_subset_iff.1 hsU⟩
end

/-- An [exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets) of a
topological space is a sequence of compact sets `K n` such that `K n ⊆ interior (K (n + 1))` and
`⋃ n, K n = univ`.

If `X` is a locally compact sigma compact space, then `CompactExhaustion.choice X` provides
a choice of an exhaustion by compact sets. This choice is also available as
`(default : CompactExhaustion X)`. -/
structure CompactExhaustion (X : Type*) [TopologicalSpace X] where
  /-- The sequence of compact sets that form a compact exhaustion. -/
  toFun : ℕ → Set X
  /-- The sets in the compact exhaustion are in fact compact. -/
  isCompact' : ∀ n, IsCompact (toFun n)
  /-- The sets in the compact exhaustion form a sequence:
  each set is contained in the interior of the next. -/
  subset_interior_succ' : ∀ n, toFun n ⊆ interior (toFun (n + 1))
  /-- The union of all sets in a compact exhaustion equals the entire space. -/
  iUnion_eq' : ⋃ n, toFun n = univ

namespace CompactExhaustion

instance : FunLike (CompactExhaustion X) ℕ (Set X) where
  coe := toFun
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

instance : RelHomClass (CompactExhaustion X) LE.le HasSubset.Subset where
  map_rel f _ _ h := monotone_nat_of_le_succ
    (fun n ↦ (f.subset_interior_succ' n).trans interior_subset) h

variable (K : CompactExhaustion X)

@[simp]
theorem toFun_eq_coe : K.toFun = K := rfl

protected theorem isCompact (n : ℕ) : IsCompact (K n) :=
  K.isCompact' n

theorem subset_interior_succ (n : ℕ) : K n ⊆ interior (K (n + 1)) :=
  K.subset_interior_succ' n

@[mono]
protected theorem subset ⦃m n : ℕ⦄ (h : m ≤ n) : K m ⊆ K n :=
  OrderHomClass.mono K h

theorem subset_succ (n : ℕ) : K n ⊆ K (n + 1) := K.subset n.le_succ

theorem subset_interior ⦃m n : ℕ⦄ (h : m < n) : K m ⊆ interior (K n) :=
  Subset.trans (K.subset_interior_succ m) <| interior_mono <| K.subset h

theorem iUnion_eq : ⋃ n, K n = univ :=
  K.iUnion_eq'

theorem exists_mem (x : X) : ∃ n, x ∈ K n :=
  iUnion_eq_univ_iff.1 K.iUnion_eq x

theorem exists_mem_nhds (x : X) : ∃ n, K n ∈ 𝓝 x := by
  rcases K.exists_mem x with ⟨n, hn⟩
  exact ⟨n + 1, mem_interior_iff_mem_nhds.mp <| K.subset_interior_succ n hn⟩

/-- A compact exhaustion eventually covers any compact set. -/
theorem exists_superset_of_isCompact {s : Set X} (hs : IsCompact s) : ∃ n, s ⊆ K n := by
  suffices ∃ n, s ⊆ interior (K n) from this.imp fun _ ↦ (Subset.trans · interior_subset)
  refine hs.elim_directed_cover (interior ∘ K) (fun _ ↦ isOpen_interior) ?_ ?_
  · intro x _
    rcases K.exists_mem x with ⟨k, hk⟩
    exact mem_iUnion.2 ⟨k + 1, K.subset_interior_succ _ hk⟩
  · exact Monotone.directed_le fun _ _ h ↦ interior_mono <| K.subset h

open Classical in
/-- The minimal `n` such that `x ∈ K n`. -/
protected noncomputable def find (x : X) : ℕ :=
  Nat.find (K.exists_mem x)

theorem mem_find (x : X) : x ∈ K (K.find x) := by
  classical
  exact Nat.find_spec (K.exists_mem x)

theorem mem_iff_find_le {x : X} {n : ℕ} : x ∈ K n ↔ K.find x ≤ n := by
  classical
  exact ⟨fun h ↦ Nat.find_min' (K.exists_mem x) h, fun h ↦ K.subset h <| K.mem_find x⟩

/-- Prepend the empty set to a compact exhaustion `K n`. -/
def shiftr : CompactExhaustion X where
  toFun n := Nat.casesOn n ∅ K
  isCompact' n := Nat.casesOn n isCompact_empty K.isCompact
  subset_interior_succ' n := Nat.casesOn n (empty_subset _) K.subset_interior_succ
  iUnion_eq' := iUnion_eq_univ_iff.2 fun x ↦ ⟨K.find x + 1, K.mem_find x⟩

@[simp]
theorem find_shiftr (x : X) : K.shiftr.find x = K.find x + 1 := by
  classical
  exact Nat.find_comp_succ _ _ (notMem_empty _)

theorem mem_diff_shiftr_find (x : X) : x ∈ K.shiftr (K.find x + 1) \ K.shiftr (K.find x) :=
  ⟨K.mem_find _,
    mt K.shiftr.mem_iff_find_le.1 <| by simp only [find_shiftr, not_le, Nat.lt_succ_self]⟩

/-- A choice of an
[exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets)
of a weakly locally compact σ-compact space. -/
noncomputable def choice (X : Type*) [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] : CompactExhaustion X := by
  apply Classical.choice
  let K : ℕ → { s : Set X // IsCompact s } := fun n ↦
    Nat.recOn n ⟨∅, isCompact_empty⟩ fun n s ↦
      ⟨(exists_compact_superset s.2).choose ∪ compactCovering X n,
        (exists_compact_superset s.2).choose_spec.1.union (isCompact_compactCovering _ _)⟩
  refine ⟨⟨fun n ↦ (K n).1, fun n ↦ (K n).2, fun n ↦ ?_, ?_⟩⟩
  · exact Subset.trans (exists_compact_superset (K n).2).choose_spec.2
      (interior_mono subset_union_left)
  · refine univ_subset_iff.1 (iUnion_compactCovering X ▸ ?_)
    exact iUnion_mono' fun n ↦ ⟨n + 1, subset_union_right⟩

noncomputable instance [SigmaCompactSpace X] [WeaklyLocallyCompactSpace X] :
    Inhabited (CompactExhaustion X) :=
  ⟨CompactExhaustion.choice X⟩

end CompactExhaustion
