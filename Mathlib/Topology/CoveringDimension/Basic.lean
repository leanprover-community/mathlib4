/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.OpenCover

/-!
# Lebesgue covering dimension

This file defines the Lebesgue covering dimension of a topological space in terms of open
refinements of bounded order. The dimension takes values in `WithBot ℕ∞`, with `⊥` representing
the empty space and `⊤` representing the absence of a finite bound.
We also prove invariance under homeomorphisms and monotonicity for closed subspaces.

## Main definitions

* `Set.HasOrderLE`: every point belongs to at most a prescribed number of members.
* `HasCoveringDimensionLE`: every `IsOpenCover` has an open refinement of order at most `n + 1`.
* `HasCoveringDimensionLT`: strict finite covering-dimension bounds, including the empty case.
* `coveringDimension`: the Lebesgue covering dimension, valued in `WithBot ℕ∞`.

## References

* James R. Munkres, *Topology*.
-/

public section

open Set TopologicalSpace

universe u v

/-! ### Order of covers -/

namespace Set

/-- A collection has order at most `n` when every point belongs to at most `n` members. -/
def HasOrderLE {X : Type u} (𝒜 : Set (Set X)) (n : ℕ) : Prop :=
  ∀ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} ≤ n

/-- The pointwise cardinality characterization of `Set.HasOrderLE`. -/
theorem hasOrderLE_iff {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} :
    𝒜.HasOrderLE n ↔ ∀ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} ≤ n := by
  rfl

/-- A family has order at most one exactly when its members are pairwise disjoint. -/
theorem hasOrderLE_one_iff {X : Type u} {𝒜 : Set (Set X)} :
    𝒜.HasOrderLE 1 ↔ 𝒜.PairwiseDisjoint id := by
  simp only [HasOrderLE, Nat.cast_one, encard_le_one_iff, mem_ofPred_eq,
    PairwiseDisjoint, Set.Pairwise, Function.onFun, id_eq, disjoint_left]
  grind

namespace HasOrderLE

/-- An upper bound on the order remains valid after increasing the bound. -/
theorem mono {X : Type u} {𝒜 : Set (Set X)} {n k : ℕ}
    (h : 𝒜.HasOrderLE n) (hnk : n ≤ k) : 𝒜.HasOrderLE k :=
  fun x ↦ (h x).trans (by simpa using hnk)

/-- Passing to a subfamily does not increase its order. -/
theorem of_subset {X : Type u} {𝒜 ℬ : Set (Set X)} {n : ℕ}
    (h : 𝒜.HasOrderLE n) (hℬ : ℬ ⊆ 𝒜) : ℬ.HasOrderLE n :=
  fun x ↦ (Set.encard_mono (Set.inter_subset_inter_left _ hℬ)).trans (h x)

/-- The order of a union is bounded by the sum of the orders. -/
theorem union {X : Type u} {𝒜 ℬ : Set (Set X)} {n m : ℕ}
    (h𝒜 : 𝒜.HasOrderLE n) (hℬ : ℬ.HasOrderLE m) : (𝒜 ∪ ℬ).HasOrderLE (n + m) := by
  intro x
  simp only [Set.mem_union, Set.sep_union, Nat.cast_add]
  exact (Set.encard_union_le _ _).trans (add_le_add (h𝒜 x) (hℬ x))

/-- Taking preimages of every member of a family does not increase its order. -/
theorem preimage {Y : Type u} {Z : Type v} {𝒞 : Set (Set Z)} {n : ℕ}
    (h𝒞 : 𝒞.HasOrderLE n) (f : Y → Z) :
    ((fun V : Set Z ↦ f ⁻¹' V) '' 𝒞).HasOrderLE n := by
  intro y
  change (((fun V : Set Z ↦ f ⁻¹' V) '' 𝒞) ∩ {B | y ∈ B}).encard ≤ n
  rw [← Set.image_inter_preimage]
  exact (Set.encard_image_le _ _).trans (h𝒞 (f y))

end HasOrderLE

/-- A collection has order `n` when the upper bound `n` is attained at some point. -/
def HasOrder {X : Type u} (𝒜 : Set (Set X)) (n : ℕ) : Prop :=
  (∃ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} = n) ∧ 𝒜.HasOrderLE n

/-- The attained pointwise cardinality characterization of `Set.HasOrder`. -/
theorem hasOrder_iff {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} :
    𝒜.HasOrder n ↔
      (∃ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} = n) ∧
        ∀ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} ≤ n := by
  rfl

namespace HasOrder

/-- Exact order gives the corresponding upper bound. -/
theorem le {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} (h : 𝒜.HasOrder n) :
    𝒜.HasOrderLE n := h.2

/-- Exact order is attained at some point. -/
theorem exists_eq {X : Type u} {𝒜 : Set (Set X)} {n : ℕ} (h : 𝒜.HasOrder n) :
    ∃ x : X, Set.encard {U ∈ 𝒜 | x ∈ U} = n := h.1

end HasOrder

end Set

/-! ### Covering dimension -/

/-- A space has covering dimension at most `n` when every open cover has an open refining cover
of point multiplicity at most `n + 1`.

Both covers are indexed families of `Opens X`, with the covering condition expressed using
`IsOpenCover` and refinement using `IsCofinalFor`. Multiplicity is measured on the range of the
refining family, so repeated indices representing the same open set are counted only once.
It suffices to use index types in the same universe as `X`, since any family can be reindexed by
its range. -/
abbrev HasCoveringDimensionLE (X : Type u) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (ι : Type u) (U : ι → Opens X), IsOpenCover U →
    ∃ (κ : Type u) (V : κ → Opens X), IsOpenCover V ∧
      IsCofinalFor (Set.range V) (Set.range U) ∧
        (Set.range fun j ↦ (V j : Set X)).HasOrderLE (n + 1)

/-- A space has covering dimension less than `0` exactly when it is empty, and has covering
dimension less than `n + 1` exactly when it has covering dimension at most `n`. -/
abbrev HasCoveringDimensionLT (X : Type u) [TopologicalSpace X] : ℕ → Prop
  | 0 => IsEmpty X
  | n + 1 => HasCoveringDimensionLE X n

/-- A space has finite covering dimension when it has some finite covering-dimension bound. -/
abbrev FiniteCoveringDimension (X : Type u) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, HasCoveringDimensionLE X n

/-- The covering dimension of a space, with `⊥` for dimension `-1` and `⊤` when no finite
covering-dimension bound exists. -/
noncomputable def coveringDimension (X : Type u) [TopologicalSpace X] : WithBot ℕ∞ :=
  sInf {d : WithBot ℕ∞ | ∀ n : ℕ, d < n → HasCoveringDimensionLT X n}

/-- Covering dimension expressed as the infimum of its strict natural-number bounds. -/
theorem coveringDimension_eq_sInf (X : Type u) [TopologicalSpace X] :
    coveringDimension X =
      sInf {d : WithBot ℕ∞ | ∀ n : ℕ, d < n → HasCoveringDimensionLT X n} := by
  rfl

namespace CoveringDimension

/-- Notation for the covering dimension of a space. -/
scoped notation "dim " X:arg => coveringDimension X

end CoveringDimension

/-- The characterization of `HasCoveringDimensionLE` using collections of sets. -/
theorem hasCoveringDimensionLE_iff (X : Type u) [TopologicalSpace X] (n : ℕ) :
    HasCoveringDimensionLE X n ↔
      ∀ 𝒜 : Set (Set X),
        (∀ U ∈ 𝒜, IsOpen U) →
        ⋃₀ 𝒜 = Set.univ →
        ∃ ℬ : Set (Set X),
          IsCofinalFor ℬ 𝒜 ∧ (∀ U ∈ ℬ, IsOpen U) ∧
            ⋃₀ ℬ = Set.univ ∧ ℬ.HasOrderLE (n + 1) := by
  constructor
  · intro h 𝒜 hopen hcover
    let U : 𝒜 → Opens X := fun A ↦ ⟨A.1, hopen A.1 A.2⟩
    have hU : IsOpenCover U :=
      IsOpenCover.of_sets _ (by simpa only [← Set.sUnion_eq_iUnion] using hcover)
    obtain ⟨κ, V, hV, hVU, horder⟩ := h _ U hU
    refine ⟨Set.range (fun j ↦ (V j : Set X)), ?_, ?_, ?_, horder⟩
    · rintro _ ⟨j, rfl⟩
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hVU (Set.mem_range_self j)
      exact ⟨i.1, i.2, hi⟩
    · rintro _ ⟨j, rfl⟩
      exact (V j).isOpen
    · simpa only [Set.sUnion_range] using hV.iSup_set_eq_univ
  · intro h ι U hU
    obtain ⟨ℬ, hrefines, hopen, hcover, horder⟩ := h (Set.range fun i ↦ (U i : Set X))
      (by rintro _ ⟨i, rfl⟩; exact (U i).isOpen)
      (by simpa only [Set.sUnion_range] using hU.iSup_set_eq_univ)
    let V : ℬ → Opens X := fun B ↦ ⟨B.1, hopen B.1 B.2⟩
    refine ⟨ℬ, V, ?_, ?_, ?_⟩
    · exact IsOpenCover.of_sets _
        (by simpa only [← Set.sUnion_eq_iUnion] using hcover)
    · rintro _ ⟨j, rfl⟩
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hrefines j.2
      exact ⟨U i, Set.mem_range_self i, hi⟩
    · change (Set.range (Subtype.val : ℬ → Set X)).HasOrderLE (n + 1)
      simpa only [Subtype.range_val] using horder

namespace HasCoveringDimensionLE

/-- A covering-dimension bound applies to open covers indexed in any universe. -/
theorem exists_refinement {X : Type u} [TopologicalSpace X] {n : ℕ}
    (h : HasCoveringDimensionLE X n) {ι : Type v} (U : ι → Opens X)
    (hU : IsOpenCover U) :
    ∃ (κ : Type u) (V : κ → Opens X), IsOpenCover V ∧
      IsCofinalFor (Set.range V) (Set.range U) ∧
        (Set.range fun j ↦ (V j : Set X)).HasOrderLE (n + 1) := by
  have hU' : IsOpenCover (fun W : Set.range U ↦ W.1) :=
    IsOpenCover.mk ((iSup_range' id U).trans hU.iSup_eq_top)
  obtain ⟨κ, V, hV, hVU, horder⟩ := h _ _ hU'
  exact ⟨κ, V, hV, by simpa only [Subtype.range_val] using hVU, horder⟩

/-- A covering-dimension bound remains valid after increasing the bound. -/
theorem mono {X : Type u} [TopologicalSpace X] {n m : ℕ}
    (h : HasCoveringDimensionLE X n) (hnm : n ≤ m) : HasCoveringDimensionLE X m := by
  intro ι U hU
  obtain ⟨κ, V, hV, hVU, horder⟩ := h _ U hU
  exact ⟨κ, V, hV, hVU, horder.mono (Nat.add_le_add_right hnm 1)⟩

end HasCoveringDimensionLE

@[simp]
theorem hasCoveringDimensionLT_zero_iff (X : Type u) [TopologicalSpace X] :
    HasCoveringDimensionLT X 0 ↔ IsEmpty X := by
  rfl

lemma hasCoveringDimensionLT_of_bound {X : Type u} [TopologicalSpace X] {n k : ℕ}
    (h : HasCoveringDimensionLE X n) (hnk : n < k) : HasCoveringDimensionLT X k := by
  cases k with
  | zero => exact (Nat.not_lt_zero n hnk).elim
  | succ k => exact h.mono (Nat.lt_succ_iff.mp hnk)

lemma hasCoveringDimensionLE_of_isEmpty {X : Type u} [TopologicalSpace X]
    (hX : IsEmpty X) (n : ℕ) : HasCoveringDimensionLE X n := by
  intro ι U hU
  exact ⟨ι, U, hU, fun _ h ↦ ⟨_, h, le_rfl⟩, fun x ↦ isEmptyElim x⟩

/-- The existence-of-a-bound characterization of finite covering dimension. -/
theorem finiteCoveringDimension_iff (X : Type u) [TopologicalSpace X] :
    FiniteCoveringDimension X ↔ ∃ n : ℕ, HasCoveringDimensionLE X n := by
  rfl

open scoped CoveringDimension

/-- The numerical covering dimension is at most `n` exactly when `n` is a covering-dimension
bound. -/
theorem coveringDimension_le_iff (X : Type u) [TopologicalSpace X] (n : ℕ) :
    dim X ≤ (n : WithBot ℕ∞) ↔ HasCoveringDimensionLE X n := by
  constructor
  · intro hdim
    have hdim_succ : dim X < (n + 1 : ℕ) := ENat.WithBot.lt_add_one_iff.mpr hdim
    rw [coveringDimension] at hdim_succ
    obtain ⟨d, hd_bounds, hd_succ⟩ := sInf_lt_iff.mp hdim_succ
    exact hd_bounds (n + 1) hd_succ
  · intro hbound
    rw [coveringDimension]
    apply sInf_le
    intro k hnk
    exact hasCoveringDimensionLT_of_bound hbound (by exact_mod_cast hnk)

/-- The covering dimension has value `-1` exactly for empty spaces. -/
@[simp]
theorem coveringDimension_eq_bot_iff (X : Type u) [TopologicalSpace X] :
    dim X = ⊥ ↔ IsEmpty X := by
  constructor
  · intro hdim
    have hdim_zero : dim X < (0 : WithBot ℕ∞) := by
      rw [hdim]
      exact WithBot.bot_lt_coe 0
    rw [coveringDimension] at hdim_zero
    obtain ⟨d, hd_bounds, hd_zero⟩ := sInf_lt_iff.mp hdim_zero
    exact hd_bounds 0 hd_zero
  · intro hX
    apply bot_unique
    apply sInf_le
    intro n _
    cases n with
    | zero => exact hX
    | succ n => exact hasCoveringDimensionLE_of_isEmpty hX n

/-- Finite covering dimension is equivalent to the numerical covering dimension being different
from `⊤`. -/
theorem finiteCoveringDimension_iff_coveringDimension_ne_top
    (X : Type u) [TopologicalSpace X] : FiniteCoveringDimension X ↔ dim X ≠ ⊤ := by
  constructor
  · rintro ⟨n, hn⟩
    exact ne_top_of_le_ne_top (fun h ↦ ENat.natCast_ne_top n (WithBot.coe_eq_top.mp h))
      ((coveringDimension_le_iff X n).mpr hn)
  · intro hdim
    obtain ⟨n, hn⟩ := not_forall.mp (ENat.WithBot.eq_top_iff_forall_ge.not.mp hdim)
    exact ⟨n, (coveringDimension_le_iff X n).mp (le_of_not_ge hn)⟩

/-! ### Invariance under homeomorphisms -/

/-- A covering-dimension bound is transported along a homeomorphism. -/
theorem Homeomorph.hasCoveringDimensionLE_of
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) {n : ℕ} (h : HasCoveringDimensionLE A n) :
    HasCoveringDimensionLE B n := by
  rw [hasCoveringDimensionLE_iff] at h ⊢
  intro ℰ hℰopen hℰcover
  let ℰ' : Set (Set A) := (fun U : Set B ↦ e ⁻¹' U) '' ℰ
  have hℰ'open : ∀ U ∈ ℰ', IsOpen U := by
    rintro U ⟨V, hV, rfl⟩
    exact (hℰopen V hV).preimage e.continuous
  have hℰ'cover : ⋃₀ ℰ' = (_root_.Set.univ : Set A) := by
    simp only [ℰ', Set.sUnion_image, ← Set.preimage_sUnion, hℰcover,
      Set.preimage_univ]
  obtain ⟨𝒯, h𝒯refines, h𝒯open, h𝒯cover, h𝒯order⟩ := h ℰ' hℰ'open hℰ'cover
  let 𝒯' : Set (Set B) := (fun U : Set A ↦ e '' U) '' 𝒯
  refine ⟨𝒯', ?_, ?_, ?_, ?_⟩
  · rintro V ⟨U, hU, rfl⟩
    obtain ⟨W, hW, hUW⟩ := h𝒯refines hU
    obtain ⟨Z, hZ, rfl⟩ := hW
    exact ⟨Z, hZ, Set.image_subset_iff.mpr hUW⟩
  · rintro V ⟨U, hU, rfl⟩
    exact e.isOpen_image.mpr (h𝒯open U hU)
  · simp only [𝒯', ← Set.image_sUnion, h𝒯cover, Set.image_univ,
      e.surjective.range_eq]
  · simpa only [𝒯', e.image_eq_preimage_symm] using h𝒯order.preimage e.symm

/-- Covering-dimension bounds are preserved by homeomorphisms. -/
protected theorem Homeomorph.hasCoveringDimensionLE
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (n : ℕ) : HasCoveringDimensionLE A n ↔ HasCoveringDimensionLE B n :=
  ⟨e.hasCoveringDimensionLE_of, e.symm.hasCoveringDimensionLE_of⟩

/-- Strict covering-dimension bounds are preserved by homeomorphisms. -/
protected theorem Homeomorph.hasCoveringDimensionLT
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (n : ℕ) : HasCoveringDimensionLT A n ↔ HasCoveringDimensionLT B n := by
  cases n with
  | zero => exact ⟨fun h ↦ Function.isEmpty e.symm, fun h ↦ Function.isEmpty e⟩
  | succ n => exact e.hasCoveringDimensionLE n

/-- Covering dimension is preserved by homeomorphisms. -/
protected theorem Homeomorph.coveringDimension_congr
    {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) : coveringDimension A = coveringDimension B := by
  unfold coveringDimension
  apply congrArg sInf
  ext d
  exact forall_congr' fun n ↦ forall_congr' fun _ ↦ e.hasCoveringDimensionLT n

/-! ### Closed subspaces -/

namespace HasCoveringDimensionLE

/-- A covering-dimension bound remains valid on a closed subtype. -/
theorem closedSubtype {X : Type u} [TopologicalSpace X] {Y : Set X} {n : ℕ}
    (hX : HasCoveringDimensionLE X n) (hY : IsClosed Y) :
    HasCoveringDimensionLE Y n := by
  rw [hasCoveringDimensionLE_iff] at hX ⊢
  intro 𝒜 h𝒜open h𝒜cover
  -- Extend the open cover to the ambient space and add the complement of `Y`.
  let 𝒰 : Set (Set X) :=
    {U | IsOpen U ∧ (Subtype.val : Y → X) ⁻¹' U ∈ 𝒜} ∪ {Yᶜ}
  have h𝒰open : ∀ U ∈ 𝒰, IsOpen U := by
    rintro U (⟨hU, _⟩ | rfl)
    · exact hU
    · exact hY.isOpen_compl
  have h𝒰cover : ⋃₀ 𝒰 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ Y
    · obtain ⟨A, hA, hxA⟩ := Set.mem_sUnion.mp
        (h𝒜cover.symm ▸ Set.mem_univ (⟨x, hx⟩ : Y))
      obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp (h𝒜open A hA)
      exact Set.mem_sUnion.mpr ⟨U, Or.inl ⟨hU, hA⟩, hxA⟩
    · exact Set.mem_sUnion.mpr ⟨Yᶜ, Or.inr rfl, hx⟩
  obtain ⟨ℬ, hℬrefines, hℬopen, hℬcover, hℬorder⟩ := hX 𝒰 h𝒰open h𝒰cover
  -- Restrict the refinement to `Y`; discard the empty restriction of its complement.
  refine ⟨((fun U : Set X ↦ (Subtype.val : Y → X) ⁻¹' U) '' ℬ) \ {∅},
    ?_, ?_, ?_, hℬorder.preimage Subtype.val |>.of_subset Set.sdiff_subset⟩
  · rintro V ⟨⟨B, hB, rfl⟩, hne⟩
    obtain ⟨U, hU, hBU⟩ := hℬrefines hB
    rcases hU with ⟨_, hU⟩ | rfl
    · exact ⟨Subtype.val ⁻¹' U, hU, Set.preimage_mono hBU⟩
    · obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
      exact (hBU hy y.2).elim
  · rintro V ⟨⟨B, hB, rfl⟩, _⟩
    exact (hℬopen B hB).preimage continuous_subtype_val
  · apply Set.eq_univ_of_forall
    intro y
    obtain ⟨B, hB, hy⟩ := Set.mem_sUnion.mp (hℬcover.symm ▸ Set.mem_univ y.1)
    exact Set.mem_sUnion.mpr ⟨Subtype.val ⁻¹' B,
      ⟨⟨B, hB, rfl⟩, Set.nonempty_iff_ne_empty.mp ⟨y, hy⟩⟩, hy⟩

end HasCoveringDimensionLE

/-- A closed subspace of a finite-covering-dimensional space has finite covering dimension. -/
theorem IsClosed.finiteCoveringDimension
    {X : Type u} [TopologicalSpace X] {Y : Set X}
    (hY : IsClosed Y) (hX : FiniteCoveringDimension X) :
    FiniteCoveringDimension Y :=
  hX.imp fun _ hn ↦ hn.closedSubtype hY

namespace HasCoveringDimensionLT

/-- A strict covering-dimension bound remains valid on a closed subtype. -/
lemma closedSubtype {X : Type u} [TopologicalSpace X] {Y : Set X} {n : ℕ}
    (hX : HasCoveringDimensionLT X n) (hY : IsClosed Y) :
    HasCoveringDimensionLT Y n := by
  cases n with
  | zero => exact ⟨fun y ↦ hX.false y.1⟩
  | succ n => exact HasCoveringDimensionLE.closedSubtype hX hY

end HasCoveringDimensionLT

/-- The covering dimension of a closed subspace is at most the covering dimension of the
ambient space. -/
theorem IsClosed.coveringDimension_le
    {X : Type u} [TopologicalSpace X] {Y : Set X} (hY : IsClosed Y) :
    _root_.coveringDimension Y ≤ _root_.coveringDimension X := by
  rw [coveringDimension_eq_sInf, coveringDimension_eq_sInf]
  refine sInf_le_sInf ?_
  intro d hd n hdn
  exact (hd n hdn).closedSubtype hY

/-- A closed subspace of a space with a strict
covering-dimension bound inherits that bound. -/
lemma HasCoveringDimensionLT.closedSubset
    {X : Type u} [TopologicalSpace X] {Y Z : Set X} {n : ℕ}
    (h : HasCoveringDimensionLT Z n) (hYZ : Y ⊆ Z) (hY : IsClosed Y) :
    HasCoveringDimensionLT Y n := by
  let e : ((Subtype.val : Z → X) ⁻¹' Y) ≃ₜ Y :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by simpa using hYZ)
  exact (e.hasCoveringDimensionLT n).mp
    (h.closedSubtype (hY.preimage continuous_subtype_val))
