/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Felix Weilacher
-/
import Mathlib.Data.Real.Cardinality
import Mathlib.Topology.Perfect
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

#align_import measure_theory.constructions.polish from "leanprover-community/mathlib"@"9f55d0d4363ae59948c33864cbc52e0b12e0e8ce"

/-!
# The Borel sigma-algebra on Polish spaces

We discuss several results pertaining to the relationship between the topology and the Borel
structure on Polish spaces.

## Main definitions and results

First, we define the class of analytic sets and establish its basic properties.

* `MeasureTheory.AnalyticSet s`: a set in a topological space is analytic if it is the continuous
  image of a Polish space. Equivalently, it is empty, or the image of `ℕ → ℕ`.
* `MeasureTheory.AnalyticSet.image_of_continuous`: a continuous image of an analytic set is
  analytic.
* `MeasurableSet.analyticSet`: in a Polish space, any Borel-measurable set is analytic.

Then, we show Lusin's theorem that two disjoint analytic sets can be separated by Borel sets.

* `MeasurablySeparable s t` states that there exists a measurable set containing `s` and disjoint
  from `t`.
* `AnalyticSet.measurablySeparable` shows that two disjoint analytic sets are separated by a
  Borel set.

We then prove the Lusin-Souslin theorem that a continuous injective image of a Borel subset of
a Polish space is Borel. The proof of this nontrivial result relies on the above results on
analytic sets.

* `MeasurableSet.image_of_continuousOn_injOn` asserts that, if `s` is a Borel measurable set in
  a Polish space, then the image of `s` under a continuous injective map is still Borel measurable.
* `Continuous.measurableEmbedding` states that a continuous injective map on a Polish space
  is a measurable embedding for the Borel sigma-algebra.
* `ContinuousOn.measurableEmbedding` is the same result for a map restricted to a measurable set
  on which it is continuous.
* `Measurable.measurableEmbedding` states that a measurable injective map from a Polish space
  to a second-countable topological space is a measurable embedding.
* `isClopenable_iff_measurableSet`: in a Polish space, a set is clopenable (i.e., it can be made
  open and closed by using a finer Polish topology) if and only if it is Borel-measurable.

We use this to prove several versions of the Borel isomorphism theorem.

* `PolishSpace.measurableEquivOfNotCountable` : Any two uncountable Polish spaces
  are Borel isomorphic.
* `PolishSpace.Equiv.measurableEquiv` : Any two Polish spaces of the same cardinality
  are Borel isomorphic.
-/


open Set Function PolishSpace PiNat TopologicalSpace Metric Filter Topology MeasureTheory

variable {α : Type*} [TopologicalSpace α] {ι : Type*}

namespace MeasureTheory

/-! ### Analytic sets -/


/-- An analytic set is a set which is the continuous image of some Polish space. There are several
equivalent characterizations of this definition. For the definition, we pick one that avoids
universe issues: a set is analytic if and only if it is a continuous image of `ℕ → ℕ` (or if it
is empty). The above more usual characterization is given
in `analyticSet_iff_exists_polishSpace_range`.

Warning: these are analytic sets in the context of descriptive set theory (which is why they are
registered in the namespace `MeasureTheory`). They have nothing to do with analytic sets in the
context of complex analysis. -/
irreducible_def AnalyticSet (s : Set α) : Prop :=
  s = ∅ ∨ ∃ f : (ℕ → ℕ) → α, Continuous f ∧ range f = s
#align measure_theory.analytic_set MeasureTheory.AnalyticSet

theorem analyticSet_empty : AnalyticSet (∅ : Set α) := by
  rw [AnalyticSet]
  -- ⊢ ∅ = ∅ ∨ ∃ f, Continuous f ∧ range f = ∅
  exact Or.inl rfl
  -- 🎉 no goals
#align measure_theory.analytic_set_empty MeasureTheory.analyticSet_empty

theorem analyticSet_range_of_polishSpace {β : Type*} [TopologicalSpace β] [PolishSpace β]
    {f : β → α} (f_cont : Continuous f) : AnalyticSet (range f) := by
  cases isEmpty_or_nonempty β
  -- ⊢ AnalyticSet (range f)
  · rw [range_eq_empty]
    -- ⊢ AnalyticSet ∅
    exact analyticSet_empty
    -- 🎉 no goals
  · rw [AnalyticSet]
    -- ⊢ range f = ∅ ∨ ∃ f_1, Continuous f_1 ∧ range f_1 = range f
    obtain ⟨g, g_cont, hg⟩ : ∃ g : (ℕ → ℕ) → β, Continuous g ∧ Surjective g :=
      exists_nat_nat_continuous_surjective β
    refine' Or.inr ⟨f ∘ g, f_cont.comp g_cont, _⟩
    -- ⊢ range (f ∘ g) = range f
    rw [hg.range_comp]
    -- 🎉 no goals
#align measure_theory.analytic_set_range_of_polish_space MeasureTheory.analyticSet_range_of_polishSpace

/-- The image of an open set under a continuous map is analytic. -/
theorem _root_.IsOpen.analyticSet_image {β : Type*} [TopologicalSpace β] [PolishSpace β]
    {s : Set β} (hs : IsOpen s) {f : β → α} (f_cont : Continuous f) : AnalyticSet (f '' s) := by
  rw [image_eq_range]
  -- ⊢ AnalyticSet (range fun x => f ↑x)
  haveI : PolishSpace s := hs.polishSpace
  -- ⊢ AnalyticSet (range fun x => f ↑x)
  exact analyticSet_range_of_polishSpace (f_cont.comp continuous_subtype_val)
  -- 🎉 no goals
#align is_open.analytic_set_image IsOpen.analyticSet_image

/-- A set is analytic if and only if it is the continuous image of some Polish space. -/
theorem analyticSet_iff_exists_polishSpace_range {s : Set α} :
    AnalyticSet s ↔
      ∃ (β : Type) (h : TopologicalSpace β) (_ : @PolishSpace β h) (f : β → α),
        @Continuous _ _ h _ f ∧ range f = s := by
  constructor
  -- ⊢ AnalyticSet s → ∃ β h x f, Continuous f ∧ range f = s
  · intro h
    -- ⊢ ∃ β h x f, Continuous f ∧ range f = s
    rw [AnalyticSet] at h
    -- ⊢ ∃ β h x f, Continuous f ∧ range f = s
    cases' h with h h
    -- ⊢ ∃ β h x f, Continuous f ∧ range f = s
    · refine' ⟨Empty, inferInstance, inferInstance, Empty.elim, continuous_bot, _⟩
      -- ⊢ range Empty.elim = s
      rw [h]
      -- ⊢ range Empty.elim = ∅
      exact range_eq_empty _
      -- 🎉 no goals
    · exact ⟨ℕ → ℕ, inferInstance, inferInstance, h⟩
      -- 🎉 no goals
  · rintro ⟨β, h, h', f, f_cont, f_range⟩
    -- ⊢ AnalyticSet s
    skip
    -- ⊢ AnalyticSet s
    rw [← f_range]
    -- ⊢ AnalyticSet (range f)
    exact analyticSet_range_of_polishSpace f_cont
    -- 🎉 no goals
#align measure_theory.analytic_set_iff_exists_polish_space_range MeasureTheory.analyticSet_iff_exists_polishSpace_range

/-- The continuous image of an analytic set is analytic -/
theorem AnalyticSet.image_of_continuousOn {β : Type*} [TopologicalSpace β] {s : Set α}
    (hs : AnalyticSet s) {f : α → β} (hf : ContinuousOn f s) : AnalyticSet (f '' s) := by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨γ, γtop, γpolish, g, g_cont, gs⟩
  -- ⊢ AnalyticSet (f '' s)
  skip
  -- ⊢ AnalyticSet (f '' s)
  have : f '' s = range (f ∘ g) := by rw [range_comp, gs]
  -- ⊢ AnalyticSet (f '' s)
  rw [this]
  -- ⊢ AnalyticSet (range (f ∘ g))
  apply analyticSet_range_of_polishSpace
  -- ⊢ Continuous (f ∘ g)
  apply hf.comp_continuous g_cont fun x => _
  -- ⊢ ∀ (x : γ), g x ∈ s
  rw [← gs]
  -- ⊢ ∀ (x : γ), g x ∈ range g
  exact mem_range_self
  -- 🎉 no goals
#align measure_theory.analytic_set.image_of_continuous_on MeasureTheory.AnalyticSet.image_of_continuousOn

theorem AnalyticSet.image_of_continuous {β : Type*} [TopologicalSpace β] {s : Set α}
    (hs : AnalyticSet s) {f : α → β} (hf : Continuous f) : AnalyticSet (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn
#align measure_theory.analytic_set.image_of_continuous MeasureTheory.AnalyticSet.image_of_continuous

/-- A countable intersection of analytic sets is analytic. -/
theorem AnalyticSet.iInter [hι : Nonempty ι] [Countable ι] [T2Space α] {s : ι → Set α}
    (hs : ∀ n, AnalyticSet (s n)) : AnalyticSet (⋂ n, s n) := by
  rcases hι with ⟨i₀⟩
  -- ⊢ AnalyticSet (⋂ (n : ι), s n)
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The product space `γ = Π n, β n` is also Polish, and so is the subset
    `t` of sequences `x n` for which `f n (x n)` is independent of `n`. The set `t` is Polish, and
    the range of `x ↦ f 0 (x 0)` on `t` is exactly `⋂ n, s n`, so this set is analytic. -/
  choose β hβ h'β f f_cont f_range using fun n =>
    analyticSet_iff_exists_polishSpace_range.1 (hs n)
  skip
  -- ⊢ AnalyticSet (⋂ (n : ι), s n)
  let γ := ∀ n, β n
  -- ⊢ AnalyticSet (⋂ (n : ι), s n)
  let t : Set γ := ⋂ n, { x | f n (x n) = f i₀ (x i₀) }
  -- ⊢ AnalyticSet (⋂ (n : ι), s n)
  have t_closed : IsClosed t := by
    apply isClosed_iInter
    intro n
    exact
      isClosed_eq ((f_cont n).comp (continuous_apply n)) ((f_cont i₀).comp (continuous_apply i₀))
  haveI : PolishSpace t := t_closed.polishSpace
  -- ⊢ AnalyticSet (⋂ (n : ι), s n)
  let F : t → α := fun x => f i₀ ((x : γ) i₀)
  -- ⊢ AnalyticSet (⋂ (n : ι), s n)
  have F_cont : Continuous F := (f_cont i₀).comp ((continuous_apply i₀).comp continuous_subtype_val)
  -- ⊢ AnalyticSet (⋂ (n : ι), s n)
  have F_range : range F = ⋂ n : ι, s n := by
    apply Subset.antisymm
    · rintro y ⟨x, rfl⟩
      refine mem_iInter.2 fun n => ?_
      have : f n ((x : γ) n) = F x := (mem_iInter.1 x.2 n : _)
      rw [← this, ← f_range n]
      exact mem_range_self _
    · intro y hy
      have A : ∀ n, ∃ x : β n, f n x = y := by
        intro n
        rw [← mem_range, f_range n]
        exact mem_iInter.1 hy n
      choose x hx using A
      have xt : x ∈ t := by
        refine mem_iInter.2 fun n => ?_
        simp [hx]
      refine' ⟨⟨x, xt⟩, _⟩
      exact hx i₀
  rw [← F_range]
  -- ⊢ AnalyticSet (range F)
  exact analyticSet_range_of_polishSpace F_cont
  -- 🎉 no goals
#align measure_theory.analytic_set.Inter MeasureTheory.AnalyticSet.iInter

/-- A countable union of analytic sets is analytic. -/
theorem AnalyticSet.iUnion [Countable ι] {s : ι → Set α} (hs : ∀ n, AnalyticSet (s n)) :
    AnalyticSet (⋃ n, s n) := by
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The union space `γ = Σ n, β n` is also Polish, and the map `F : γ → α` which
    coincides with `f n` on `β n` sends it to `⋃ n, s n`. -/
  choose β hβ h'β f f_cont f_range using fun n =>
    analyticSet_iff_exists_polishSpace_range.1 (hs n)
  skip
  -- ⊢ AnalyticSet (⋃ (n : ι), s n)
  let γ := Σn, β n
  -- ⊢ AnalyticSet (⋃ (n : ι), s n)
  let F : γ → α := by
    rintro ⟨n, x⟩
    exact f n x
  have F_cont : Continuous F := continuous_sigma f_cont
  -- ⊢ AnalyticSet (⋃ (n : ι), s n)
  have F_range : range F = ⋃ n, s n := by
    rw [range_sigma_eq_iUnion_range]
    apply congr_arg
    ext1 n
    rw [← f_range n]
  rw [← F_range]
  -- ⊢ AnalyticSet (range F)
  exact analyticSet_range_of_polishSpace F_cont
  -- 🎉 no goals
#align measure_theory.analytic_set.Union MeasureTheory.AnalyticSet.iUnion

theorem _root_.IsClosed.analyticSet [PolishSpace α] {s : Set α} (hs : IsClosed s) :
    AnalyticSet s := by
  haveI : PolishSpace s := hs.polishSpace
  -- ⊢ AnalyticSet s
  rw [← @Subtype.range_val α s]
  -- ⊢ AnalyticSet (range Subtype.val)
  exact analyticSet_range_of_polishSpace continuous_subtype_val
  -- 🎉 no goals
#align is_closed.analytic_set IsClosed.analyticSet

/-- Given a Borel-measurable set in a Polish space, there exists a finer Polish topology making
it clopen. This is in fact an equivalence, see `isClopenable_iff_measurableSet`. -/
theorem _root_.MeasurableSet.isClopenable [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    {s : Set α} (hs : MeasurableSet s) : IsClopenable s := by
  revert s
  -- ⊢ ∀ {s : Set α}, MeasurableSet s → IsClopenable s
  apply MeasurableSet.induction_on_open
  · exact fun u hu => hu.isClopenable
    -- 🎉 no goals
  · exact fun u _ h'u => h'u.compl
    -- 🎉 no goals
  · exact fun f _ _ hf => IsClopenable.iUnion hf
    -- 🎉 no goals
#align measurable_set.is_clopenable MeasurableSet.isClopenable

theorem _root_.MeasurableSet.analyticSet {α : Type*} [t : TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] {s : Set α} (hs : MeasurableSet s) : AnalyticSet s := by
  /- For a short proof (avoiding measurable induction), one sees `s` as a closed set for a finer
    topology `t'`. It is analytic for this topology. As the identity from `t'` to `t` is continuous
    and the image of an analytic set is analytic, it follows that `s` is also analytic for `t`. -/
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
    ∃ t' : TopologicalSpace α, t' ≤ t ∧ @PolishSpace α t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  have A := @IsClosed.analyticSet α t' t'_polish s s_closed
  -- ⊢ AnalyticSet s
  convert @AnalyticSet.image_of_continuous α t' α t s A id (continuous_id_of_le t't)
  -- ⊢ s = id '' s
  simp only [id.def, image_id']
  -- 🎉 no goals
#align measurable_set.analytic_set MeasurableSet.analyticSet

/-- Given a Borel-measurable function from a Polish space to a second-countable space, there exists
a finer Polish topology on the source space for which the function is continuous. -/
theorem _root_.Measurable.exists_continuous {α β : Type*} [t : TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [tβ : TopologicalSpace β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {f : α → β} [SecondCountableTopology (range f)] (hf : Measurable f) :
    ∃ t' : TopologicalSpace α, t' ≤ t ∧ @Continuous α β t' tβ f ∧ @PolishSpace α t' := by
  obtain ⟨b, b_count, -, hb⟩ :
    ∃ b : Set (Set (range f)), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b :=
    exists_countable_basis (range f)
  haveI : Countable b := b_count.to_subtype
  -- ⊢ ∃ t', t' ≤ t ∧ Continuous f ∧ PolishSpace α
  have : ∀ s : b, IsClopenable (rangeFactorization f ⁻¹' s) := fun s ↦ by
    apply MeasurableSet.isClopenable
    exact hf.subtype_mk (hb.isOpen s.2).measurableSet
  choose T Tt Tpolish _ Topen using this
  -- ⊢ ∃ t', t' ≤ t ∧ Continuous f ∧ PolishSpace α
  obtain ⟨t', t'T, t't, t'_polish⟩ :
    ∃ t' : TopologicalSpace α, (∀ i, t' ≤ T i) ∧ t' ≤ t ∧ @PolishSpace α t' :=
    exists_polishSpace_forall_le T Tt Tpolish
  refine' ⟨t', t't, _, t'_polish⟩
  -- ⊢ Continuous f
  have : Continuous[t', _] (rangeFactorization f) :=
    hb.continuous _ fun s hs => t'T ⟨s, hs⟩ _ (Topen ⟨s, hs⟩)
  exact continuous_subtype_val.comp this
  -- 🎉 no goals
#align measurable.exists_continuous Measurable.exists_continuous

/-- The image of a measurable set in a Polish space under a measurable map is an analytic set. -/
theorem _root_.MeasurableSet.analyticSet_image {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {f : X → Y} [SecondCountableTopology (range f)] {s : Set X}
    (hs : MeasurableSet s) (hf : Measurable f) : AnalyticSet (f '' s) := by
  borelize X
  -- ⊢ AnalyticSet (f '' s)
  rcases hf.exists_continuous with ⟨τ', hle, hfc, hτ'⟩
  -- ⊢ AnalyticSet (f '' s)
  letI m' : MeasurableSpace X := @borel _ τ'
  -- ⊢ AnalyticSet (f '' s)
  haveI b' : BorelSpace X := ⟨rfl⟩
  -- ⊢ AnalyticSet (f '' s)
  have hle := borel_anti hle
  -- ⊢ AnalyticSet (f '' s)
  exact (hle _ hs).analyticSet.image_of_continuous hfc
  -- 🎉 no goals
#align measurable_set.analytic_set_image MeasurableSet.analyticSet_image

/-! ### Separating sets with measurable sets -/


/-- Two sets `u` and `v` in a measurable space are measurably separable if there
exists a measurable set containing `u` and disjoint from `v`.
This is mostly interesting for Borel-separable sets. -/
def MeasurablySeparable {α : Type*} [MeasurableSpace α] (s t : Set α) : Prop :=
  ∃ u, s ⊆ u ∧ Disjoint t u ∧ MeasurableSet u
#align measure_theory.measurably_separable MeasureTheory.MeasurablySeparable

theorem MeasurablySeparable.iUnion [Countable ι] {α : Type*} [MeasurableSpace α] {s t : ι → Set α}
    (h : ∀ m n, MeasurablySeparable (s m) (t n)) : MeasurablySeparable (⋃ n, s n) (⋃ m, t m) := by
  choose u hsu htu hu using h
  -- ⊢ MeasurablySeparable (⋃ (n : ι), s n) (⋃ (m : ι), t m)
  refine' ⟨⋃ m, ⋂ n, u m n, _, _, _⟩
  · refine' iUnion_subset fun m => subset_iUnion_of_subset m _
    -- ⊢ s m ⊆ ⋂ (n : ι), u m n
    exact subset_iInter fun n => hsu m n
    -- 🎉 no goals
  · simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    -- ⊢ ∀ (i i_1 : ι), Disjoint (t i) (⋂ (n : ι), u i_1 n)
    intro n m
    -- ⊢ Disjoint (t n) (⋂ (n : ι), u m n)
    apply Disjoint.mono_right _ (htu m n)
    -- ⊢ ⋂ (n : ι), u m n ≤ u m n
    apply iInter_subset
    -- 🎉 no goals
  · refine' MeasurableSet.iUnion fun m => _
    -- ⊢ MeasurableSet (⋂ (n : ι), u m n)
    exact MeasurableSet.iInter fun n => hu m n
    -- 🎉 no goals
#align measure_theory.measurably_separable.Union MeasureTheory.MeasurablySeparable.iUnion

/-- The hard part of the Lusin separation theorem saying that two disjoint analytic sets are
contained in disjoint Borel sets (see the full statement in `AnalyticSet.measurablySeparable`).
Here, we prove this when our analytic sets are the ranges of functions from `ℕ → ℕ`.
-/
theorem measurablySeparable_range_of_disjoint [T2Space α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {f g : (ℕ → ℕ) → α} (hf : Continuous f) (hg : Continuous g)
    (h : Disjoint (range f) (range g)) : MeasurablySeparable (range f) (range g) := by
  /- We follow [Kechris, *Classical Descriptive Set Theory* (Theorem 14.7)][kechris1995].
    If the ranges are not Borel-separated, then one can find two cylinders of length one whose
    images are not Borel-separated, and then two smaller cylinders of length two whose images are
    not Borel-separated, and so on. One thus gets two sequences of cylinders, that decrease to two
    points `x` and `y`. Their images are different by the disjointness assumption, hence contained
    in two disjoint open sets by the T2 property. By continuity, long enough cylinders around `x`
    and `y` have images which are separated by these two disjoint open sets, a contradiction.
    -/
  by_contra hfg
  -- ⊢ False
  have I : ∀ n x y, ¬MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) →
      ∃ x' y', x' ∈ cylinder x n ∧ y' ∈ cylinder y n ∧
      ¬MeasurablySeparable (f '' cylinder x' (n + 1)) (g '' cylinder y' (n + 1)) := by
    intro n x y
    contrapose!
    intro H
    rw [← iUnion_cylinder_update x n, ← iUnion_cylinder_update y n, image_iUnion, image_iUnion]
    refine' MeasurablySeparable.iUnion fun i j => _
    exact H _ _ (update_mem_cylinder _ _ _) (update_mem_cylinder _ _ _)
  -- consider the set of pairs of cylinders of some length whose images are not Borel-separated
  let A :=
    { p : ℕ × (ℕ → ℕ) × (ℕ → ℕ) //
      ¬MeasurablySeparable (f '' cylinder p.2.1 p.1) (g '' cylinder p.2.2 p.1) }
  -- for each such pair, one can find longer cylinders whose images are not Borel-separated either
  have : ∀ p : A, ∃ q : A,
      q.1.1 = p.1.1 + 1 ∧ q.1.2.1 ∈ cylinder p.1.2.1 p.1.1 ∧ q.1.2.2 ∈ cylinder p.1.2.2 p.1.1 := by
    rintro ⟨⟨n, x, y⟩, hp⟩
    rcases I n x y hp with ⟨x', y', hx', hy', h'⟩
    exact ⟨⟨⟨n + 1, x', y'⟩, h'⟩, rfl, hx', hy'⟩
  choose F hFn hFx hFy using this
  -- ⊢ False
  let p0 : A := ⟨⟨0, fun _ => 0, fun _ => 0⟩, by simp [hfg]⟩
  -- ⊢ False
  -- construct inductively decreasing sequences of cylinders whose images are not separated
  let p : ℕ → A := fun n => F^[n] p0
  -- ⊢ False
  have prec : ∀ n, p (n + 1) = F (p n) := fun n => by simp only [iterate_succ', Function.comp]
  -- ⊢ False
  -- check that at the `n`-th step we deal with cylinders of length `n`
  have pn_fst : ∀ n, (p n).1.1 = n := by
    intro n
    induction' n with n IH
    · rfl
    · simp only [prec, hFn, IH]
  -- check that the cylinders we construct are indeed decreasing, by checking that the coordinates
  -- are stationary.
  have Ix : ∀ m n, m + 1 ≤ n → (p n).1.2.1 m = (p (m + 1)).1.2.1 m := by
    intro m
    apply Nat.le_induction
    · rfl
    intro n hmn IH
    have I : (F (p n)).val.snd.fst m = (p n).val.snd.fst m := by
      apply hFx (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec, I, IH]
  have Iy : ∀ m n, m + 1 ≤ n → (p n).1.2.2 m = (p (m + 1)).1.2.2 m := by
    intro m
    apply Nat.le_induction
    · rfl
    intro n hmn IH
    have I : (F (p n)).val.snd.snd m = (p n).val.snd.snd m := by
      apply hFy (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec, I, IH]
  -- denote by `x` and `y` the limit points of these two sequences of cylinders.
  set x : ℕ → ℕ := fun n => (p (n + 1)).1.2.1 n with hx
  -- ⊢ False
  set y : ℕ → ℕ := fun n => (p (n + 1)).1.2.2 n with hy
  -- ⊢ False
  -- by design, the cylinders around these points have images which are not Borel-separable.
  have M : ∀ n, ¬MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) := by
    intro n
    convert(p n).2 using 3
    · rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff]
      intro i hi
      rw [hx]
      exact (Ix i n hi).symm
    · rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff]
      intro i hi
      rw [hy]
      exact (Iy i n hi).symm
  -- consider two open sets separating `f x` and `g y`.
  obtain ⟨u, v, u_open, v_open, xu, yv, huv⟩ :
    ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ f x ∈ u ∧ g y ∈ v ∧ Disjoint u v := by
    apply t2_separation
    exact disjoint_iff_forall_ne.1 h (mem_range_self _) (mem_range_self _)
  letI : MetricSpace (ℕ → ℕ) := metricSpaceNatNat
  -- ⊢ False
  obtain ⟨εx, εxpos, hεx⟩ : ∃ (εx : ℝ), εx > 0 ∧ Metric.ball x εx ⊆ f ⁻¹' u := by
    apply Metric.mem_nhds_iff.1
    exact hf.continuousAt.preimage_mem_nhds (u_open.mem_nhds xu)
  obtain ⟨εy, εypos, hεy⟩ : ∃ (εy : ℝ), εy > 0 ∧ Metric.ball y εy ⊆ g ⁻¹' v := by
    apply Metric.mem_nhds_iff.1
    exact hg.continuousAt.preimage_mem_nhds (v_open.mem_nhds yv)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < min εx εy :=
    exists_pow_lt_of_lt_one (lt_min εxpos εypos) (by norm_num)
  -- for large enough `n`, these open sets separate the images of long cylinders around `x` and `y`
  have B : MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) := by
    refine' ⟨u, _, _, u_open.measurableSet⟩
    · rw [image_subset_iff]
      apply Subset.trans _ hεx
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      exact hz.trans_lt (hn.trans_le (min_le_left _ _))
    · refine' Disjoint.mono_left _ huv.symm
      change g '' cylinder y n ⊆ v
      rw [image_subset_iff]
      apply Subset.trans _ hεy
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      exact hz.trans_lt (hn.trans_le (min_le_right _ _))
  -- this is a contradiction.
  exact M n B
  -- 🎉 no goals
#align measure_theory.measurably_separable_range_of_disjoint MeasureTheory.measurablySeparable_range_of_disjoint

/-- The Lusin separation theorem: if two analytic sets are disjoint, then they are contained in
disjoint Borel sets. -/
theorem AnalyticSet.measurablySeparable [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s t : Set α} (hs : AnalyticSet s) (ht : AnalyticSet t) (h : Disjoint s t) :
    MeasurablySeparable s t := by
  rw [AnalyticSet] at hs ht
  -- ⊢ MeasurablySeparable s t
  rcases hs with (rfl | ⟨f, f_cont, rfl⟩)
  -- ⊢ MeasurablySeparable ∅ t
  · refine' ⟨∅, Subset.refl _, by simp, MeasurableSet.empty⟩
    -- 🎉 no goals
  rcases ht with (rfl | ⟨g, g_cont, rfl⟩)
  -- ⊢ MeasurablySeparable (range f) ∅
  · exact ⟨univ, subset_univ _, by simp, MeasurableSet.univ⟩
    -- 🎉 no goals
  exact measurablySeparable_range_of_disjoint f_cont g_cont h
  -- 🎉 no goals
#align measure_theory.analytic_set.measurably_separable MeasureTheory.AnalyticSet.measurablySeparable

/-- **Suslin's Theorem**: in a Hausdorff topological space, an analytic set with an analytic
complement is measurable. -/
theorem AnalyticSet.measurableSet_of_compl [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (hs : AnalyticSet s) (hsc : AnalyticSet sᶜ) : MeasurableSet s := by
  rcases hs.measurablySeparable hsc disjoint_compl_right with ⟨u, hsu, hdu, hmu⟩
  -- ⊢ MeasurableSet s
  obtain rfl : s = u := hsu.antisymm (disjoint_compl_left_iff_subset.1 hdu)
  -- ⊢ MeasurableSet s
  exact hmu
  -- 🎉 no goals
#align measure_theory.analytic_set.measurable_set_of_compl MeasureTheory.AnalyticSet.measurableSet_of_compl

end MeasureTheory

/-!
### Measurability of preimages under measurable maps
-/

namespace Measurable

variable {X Y β : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [MeasurableSpace β]

/-- If `f : X → Y` is a surjective Borel measurable map from a Polish space to a topological space
with second countable topology, then the preimage of a set `s` is measurable if and only if the set
is measurable.
One implication is the definition of measurability, the other one heavily relies on `X` being a
Polish space. -/
theorem measurableSet_preimage_iff_of_surjective [SecondCountableTopology Y] {f : X → Y}
    (hf : Measurable f) (hsurj : Surjective f) {s : Set Y} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet s := by
  refine ⟨fun h => ?_, fun h => hf h⟩
  -- ⊢ MeasurableSet s
  apply AnalyticSet.measurableSet_of_compl
  -- ⊢ AnalyticSet s
  · rw [← image_preimage_eq s hsurj]
    -- ⊢ AnalyticSet (f '' (f ⁻¹' s))
    exact h.analyticSet_image hf
    -- 🎉 no goals
  · rw [← image_preimage_eq sᶜ hsurj]
    -- ⊢ AnalyticSet (f '' (f ⁻¹' sᶜ))
    exact h.compl.analyticSet_image hf
    -- 🎉 no goals
#align measurable.measurable_set_preimage_iff_of_surjective Measurable.measurableSet_preimage_iff_of_surjective

theorem map_measurableSpace_eq [SecondCountableTopology Y] {f : X → Y} (hf : Measurable f)
    (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace X› = ‹MeasurableSpace Y› :=
  MeasurableSpace.ext fun _ => hf.measurableSet_preimage_iff_of_surjective hsurj
#align measurable.map_measurable_space_eq Measurable.map_measurableSpace_eq

theorem map_measurableSpace_eq_borel [SecondCountableTopology Y] {f : X → Y} (hf : Measurable f)
    (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace X› = borel Y := by
  have d := hf.mono le_rfl OpensMeasurableSpace.borel_le
  -- ⊢ MeasurableSpace.map f inst✝⁷ = borel Y
  letI := borel Y; haveI : BorelSpace Y := ⟨rfl⟩
  -- ⊢ MeasurableSpace.map f inst✝⁷ = borel Y
                   -- ⊢ MeasurableSpace.map f inst✝⁷ = borel Y
  exact d.map_measurableSpace_eq hsurj
  -- 🎉 no goals
#align measurable.map_measurable_space_eq_borel Measurable.map_measurableSpace_eq_borel

theorem borelSpace_codomain [SecondCountableTopology Y] {f : X → Y} (hf : Measurable f)
    (hsurj : Surjective f) : BorelSpace Y :=
  ⟨(hf.map_measurableSpace_eq hsurj).symm.trans <| hf.map_measurableSpace_eq_borel hsurj⟩
#align measurable.borel_space_codomain Measurable.borelSpace_codomain

/-- If `f : X → Y` is a Borel measurable map from a Polish space to a topological space with second
countable topology, then the preimage of a set `s` is measurable if and only if the set is
measurable in `Set.range f`. -/
theorem measurableSet_preimage_iff_preimage_val {f : X → Y} [SecondCountableTopology (range f)]
    (hf : Measurable f) {s : Set Y} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet ((↑) ⁻¹' s : Set (range f)) :=
  have hf' : Measurable (rangeFactorization f) := hf.subtype_mk
  hf'.measurableSet_preimage_iff_of_surjective (s := Subtype.val ⁻¹' s) surjective_onto_range
#align measurable.measurable_set_preimage_iff_preimage_coe Measurable.measurableSet_preimage_iff_preimage_val

/-- If `f : X → Y` is a Borel measurable map from a Polish space to a topological space with second
countable topology and the range of `f` is measurable, then the preimage of a set `s` is measurable
if and only if the intesection with `Set.range f` is measurable. -/
theorem measurableSet_preimage_iff_inter_range {f : X → Y} [SecondCountableTopology (range f)]
    (hf : Measurable f) (hr : MeasurableSet (range f)) {s : Set Y} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [hf.measurableSet_preimage_iff_preimage_val,
    ← (MeasurableEmbedding.subtype_coe hr).measurableSet_image, Subtype.image_preimage_coe]
#align measurable.measurable_set_preimage_iff_inter_range Measurable.measurableSet_preimage_iff_inter_range

/-- If `f : X → Y` is a Borel measurable map from a Polish space to a topological space with second
countable topology, then for any measurable space `β` and `g : Y → β`, the composition `g ∘ f` is
measurable if and only if the restriction of `g` to the range of `f` is measurable. -/
theorem measurable_comp_iff_restrict {f : X → Y} [SecondCountableTopology (range f)]
    (hf : Measurable f) {g : Y → β} : Measurable (g ∘ f) ↔ Measurable (restrict (range f) g) :=
  forall₂_congr fun s _ => measurableSet_preimage_iff_preimage_val hf (s := g ⁻¹' s)
#align measurable.measurable_comp_iff_restrict Measurable.measurable_comp_iff_restrict

/-- If `f : X → Y` is a surjective Borel measurable map from a Polish space to a topological space
with second countable topology, then for any measurable space `α` and `g : Y → α`, the composition
`g ∘ f` is measurable if and only if `g` is measurable. -/
theorem measurable_comp_iff_of_surjective [SecondCountableTopology Y] {f : X → Y}
    (hf : Measurable f) (hsurj : Surjective f) {g : Y → β} : Measurable (g ∘ f) ↔ Measurable g :=
  forall₂_congr fun s _ => measurableSet_preimage_iff_of_surjective hf hsurj (s := g ⁻¹' s)
#align measurable.measurable_comp_iff_of_surjective Measurable.measurable_comp_iff_of_surjective

end Measurable

theorem Continuous.map_eq_borel {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    {f : X → Y} (hf : Continuous f) (hsurj : Surjective f) :
    MeasurableSpace.map f ‹MeasurableSpace X› = borel Y := by
  borelize Y
  -- ⊢ MeasurableSpace.map f inst✝⁴ = borel Y
  exact hf.measurable.map_measurableSpace_eq hsurj
  -- 🎉 no goals
#align continuous.map_eq_borel Continuous.map_eq_borel

theorem Continuous.map_borel_eq {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] {f : X → Y} (hf : Continuous f)
    (hsurj : Surjective f) : MeasurableSpace.map f (borel X) = borel Y := by
  borelize X
  -- ⊢ MeasurableSpace.map f (borel X) = borel Y
  exact hf.map_eq_borel hsurj
  -- 🎉 no goals
#align continuous.map_borel_eq Continuous.map_borel_eq

instance Quotient.borelSpace {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Setoid X} [T2Space (Quotient s)] [SecondCountableTopology (Quotient s)] :
    BorelSpace (Quotient s) :=
  ⟨continuous_quotient_mk'.map_eq_borel (surjective_quotient_mk _)⟩
#align quotient.borel_space Quotient.borelSpace

@[to_additive]
instance QuotientGroup.borelSpace {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G]
    [TopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [N.Normal]
    [IsClosed (N : Set G)] : BorelSpace (G ⧸ N) :=
  -- porting note: 1st and 3rd `haveI`s were not needed in Lean 3
  haveI := Subgroup.t3_quotient_of_isClosed N
  haveI := @PolishSpace.secondCountableTopology G
  haveI := QuotientGroup.secondCountableTopology (Γ := N)
  Quotient.borelSpace
#align quotient_group.borel_space QuotientGroup.borelSpace
#align quotient_add_group.borel_space QuotientAddGroup.borelSpace

namespace MeasureTheory

/-! ### Injective images of Borel sets -/

variable {γ : Type*} [tγ : TopologicalSpace γ] [PolishSpace γ]

/-- The Lusin-Souslin theorem: the range of a continuous injective function defined on a Polish
space is Borel-measurable. -/
theorem measurableSet_range_of_continuous_injective {β : Type*} [TopologicalSpace β] [T2Space β]
    [MeasurableSpace β] [BorelSpace β] {f : γ → β} (f_cont : Continuous f) (f_inj : Injective f) :
    MeasurableSet (range f) := by
  /- We follow [Fremlin, *Measure Theory* (volume 4, 423I)][fremlin_vol4].
    Let `b = {s i}` be a countable basis for `α`. When `s i` and `s j` are disjoint, their images
    are disjoint analytic sets, hence by the separation theorem one can find a Borel-measurable set
    `q i j` separating them.
    Let `E i = closure (f '' s i) ∩ ⋂ j, q i j \ q j i`. It contains `f '' (s i)` and it is
    measurable. Let `F n = ⋃ E i`, where the union is taken over those `i` for which `diam (s i)`
    is bounded by some number `u n` tending to `0` with `n`.
    We claim that `range f = ⋂ F n`, from which the measurability is obvious. The inclusion `⊆` is
    straightforward. To show `⊇`, consider a point `x` in the intersection. For each `n`, it belongs
    to some `E i` with `diam (s i) ≤ u n`. Pick a point `y i ∈ s i`. We claim that for such `i`
    and `j`, the intersection `s i ∩ s j` is nonempty: if it were empty, then thanks to the
    separating set `q i j` in the definition of `E i` one could not have `x ∈ E i ∩ E j`.
    Since these two sets have small diameter, it follows that `y i` and `y j` are close.
    Thus, `y` is a Cauchy sequence, converging to a limit `z`. We claim that `f z = x`, completing
    the proof.
    Otherwise, one could find open sets `v` and `w` separating `f z` from `x`. Then, for large `n`,
    the image `f '' (s i)` would be included in `v` by continuity of `f`, so its closure would be
    contained in the closure of `v`, and therefore it would be disjoint from `w`. This is a
    contradiction since `x` belongs both to this closure and to `w`. -/
  letI := upgradePolishSpace γ
  -- ⊢ MeasurableSet (range f)
  obtain ⟨b, b_count, b_nonempty, hb⟩ :
    ∃ b : Set (Set γ), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := exists_countable_basis γ
  haveI : Encodable b := b_count.toEncodable
  -- ⊢ MeasurableSet (range f)
  let A := { p : b × b // Disjoint (p.1 : Set γ) p.2 }
  -- ⊢ MeasurableSet (range f)
  -- for each pair of disjoint sets in the topological basis `b`, consider Borel sets separating
  -- their images, by injectivity of `f` and the Lusin separation theorem.
  have : ∀ p : A, ∃ q : Set β,
      f '' (p.1.1 : Set γ) ⊆ q ∧ Disjoint (f '' (p.1.2 : Set γ)) q ∧ MeasurableSet q := by
    intro p
    apply
      AnalyticSet.measurablySeparable ((hb.isOpen p.1.1.2).analyticSet_image f_cont)
        ((hb.isOpen p.1.2.2).analyticSet_image f_cont)
    exact Disjoint.image p.2 (f_inj.injOn univ) (subset_univ _) (subset_univ _)
  choose q hq1 hq2 q_meas using this
  -- ⊢ MeasurableSet (range f)
  -- define sets `E i` and `F n` as in the proof sketch above
  let E : b → Set β := fun s =>
    closure (f '' s) ∩ ⋂ (t : b) (ht : Disjoint s.1 t.1), q ⟨(s, t), ht⟩ \ q ⟨(t, s), ht.symm⟩
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  let F : ℕ → Set β := fun n => ⋃ (s : b) (_ : Bounded s.1 ∧ diam s.1 ≤ u n), E s
  -- ⊢ MeasurableSet (range f)
  -- it is enough to show that `range f = ⋂ F n`, as the latter set is obviously measurable.
  suffices range f = ⋂ n, F n by
    have E_meas : ∀ s : b, MeasurableSet (E s) := by
      intro b
      refine' isClosed_closure.measurableSet.inter _
      refine' MeasurableSet.iInter fun s => _
      exact MeasurableSet.iInter fun hs => (q_meas _).diff (q_meas _)
    have F_meas : ∀ n, MeasurableSet (F n) := by
      intro n
      refine' MeasurableSet.iUnion fun s => _
      exact MeasurableSet.iUnion fun _ => E_meas _
    rw [this]
    exact MeasurableSet.iInter fun n => F_meas n
  -- we check both inclusions.
  apply Subset.antisymm
  -- ⊢ range f ⊆ ⋂ (n : ℕ), F n
  -- we start with the easy inclusion `range f ⊆ ⋂ F n`. One just needs to unfold the definitions.
  · rintro x ⟨y, rfl⟩
    -- ⊢ f y ∈ ⋂ (n : ℕ), F n
    refine mem_iInter.2 fun n => ?_
    -- ⊢ f y ∈ F n
    obtain ⟨s, sb, ys, hs⟩ : ∃ (s : Set γ), s ∈ b ∧ y ∈ s ∧ s ⊆ ball y (u n / 2) := by
      apply hb.mem_nhds_iff.1
      exact ball_mem_nhds _ (half_pos (u_pos n))
    have diam_s : diam s ≤ u n := by
      apply (diam_mono hs bounded_ball).trans
      convert diam_ball (x := y) (half_pos (u_pos n)).le
      ring
    refine' mem_iUnion.2 ⟨⟨s, sb⟩, _⟩
    -- ⊢ f y ∈ ⋃ (_ : Metric.Bounded ↑{ val := s, property := sb } ∧ diam ↑{ val := s …
    refine' mem_iUnion.2 ⟨⟨Metric.Bounded.mono hs bounded_ball, diam_s⟩, _⟩
    -- ⊢ f y ∈ E { val := s, property := sb }
    apply mem_inter (subset_closure (mem_image_of_mem _ ys))
    -- ⊢ f y ∈ ⋂ (t : ↑b) (ht : Disjoint ↑{ val := s, property := sb } ↑t), q { val : …
    refine' mem_iInter.2 fun t => mem_iInter.2 fun ht => ⟨_, _⟩
    -- ⊢ f y ∈ q { val := ({ val := s, property := sb }, t), property := ht }
    · apply hq1
      -- ⊢ f y ∈ f '' ↑(↑{ val := ({ val := s, property := sb }, t), property := ht }). …
      exact mem_image_of_mem _ ys
      -- 🎉 no goals
    · apply disjoint_left.1 (hq2 ⟨(t, ⟨s, sb⟩), ht.symm⟩)
      -- ⊢ f y ∈ f '' ↑(↑{ val := (t, { val := s, property := sb }), property := (_ : D …
      exact mem_image_of_mem _ ys
      -- 🎉 no goals
  -- Now, let us prove the harder inclusion `⋂ F n ⊆ range f`.
  · intro x hx
    -- ⊢ x ∈ range f
    -- pick for each `n` a good set `s n` of small diameter for which `x ∈ E (s n)`.
    have C1 : ∀ n, ∃ (s : b) (_ : Bounded s.1 ∧ diam s.1 ≤ u n), x ∈ E s := fun n => by
      simpa only [mem_iUnion] using mem_iInter.1 hx n
    choose s hs hxs using C1
    -- ⊢ x ∈ range f
    have C2 : ∀ n, (s n).1.Nonempty := by
      intro n
      rw [nonempty_iff_ne_empty]
      intro hn
      have := (s n).2
      rw [hn] at this
      exact b_nonempty this
    -- choose a point `y n ∈ s n`.
    choose y hy using C2
    -- ⊢ x ∈ range f
    have I : ∀ m n, ((s m).1 ∩ (s n).1).Nonempty := by
      intro m n
      rw [← not_disjoint_iff_nonempty_inter]
      by_contra' h
      have A : x ∈ q ⟨(s m, s n), h⟩ \ q ⟨(s n, s m), h.symm⟩ :=
        haveI := mem_iInter.1 (hxs m).2 (s n)
        (mem_iInter.1 this h : _)
      have B : x ∈ q ⟨(s n, s m), h.symm⟩ \ q ⟨(s m, s n), h⟩ :=
        haveI := mem_iInter.1 (hxs n).2 (s m)
        (mem_iInter.1 this h.symm : _)
      exact A.2 B.1
    -- the points `y n` are nearby, and therefore they form a Cauchy sequence.
    have cauchy_y : CauchySeq y := by
      have : Tendsto (fun n => 2 * u n) atTop (𝓝 0) := by
        simpa only [mul_zero] using u_lim.const_mul 2
      refine cauchySeq_of_le_tendsto_0' (fun n => 2 * u n) (fun m n hmn => ?_) this
      rcases I m n with ⟨z, zsm, zsn⟩
      calc
        dist (y m) (y n) ≤ dist (y m) z + dist z (y n) := dist_triangle _ _ _
        _ ≤ u m + u n :=
          (add_le_add ((dist_le_diam_of_mem (hs m).1 (hy m) zsm).trans (hs m).2)
            ((dist_le_diam_of_mem (hs n).1 zsn (hy n)).trans (hs n).2))
        _ ≤ 2 * u m := by linarith [u_anti.antitone hmn]
    haveI : Nonempty γ := ⟨y 0⟩
    -- ⊢ x ∈ range f
    -- let `z` be its limit.
    let z := limUnder atTop y
    -- ⊢ x ∈ range f
    have y_lim : Tendsto y atTop (𝓝 z) := cauchy_y.tendsto_limUnder
    -- ⊢ x ∈ range f
    suffices f z = x by
      rw [← this]
      exact mem_range_self _
    -- assume for a contradiction that `f z ≠ x`.
    by_contra' hne
    -- ⊢ False
    -- introduce disjoint open sets `v` and `w` separating `f z` from `x`.
    obtain ⟨v, w, v_open, w_open, fzv, xw, hvw⟩ := t2_separation hne
    -- ⊢ False
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ > (0 : ℝ), ball z δ ⊆ f ⁻¹' v := by
      apply Metric.mem_nhds_iff.1
      exact f_cont.continuousAt.preimage_mem_nhds (v_open.mem_nhds fzv)
    obtain ⟨n, hn⟩ : ∃ n, u n + dist (y n) z < δ :=
      haveI : Tendsto (fun n => u n + dist (y n) z) atTop (𝓝 0) := by
        simpa only [add_zero] using u_lim.add (tendsto_iff_dist_tendsto_zero.1 y_lim)
      ((tendsto_order.1 this).2 _ δpos).exists
    -- for large enough `n`, the image of `s n` is contained in `v`, by continuity of `f`.
    have fsnv : f '' s n ⊆ v := by
      rw [image_subset_iff]
      apply Subset.trans _ hδ
      intro a ha
      calc
        dist a z ≤ dist a (y n) + dist (y n) z := dist_triangle _ _ _
        _ ≤ u n + dist (y n) z :=
          (add_le_add_right ((dist_le_diam_of_mem (hs n).1 ha (hy n)).trans (hs n).2) _)
        _ < δ := hn
    -- as `x` belongs to the closure of `f '' (s n)`, it belongs to the closure of `v`.
    have : x ∈ closure v := closure_mono fsnv (hxs n).1
    -- ⊢ False
    -- this is a contradiction, as `x` is supposed to belong to `w`, which is disjoint from
    -- the closure of `v`.
    exact disjoint_left.1 (hvw.closure_left w_open) this xw
    -- 🎉 no goals
#align measure_theory.measurable_set_range_of_continuous_injective MeasureTheory.measurableSet_range_of_continuous_injective

theorem _root_.IsClosed.measurableSet_image_of_continuousOn_injOn {β : Type*} [TopologicalSpace β]
    [T2Space β] [MeasurableSpace β] [BorelSpace β] {s : Set γ} (hs : IsClosed s) {f : γ → β}
    (f_cont : ContinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  rw [image_eq_range]
  -- ⊢ MeasurableSet (range fun x => f ↑x)
  haveI : PolishSpace s := IsClosed.polishSpace hs
  -- ⊢ MeasurableSet (range fun x => f ↑x)
  apply measurableSet_range_of_continuous_injective
  -- ⊢ Continuous fun x => f ↑x
  · rwa [continuousOn_iff_continuous_restrict] at f_cont
    -- 🎉 no goals
  · rwa [injOn_iff_injective] at f_inj
    -- 🎉 no goals
#align is_closed.measurable_set_image_of_continuous_on_inj_on IsClosed.measurableSet_image_of_continuousOn_injOn

variable [MeasurableSpace γ] [hγb : BorelSpace γ] {β : Type*} [tβ : TopologicalSpace β] [T2Space β]
  [MeasurableSpace β] [BorelSpace β] {s : Set γ} {f : γ → β}

/-- The Lusin-Souslin theorem: if `s` is Borel-measurable in a Polish space, then its image under
a continuous injective map is also Borel-measurable. -/
theorem _root_.MeasurableSet.image_of_continuousOn_injOn (hs : MeasurableSet s)
    (f_cont : ContinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
    ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  exact
    @IsClosed.measurableSet_image_of_continuousOn_injOn γ t' t'_polish β _ _ _ _ s s_closed f
      (f_cont.mono_dom t't) f_inj
#align measurable_set.image_of_continuous_on_inj_on MeasurableSet.image_of_continuousOn_injOn

/-- The Lusin-Souslin theorem: if `s` is Borel-measurable in a Polish space, then its image under
a measurable injective map taking values in a second-countable topological space
is also Borel-measurable. -/
theorem _root_.MeasurableSet.image_of_measurable_injOn [SecondCountableTopology β]
    (hs : MeasurableSet s) (f_meas : Measurable f) (f_inj : InjOn f s) :
    MeasurableSet (f '' s) := by
  -- for a finer Polish topology, `f` is continuous. Therefore, one may apply the corresponding
  -- result for continuous maps.
  obtain ⟨t', t't, f_cont, t'_polish⟩ :
    ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @Continuous γ β t' tβ f ∧ @PolishSpace γ t' :=
    f_meas.exists_continuous
  have M : MeasurableSet[@borel γ t'] s :=
    @Continuous.measurable γ γ t' (@borel γ t')
      (@BorelSpace.opensMeasurable γ t' (@borel γ t') (@BorelSpace.mk _ _ (borel γ) rfl))
      tγ _ _ _ (continuous_id_of_le t't) s hs
  exact
    @MeasurableSet.image_of_continuousOn_injOn γ t' t'_polish (@borel γ t')
      (@BorelSpace.mk _ _ (borel γ) rfl)
      β _ _ _ _ s f M (@Continuous.continuousOn γ β t' tβ f s f_cont) f_inj
#align measurable_set.image_of_measurable_inj_on MeasurableSet.image_of_measurable_injOn

/-- An injective continuous function on a Polish space is a measurable embedding. -/
theorem _root_.Continuous.measurableEmbedding (f_cont : Continuous f) (f_inj : Injective f) :
    MeasurableEmbedding f :=
  { injective := f_inj
    measurable := f_cont.measurable
    measurableSet_image' := fun _u hu =>
      hu.image_of_continuousOn_injOn f_cont.continuousOn (f_inj.injOn _) }
#align continuous.measurable_embedding Continuous.measurableEmbedding

/-- If `s` is Borel-measurable in a Polish space and `f` is continuous injective on `s`, then
the restriction of `f` to `s` is a measurable embedding. -/
theorem _root_.ContinuousOn.measurableEmbedding (hs : MeasurableSet s) (f_cont : ContinuousOn f s)
    (f_inj : InjOn f s) : MeasurableEmbedding (s.restrict f) :=
  { injective := injOn_iff_injective.1 f_inj
    measurable := (continuousOn_iff_continuous_restrict.1 f_cont).measurable
    measurableSet_image' := by
      intro u hu
      -- ⊢ MeasurableSet (restrict s f '' u)
      have A : MeasurableSet (((↑) : s → γ) '' u) :=
        (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 hu
      have B : MeasurableSet (f '' (((↑) : s → γ) '' u)) :=
        A.image_of_continuousOn_injOn (f_cont.mono (Subtype.coe_image_subset s u))
          (f_inj.mono (Subtype.coe_image_subset s u))
      rwa [← image_comp] at B }
      -- 🎉 no goals
#align continuous_on.measurable_embedding ContinuousOn.measurableEmbedding

/-- An injective measurable function from a Polish space to a second-countable topological space
is a measurable embedding. -/
theorem _root_.Measurable.measurableEmbedding [SecondCountableTopology β] (f_meas : Measurable f)
    (f_inj : Injective f) : MeasurableEmbedding f :=
  { injective := f_inj
    measurable := f_meas
    measurableSet_image' := fun _u hu => hu.image_of_measurable_injOn f_meas (f_inj.injOn _) }
#align measurable.measurable_embedding Measurable.measurableEmbedding

/-- In a Polish space, a set is clopenable if and only if it is Borel-measurable. -/
theorem isClopenable_iff_measurableSet : IsClopenable s ↔ MeasurableSet s := by
  -- we already know that a measurable set is clopenable. Conversely, assume that `s` is clopenable.
  refine' ⟨fun hs => _, fun hs => hs.isClopenable⟩
  -- ⊢ MeasurableSet s
  -- consider a finer topology `t'` in which `s` is open and closed.
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
    ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s := hs
  -- the identity is continuous from `t'` to `tγ`.
  have C : @Continuous γ γ t' tγ id := continuous_id_of_le t't
  -- ⊢ MeasurableSet s
  -- therefore, it is also a measurable embedding, by the Lusin-Souslin theorem
  have E :=
    @Continuous.measurableEmbedding γ t' t'_polish (@borel γ t')
      (@BorelSpace.mk _ _ (borel γ) rfl)
      γ tγ (@PolishSpace.t2Space γ tγ _) _ _ id C injective_id
  -- the set `s` is measurable for `t'` as it is closed.
  have M : @MeasurableSet γ (@borel γ t') s :=
    @IsClosed.measurableSet γ s t' (@borel γ t')
      (@BorelSpace.opensMeasurable γ t' (@borel γ t') (@BorelSpace.mk _ _ (borel γ) rfl))
      s_closed
  -- therefore, its image under the measurable embedding `id` is also measurable for `tγ`.
  convert E.measurableSet_image.2 M
  -- ⊢ s = id '' s
  simp only [id.def, image_id']
  -- 🎉 no goals
#align measure_theory.is_clopenable_iff_measurable_set MeasureTheory.isClopenable_iff_measurableSet

/-- The set of points for which a measurable sequence of functions converges is measurable. -/
@[measurability]
theorem measurableSet_exists_tendsto [hγ : OpensMeasurableSpace γ] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → β → γ} (hf : ∀ i, Measurable (f i)) :
    MeasurableSet { x | ∃ c, Tendsto (fun n => f n x) l (𝓝 c) } := by
  rcases l.eq_or_neBot with rfl | hl
  -- ⊢ MeasurableSet {x | ∃ c, Tendsto (fun n => f n x) ⊥ (𝓝 c)}
  · simp
    -- 🎉 no goals
  letI := upgradePolishSpace γ
  -- ⊢ MeasurableSet {x | ∃ c, Tendsto (fun n => f n x) l (𝓝 c)}
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  -- ⊢ MeasurableSet {x | ∃ c, Tendsto (fun n => f n x) l (𝓝 c)}
  simp_rw [← cauchy_map_iff_exists_tendsto]
  -- ⊢ MeasurableSet {x | Cauchy (map (fun n => f n x) l)}
  change MeasurableSet { x | _ ∧ _ }
  -- ⊢ MeasurableSet {x | NeBot (map (fun n => f n x) l) ∧ map (fun n => f n x) l × …
  have :
    ∀ x,
      (map (fun i => f i x) l ×ˢ map (fun i => f i x) l).HasAntitoneBasis fun n =>
        ((fun i => f i x) '' u n) ×ˢ ((fun i => f i x) '' u n) :=
    fun x => hu.map.prod hu.map
  simp_rw [and_iff_right (hl.map _),
    Filter.HasBasis.le_basis_iff (this _).toHasBasis Metric.uniformity_basis_dist_inv_nat_succ,
    Set.setOf_forall]
  refine' MeasurableSet.biInter Set.countable_univ fun K _ => _
  -- ⊢ MeasurableSet {x | ∃ i, True ∧ ((fun n => f n x) '' u i) ×ˢ ((fun n => f n x …
  simp_rw [Set.setOf_exists, true_and]
  -- ⊢ MeasurableSet (⋃ (i : ℕ), {x | ((fun n => f n x) '' u i) ×ˢ ((fun n => f n x …
  refine' MeasurableSet.iUnion fun N => _
  -- ⊢ MeasurableSet {x | ((fun n => f n x) '' u N) ×ˢ ((fun n => f n x) '' u N) ⊆  …
  simp_rw [prod_image_image_eq, image_subset_iff, prod_subset_iff, Set.setOf_forall]
  -- ⊢ MeasurableSet (⋂ (i : ι) (_ : i ∈ u N) (i_1 : ι) (_ : i_1 ∈ u N), {x | (i, i …
  exact
    MeasurableSet.biInter (to_countable (u N)) fun i _ =>
      MeasurableSet.biInter (to_countable (u N)) fun j _ =>
        measurableSet_lt (Measurable.dist (hf i) (hf j)) measurable_const
#align measure_theory.measurable_set_exists_tendsto MeasureTheory.measurableSet_exists_tendsto

end MeasureTheory

/-! ### The Borel Isomorphism Theorem -/

-- Porting note: Move to topology/metric_space/polish when porting.
instance (priority := 50) polish_of_countable [h : Countable α] [DiscreteTopology α] :
    PolishSpace α := by
  obtain ⟨f, hf⟩ := h.exists_injective_nat
  -- ⊢ PolishSpace α
  have : ClosedEmbedding f := by
    apply closedEmbedding_of_continuous_injective_closed continuous_of_discreteTopology hf
    exact fun t _ => isClosed_discrete _
  exact this.polishSpace
  -- 🎉 no goals
#align polish_of_countable polish_of_countable

namespace PolishSpace

/- Porting note: This is to avoid a loop in TC inference. When ported to Lean 4, this will not
be necessary, and `secondCountable_of_polish` should probably
just be added as an instance soon after the definition of `PolishSpace`.-/
private theorem secondCountable_of_polish [h : PolishSpace α] : SecondCountableTopology α :=
  h.secondCountableTopology

attribute [-instance] polishSpace_of_complete_second_countable

attribute [local instance] secondCountable_of_polish

variable {β : Type*} [TopologicalSpace β] [PolishSpace α] [PolishSpace β]

variable [MeasurableSpace α] [MeasurableSpace β] [BorelSpace α] [BorelSpace β]

/-- If two Polish spaces admit Borel measurable injections to one another,
then they are Borel isomorphic.-/
noncomputable def borelSchroederBernstein {f : α → β} {g : β → α} (fmeas : Measurable f)
    (finj : Function.Injective f) (gmeas : Measurable g) (ginj : Function.Injective g) : α ≃ᵐ β :=
  (fmeas.measurableEmbedding finj).schroederBernstein (gmeas.measurableEmbedding ginj)
#align polish_space.borel_schroeder_bernstein PolishSpace.borelSchroederBernstein

/-- Any uncountable Polish space is Borel isomorphic to the Cantor space `ℕ → Bool`.-/
noncomputable def measurableEquivNatBoolOfNotCountable (h : ¬Countable α) : α ≃ᵐ (ℕ → Bool) := by
  apply Nonempty.some
  -- ⊢ Nonempty (α ≃ᵐ (ℕ → Bool))
  obtain ⟨f, -, fcts, finj⟩ :=
    isClosed_univ.exists_nat_bool_injection_of_not_countable
      (by rwa [← countable_coe_iff, (Equiv.Set.univ _).countable_iff])
  obtain ⟨g, gmeas, ginj⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablyGenerated α
  -- ⊢ Nonempty (α ≃ᵐ (ℕ → Bool))
  exact ⟨borelSchroederBernstein gmeas ginj fcts.measurable finj⟩
  -- 🎉 no goals
#align polish_space.measurable_equiv_nat_bool_of_not_countable PolishSpace.measurableEquivNatBoolOfNotCountable

/-- The **Borel Isomorphism Theorem**: Any two uncountable Polish spaces are Borel isomorphic.-/
noncomputable def measurableEquivOfNotCountable (hα : ¬Countable α) (hβ : ¬Countable β) : α ≃ᵐ β :=
  (measurableEquivNatBoolOfNotCountable hα).trans (measurableEquivNatBoolOfNotCountable hβ).symm
#align polish_space.measurable_equiv_of_not_countable PolishSpace.measurableEquivOfNotCountable

/-- The **Borel Isomorphism Theorem**: If two Polish spaces have the same cardinality,
they are Borel isomorphic.-/
noncomputable def Equiv.measurableEquiv (e : α ≃ β) : α ≃ᵐ β := by
  by_cases h : Countable α
  -- ⊢ α ≃ᵐ β
  · letI := Countable.of_equiv α e
    -- ⊢ α ≃ᵐ β
    refine ⟨e, ?_, ?_⟩ <;> apply measurable_of_countable
    -- ⊢ Measurable ↑e
                           -- 🎉 no goals
                           -- 🎉 no goals
  refine' measurableEquivOfNotCountable h _
  -- ⊢ ¬Countable β
  rwa [e.countable_iff] at h
  -- 🎉 no goals
#align polish_space.equiv.measurable_equiv PolishSpace.Equiv.measurableEquiv

end PolishSpace

namespace MeasureTheory

-- Porting note: todo after the port: move to topology/metric_space/polish
instance instPolishSpaceUniv [PolishSpace α] : PolishSpace (univ : Set α) :=
  isClosed_univ.polishSpace
#align measure_theory.set.univ.polish_space MeasureTheory.instPolishSpaceUniv

variable (α)
variable [MeasurableSpace α] [PolishSpace α] [BorelSpace α]

theorem exists_nat_measurableEquiv_range_coe_fin_of_finite [Finite α] :
    ∃ n : ℕ, Nonempty (α ≃ᵐ range ((↑) : Fin n → ℝ)) := by
  obtain ⟨n, ⟨n_equiv⟩⟩ := Finite.exists_equiv_fin α
  -- ⊢ ∃ n, Nonempty (α ≃ᵐ ↑(range fun x => ↑↑x))
  refine' ⟨n, ⟨PolishSpace.Equiv.measurableEquiv (n_equiv.trans _)⟩⟩
  -- ⊢ Fin n ≃ ↑(range fun x => ↑↑x)
  exact Equiv.ofInjective _ (Nat.cast_injective.comp Fin.val_injective)
  -- 🎉 no goals
#align measure_theory.exists_nat_measurable_equiv_range_coe_fin_of_finite MeasureTheory.exists_nat_measurableEquiv_range_coe_fin_of_finite

theorem measurableEquiv_range_coe_nat_of_infinite_of_countable [Infinite α] [Countable α] :
    Nonempty (α ≃ᵐ range ((↑) : ℕ → ℝ)) := by
  have : PolishSpace (range ((↑) : ℕ → ℝ)) :=
    Nat.closedEmbedding_coe_real.isClosedMap.closed_range.polishSpace
  refine' ⟨PolishSpace.Equiv.measurableEquiv _⟩
  -- ⊢ α ≃ ↑(range Nat.cast)
  refine' (nonempty_equiv_of_countable.some : α ≃ ℕ).trans _
  -- ⊢ ℕ ≃ ↑(range Nat.cast)
  exact Equiv.ofInjective ((↑) : ℕ → ℝ) Nat.cast_injective
  -- 🎉 no goals
#align measure_theory.measurable_equiv_range_coe_nat_of_infinite_of_countable MeasureTheory.measurableEquiv_range_coe_nat_of_infinite_of_countable

/-- Any Polish Borel space is measurably equivalent to a subset of the reals. -/
theorem exists_subset_real_measurableEquiv : ∃ s : Set ℝ, MeasurableSet s ∧ Nonempty (α ≃ᵐ s) := by
  by_cases hα : Countable α
  -- ⊢ ∃ s, MeasurableSet s ∧ Nonempty (α ≃ᵐ ↑s)
  · cases finite_or_infinite α
    -- ⊢ ∃ s, MeasurableSet s ∧ Nonempty (α ≃ᵐ ↑s)
    · obtain ⟨n, h_nonempty_equiv⟩ := exists_nat_measurableEquiv_range_coe_fin_of_finite α
      -- ⊢ ∃ s, MeasurableSet s ∧ Nonempty (α ≃ᵐ ↑s)
      refine' ⟨_, _, h_nonempty_equiv⟩
      -- ⊢ MeasurableSet (range fun x => ↑↑x)
      letI : MeasurableSpace (Fin n) := borel (Fin n)
      -- ⊢ MeasurableSet (range fun x => ↑↑x)
      haveI : BorelSpace (Fin n) := ⟨rfl⟩
      -- ⊢ MeasurableSet (range fun x => ↑↑x)
      refine' MeasurableEmbedding.measurableSet_range _
      -- ⊢ MeasurableSpace (Fin n)
      · infer_instance
        -- 🎉 no goals
      · exact
          continuous_of_discreteTopology.measurableEmbedding
            (Nat.cast_injective.comp Fin.val_injective)
    · refine' ⟨_, _, measurableEquiv_range_coe_nat_of_infinite_of_countable α⟩
      -- ⊢ MeasurableSet (range Nat.cast)
      refine' MeasurableEmbedding.measurableSet_range _
      -- ⊢ MeasurableSpace ℕ
      · infer_instance
        -- 🎉 no goals
      · exact continuous_of_discreteTopology.measurableEmbedding Nat.cast_injective
        -- 🎉 no goals
  · refine'
      ⟨univ, MeasurableSet.univ,
        ⟨(PolishSpace.measurableEquivOfNotCountable hα _ : α ≃ᵐ (univ : Set ℝ))⟩⟩
    rw [countable_coe_iff]
    -- ⊢ ¬Set.Countable univ
    exact Cardinal.not_countable_real
    -- 🎉 no goals
#align measure_theory.exists_subset_real_measurable_equiv MeasureTheory.exists_subset_real_measurableEquiv

/-- Any Polish Borel space embeds measurably into the reals. -/
theorem exists_measurableEmbedding_real : ∃ f : α → ℝ, MeasurableEmbedding f := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_subset_real_measurableEquiv α
  -- ⊢ ∃ f, MeasurableEmbedding f
  exact ⟨(↑) ∘ e, (MeasurableEmbedding.subtype_coe hs).comp e.measurableEmbedding⟩
  -- 🎉 no goals
#align measure_theory.exists_measurable_embedding_real MeasureTheory.exists_measurableEmbedding_real

end MeasureTheory
