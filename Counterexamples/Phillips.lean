/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.ContinuousFunction.Bounded

#align_import phillips from "leanprover-community/mathlib"@"328375597f2c0dd00522d9c2e5a33b6a6128feeb"

/-!
# A counterexample on Pettis integrability

There are several theories of integration for functions taking values in Banach spaces. Bochner
integration, requiring approximation by simple functions, is the analogue of the one-dimensional
theory. It is very well behaved, but only works for functions with second-countable range.

For functions `f` taking values in a larger Banach space `B`, one can define the Dunford integral
as follows. Assume that, for all continuous linear functional `φ`, the function `φ ∘ f` is
measurable (we say that `f` is weakly measurable, or scalarly measurable) and integrable.
Then `φ ↦ ∫ φ ∘ f` is continuous (by the closed graph theorem), and therefore defines an element
of the bidual `B**`. This is the Dunford integral of `f`.

This Dunford integral is not usable in practice as it does not belong to the right space. Let us
say that a function is Pettis integrable if its Dunford integral belongs to the canonical image of
`B` in `B**`. In this case, we define the Pettis integral as the Dunford integral inside `B`.

This integral is very general, but not really usable to do analysis. This file illustrates this,
by giving an example of a function with nice properties but which is *not* Pettis-integrable.
This function:
- is defined from `[0, 1]` to a complete Banach space;
- is weakly measurable;
- has norm everywhere bounded by `1` (in particular, its norm is integrable);
- and yet it is not Pettis-integrable with respect to Lebesgue measure.

This construction is due to [Ralph S. Phillips, *Integration in a convex linear
topological space*][phillips1940], in Example 10.8. It requires the continuum hypothesis. The
example is the following.

Under the continuum hypothesis, one can find a subset of `ℝ²` which,
along each vertical line, only misses a countable set of points, while it is countable along each
horizontal line. This is due to Sierpinski, and formalized in `sierpinski_pathological_family`.
(In fact, Sierpinski proves that the existence of such a set is equivalent to the continuum
hypothesis).

Let `B` be the set of all bounded functions on `ℝ` (we are really talking about everywhere defined
functions here). Define `f : ℝ → B` by taking `f x` to be the characteristic function of the
vertical slice at position `x` of Sierpinski's set. It is our counterexample.

To show that it is weakly measurable, we should consider `φ ∘ f` where `φ` is an arbitrary
continuous linear form on `B`. There is no reasonable classification of such linear forms (they can
be very wild). But if one restricts such a linear form to characteristic functions, one gets a
finitely additive signed "measure". Such a "measure" can be decomposed into a discrete part
(supported on a countable set) and a continuous part (giving zero mass to countable sets).
For all but countably many points, `f x` will not intersect the discrete support of `φ` thanks to
the definition of the Sierpinski set. This implies that `φ ∘ f` is constant outside of a countable
set, and equal to the total mass of the continuous part of `φ` there. In particular, it is
measurable (and its integral is the total mass of the continuous part of `φ`).

Assume that `f` has a Pettis integral `g`. For all continuous linear form `φ`, then `φ g` should
be the total mass of the continuous part of `φ`. Taking for `φ` the evaluation at the point `x`
(which has no continuous part), one gets `g x = 0`. Take then for `φ` the Lebesgue integral on
`[0, 1]` (or rather an arbitrary extension of Lebesgue integration to all bounded functions,
thanks to Hahn-Banach). Then `φ g` should be the total mass of the continuous part of `φ`,
which is `1`. This contradicts the fact that `g = 0`, and concludes the proof that `f` has no
Pettis integral.

## Implementation notes

The space of all bounded functions is defined as the space of all bounded continuous functions
on a discrete copy of the original type, as mathlib only contains the space of all bounded
continuous functions (which is the useful one).
-/


namespace Counterexample

universe u

variable {α : Type u}

open Set BoundedContinuousFunction MeasureTheory

open Cardinal (aleph)

open scoped Cardinal BoundedContinuousFunction

noncomputable section

/-- A copy of a type, endowed with the discrete topology -/
def DiscreteCopy (α : Type u) : Type u :=
  α
#align counterexample.discrete_copy Counterexample.DiscreteCopy

instance : TopologicalSpace (DiscreteCopy α) :=
  ⊥

instance : DiscreteTopology (DiscreteCopy α) :=
  ⟨rfl⟩

instance [Inhabited α] : Inhabited (DiscreteCopy α) :=
  ⟨show α from default⟩

namespace Phillips1940

/-!
### Extending the integral

Thanks to Hahn-Banach, one can define a (non-canonical) continuous linear functional on the space
of all bounded functions, coinciding with the integral on the integrable ones.
-/

/-- The subspace of integrable functions in the space of all bounded functions on a type.
This is a technical device, used to apply Hahn-Banach theorem to construct an extension of the
integral to all bounded functions. -/
def boundedIntegrableFunctions [MeasurableSpace α] (μ : Measure α) :
    Subspace ℝ (DiscreteCopy α →ᵇ ℝ) where
  carrier := {f | Integrable f μ}
  zero_mem' := integrable_zero _ _ _
  add_mem' hf hg := Integrable.add hf hg
  smul_mem' c _ hf := Integrable.smul c hf
#align counterexample.phillips_1940.bounded_integrable_functions Counterexample.Phillips1940.boundedIntegrableFunctions

/-- The integral, as a continuous linear map on the subspace of integrable functions in the space
of all bounded functions on a type. This is a technical device, that we will extend through
Hahn-Banach. -/
def boundedIntegrableFunctionsIntegralCLM [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] :
    boundedIntegrableFunctions μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous (E := ↥(boundedIntegrableFunctions μ))
    { toFun := fun f => ∫ x, f.1 x ∂μ
      map_add' := fun f g => integral_add f.2 g.2
      map_smul' := fun c f => integral_smul c f.1 } (μ univ).toReal
    (by
      intro f
      rw [mul_comm]
      apply norm_integral_le_of_norm_le_const
      apply Filter.eventually_of_forall
      intro x
      exact BoundedContinuousFunction.norm_coe_le_norm f.1 x)
#align counterexample.phillips_1940.bounded_integrable_functions_integral_clm Counterexample.Phillips1940.boundedIntegrableFunctionsIntegralCLM

/-- Given a measure, there exists a continuous linear form on the space of all bounded functions
(not necessarily measurable) that coincides with the integral on bounded measurable functions. -/
theorem exists_linear_extension_to_boundedFunctions [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] :
    ∃ φ : (DiscreteCopy α →ᵇ ℝ) →L[ℝ] ℝ,
      ∀ f : DiscreteCopy α →ᵇ ℝ, Integrable f μ → φ f = ∫ x, f x ∂μ := by
  rcases exists_extension_norm_eq _ (boundedIntegrableFunctionsIntegralCLM μ) with ⟨φ, hφ⟩
  exact ⟨φ, fun f hf => hφ.1 ⟨f, hf⟩⟩
#align counterexample.phillips_1940.exists_linear_extension_to_bounded_functions Counterexample.Phillips1940.exists_linear_extension_to_boundedFunctions

/-- An arbitrary extension of the integral to all bounded functions, as a continuous linear map.
It is not at all canonical, and constructed using Hahn-Banach. -/
def _root_.MeasureTheory.Measure.extensionToBoundedFunctions [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] : (DiscreteCopy α →ᵇ ℝ) →L[ℝ] ℝ :=
  (exists_linear_extension_to_boundedFunctions μ).choose
#align measure_theory.measure.extension_to_bounded_functions MeasureTheory.Measure.extensionToBoundedFunctions

theorem extensionToBoundedFunctions_apply [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : DiscreteCopy α →ᵇ ℝ) (hf : Integrable f μ) :
    μ.extensionToBoundedFunctions f = ∫ x, f x ∂μ :=
  (exists_linear_extension_to_boundedFunctions μ).choose_spec f hf
#align counterexample.phillips_1940.extension_to_bounded_functions_apply Counterexample.Phillips1940.extensionToBoundedFunctions_apply

/-!
### Additive measures on the space of all sets

We define bounded finitely additive signed measures on the space of all subsets of a type `α`,
and show that such an object can be split into a discrete part and a continuous part.
-/


/-- A bounded signed finitely additive measure defined on *all* subsets of a type. -/
structure BoundedAdditiveMeasure (α : Type u) where
  toFun : Set α → ℝ
  additive' : ∀ s t, Disjoint s t → toFun (s ∪ t) = toFun s + toFun t
  exists_bound : ∃ C : ℝ, ∀ s, |toFun s| ≤ C
#align counterexample.phillips_1940.bounded_additive_measure Counterexample.Phillips1940.BoundedAdditiveMeasure

attribute [coe] BoundedAdditiveMeasure.toFun

instance : Inhabited (BoundedAdditiveMeasure α) :=
  ⟨{  toFun := fun _ => 0
      additive' := fun s t _ => by simp
      exists_bound := ⟨0, fun _ => by simp⟩ }⟩

instance : CoeFun (BoundedAdditiveMeasure α) fun _ => Set α → ℝ :=
  ⟨fun f => f.toFun⟩

namespace BoundedAdditiveMeasure

/-- A constant bounding the mass of any set for `f`. -/
def C (f : BoundedAdditiveMeasure α) :=
  f.exists_bound.choose
set_option linter.uppercaseLean3 false in
#align counterexample.phillips_1940.bounded_additive_measure.C Counterexample.Phillips1940.BoundedAdditiveMeasure.C

theorem additive (f : BoundedAdditiveMeasure α) (s t : Set α) (h : Disjoint s t) :
    f (s ∪ t) = f s + f t :=
  f.additive' s t h
#align counterexample.phillips_1940.bounded_additive_measure.additive Counterexample.Phillips1940.BoundedAdditiveMeasure.additive

theorem abs_le_bound (f : BoundedAdditiveMeasure α) (s : Set α) : |f s| ≤ f.C :=
  f.exists_bound.choose_spec s
#align counterexample.phillips_1940.bounded_additive_measure.abs_le_bound Counterexample.Phillips1940.BoundedAdditiveMeasure.abs_le_bound

theorem le_bound (f : BoundedAdditiveMeasure α) (s : Set α) : f s ≤ f.C :=
  le_trans (le_abs_self _) (f.abs_le_bound s)
#align counterexample.phillips_1940.bounded_additive_measure.le_bound Counterexample.Phillips1940.BoundedAdditiveMeasure.le_bound

@[simp]
theorem empty (f : BoundedAdditiveMeasure α) : f ∅ = 0 := by
  have : (∅ : Set α) = ∅ ∪ ∅ := by simp only [empty_union]
  apply_fun f at this
  rwa [f.additive _ _ (empty_disjoint _), self_eq_add_left] at this
#align counterexample.phillips_1940.bounded_additive_measure.empty Counterexample.Phillips1940.BoundedAdditiveMeasure.empty

instance : Neg (BoundedAdditiveMeasure α) :=
  ⟨fun f =>
    { toFun := fun s => -f s
      additive' := fun s t hst => by simp only [f.additive s t hst, add_comm, neg_add_rev]
      exists_bound := ⟨f.C, fun s => by simp [f.abs_le_bound]⟩ }⟩

@[simp]
theorem neg_apply (f : BoundedAdditiveMeasure α) (s : Set α) : (-f) s = -f s :=
  rfl
#align counterexample.phillips_1940.bounded_additive_measure.neg_apply Counterexample.Phillips1940.BoundedAdditiveMeasure.neg_apply

/-- Restricting a bounded additive measure to a subset still gives a bounded additive measure. -/
def restrict (f : BoundedAdditiveMeasure α) (t : Set α) : BoundedAdditiveMeasure α where
  toFun s := f (t ∩ s)
  additive' s s' h := by
    dsimp only
    rw [← f.additive (t ∩ s) (t ∩ s'), inter_union_distrib_left]
    exact h.mono inter_subset_right inter_subset_right
  exists_bound := ⟨f.C, fun s => f.abs_le_bound _⟩
#align counterexample.phillips_1940.bounded_additive_measure.restrict Counterexample.Phillips1940.BoundedAdditiveMeasure.restrict

@[simp]
theorem restrict_apply (f : BoundedAdditiveMeasure α) (s t : Set α) : f.restrict s t = f (s ∩ t) :=
  rfl
#align counterexample.phillips_1940.bounded_additive_measure.restrict_apply Counterexample.Phillips1940.BoundedAdditiveMeasure.restrict_apply

/-- There is a maximal countable set of positive measure, in the sense that any countable set
not intersecting it has nonpositive measure. Auxiliary lemma to prove `exists_discrete_support`. -/
theorem exists_discrete_support_nonpos (f : BoundedAdditiveMeasure α) :
    ∃ s : Set α, s.Countable ∧ ∀ t : Set α, t.Countable → f (t \ s) ≤ 0 := by
  /- The idea of the proof is to construct the desired set inductively, adding at each step a
    countable set with close to maximal measure among those points that have not already been
    chosen. Doing this countably many steps will be enough. Indeed, otherwise, a remaining set would
    have positive measure `ε`. This means that at each step the set we have added also had a large
    measure, say at least `ε / 2`. After `n` steps, the set we have constructed has therefore
    measure at least `n * ε / 2`. This is a contradiction since the measures have to remain
    uniformly bounded.

    We argue from the start by contradiction, as this means that our inductive construction will
    never be stuck, so we won't have to consider this case separately.

    In this proof, we use explicit coercions `↑s` for `s : A` as otherwise the system tries to find
    a `CoeFun` instance on `↥A`, which is too costly.
    -/
  by_contra! h
  -- We will formulate things in terms of the type of countable subsets of `α`, as this is more
  -- convenient to formalize the inductive construction.
  let A : Set (Set α) := {t | t.Countable}
  let empty : A := ⟨∅, countable_empty⟩
  haveI : Nonempty A := ⟨empty⟩
  -- given a countable set `s`, one can find a set `t` in its complement with measure close to
  -- maximal.
  have : ∀ s : A, ∃ t : A, ∀ u : A, f (↑u \ ↑s) ≤ 2 * f (↑t \ ↑s) := by
    intro s
    have B : BddAbove (range fun u : A => f (↑u \ ↑s)) := by
      refine ⟨f.C, fun x hx => ?_⟩
      rcases hx with ⟨u, hu⟩
      rw [← hu]
      exact f.le_bound _
    let S := iSup fun t : A => f (↑t \ ↑s)
    have S_pos : 0 < S := by
      rcases h s.1 s.2 with ⟨t, t_count, ht⟩
      apply ht.trans_le
      let t' : A := ⟨t, t_count⟩
      change f (↑t' \ ↑s) ≤ S
      exact le_ciSup B t'
    rcases exists_lt_of_lt_ciSup (half_lt_self S_pos) with ⟨t, ht⟩
    refine ⟨t, fun u => ?_⟩
    calc
      f (↑u \ ↑s) ≤ S := le_ciSup B _
      _ ≤ 2 * f (↑t \ ↑s) := (div_le_iff' two_pos).1 ht.le
  choose! F hF using this
  -- iterate the above construction, by adding at each step a set with measure close to maximal in
  -- the complement of already chosen points. This is the set `s n` at step `n`.
  let G : A → A := fun u => ⟨(↑u : Set α) ∪ ↑(F u), u.2.union (F u).2⟩
  let s : ℕ → A := fun n => G^[n] empty
  -- We will get a contradiction from the fact that there is a countable set `u` with positive
  -- measure in the complement of `⋃ n, s n`.
  rcases h (⋃ n, ↑(s n)) (countable_iUnion fun n => (s n).2) with ⟨t, t_count, ht⟩
  let u : A := ⟨t \ ⋃ n, ↑(s n), t_count.mono diff_subset⟩
  set ε := f ↑u with hε
  have ε_pos : 0 < ε := ht
  have I1 : ∀ n, ε / 2 ≤ f (↑(s (n + 1)) \ ↑(s n)) := by
    intro n
    rw [div_le_iff' (show (0 : ℝ) < 2 by norm_num), hε]
    convert hF (s n) u using 2
    · dsimp
      ext x
      simp only [not_exists, mem_iUnion, mem_diff]
      tauto
    · congr 1
      simp only [s, Function.iterate_succ', Subtype.coe_mk, union_diff_left, Function.comp]
  have I2 : ∀ n : ℕ, (n : ℝ) * (ε / 2) ≤ f ↑(s n) := by
    intro n
    induction' n with n IH
    · simp only [s, BoundedAdditiveMeasure.empty, id, Nat.cast_zero, zero_mul,
        Function.iterate_zero, Subtype.coe_mk, Nat.zero_eq]
      rfl
    · have : (s (n + 1)).1 = (s (n + 1)).1 \ (s n).1 ∪ (s n).1 := by
        simpa only [s, Function.iterate_succ', union_diff_self]
          using (diff_union_of_subset subset_union_left).symm
      rw [this, f.additive]
      swap; · exact disjoint_sdiff_self_left
      calc
        ((n + 1 : ℕ) : ℝ) * (ε / 2) = ε / 2 + n * (ε / 2) := by simp only [Nat.cast_succ]; ring
        _ ≤ f (↑(s (n + 1 : ℕ)) \ ↑(s n)) + f ↑(s n) := add_le_add (I1 n) IH
  rcases exists_nat_gt (f.C / (ε / 2)) with ⟨n, hn⟩
  have : (n : ℝ) ≤ f.C / (ε / 2) := by
    rw [le_div_iff (half_pos ε_pos)]; exact (I2 n).trans (f.le_bound _)
  exact lt_irrefl _ (this.trans_lt hn)
#align counterexample.phillips_1940.bounded_additive_measure.exists_discrete_support_nonpos Counterexample.Phillips1940.BoundedAdditiveMeasure.exists_discrete_support_nonpos

theorem exists_discrete_support (f : BoundedAdditiveMeasure α) :
    ∃ s : Set α, s.Countable ∧ ∀ t : Set α, t.Countable → f (t \ s) = 0 := by
  rcases f.exists_discrete_support_nonpos with ⟨s₁, s₁_count, h₁⟩
  rcases (-f).exists_discrete_support_nonpos with ⟨s₂, s₂_count, h₂⟩
  refine ⟨s₁ ∪ s₂, s₁_count.union s₂_count, fun t ht => le_antisymm ?_ ?_⟩
  · have : t \ (s₁ ∪ s₂) = (t \ (s₁ ∪ s₂)) \ s₁ := by
      rw [diff_diff, union_comm, union_assoc, union_self]
    rw [this]
    exact h₁ _ (ht.mono diff_subset)
  · have : t \ (s₁ ∪ s₂) = (t \ (s₁ ∪ s₂)) \ s₂ := by rw [diff_diff, union_assoc, union_self]
    rw [this]
    simp only [neg_nonpos, neg_apply] at h₂
    exact h₂ _ (ht.mono diff_subset)
#align counterexample.phillips_1940.bounded_additive_measure.exists_discrete_support Counterexample.Phillips1940.BoundedAdditiveMeasure.exists_discrete_support

/-- A countable set outside of which the measure gives zero mass to countable sets. We are not
claiming this set is unique, but we make an arbitrary choice of such a set. -/
def discreteSupport (f : BoundedAdditiveMeasure α) : Set α :=
  (exists_discrete_support f).choose
#align counterexample.phillips_1940.bounded_additive_measure.discrete_support Counterexample.Phillips1940.BoundedAdditiveMeasure.discreteSupport

theorem countable_discreteSupport (f : BoundedAdditiveMeasure α) : f.discreteSupport.Countable :=
  (exists_discrete_support f).choose_spec.1
#align counterexample.phillips_1940.bounded_additive_measure.countable_discrete_support Counterexample.Phillips1940.BoundedAdditiveMeasure.countable_discreteSupport

theorem apply_countable (f : BoundedAdditiveMeasure α) (t : Set α) (ht : t.Countable) :
    f (t \ f.discreteSupport) = 0 :=
  (exists_discrete_support f).choose_spec.2 t ht
#align counterexample.phillips_1940.bounded_additive_measure.apply_countable Counterexample.Phillips1940.BoundedAdditiveMeasure.apply_countable

/-- The discrete part of a bounded additive measure, obtained by restricting the measure to its
countable support. -/
def discretePart (f : BoundedAdditiveMeasure α) : BoundedAdditiveMeasure α :=
  f.restrict f.discreteSupport
#align counterexample.phillips_1940.bounded_additive_measure.discrete_part Counterexample.Phillips1940.BoundedAdditiveMeasure.discretePart

/-- The continuous part of a bounded additive measure, giving zero measure to every countable
set. -/
def continuousPart (f : BoundedAdditiveMeasure α) : BoundedAdditiveMeasure α :=
  f.restrict (univ \ f.discreteSupport)
#align counterexample.phillips_1940.bounded_additive_measure.continuous_part Counterexample.Phillips1940.BoundedAdditiveMeasure.continuousPart

theorem eq_add_parts (f : BoundedAdditiveMeasure α) (s : Set α) :
    f s = f.discretePart s + f.continuousPart s := by
  simp only [discretePart, continuousPart, restrict_apply]
  rw [← f.additive, ← union_inter_distrib_right]
  · simp only [union_univ, union_diff_self, univ_inter]
  · have : Disjoint f.discreteSupport (univ \ f.discreteSupport) := disjoint_sdiff_self_right
    exact this.mono inter_subset_left inter_subset_left
#align counterexample.phillips_1940.bounded_additive_measure.eq_add_parts Counterexample.Phillips1940.BoundedAdditiveMeasure.eq_add_parts

theorem discretePart_apply (f : BoundedAdditiveMeasure α) (s : Set α) :
    f.discretePart s = f (f.discreteSupport ∩ s) :=
  rfl
#align counterexample.phillips_1940.bounded_additive_measure.discrete_part_apply Counterexample.Phillips1940.BoundedAdditiveMeasure.discretePart_apply

theorem continuousPart_apply_eq_zero_of_countable (f : BoundedAdditiveMeasure α) (s : Set α)
    (hs : s.Countable) : f.continuousPart s = 0 := by
  simp [continuousPart]
  convert f.apply_countable s hs using 2
  ext x
  simp [and_comm]
#align counterexample.phillips_1940.bounded_additive_measure.continuous_part_apply_eq_zero_of_countable Counterexample.Phillips1940.BoundedAdditiveMeasure.continuousPart_apply_eq_zero_of_countable

theorem continuousPart_apply_diff (f : BoundedAdditiveMeasure α) (s t : Set α) (hs : s.Countable) :
    f.continuousPart (t \ s) = f.continuousPart t := by
  conv_rhs => rw [← diff_union_inter t s]
  rw [additive, self_eq_add_right]
  · exact continuousPart_apply_eq_zero_of_countable _ _ (hs.mono inter_subset_right)
  · exact Disjoint.mono_right inter_subset_right disjoint_sdiff_self_left
#align counterexample.phillips_1940.bounded_additive_measure.continuous_part_apply_diff Counterexample.Phillips1940.BoundedAdditiveMeasure.continuousPart_apply_diff

end BoundedAdditiveMeasure

open BoundedAdditiveMeasure

section

/-!
### Relationship between continuous functionals and finitely additive measures.
-/


theorem norm_indicator_le_one (s : Set α) (x : α) : ‖(indicator s (1 : α → ℝ)) x‖ ≤ 1 := by
  simp only [indicator, Pi.one_apply]; split_ifs <;>
  set_option tactic.skipAssignedInstances false in norm_num
#align counterexample.phillips_1940.norm_indicator_le_one Counterexample.Phillips1940.norm_indicator_le_one

/-- A functional in the dual space of bounded functions gives rise to a bounded additive measure,
by applying the functional to the indicator functions. -/
def _root_.ContinuousLinearMap.toBoundedAdditiveMeasure [TopologicalSpace α] [DiscreteTopology α]
    (f : (α →ᵇ ℝ) →L[ℝ] ℝ) : BoundedAdditiveMeasure α where
  toFun s := f (ofNormedAddCommGroupDiscrete (indicator s 1) 1 (norm_indicator_le_one s))
  additive' s t hst := by
    dsimp only
    have :
      ofNormedAddCommGroupDiscrete (indicator (s ∪ t) 1) 1 (norm_indicator_le_one _) =
        ofNormedAddCommGroupDiscrete (indicator s 1) 1 (norm_indicator_le_one s) +
          ofNormedAddCommGroupDiscrete (indicator t 1) 1 (norm_indicator_le_one t) := by
      ext x; simp [indicator_union_of_disjoint hst]
    rw [this, f.map_add]
  exists_bound :=
    ⟨‖f‖, fun s => by
      have I :
        ‖ofNormedAddCommGroupDiscrete (indicator s 1) 1 (norm_indicator_le_one s)‖ ≤ 1 := by
        apply norm_ofNormedAddCommGroup_le _ zero_le_one
      apply le_trans (f.le_opNorm _)
      simpa using mul_le_mul_of_nonneg_left I (norm_nonneg f)⟩
#align continuous_linear_map.to_bounded_additive_measure ContinuousLinearMap.toBoundedAdditiveMeasure

@[simp]
theorem continuousPart_evalCLM_eq_zero [TopologicalSpace α] [DiscreteTopology α] (s : Set α)
    (x : α) : (evalCLM ℝ x).toBoundedAdditiveMeasure.continuousPart s = 0 :=
  let f := (evalCLM ℝ x).toBoundedAdditiveMeasure
  calc
    f.continuousPart s = f.continuousPart (s \ {x}) :=
      (continuousPart_apply_diff _ _ _ (countable_singleton x)).symm
    _ = f (univ \ f.discreteSupport ∩ (s \ {x})) := rfl
    _ = indicator (univ \ f.discreteSupport ∩ (s \ {x})) 1 x := rfl
    _ = 0 := by simp
#align counterexample.phillips_1940.continuous_part_eval_clm_eq_zero Counterexample.Phillips1940.continuousPart_evalCLM_eq_zero

theorem toFunctions_toMeasure [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (s : Set α)
    (hs : MeasurableSet s) :
    μ.extensionToBoundedFunctions.toBoundedAdditiveMeasure s = (μ s).toReal := by
  change
    μ.extensionToBoundedFunctions
        (ofNormedAddCommGroupDiscrete (indicator s 1) 1 (norm_indicator_le_one s)) =
      (μ s).toReal
  rw [extensionToBoundedFunctions_apply]
  · change ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ = _
    simp [integral_indicator hs]
  · change Integrable (indicator s 1) μ
    have : Integrable (fun _ => (1 : ℝ)) μ := integrable_const (1 : ℝ)
    apply
      this.mono' (Measurable.indicator (@measurable_const _ _ _ _ (1 : ℝ)) hs).aestronglyMeasurable
    apply Filter.eventually_of_forall
    exact norm_indicator_le_one _
#align counterexample.phillips_1940.to_functions_to_measure Counterexample.Phillips1940.toFunctions_toMeasure

theorem toFunctions_toMeasure_continuousPart [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsFiniteMeasure μ] [NoAtoms μ] (s : Set α) (hs : MeasurableSet s) :
    μ.extensionToBoundedFunctions.toBoundedAdditiveMeasure.continuousPart s = (μ s).toReal := by
  let f := μ.extensionToBoundedFunctions.toBoundedAdditiveMeasure
  change f (univ \ f.discreteSupport ∩ s) = (μ s).toReal
  rw [toFunctions_toMeasure]; swap
  · exact
      MeasurableSet.inter
        (MeasurableSet.univ.diff (Countable.measurableSet f.countable_discreteSupport)) hs
  congr 1
  rw [inter_comm, ← inter_diff_assoc, inter_univ]
  exact measure_diff_null (f.countable_discreteSupport.measure_zero _)
#align counterexample.phillips_1940.to_functions_to_measure_continuous_part Counterexample.Phillips1940.toFunctions_toMeasure_continuousPart

end

/-!
### A set in `ℝ²` large along verticals, small along horizontals

We construct a subset of `ℝ²`, given as a family of sets, which is large along verticals (i.e.,
it only misses a countable set along each vertical) but small along horizontals (it is countable
along horizontals). Such a set can not be measurable as it would contradict Fubini theorem.
We need the continuum hypothesis to construct it.
-/


theorem sierpinski_pathological_family (Hcont : #ℝ = aleph 1) :
    ∃ f : ℝ → Set ℝ, (∀ x, (univ \ f x).Countable) ∧ ∀ y, {x : ℝ | y ∈ f x}.Countable := by
  rcases Cardinal.ord_eq ℝ with ⟨r, hr, H⟩
  refine ⟨fun x => {y | r x y}, fun x => ?_, fun y => ?_⟩
  · have : univ \ {y | r x y} = {y | r y x} ∪ {x} := by
      ext y
      simp only [true_and_iff, mem_univ, mem_setOf_eq, mem_insert_iff, union_singleton, mem_diff]
      rcases trichotomous_of r x y with (h | rfl | h)
      · simp only [h, not_or, false_iff_iff, not_true]
        constructor
        · rintro rfl; exact irrefl_of r y h
        · exact asymm h
      · simp only [true_or_iff, eq_self_iff_true, iff_true_iff]; exact irrefl x
      · simp only [h, iff_true_iff, or_true_iff]; exact asymm h
    rw [this]
    apply Countable.union _ (countable_singleton _)
    rw [Cardinal.countable_iff_lt_aleph_one, ← Hcont]
    exact Cardinal.card_typein_lt r x H
  · rw [Cardinal.countable_iff_lt_aleph_one, ← Hcont]
    exact Cardinal.card_typein_lt r y H
#align counterexample.phillips_1940.sierpinski_pathological_family Counterexample.Phillips1940.sierpinski_pathological_family

/-- A family of sets in `ℝ` which only miss countably many points, but such that any point is
contained in only countably many of them. -/
def spf (Hcont : #ℝ = aleph 1) (x : ℝ) : Set ℝ :=
  (sierpinski_pathological_family Hcont).choose x
#align counterexample.phillips_1940.spf Counterexample.Phillips1940.spf

theorem countable_compl_spf (Hcont : #ℝ = aleph 1) (x : ℝ) : (univ \ spf Hcont x).Countable :=
  (sierpinski_pathological_family Hcont).choose_spec.1 x
#align counterexample.phillips_1940.countable_compl_spf Counterexample.Phillips1940.countable_compl_spf

theorem countable_spf_mem (Hcont : #ℝ = aleph 1) (y : ℝ) : {x | y ∈ spf Hcont x}.Countable :=
  (sierpinski_pathological_family Hcont).choose_spec.2 y
#align counterexample.phillips_1940.countable_spf_mem Counterexample.Phillips1940.countable_spf_mem

/-!
### A counterexample for the Pettis integral

We construct a function `f` from `[0,1]` to a complete Banach space `B`, which is weakly measurable
(i.e., for any continuous linear form `φ` on `B` the function `φ ∘ f` is measurable), bounded in
norm (i.e., for all `x`, one has `‖f x‖ ≤ 1`), and still `f` has no Pettis integral.

This construction, due to Phillips, requires the continuum hypothesis. We will take for `B` the
space of all bounded functions on `ℝ`, with the supremum norm (no measure here, we are really
talking of everywhere defined functions). And `f x` will be the characteristic function of a set
which is large (it has countable complement), as in the Sierpinski pathological family.
-/


/-- A family of bounded functions `f_x` from `ℝ` (seen with the discrete topology) to `ℝ` (in fact
taking values in `{0, 1}`), indexed by a real parameter `x`, corresponding to the characteristic
functions of the different fibers of the Sierpinski pathological family -/
def f (Hcont : #ℝ = aleph 1) (x : ℝ) : DiscreteCopy ℝ →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (indicator (spf Hcont x) 1) 1 (norm_indicator_le_one _)
#align counterexample.phillips_1940.f Counterexample.Phillips1940.f

theorem apply_f_eq_continuousPart (Hcont : #ℝ = aleph 1) (φ : (DiscreteCopy ℝ →ᵇ ℝ) →L[ℝ] ℝ)
    (x : ℝ) (hx : φ.toBoundedAdditiveMeasure.discreteSupport ∩ spf Hcont x = ∅) :
    φ (f Hcont x) = φ.toBoundedAdditiveMeasure.continuousPart univ := by
  set ψ := φ.toBoundedAdditiveMeasure
  have : φ (f Hcont x) = ψ (spf Hcont x) := rfl
  have U : univ = spf Hcont x ∪ univ \ spf Hcont x := by simp only [union_univ, union_diff_self]
  rw [this, eq_add_parts, discretePart_apply, hx, ψ.empty, zero_add, U,
    ψ.continuousPart.additive _ _ disjoint_sdiff_self_right,
    ψ.continuousPart_apply_eq_zero_of_countable _ (countable_compl_spf Hcont x), add_zero]
#align counterexample.phillips_1940.apply_f_eq_continuous_part Counterexample.Phillips1940.apply_f_eq_continuousPart

theorem countable_ne (Hcont : #ℝ = aleph 1) (φ : (DiscreteCopy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
    {x | φ.toBoundedAdditiveMeasure.continuousPart univ ≠ φ (f Hcont x)}.Countable := by
  have A :
    {x | φ.toBoundedAdditiveMeasure.continuousPart univ ≠ φ (f Hcont x)} ⊆
      {x | φ.toBoundedAdditiveMeasure.discreteSupport ∩ spf Hcont x ≠ ∅} := by
    intro x hx
    simp only [mem_setOf] at *
    contrapose! hx
    exact apply_f_eq_continuousPart Hcont φ x hx |>.symm
  have B :
    {x | φ.toBoundedAdditiveMeasure.discreteSupport ∩ spf Hcont x ≠ ∅} ⊆
      ⋃ y ∈ φ.toBoundedAdditiveMeasure.discreteSupport, {x | y ∈ spf Hcont x} := by
    intro x hx
    dsimp at hx
    rw [← Ne, ← nonempty_iff_ne_empty] at hx
    simp only [exists_prop, mem_iUnion, mem_setOf_eq]
    exact hx
  apply Countable.mono (Subset.trans A B)
  exact Countable.biUnion (countable_discreteSupport _) fun a _ => countable_spf_mem Hcont a
#align counterexample.phillips_1940.countable_ne Counterexample.Phillips1940.countable_ne

theorem comp_ae_eq_const (Hcont : #ℝ = aleph 1) (φ : (DiscreteCopy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
    ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) 1),
      φ.toBoundedAdditiveMeasure.continuousPart univ = φ (f Hcont x) := by
  apply ae_restrict_of_ae
  refine measure_mono_null ?_ ((countable_ne Hcont φ).measure_zero _)
  intro x
  simp only [imp_self, mem_setOf_eq, mem_compl_iff]
#align counterexample.phillips_1940.comp_ae_eq_const Counterexample.Phillips1940.comp_ae_eq_const

theorem integrable_comp (Hcont : #ℝ = aleph 1) (φ : (DiscreteCopy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
    IntegrableOn (fun x => φ (f Hcont x)) (Icc 0 1) := by
  have :
    IntegrableOn (fun _ => φ.toBoundedAdditiveMeasure.continuousPart univ) (Icc (0 : ℝ) 1)
      volume := by
    simp [integrableOn_const]
  apply Integrable.congr this (comp_ae_eq_const Hcont φ)
#align counterexample.phillips_1940.integrable_comp Counterexample.Phillips1940.integrable_comp

theorem integral_comp (Hcont : #ℝ = aleph 1) (φ : (DiscreteCopy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
    ∫ x in Icc 0 1, φ (f Hcont x) = φ.toBoundedAdditiveMeasure.continuousPart univ := by
  rw [← integral_congr_ae (comp_ae_eq_const Hcont φ)]
  simp
#align counterexample.phillips_1940.integral_comp Counterexample.Phillips1940.integral_comp

/-!
The next few statements show that the function `f Hcont : ℝ → (DiscreteCopy ℝ →ᵇ ℝ)` takes its
values in a complete space, is scalarly measurable, is everywhere bounded by `1`, and still has
no Pettis integral.
-/


example : CompleteSpace (DiscreteCopy ℝ →ᵇ ℝ) := by infer_instance

/-- The function `f Hcont : ℝ → (DiscreteCopy ℝ →ᵇ ℝ)` is scalarly measurable. -/
theorem measurable_comp (Hcont : #ℝ = aleph 1) (φ : (DiscreteCopy ℝ →ᵇ ℝ) →L[ℝ] ℝ) :
    Measurable fun x => φ (f Hcont x) := by
  have : Measurable fun _ : ℝ => φ.toBoundedAdditiveMeasure.continuousPart univ := measurable_const
  refine this.measurable_of_countable_ne ?_
  exact countable_ne Hcont φ
#align counterexample.phillips_1940.measurable_comp Counterexample.Phillips1940.measurable_comp

/-- The function `f Hcont : ℝ → (DiscreteCopy ℝ →ᵇ ℝ)` is uniformly bounded by `1` in norm. -/
theorem norm_bound (Hcont : #ℝ = aleph 1) (x : ℝ) : ‖f Hcont x‖ ≤ 1 :=
  norm_ofNormedAddCommGroup_le _ zero_le_one (norm_indicator_le_one _)
#align counterexample.phillips_1940.norm_bound Counterexample.Phillips1940.norm_bound

/-- The function `f Hcont : ℝ → (DiscreteCopy ℝ →ᵇ ℝ)` has no Pettis integral. -/
theorem no_pettis_integral (Hcont : #ℝ = aleph 1) :
    ¬∃ g : DiscreteCopy ℝ →ᵇ ℝ,
        ∀ φ : (DiscreteCopy ℝ →ᵇ ℝ) →L[ℝ] ℝ, ∫ x in Icc 0 1, φ (f Hcont x) = φ g := by
  rintro ⟨g, h⟩
  simp only [integral_comp] at h
  have : g = 0 := by
    ext x
    have : g x = evalCLM ℝ x g := rfl
    rw [this, ← h]
    simp
  simp only [this, ContinuousLinearMap.map_zero] at h
  specialize h (volume.restrict (Icc (0 : ℝ) 1)).extensionToBoundedFunctions
  simp_rw [toFunctions_toMeasure_continuousPart _ _ MeasurableSet.univ] at h
  simp at h
#align counterexample.phillips_1940.no_pettis_integral Counterexample.Phillips1940.no_pettis_integral

end Phillips1940

end

end Counterexample
