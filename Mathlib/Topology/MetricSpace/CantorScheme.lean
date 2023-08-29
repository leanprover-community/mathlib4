/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import Mathlib.Topology.MetricSpace.PiNat

#align_import topology.metric_space.cantor_scheme from "leanprover-community/mathlib"@"49b7f94aab3a3bdca1f9f34c5d818afb253b3993"

/-!
# (Topological) Schemes and their induced maps

In topology, and especially descriptive set theory, one often constructs functions `(ℕ → β) → α`,
where α is some topological space and β is a discrete space, as an appropriate limit of some map
`List β → Set α`. We call the latter type of map a "`β`-scheme on `α`".

This file develops the basic, abstract theory of these schemes and the functions they induce.

## Main Definitions

* `CantorScheme.inducedMap A` : The aforementioned "limit" of a scheme `A : List β → Set α`.
  This is a partial function from `ℕ → β` to `a`,
  implemented here as an object of type `Σ s : Set (ℕ → β), s → α`.
  That is, `(inducedMap A).1` is the domain and `(inducedMap A).2` is the function.

## Implementation Notes

We consider end-appending to be the fundamental way to build lists (say on `β`) inductively,
as this interacts better with the topology on `ℕ → β`.
As a result, functions like `List.get?` or `Stream'.take` do not have their intended meaning
in this file. See instead `PiNat.res`.

## References

* [kechris1995] (Chapters 6-7)

## Tags

scheme, cantor scheme, lusin scheme, approximation.

-/


namespace CantorScheme

open List Function Filter Set PiNat

open Classical Topology

variable {β α : Type*} (A : List β → Set α)

/-- From a `β`-scheme on `α` `A`, we define a partial function from `(ℕ → β)` to `α`
which sends each infinite sequence `x` to an element of the intersection along the
branch corresponding to `x`, if it exists.
We call this the map induced by the scheme. -/
noncomputable def inducedMap : Σs : Set (ℕ → β), s → α :=
  ⟨fun x => Set.Nonempty (⋂ n : ℕ, A (res x n)), fun x => x.property.some⟩
#align cantor_scheme.induced_map CantorScheme.inducedMap

section Topology

/-- A scheme is antitone if each set contains its children. -/
protected def Antitone : Prop :=
  ∀ l : List β, ∀ a : β, A (a :: l) ⊆ A l
#align cantor_scheme.antitone CantorScheme.Antitone

/-- A useful strengthening of being antitone is to require that each set contains
the closure of each of its children. -/
def ClosureAntitone [TopologicalSpace α] : Prop :=
  ∀ l : List β, ∀ a : β, closure (A (a :: l)) ⊆ A l
#align cantor_scheme.closure_antitone CantorScheme.ClosureAntitone

/-- A scheme is disjoint if the children of each set of pairwise disjoint. -/
protected def Disjoint : Prop :=
  ∀ l : List β, Pairwise fun a b => Disjoint (A (a :: l)) (A (b :: l))
#align cantor_scheme.disjoint CantorScheme.Disjoint

variable {A}

/-- If `x` is in the domain of the induced map of a scheme `A`,
its image under this map is in each set along the corresponding branch. -/
theorem map_mem (x : (inducedMap A).1) (n : ℕ) : (inducedMap A).2 x ∈ A (res x n) := by
  have := x.property.some_mem
  -- ⊢ Sigma.snd (inducedMap A) x ∈ A (res (↑x) n)
  rw [mem_iInter] at this
  -- ⊢ Sigma.snd (inducedMap A) x ∈ A (res (↑x) n)
  exact this n
  -- 🎉 no goals
#align cantor_scheme.map_mem CantorScheme.map_mem

protected theorem ClosureAntitone.antitone [TopologicalSpace α] (hA : ClosureAntitone A) :
    CantorScheme.Antitone A := fun l a => subset_closure.trans (hA l a)
#align cantor_scheme.closure_antitone.antitone CantorScheme.ClosureAntitone.antitone

protected theorem Antitone.closureAntitone [TopologicalSpace α] (hanti : CantorScheme.Antitone A)
    (hclosed : ∀ l, IsClosed (A l)) : ClosureAntitone A := fun _ _ =>
  (hclosed _).closure_eq.subset.trans (hanti _ _)
#align cantor_scheme.antitone.closure_antitone CantorScheme.Antitone.closureAntitone

/-- A scheme where the children of each set are pairwise disjoint induces an injective map. -/
theorem Disjoint.map_injective (hA : CantorScheme.Disjoint A) : Injective (inducedMap A).2 := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  -- ⊢ { val := x, property := hx } = { val := y, property := hy }
  refine' Subtype.coe_injective (res_injective _)
  -- ⊢ res ((fun a => ↑a) { val := x, property := hx }) = res ((fun a => ↑a) { val  …
  dsimp
  -- ⊢ res x = res y
  ext n : 1
  -- ⊢ res x n = res y n
  induction' n with n ih; · simp
  -- ⊢ res x Nat.zero = res y Nat.zero
                            -- 🎉 no goals
  simp only [res_succ, cons.injEq]
  -- ⊢ x n = y n ∧ res x n = res y n
  refine' ⟨_, ih⟩
  -- ⊢ x n = y n
  contrapose hA
  -- ⊢ ¬CantorScheme.Disjoint A
  simp only [CantorScheme.Disjoint, _root_.Pairwise, Ne.def, not_forall, exists_prop]
  -- ⊢ ∃ x x_1 x_2, ¬x_1 = x_2 ∧ ¬_root_.Disjoint (A (x_1 :: x)) (A (x_2 :: x))
  refine' ⟨res x n, _, _, hA, _⟩
  -- ⊢ ¬_root_.Disjoint (A (x n :: res x n)) (A (y n :: res x n))
  rw [not_disjoint_iff]
  -- ⊢ ∃ x_1, x_1 ∈ A (x n :: res x n) ∧ x_1 ∈ A (y n :: res x n)
  refine' ⟨(inducedMap A).2 ⟨x, hx⟩, _, _⟩
  -- ⊢ Sigma.snd (inducedMap A) { val := x, property := hx } ∈ A (x n :: res x n)
  · rw [← res_succ]
    -- ⊢ Sigma.snd (inducedMap A) { val := x, property := hx } ∈ A (res x (Nat.succ n))
    apply map_mem
    -- 🎉 no goals
  rw [hxy, ih, ← res_succ]
  -- ⊢ Sigma.snd (inducedMap A) { val := y, property := hy } ∈ A (res y (Nat.succ n))
  apply map_mem
  -- 🎉 no goals
#align cantor_scheme.disjoint.map_injective CantorScheme.Disjoint.map_injective

end Topology

section Metric

variable [PseudoMetricSpace α]

/-- A scheme on a metric space has vanishing diameter if diameter approaches 0 along each branch. -/
def VanishingDiam : Prop :=
  ∀ x : ℕ → β, Tendsto (fun n : ℕ => EMetric.diam (A (res x n))) atTop (𝓝 0)
#align cantor_scheme.vanishing_diam CantorScheme.VanishingDiam

variable {A}

theorem VanishingDiam.dist_lt (hA : VanishingDiam A) (ε : ℝ) (ε_pos : 0 < ε) (x : ℕ → β) :
    ∃ n : ℕ, ∀ (y) (_ : y ∈ A (res x n)) (z) (_ : z ∈ A (res x n)), dist y z < ε := by
  specialize hA x
  -- ⊢ ∃ n, ∀ (y : α), y ∈ A (res x n) → ∀ (z : α), z ∈ A (res x n) → dist y z < ε
  rw [ENNReal.tendsto_atTop_zero] at hA
  -- ⊢ ∃ n, ∀ (y : α), y ∈ A (res x n) → ∀ (z : α), z ∈ A (res x n) → dist y z < ε
  cases' hA (ENNReal.ofReal (ε / 2)) (by
    simp only [gt_iff_lt, ENNReal.ofReal_pos]
    linarith) with n hn
  use n
  -- ⊢ ∀ (y : α), y ∈ A (res x n) → ∀ (z : α), z ∈ A (res x n) → dist y z < ε
  intro y hy z hz
  -- ⊢ dist y z < ε
  rw [← ENNReal.ofReal_lt_ofReal_iff ε_pos, ← edist_dist]
  -- ⊢ edist y z < ENNReal.ofReal ε
  apply lt_of_le_of_lt (EMetric.edist_le_diam_of_mem hy hz)
  -- ⊢ EMetric.diam (A (res x n)) < ENNReal.ofReal ε
  apply lt_of_le_of_lt (hn _ (le_refl _))
  -- ⊢ ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε
  rw [ENNReal.ofReal_lt_ofReal_iff ε_pos]
  -- ⊢ ε / 2 < ε
  linarith
  -- 🎉 no goals
#align cantor_scheme.vanishing_diam.dist_lt CantorScheme.VanishingDiam.dist_lt

/-- A scheme with vanishing diameter along each branch induces a continuous map. -/
theorem VanishingDiam.map_continuous [TopologicalSpace β] [DiscreteTopology β]
    (hA : VanishingDiam A) : Continuous (inducedMap A).2 := by
  rw [Metric.continuous_iff']
  -- ⊢ ∀ (a : ↑(inducedMap A).fst) (ε : ℝ), ε > 0 → ∀ᶠ (x : ↑(inducedMap A).fst) in …
  rintro ⟨x, hx⟩ ε ε_pos
  -- ⊢ ∀ᶠ (x_1 : ↑(inducedMap A).fst) in 𝓝 { val := x, property := hx }, dist (Sigm …
  cases' hA.dist_lt _ ε_pos x with n hn
  -- ⊢ ∀ᶠ (x_1 : ↑(inducedMap A).fst) in 𝓝 { val := x, property := hx }, dist (Sigm …
  rw [_root_.eventually_nhds_iff]
  -- ⊢ ∃ t, (∀ (x_1 : ↑(inducedMap A).fst), x_1 ∈ t → dist (Sigma.snd (inducedMap A …
  refine' ⟨(↑)⁻¹' cylinder x n, _, _, by simp⟩
  -- ⊢ ∀ (x_1 : ↑(inducedMap A).fst), x_1 ∈ Subtype.val ⁻¹' cylinder x n → dist (Si …
  · rintro ⟨y, hy⟩ hyx
    -- ⊢ dist (Sigma.snd (inducedMap A) { val := y, property := hy }) (Sigma.snd (ind …
    rw [mem_preimage, Subtype.coe_mk, cylinder_eq_res, mem_setOf] at hyx
    -- ⊢ dist (Sigma.snd (inducedMap A) { val := y, property := hy }) (Sigma.snd (ind …
    apply hn
    -- ⊢ Sigma.snd (inducedMap A) { val := y, property := hy } ∈ A (res x n)
    · rw [← hyx]
      -- ⊢ Sigma.snd (inducedMap A) { val := y, property := hy } ∈ A (res y n)
      apply map_mem
      -- 🎉 no goals
    apply map_mem
    -- 🎉 no goals
  apply continuous_subtype_val.isOpen_preimage
  -- ⊢ IsOpen (cylinder x n)
  apply isOpen_cylinder
  -- 🎉 no goals
#align cantor_scheme.vanishing_diam.map_continuous CantorScheme.VanishingDiam.map_continuous

/-- A scheme on a complete space with vanishing diameter
such that each set contains the closure of its children
induces a total map. -/
theorem ClosureAntitone.map_of_vanishingDiam [CompleteSpace α] (hdiam : VanishingDiam A)
    (hanti : ClosureAntitone A) (hnonempty : ∀ l, (A l).Nonempty) : (inducedMap A).1 = univ := by
  rw [eq_univ_iff_forall]
  -- ⊢ ∀ (x : ℕ → β), x ∈ (inducedMap A).fst
  intro x
  -- ⊢ x ∈ (inducedMap A).fst
  choose u hu using fun n => hnonempty (res x n)
  -- ⊢ x ∈ (inducedMap A).fst
  have umem : ∀ n m : ℕ, n ≤ m → u m ∈ A (res x n) := by
    have : Antitone fun n : ℕ => A (res x n) := by
      refine' antitone_nat_of_succ_le _
      intro n
      apply hanti.antitone
    intro n m hnm
    exact this hnm (hu _)
  have : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε ε_pos
    cases' hdiam.dist_lt _ ε_pos x with n hn
    use n
    intro m₀ hm₀ m₁ hm₁
    apply hn <;> apply umem <;> assumption
  cases' cauchySeq_tendsto_of_complete this with y hy
  -- ⊢ x ∈ (inducedMap A).fst
  use y
  -- ⊢ y ∈ ⋂ (n : ℕ), A (res x n)
  rw [mem_iInter]
  -- ⊢ ∀ (i : ℕ), y ∈ A (res x i)
  intro n
  -- ⊢ y ∈ A (res x n)
  apply hanti _ (x n)
  -- ⊢ y ∈ closure (A (x n :: res x n))
  apply mem_closure_of_tendsto hy
  -- ⊢ ∀ᶠ (x_1 : ℕ) in atTop, u x_1 ∈ A (x n :: res x n)
  rw [eventually_atTop]
  -- ⊢ ∃ a, ∀ (b : ℕ), b ≥ a → u b ∈ A (x n :: res x n)
  exact ⟨n.succ, umem _⟩
  -- 🎉 no goals
#align cantor_scheme.closure_antitone.map_of_vanishing_diam CantorScheme.ClosureAntitone.map_of_vanishingDiam

end Metric

end CantorScheme
