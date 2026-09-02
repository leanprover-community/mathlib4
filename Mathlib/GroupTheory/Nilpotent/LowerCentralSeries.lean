/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ines Wright, Joachim Breitner
-/
module

public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.GroupTheory.Solvable

/-!

# Lower Central Series

This file defines the lower central series of a subgroup.

## Main definitions

Recall that if `H K : Subgroup G` then `⁅H, K⁆ : Subgroup G` is the subgroup of `G` generated
by the commutators `h * k * h⁻¹ * k⁻¹`. Recall also Lean's conventions that `⊤` denotes the
subgroup `G` of `G`, and `⊥` denotes the trivial subgroup `{1}`.

* `Subgroup.lowerCentralSeries (H : Subgroup G) : ℕ → Subgroup G` : the lower central series of `H`,
    computed in the ambient group `G`. This is the iterated commutators `H, ⁅H, H⁆, ⁅⁅H, H⁆, H⁆, …`.
    The classical lower central series of `G` is the case `H = ⊤`.
* `IsDescendingCentralSeries (H : ℕ → Subgroup G) : Prop` : Note that in the literature
    a "central series" for a group is usually defined to be a *finite* sequence of normal subgroups
    `H 0`, `H 1`, ..., starting at `⊤`, finishing at `⊥`, and with each `H n / H (n + 1)`
    central in `G / H (n + 1)`. In this formalisation it is convenient to have a weaker predicate
    on an infinite sequence of subgroups `H n` of `G`: we say a sequence is a *descending central
    series* if it starts at `G` and `⁅H n, ⊤⁆ ⊆ H (n + 1)` for all `n`. Note that this series
    may not terminate at `⊥`, and the `H i` need not be normal.

-/

@[expose] public section

open scoped commutatorElement

variable {G : Type*} [Group G] (H N : Subgroup G) [N.Normal]

namespace Subgroup

/-- A sequence of subgroups of `G` is a descending central series if `H 0` is `G` and
`⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. Note that we do not require that `H n = {1}` for some `n`. -/
@[to_additive /-- A sequence of additive subgroups of `G` is a descending central series if `H 0` is
`G` and `⁅H n, G⁆ ⊆ H (n + 1)` for all `n`. We do not require that `H n = {1}` for some `n`. -/]
def IsDescendingCentralSeries (H : ℕ → Subgroup G) :=
  H 0 = ⊤ ∧ ∀ (x : G) (n : ℕ), x ∈ H n → ∀ g, ⁅x, g⁆ ∈ H (n + 1)

/-- The lower central series of an additive subgroup `S` of `G`, computed in the ambient additive
group `G`. -/
def _root_.AddSubgroup.lowerCentralSeries {G : Type*} [AddGroup G] (S : AddSubgroup G) :
    ℕ → AddSubgroup G
  | 0 => S
  | n + 1 => ⁅lowerCentralSeries S n, S⁆

/-- The lower central series of a subgroup `S` of `G`, computed in the ambient group `G`.
This is the iterated commutator `⁅⁅⋯⁅S, S⁆, S⁆⋯, S⁆`, a subgroup of `G`. The lower central series
of `G` itself is the case `S = ⊤`. -/
@[to_additive existing]
def lowerCentralSeries (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅lowerCentralSeries H n, H⁆

@[to_additive (attr := simp)]
theorem lowerCentralSeries_zero : H.lowerCentralSeries 0 = H := rfl

@[to_additive (attr := simp)]
theorem lowerCentralSeries_succ (n : ℕ) :
    H.lowerCentralSeries (n + 1) = ⁅H.lowerCentralSeries n, H⁆ := rfl

@[to_additive top_lowerCentralSeries_one]
theorem top_lowerCentralSeries_one : (⊤ : Subgroup G).lowerCentralSeries 1 = _root_.commutator G :=
  rfl

@[deprecated (since := "2026-05-25")]
alias _root_.AddSubgroup.lowerCentralSeries_one := AddSubgroup.top_lowerCentralSeries_one

@[to_additive existing lowerCentralSeries_one, deprecated (since := "2026-05-25")]
alias lowerCentralSeries_one := top_lowerCentralSeries_one

@[to_additive]
theorem mem_lowerCentralSeries_succ_iff (n : ℕ) (q : G) :
    q ∈ H.lowerCentralSeries (n + 1) ↔
    q ∈ closure { x | ∃ p ∈ H.lowerCentralSeries n, ∃ q ∈ H, ⁅p, q⁆ = x } := Iff.rfl

@[to_additive]
instance lowerCentralSeries_normal (n : ℕ) : (N.lowerCentralSeries n).Normal := by
  induction n with
  | zero => simpa
  | succ n _ => rw [lowerCentralSeries_succ]; infer_instance

@[to_additive]
instance lowerCentralSeries_characteristic [H.Characteristic] (n : ℕ) :
    (H.lowerCentralSeries n).Characteristic := by
  induction n with
  | zero => simpa
  | succ d _ => rw [lowerCentralSeries_succ]; infer_instance

@[to_additive]
theorem self_le_normalizer_lowerCentralSeries :
    ∀ n, H ≤ Subgroup.normalizer (H.lowerCentralSeries n : Set G)
  | 0 => Subgroup.le_normalizer
  | n + 1 => by
    rw [lowerCentralSeries_succ]
    apply normalizer_commutator_ge_right

@[to_additive]
theorem lowerCentralSeries_antitone : Antitone H.lowerCentralSeries := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [lowerCentralSeries_succ, ← le_normalizer_iff_commutator_le_left]
  exact H.self_le_normalizer_lowerCentralSeries n

/-- The lower central series of a group is a descending central series. -/
@[to_additive /-- The lower central series of an additive group is a descending central series. -/]
theorem lowerCentralSeries_isDescendingCentralSeries :
    IsDescendingCentralSeries (G := G) (lowerCentralSeries ⊤) := by
  constructor
  · rfl
  intro x n hxn g
  exact commutator_mem_commutator hxn (mem_top g)

/-- Any descending central series for a group is bounded below by the lower central series. -/
@[to_additive /-- Any descending central series for an additive group is bounded below by the lower
central series. -/]
theorem descending_central_series_ge_lower (H : ℕ → Subgroup G) (hH : IsDescendingCentralSeries H) :
    ∀ n : ℕ, lowerCentralSeries ⊤ n ≤ H n
  | 0 => hH.1.symm ▸ le_refl ⊤
  | n + 1 => commutator_le.mpr fun x hx q _ =>
      hH.2 x n (descending_central_series_ge_lower H hH n hx) q

/-- The lower central series commutes with images under a group homomorphism. -/
@[to_additive
/-- The lower central series commutes with images under an additive group homomorphism. -/]
theorem map_lowerCentralSeries {G' : Type*} [Group G'] (f : G →* G') (n : ℕ) :
    (H.lowerCentralSeries n).map f = (H.map f).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ d hd =>
    rw [lowerCentralSeries_succ, lowerCentralSeries_succ, Subgroup.map_commutator, hd]

/-- The lower central series of `H : Subgroup G` computed in the ambient group `G` coincides with
the lower central series of `H` viewed as its own group, mapped back to `G`. -/
@[to_additive (attr := simp)
/-- The lower central series of `H : AddSubgroup G` computed in the ambient additive group `G`
coincides with the lower central series of `H` viewed as its own additive group, mapped back
to `G`. -/]
theorem top_subtype_lowerCentralSeries (n : ℕ) :
    (lowerCentralSeries ⊤ n).map H.subtype = H.lowerCentralSeries n := by
  rw [map_lowerCentralSeries, ← MonoidHom.range_eq_map, subtype_range]

@[to_additive]
theorem lowerCentralSeries_le_self (n : ℕ) : H.lowerCentralSeries n ≤ H := by
  simpa using H.lowerCentralSeries_antitone (Nat.zero_le n)

@[to_additive]
theorem lowerCentralSeries_mono (n : ℕ) :
    Monotone (fun H : Subgroup G ↦ H.lowerCentralSeries n) := by
  induction n with
  | zero => intro S T h; simpa
  | succ d hd => intro S T h; simp only [lowerCentralSeries_succ]; exact commutator_mono (hd h) h

@[to_additive (attr := deprecated "Use `top_subtype_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-27"))]
theorem lowerCentralSeries_map_subtype_le (n : ℕ) :
    ((⊤ : Subgroup H).lowerCentralSeries n).map H.subtype ≤ lowerCentralSeries ⊤ n := by
  rw [top_subtype_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive (attr := deprecated "Use `map_lowerCentralSeries` and \
  `lowerCentralSeries_mono` instead." (since := "2026-05-28"))]
theorem lowerCentralSeries.map {G' : Type*} [Group G'] (f : G →* G') (n : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries n).map f ≤ (⊤ : Subgroup G').lowerCentralSeries n := by
  rw [map_lowerCentralSeries]
  exact lowerCentralSeries_mono n le_top

@[to_additive]
theorem lowerCentralSeries_succ_eq_bot {n : ℕ} (h : H.lowerCentralSeries n ≤ center G) :
    H.lowerCentralSeries (n + 1) = ⊥ := by
  grw [eq_bot_iff, lowerCentralSeries_succ, h, commutator_center_left]

-- todo: namespace `derivedSeries` and to_additivize.
theorem derived_le_lower_central (n : ℕ) : derivedSeries G n ≤ lowerCentralSeries ⊤ n := by
  induction n with
  | zero => simp
  | succ i ih => apply commutator_mono ih; simp

section Prod

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

@[to_additive]
theorem lowerCentralSeries_prod (H₁ : Subgroup G₁) (H₂ : Subgroup G₂) (n : ℕ) :
    (H₁.prod H₂).lowerCentralSeries n =
      (H₁.lowerCentralSeries n).prod (H₂.lowerCentralSeries n) := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_prod_prod]

/-- The `⊤`-specialization of `lowerCentralSeries_prod`. -/
@[to_additive /-- The `⊤`-specialization of `lowerCentralSeries_sum`. -/]
theorem top_lowerCentralSeries_prod (n : ℕ) :
    (⊤ : Subgroup (G₁ × G₂)).lowerCentralSeries n =
      ((⊤ : Subgroup G₁).lowerCentralSeries n).prod ((⊤ : Subgroup G₂).lowerCentralSeries n) := by
  rw [← lowerCentralSeries_prod, top_prod_top]

end Prod

section Pi

variable {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]

@[to_additive]
theorem lowerCentralSeries_pi_le (Hs : ∀ i, Subgroup (Gs i)) (n : ℕ) :
    (pi Set.univ Hs).lowerCentralSeries n ≤ pi Set.univ fun i ↦ (Hs i).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp_rw [lowerCentralSeries_succ]
    grw [ih, commutator_pi_pi_le]

/-- The `⊤`-specialization of `lowerCentralSeries_pi_le`. -/
@[to_additive /-- The `⊤`-specialization of `lowerCentralSeries_pi_le`. -/]
theorem top_lowerCentralSeries_pi_le (n : ℕ) :
    (⊤ : Subgroup (∀ i, Gs i)).lowerCentralSeries n ≤
      pi Set.univ fun i ↦ (⊤ : Subgroup (Gs i)).lowerCentralSeries n := by
  grw [← lowerCentralSeries_pi_le, pi_top]

variable [Finite η]

@[to_additive]
theorem lowerCentralSeries_pi_of_finite (Hs : ∀ i, Subgroup (Gs i)) (n : ℕ) :
    (pi Set.univ Hs).lowerCentralSeries n = pi Set.univ fun i ↦ (Hs i).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_pi_pi_of_finite]

/-- The `⊤`-specialization of `lowerCentralSeries_pi_of_finite`. -/
@[to_additive /-- The `⊤`-specialization of `lowerCentralSeries_pi_of_finite`. -/]
theorem top_lowerCentralSeries_pi_of_finite (n : ℕ) :
    (⊤ : Subgroup (∀ i, Gs i)).lowerCentralSeries n =
      pi Set.univ fun i ↦ (⊤ : Subgroup (Gs i)).lowerCentralSeries n := by
  rw [← lowerCentralSeries_pi_of_finite, pi_top]

end Pi

end Subgroup
