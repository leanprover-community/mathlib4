/-
Copyright (c) 2025 Michael Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Lee
-/
module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Zorn
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Maximal Solutions to Ordinary Differential Equations

This file defines the concept of a maximal integral curve of an ODE `x' = v(t, x)` with initial
condition `x(t₀) = x₀`. It proves that under the conditions of the Picard-Lindelöf theorem,
such a maximal integral curve exists. Some auxiliary structures (e.g. `IsLocalIntegralCurveOn`) are
introduced only for the Zorn's Lemma proof and are not intended for public use.

The strategy involves using Zorn's Lemma on the set of all local integral curves, ordered by
extension. Picard-Lindelöf's theorem provides the existence of at least one local integral curve,
ensuring the set is non-empty. The core of the Zorn's Lemma application is showing that
every chain of integral curves has an upper bound, constructed by "gluing" the integral curves in
the chain together.

## Main Definitions

* `IsMaximalIntegralCurveOn`: Predicate stating that an integral curve `(f, I)` cannot be extended
  to an integral curve on any strictly larger open preconnected domain.

## Main Theorem

* `exists_maximal_integralCurveOn`: Under Picard-Lindelöf conditions (ensuring local existence
  on an open interval around `t₀`), there exists a function `f` and an open preconnected set `I`
  (an open interval) such that `(f, I)` is a maximal integral curve.

## TODO

* Implement the compact exit lemma ("lemme des bouts").
-/

@[expose] public section

open Set Filter NNReal Topology TopologicalSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (v : ℝ → E → E) (t₀ : ℝ) (x₀ : E)

/--
An integral curve `(f, I)` of `x' = v(t, x)` is maximal if it cannot be extended
to an integral curve on any strictly larger open preconnected domain `J`.
Initial conditions are added as separate hypotheses in the theorems below.
-/
structure IsMaximalIntegralCurveOn (v : ℝ → E → E) (f : ℝ → E) (I : Set ℝ) : Prop where
  /-- The domain `I` must be an open set. -/
  isOpen_domain : IsOpen I
  /-- The domain `I` must be preconnected. -/
  isPreconnected_domain : IsPreconnected I
  /-- The function `f` must have the derivative `v t (f t)` at every point `t` in `I`. -/
  isIntegralCurveOn : IsIntegralCurveOn f v I
  /-- The maximality condition: If `(g, J)` is another integral curve such that `I ⊆ J`
  and `f` agrees with `g` on `I`, then `I` must be equal to `J`. -/
  is_maximal : ∀ {g : ℝ → E} {J : Set ℝ}, IsIntegralCurveOn g v J → IsOpen J → IsPreconnected J →
    I ⊆ J → (EqOn f g I) → I = J

open Classical in
/--
If `h_loc` is any local integral curve and `h_max` is a maximal integral curve,
then the domain of `h_loc` is a subset of the domain of `h_max`. This relies on the
uniqueness of integral curves on the intersection of their domains, guaranteed by Lipschitz
conditions on `v`.
-/
lemma IsIntegralCurveOn.subset_maximal_domain_with_lipschitz
    {f_loc : ℝ → E} {I_loc : Set ℝ} (h_loc : IsIntegralCurveOn f_loc v I_loc)
    (h_loc_open : IsOpen I_loc) (h_loc_preconn : IsPreconnected I_loc)
    (ht₀_loc : t₀ ∈ I_loc) (hf_loc_t₀ : f_loc t₀ = x₀)
    {f_max : ℝ → E} {I_max : Set ℝ} (h_max : IsMaximalIntegralCurveOn v f_max I_max)
    (ht₀_max : t₀ ∈ I_max) (hf_max_t₀ : f_max t₀ = x₀)
    {K : ℝ≥0} (h_v_lipschitz : ∀ t ∈ I_loc ∩ I_max, LipschitzWith K (v t)) :
    I_loc ⊆ I_max := by
  have h_agree : EqOn f_loc f_max (I_loc ∩ I_max) :=
    IsIntegralCurveOn.eqOn_inter (s := fun _ ↦ univ)
      (fun t ht ↦ (h_v_lipschitz t ht).lipschitzOnWith)
      h_loc_preconn h_max.isPreconnected_domain ht₀_loc ht₀_max
      h_loc (by simp)
      h_max.isIntegralCurveOn (by simp)
      (by simp [hf_loc_t₀, hf_max_t₀])
  -- Glue the two integral curves along the overlap.
  let f_union (t : ℝ) : E := if t ∈ I_max then f_max t else f_loc t
  have h_eq : I_max = I_loc ∪ I_max := by
    refine h_max.is_maximal (g := f_union) ?_ (h_loc_open.union h_max.isOpen_domain)
      (IsPreconnected.union t₀ ht₀_loc ht₀_max h_loc_preconn h_max.isPreconnected_domain)
      subset_union_right fun t ht ↦ (if_pos ht).symm
    · rintro t ht
      by_cases ht_max : t ∈ I_max
      · have heq : f_union =ᶠ[𝓝 t] f_max :=
          Filter.mem_of_superset (h_max.isOpen_domain.mem_nhds ht_max) fun y hy ↦ if_pos hy
        simp only [f_union, if_pos ht_max]
        exact ((h_max.isIntegralCurveOn t ht_max).hasDerivAt
          (h_max.isOpen_domain.mem_nhds ht_max)).congr_of_eventuallyEq heq |>.hasDerivWithinAt
      · have ht_loc := ht.resolve_right ht_max
        have heq : f_union =ᶠ[𝓝 t] f_loc :=
          Filter.mem_of_superset (h_loc_open.mem_nhds ht_loc) fun y hy ↦ by
            by_cases hy_max : y ∈ I_max
            · simpa [f_union, hy_max] using (h_agree ⟨hy, hy_max⟩).symm
            · simp [f_union, hy_max]
        simp only [f_union, if_neg ht_max]
        exact ((h_loc t ht_loc).hasDerivAt
          (h_loc_open.mem_nhds ht_loc)).congr_of_eventuallyEq heq |>.hasDerivWithinAt
  rw [h_eq]
  exact subset_union_left

/--
If `(f₁, I₁)` and `(f₂, I₂)` are two maximal integral curves of `y' = v(t,y)`
passing through `(t₀, x₀)`, and `v(t,·)` is Lipschitz continuous with a uniform constant `K`
on the intersection of their domains `I₁ ∩ I₂`, then their domains are equal.
-/
theorem IsMaximalIntegralCurveOn.domain_eq
    {f₁ f₂ : ℝ → E} {I₁ I₂ : Set ℝ}
    (h₁_max : IsMaximalIntegralCurveOn v f₁ I₁)
    (h₂_max : IsMaximalIntegralCurveOn v f₂ I₂)
    (ht₀₁ : t₀ ∈ I₁) (ht₀₂ : t₀ ∈ I₂)
    (hf₁_t₀ : f₁ t₀ = x₀) (hf₂_t₀ : f₂ t₀ = x₀)
    {K : ℝ≥0}
    (hv_lip : ∀ t ∈ I₁ ∩ I₂, LipschitzWith K (v t)) :
    I₁ = I₂ :=
  (h₁_max.isIntegralCurveOn.subset_maximal_domain_with_lipschitz v t₀ x₀ h₁_max.isOpen_domain
    h₁_max.isPreconnected_domain ht₀₁ hf₁_t₀ h₂_max ht₀₂ hf₂_t₀ hv_lip).antisymm
    (h₂_max.isIntegralCurveOn.subset_maximal_domain_with_lipschitz v t₀ x₀ h₂_max.isOpen_domain
      h₂_max.isPreconnected_domain ht₀₂ hf₂_t₀ h₁_max ht₀₁ hf₁_t₀ fun t ht ↦ hv_lip t ht.symm)

/--
If `(f₁, I₁)` and `(f₂, I₂)` are two maximal integral curves of `y' = v(t,y)`
passing through `(t₀, x₀)`, and `v(t,·)` is Lipschitz continuous with a uniform constant `K`
on the intersection of their domains `I₁ ∩ I₂`, then the functions agree on the common domain `I₁`.
-/
theorem IsMaximalIntegralCurveOn.eqOn
    {f₁ f₂ : ℝ → E} {I₁ I₂ : Set ℝ}
    (h₁_max : IsMaximalIntegralCurveOn v f₁ I₁)
    (h₂_max : IsMaximalIntegralCurveOn v f₂ I₂)
    (ht₀₁ : t₀ ∈ I₁) (ht₀₂ : t₀ ∈ I₂)
    (hf₁_t₀ : f₁ t₀ = x₀) (hf₂_t₀ : f₂ t₀ = x₀)
    {K : ℝ≥0}
    (hv_lip : ∀ t ∈ I₁ ∩ I₂, LipschitzWith K (v t)) :
    EqOn f₁ f₂ I₁ := by
  obtain rfl : I₁ = I₂ := h₁_max.domain_eq v t₀ x₀ h₂_max ht₀₁ ht₀₂ hf₁_t₀ hf₂_t₀ hv_lip
  convert IsIntegralCurveOn.eqOn_inter (s := fun _ ↦ univ)
    (fun t ht ↦ (hv_lip t ht).lipschitzOnWith)
    h₁_max.isPreconnected_domain
    h₂_max.isPreconnected_domain
    ht₀₁ ht₀₂
    h₁_max.isIntegralCurveOn (by simp)
    h₂_max.isIntegralCurveOn (by simp)
    (hf₁_t₀.trans hf₂_t₀.symm) using 1
  simp

/-! ### Proof of Existence of Maximal Solutions -/

namespace MaximalSolutionExistence

section

/--
A local integral curve, consisting of the function, its domain (an open interval),
and a proof that it satisfies the `IsIntegralCurveOn` predicate.

This structure is auxiliary for the Zorn's Lemma argument and is not intended for public use.
-/
private structure IsLocalIntegralCurveOn (v : ℝ → E → E) (t₀ : ℝ) (x₀ : E) where
  /-- The function `f` of the local integral curve. -/
  f : ℝ → E
  /-- The open interval `I` on which `f` is an integral curve. -/
  I : Set ℝ
  isOpen_domain : IsOpen I
  isPreconnected_domain : IsPreconnected I
  isIntegralCurveOn : IsIntegralCurveOn f v I
  t₀_mem : t₀ ∈ I
  f_t₀ : f t₀ = x₀

/--
The extension relation `p₁ ≤ p₂` for local integral curves `p₁` and `p₂`.
It means `p₂` is an extension of `p₁`, i.e., the domain of `p₁` is a subset of the domain
of `p₂`, and the functions agree on the smaller domain `p₁.I`.
-/
private def IntegralCurveOnExtends (p₁ p₂ : IsLocalIntegralCurveOn v t₀ x₀) : Prop :=
  p₁.I ⊆ p₂.I ∧ (EqOn p₁.f p₂.f p₁.I)

-- Define LE instance using the extension relation
private instance : LE (IsLocalIntegralCurveOn v t₀ x₀) where
  le := IntegralCurveOnExtends v t₀ x₀

-- Now define the Preorder instance. This is sufficient for `zorn_le_nonempty`.
private instance : Preorder (IsLocalIntegralCurveOn v t₀ x₀) where
  le := IntegralCurveOnExtends v t₀ x₀
  le_refl p := ⟨Subset.rfl, fun _ _ ↦ rfl⟩
  le_trans := fun _ _ _ h₁₂ h₂₃ =>
    ⟨h₁₂.1.trans h₂₃.1, fun _ ht ↦ (h₁₂.2 ht).trans (h₂₃.2 (h₁₂.1 ht))⟩

/--
The equivalence relation `≈` on local integral curves.
Two local integral curves are equivalent if they are extensions of each other, meaning
they have the same interval and agree on that interval.
This setoid structure is defined for completeness but not directly used by `zorn_le_nonempty`.
-/
private instance IsLocalIntegralCurveOnSetoid : Setoid (IsLocalIntegralCurveOn v t₀ x₀) where
  r p₁ p₂ := p₁ ≤ p₂ ∧ p₂ ≤ p₁
  iseqv := {
    refl p := ⟨le_refl p, le_refl p⟩
    symm := And.symm
    trans h₁₂ h₂₃ := ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₂₃.2 h₁₂.2⟩
  }

/--
The quotient type of local integral curves, where curves that are extensions
of each other are identified. This type carries the structure of a partial order.
This is defined for completeness but not directly used by `zorn_le_nonempty`.
-/
private abbrev QuotientIsLocalIntegralCurveOn :=
  Quotient (IsLocalIntegralCurveOnSetoid v t₀ x₀)

private instance QuotientIsLocalIntegralCurveOn.instLE :
    LE (QuotientIsLocalIntegralCurveOn v t₀ x₀) where
  le := Quotient.lift₂
    (fun p₁ p₂ => p₁ ≤ p₂)
    (by
      intro a₁ a₂ b₁ b₂ hab hcd
      apply propext
      apply Iff.intro
      · intro h_a1_le_a2
        calc
          b₁ ≤ a₁ := hab.2
          _  ≤ a₂ := h_a1_le_a2
          _  ≤ b₂ := hcd.1
      · intro h_b1_le_b2
        calc
          a₁ ≤ b₁ := hab.1
          _  ≤ b₂ := h_b1_le_b2
          _  ≤ a₂ := hcd.2
    )

/--
The set of local integral curves modulo the extension equivalence relation forms a partial order.
The order `⟦p₁⟧ ≤ ⟦p₂⟧` is induced by the preorder relation `p₁ ≤ p₂` on the representatives.
This instance is defined for completeness; `zorn_le_nonempty` operates on the `Preorder`
of `IsLocalIntegralCurveOn` directly.
-/
private instance : PartialOrder (QuotientIsLocalIntegralCurveOn v t₀ x₀) where
  le := (QuotientIsLocalIntegralCurveOn.instLE v t₀ x₀).le
  le_refl := by
    rintro ⟨p⟩
    exact le_refl p
  le_trans := by
    rintro ⟨p₁⟩ ⟨p₂⟩ ⟨p₃⟩ h₁₂ h₂₃
    exact le_trans (α := IsLocalIntegralCurveOn v t₀ x₀) h₁₂ h₂₃
  le_antisymm := by
    rintro ⟨p₁⟩ ⟨p₂⟩ h₁₂ h₂₁
    exact Quotient.sound ⟨h₁₂, h₂₁⟩


/--
If `C` is a chain of `IsLocalIntegralCurveOn`s and `t` is in the domains of two curves in `C`,
then those curves agree at `t`. This is because chains are totally ordered by extension.
-/
private lemma chain_solutions_agree {C : Set (IsLocalIntegralCurveOn v t₀ x₀)}
  (hC : IsChain (· ≤ ·) C) {p₁ p₂ : IsLocalIntegralCurveOn v t₀ x₀}
    (hp₁ : p₁ ∈ C) (hp₂ : p₂ ∈ C)
    (t : ℝ) (ht₁ : t ∈ p₁.I) (ht₂ : t ∈ p₂.I) : p₁.f t = p₂.f t :=
  (hC.total hp₁ hp₂).elim (·.2 ht₁) fun h ↦ (h.2 ht₂).symm

open Classical in
/--
Constructs the supremum of a non-empty chain `C` of `IsLocalIntegralCurveOn`s.
This supremum is itself an `IsLocalIntegralCurveOn` and serves as an upper bound for `C`.
-/
private def chainSup (C : Set (IsLocalIntegralCurveOn v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) :
    IsLocalIntegralCurveOn v t₀ x₀ where
  I := ⋃ (p : IsLocalIntegralCurveOn v t₀ x₀) (hp : p ∈ C), p.I
  f t :=
    if ht : t ∈ ⋃ (p : IsLocalIntegralCurveOn v t₀ x₀) (hp : p ∈ C), p.I then
      (Classical.choose (Set.mem_iUnion₂.mp ht)).f t
    else x₀
  isOpen_domain := by
    exact isOpen_iUnion fun p => isOpen_iUnion fun _ => p.isOpen_domain
  isPreconnected_domain := by
    rw [← Set.sUnion_image]
    exact isPreconnected_sUnion t₀ _
      (by rintro s ⟨p, _, rfl⟩; exact p.t₀_mem)
      (by rintro s ⟨p, _, rfl⟩; exact p.isPreconnected_domain)
  isIntegralCurveOn := by
    intro t ht
    obtain ⟨p, hp, htp⟩ := Set.mem_iUnion₂.mp ht
    have heq : (fun t => if ht : t ∈ ⋃ q ∈ C, q.I
        then (Classical.choose (Set.mem_iUnion₂.mp ht)).f t else x₀) =ᶠ[𝓝 t] p.f := by
      filter_upwards [p.isOpen_domain.mem_nhds htp] with y hy
      simp only [dif_pos (Set.mem_biUnion hp hy)]
      have hspec := Classical.choose_spec (Set.mem_iUnion₂.mp (Set.mem_biUnion hp hy))
      exact chain_solutions_agree v t₀ x₀ hC hspec.1 hp y hspec.2 hy
    have hft : (if ht' : t ∈ ⋃ q ∈ C, q.I
        then (Classical.choose (Set.mem_iUnion₂.mp ht')).f t else x₀) = p.f t := by
      simp only [dif_pos ht]
      have hspec := Classical.choose_spec (Set.mem_iUnion₂.mp ht)
      exact chain_solutions_agree v t₀ x₀ hC hspec.1 hp t hspec.2 htp
    exact (((p.isIntegralCurveOn t htp).hasDerivAt
        (p.isOpen_domain.mem_nhds htp)).congr_of_eventuallyEq heq |>.hasDerivWithinAt).congr_deriv
      (congr_arg (v t) hft.symm)
  t₀_mem := by
    obtain ⟨p, hp⟩ := hCne
    exact Set.mem_biUnion hp p.t₀_mem
  f_t₀ := by
    have ht₀ : t₀ ∈ ⋃ p ∈ C, p.I := by
      obtain ⟨p, hp⟩ := hCne
      exact Set.mem_biUnion hp p.t₀_mem
    simp only [dif_pos ht₀]
    exact (Classical.choose (Set.mem_iUnion₂.mp ht₀)).f_t₀

open Classical in
/--
The `chainSup` construction provides an upper bound for any element `hp` in a non-empty chain `C`.
-/
private lemma chainSup_is_upper_bound (C : Set (IsLocalIntegralCurveOn v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) :
    ∀ hp ∈ C, hp ≤ chainSup v t₀ x₀ C hC hCne := by
  intro hp hpC
  refine ⟨?_, ?_⟩
  · intro t ht
    exact Set.mem_iUnion₂.mpr ⟨hp, hpC, ht⟩
  · intro t ht
    have hchoose := Classical.choose_spec <| Set.mem_iUnion₂.mp <| show
        t ∈ ⋃ (p : IsLocalIntegralCurveOn v t₀ x₀) (hp : p ∈ C), p.I from
      Set.mem_iUnion₂.mpr ⟨hp, hpC, ht⟩
    refine (chain_solutions_agree v t₀ x₀ hC hpC hchoose.1 t ht hchoose.2).trans ?_
    simp only [chainSup]
    rw [dif_pos (show t ∈ ⋃ (p : IsLocalIntegralCurveOn v t₀ x₀) (hp : p ∈ C), p.I from
      Set.mem_iUnion₂.mpr ⟨hp, hpC, ht⟩)]

/--
Helper lemma stating that any non-empty chain `C` has an upper bound.
This is equivalent to `BddAbove C`.
-/
private lemma chain_has_upper_bound_explicit (C : Set (IsLocalIntegralCurveOn v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : ∃ ub, ∀ p ∈ C, p ≤ ub := by
  use chainSup v t₀ x₀ C hC hCne
  exact chainSup_is_upper_bound v t₀ x₀ C hC hCne

/--
Chains of local integral curves are bounded above. This is the condition required by
`zorn_le_nonempty`.
-/
private lemma chain_is_bddAbove (C : Set (IsLocalIntegralCurveOn v t₀ x₀))
    (hC : IsChain (· ≤ ·) C) (hCne : C.Nonempty) : BddAbove C := by
  -- `BddAbove C` means `∃ x, ∀ y ∈ C, y ≤ x`.
  -- This is exactly what `chain_has_upper_bound_explicit` provides.
  exact chain_has_upper_bound_explicit v t₀ x₀ C hC hCne

@[reducible] private def isLocalIntegralCurveOnNonempty [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    Nonempty (IsLocalIntegralCurveOn v t₀ x₀) := by
  -- Picard-Lindelöf gives an integral curve `f₀` on `Icc tMin tMax`.
  have hx₀ : x₀ ∈ Metric.closedBall x₀ r := by simp
  rcases (IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt hpl_instance hx₀) with
    ⟨f₀, hf₀_t₀, hf₀_isIntegralCurveOn⟩
  -- Construct the initial local integral curve.
  let p₀ : IsLocalIntegralCurveOn v t₀ x₀ := {
    f := f₀
    I := Ioo tMin tMax
    isOpen_domain := isOpen_Ioo
    isPreconnected_domain := (isConnected_Ioo (htMin_lt_t₀.trans ht₀_lt_tMax)).isPreconnected
    isIntegralCurveOn := IsIntegralCurveOn.mono hf₀_isIntegralCurveOn Ioo_subset_Icc_self
    t₀_mem := ⟨htMin_lt_t₀, ht₀_lt_tMax⟩
    f_t₀ := by simpa [ht₀'_eq] using hf₀_t₀
  }
  exact ⟨p₀⟩

/--
The main existence theorem for maximal integral curves within this namespace.
It asserts that if Picard-Lindelöf conditions guarantee a local integral curve on an
open interval `(tMin, tMax)` containing `t₀`, then a maximal integral curve exists.
-/
theorem exists_maximal_solution
  [CompleteSpace E]
  (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
  (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
  (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
  ∃ (f : ℝ → E) (I : Set ℝ), IsMaximalIntegralCurveOn v f I ∧ t₀ ∈ I ∧ f t₀ = x₀ := by
  let S := IsLocalIntegralCurveOn v t₀ x₀
  -- Register local existence as an inline instance for `zorn_le_nonempty`.
  letI : Nonempty S := isLocalIntegralCurveOnNonempty v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq
    htMin_lt_t₀ ht₀_lt_tMax hpl_instance
  -- 2. Apply Zorn's Lemma for Preorders (`zorn_le_nonempty`).
  -- This requires that every non-empty chain has an upper bound (`BddAbove`).
  rcases zorn_le_nonempty (chain_is_bddAbove v t₀ x₀) with ⟨maximal_element, h_is_max_elem⟩
    -- `h_is_max_elem` means `∀ (x : S), maximal_element ≤ x → x ≤ maximal_element`.
  -- 3. Show this `maximal_element` corresponds to an `IsMaximalIntegralCurveOn`.
  use maximal_element.f, maximal_element.I
  refine ⟨?_, maximal_element.t₀_mem, maximal_element.f_t₀⟩
  refine ⟨maximal_element.isOpen_domain, maximal_element.isPreconnected_domain,
    maximal_element.isIntegralCurveOn, ?_⟩
  -- Prove the maximality condition.
  intro g J hg_sol hJ_open hJ_conn hIJ_subset h_eq_on_I
  -- Assume, for contradiction, that `I ≠ J`.
  by_contra h_I_ne_J
  -- Construct an `IsLocalIntegralCurveOn` from `(g, J)`.
  let p_g : IsLocalIntegralCurveOn v t₀ x₀ :=
    { f := g, I := J,
      isOpen_domain := hJ_open,
      isPreconnected_domain := hJ_conn,
      isIntegralCurveOn := hg_sol,
      t₀_mem := hIJ_subset maximal_element.t₀_mem,
      f_t₀ := by
        have h_eq_at_t₀ : g t₀ = maximal_element.f t₀ := by
          symm
          exact h_eq_on_I maximal_element.t₀_mem
        simpa [h_eq_at_t₀] using maximal_element.f_t₀ }
  exact h_I_ne_J (hIJ_subset.antisymm (h_is_max_elem (b := p_g) ⟨hIJ_subset, h_eq_on_I⟩).1)

end

end MaximalSolutionExistence

/--
Under the conditions of the Picard-Lindelöf theorem (specifically, ensuring local existence
on an open interval around `t₀`), there exists a maximal integral curve of `x' = v(t, x)`
with initial condition `f(t₀) = x₀`.
-/
theorem exists_maximal_integralCurveOn [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    ∃ (f : ℝ → E) (I : Set ℝ), IsMaximalIntegralCurveOn v f I ∧ t₀ ∈ I ∧ f t₀ = x₀ := by
  obtain ⟨f, I, hmax⟩ :=
    MaximalSolutionExistence.exists_maximal_solution v t₀ x₀
      tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance
  exact ⟨f, I, hmax⟩

open Classical in
/--
An arbitrarily chosen maximal integral curve of `x' = v(t, x)` through `(t₀, x₀)`, obtained
by choice from `exists_maximal_integralCurveOn` under the Picard–Lindelöf hypotheses.

This is a total function `ℝ → E`; it is only guaranteed to be an integral curve on the corresponding
domain `maximalIntegralCurveDomain`.
-/
noncomputable def maximalIntegralCurve [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) : ℝ → E :=
  Classical.choose (exists_maximal_integralCurveOn v t₀ x₀ tMin tMax a r L K t₀'
    ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance)

open Classical in
/--
The maximal open preconnected domain of the chosen maximal integral curve `maximalIntegralCurve`.

This set is obtained by choice from `exists_maximal_integralCurveOn` under the Picard–Lindelöf
hypotheses; it contains `t₀` and on it the function `maximalIntegralCurve` is an integral curve
of `v` with initial value `x₀`.
-/
noncomputable def maximalIntegralCurveDomain [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) : Set ℝ :=
  Classical.choose (Classical.choose_spec
    (exists_maximal_integralCurveOn v t₀ x₀ tMin tMax a r L K t₀'
      ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance))

open Classical in
private lemma maximalIntegralCurve_spec_of_exists [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    IsMaximalIntegralCurveOn v
      (maximalIntegralCurve v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      (maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      ∧ t₀ ∈ maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
        ht₀_lt_tMax hpl_instance
      ∧ maximalIntegralCurve v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance t₀ = x₀ := by
  simpa [maximalIntegralCurve, maximalIntegralCurveDomain] using
    (Classical.choose_spec
      (Classical.choose_spec
        (exists_maximal_integralCurveOn v t₀ x₀ tMin tMax a r L K t₀'
          ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance)))

open Classical in
lemma maximalIntegralCurve_spec [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    IsMaximalIntegralCurveOn v
      (maximalIntegralCurve v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      (maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      ∧ t₀ ∈ maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
        ht₀_lt_tMax hpl_instance
      ∧ maximalIntegralCurve v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance t₀ = x₀ := by
  simpa using maximalIntegralCurve_spec_of_exists v t₀ x₀ tMin tMax a r L K t₀'
    ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax hpl_instance

lemma maximalIntegralCurve_isMaximal [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    IsMaximalIntegralCurveOn v
      (maximalIntegralCurve v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      (maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance) :=
  (maximalIntegralCurve_spec v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).1

lemma maximalIntegralCurve_t₀_mem [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    t₀ ∈ maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
      ht₀_lt_tMax hpl_instance :=
  (maximalIntegralCurve_spec v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).2.1

lemma maximalIntegralCurve_t₀_eq [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    maximalIntegralCurve v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance t₀ = x₀ :=
  (maximalIntegralCurve_spec v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).2.2

lemma maximalIntegralCurve_isSolution [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K) :
    IsIntegralCurveOn
      (maximalIntegralCurve v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance)
      v
      (maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
        hpl_instance) :=
  (maximalIntegralCurve_isMaximal v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).isIntegralCurveOn

theorem maximalIntegralCurve_domain_eq [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K)
    {f₂ : ℝ → E} {I₂ : Set ℝ}
    (h₂_max : IsMaximalIntegralCurveOn v f₂ I₂)
    (ht₀₂ : t₀ ∈ I₂) (hf₂_t₀ : f₂ t₀ = x₀)
    {K' : ℝ≥0}
    (hv_lip : ∀ t ∈ maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
      ht₀_lt_tMax hpl_instance ∩ I₂, LipschitzWith K' (v t)) :
    maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance = I₂ :=
  (maximalIntegralCurve_isMaximal v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).domain_eq v t₀ x₀ h₂_max
    (maximalIntegralCurve_t₀_mem v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance) ht₀₂
    (maximalIntegralCurve_t₀_eq v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance) hf₂_t₀ hv_lip

theorem maximalIntegralCurve_eqOn [CompleteSpace E]
    (tMin tMax : ℝ) (a r L K : ℝ≥0) (t₀' : Icc tMin tMax)
    (ht₀'_eq : (t₀' : ℝ) = t₀) (htMin_lt_t₀ : tMin < t₀) (ht₀_lt_tMax : t₀ < tMax)
    (hpl_instance : IsPicardLindelof v t₀' x₀ a r L K)
    {f₂ : ℝ → E} {I₂ : Set ℝ}
    (h₂_max : IsMaximalIntegralCurveOn v f₂ I₂)
    (ht₀₂ : t₀ ∈ I₂) (hf₂_t₀ : f₂ t₀ = x₀)
    {K' : ℝ≥0}
    (hv_lip : ∀ t ∈ maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
      ht₀_lt_tMax hpl_instance ∩ I₂, LipschitzWith K' (v t)) :
    EqOn (maximalIntegralCurve v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance) f₂ (maximalIntegralCurveDomain v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀
        ht₀_lt_tMax hpl_instance) :=
  (maximalIntegralCurve_isMaximal v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
    hpl_instance).eqOn v t₀ x₀ h₂_max
    (maximalIntegralCurve_t₀_mem v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance) ht₀₂
    (maximalIntegralCurve_t₀_eq v t₀ x₀ tMin tMax a r L K t₀' ht₀'_eq htMin_lt_t₀ ht₀_lt_tMax
      hpl_instance) hf₂_t₀ hv_lip
