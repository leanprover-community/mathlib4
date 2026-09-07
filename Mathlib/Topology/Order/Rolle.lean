/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.ExtendFrom
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.T5

/-!
# Rolle's Theorem (topological part)

In this file we prove the purely topological part of Rolle's Theorem:
a function that is continuous on an interval $[a, b]$, $a < b$,
has a local extremum at a point $x ∈ (a, b)$ provided that $f(a)=f(b)$.
We also prove several variations of this statement,
including versions for the unbounded intervals $(a, +∞)$, $(-∞, b)$, and $(-∞, +∞)$,
where the equality of the values at the endpoints is replaced
by the equality of the limits along `atTop` and `atBot`.

In `Mathlib/Analysis/Calculus/LocalExtr/Rolle` we use these lemmas
to prove several versions of Rolle's Theorem from calculus.

## Keywords
local minimum, local maximum, extremum, Rolle's Theorem
-/

public section

open Filter Set

open scoped Topology

variable {X Y : Type*}
  [ConditionallyCompleteLinearOrder X] [DenselyOrdered X] [TopologicalSpace X] [OrderTopology X]
  [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
  {f : X → Y} {a b : X} {l : Y}

/-- A continuous function on a closed interval with `f a = f b`
takes either its maximum or its minimum value at a point in the interior of the interval. -/
theorem exists_Ioo_extr_on_Icc (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsExtrOn f (Icc a b) c := by
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_lt hab)
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : ∃ c ∈ Icc a b, ∀ x ∈ Icc a b, f c ≤ f x :=
    isCompact_Icc.exists_isMinOn ne hfc
  obtain ⟨C, Cmem, Cge⟩ : ∃ C ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f C :=
    isCompact_Icc.exists_isMaxOn ne hfc
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have : ∀ x ∈ Icc a b, f x = f a := fun x hx => le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases nonempty_Ioo.2 hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl fun x hx ↦ ?_⟩
      simp only [mem_ofPred_eq, this x hx, this c' (Ioo_subset_Icc_self hc'), le_rfl]
    · refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 <| mt ?_ hC, lt_of_le_of_ne Cmem.2 <| mt ?_ hC⟩, Or.inr Cge⟩
      exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
  · refine ⟨c, ⟨lt_of_le_of_ne cmem.1 <| mt ?_ hc, lt_of_le_of_ne cmem.2 <| mt ?_ hc⟩, Or.inl cle⟩
    exacts [fun h => by rw [h], fun h => by rw [h, hfI]]

/-- A continuous function on a closed interval with `f a = f b`
has a local extremum at some point of the corresponding open interval. -/
theorem exists_isLocalExtr_Ioo (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc hab hfc hfI
  ⟨c, cmem, hc.isLocalExtr <| Icc_mem_nhds cmem.1 cmem.2⟩

/-- If a function `f` is continuous on an open interval
and tends to the same value at its endpoints, then it has an extremum on this open interval. -/
lemma exists_isExtrOn_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    ∃ c ∈ Ioo a b, IsExtrOn f (Ioo a b) c := by
  have h : EqOn (extendFrom (Ioo a b) f) f (Ioo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : ∃ c ∈ Ioo a b, IsExtrOn (extendFrom (Ioo a b) f) (Icc a b) c :=
    exists_Ioo_extr_on_Icc hab (continuousOn_Icc_extendFrom_Ioo hfc ha hb)
      ((eq_lim_at_left_extendFrom_Ioo hab ha).trans (eq_lim_at_right_extendFrom_Ioo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset Ioo_subset_Icc_self).congr h (h hc)⟩

/-- If a function `f` is continuous on an open interval
and tends to the same value at its endpoints,
then it has a local extremum on this open interval. -/
lemma exists_isLocalExtr_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    ∃ c ∈ Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_isExtrOn_Ioo_of_tendsto hab hfc ha hb
  ⟨c, cmem, hc.isLocalExtr <| Ioo_mem_nhds cmem.1 cmem.2⟩

/-!
### Rolle's Theorem on an unbounded interval

If `f` tends to the same limit `l` at both ends of an interval that is unbounded on one or both
sides, then `f` has an extremum in the interior of this interval. If `f` is identically equal to
`l`, then any interior point will do. Otherwise `f` takes a value `f c₀ ≠ l`, and, in the case
`l < f c₀`, the maximum of `f` on a compact interval `[p, q]` chosen so that `f x < f c₀` outside
of `[p, q]` is a maximum of `f` on the whole interval, attained at a point of `(p, q)`. The case
`f c₀ < l` follows by applying this to the order dual of the codomain.
-/

omit [DenselyOrdered X] in
/-- Auxiliary lemma for the unbounded versions of Rolle's Theorem: if `f` is continuous on `s`,
if the interval `[p, q]` is included in `s` and contains a point `c₀`, and if `f x < f c₀` at the
points of `s` outside of `(p, q)`, then `f` attains a maximum on `s` at a point of `(p, q)`. -/
private lemma exists_isMaxOn_of_forall_lt {s : Set X} {p q c₀ : X} (hfc : ContinuousOn f s)
    (hsub : Icc p q ⊆ s) (hc₀ : c₀ ∈ Icc p q) (hlow : ∀ x ∈ s, x ≤ p → f x < f c₀)
    (hhigh : ∀ x ∈ s, q ≤ x → f x < f c₀) : ∃ c ∈ Ioo p q, IsMaxOn f s c := by
  have hpq : p ≤ q := hc₀.1.trans hc₀.2
  obtain ⟨c, hcmem, hcmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hpq) (hfc.mono hsub)
  have hcc₀ : f c₀ ≤ f c := hcmax hc₀
  have hcp : p < c := hcmem.1.lt_of_ne fun h =>
    absurd ((h ▸ hlow p (hsub (left_mem_Icc.2 hpq)) le_rfl).trans_le hcc₀) (lt_irrefl _)
  have hcq : c < q := hcmem.2.lt_of_ne fun h =>
    absurd ((h ▸ hhigh q (hsub (right_mem_Icc.2 hpq)) le_rfl).trans_le hcc₀) (lt_irrefl _)
  refine ⟨c, ⟨hcp, hcq⟩, fun x hx => ?_⟩
  rcases le_or_gt x p with hxp | hpx
  · exact ((hlow x hx hxp).trans_le hcc₀).le
  · rcases le_or_gt q x with hqx | hxq
    · exact ((hhigh x hx hqx).trans_le hcc₀).le
    · exact hcmax ⟨hpx.le, hxq.le⟩

/-- If `f` is continuous on `(a, +∞)`, tends to `l` at `𝓝[>] a` and along `atTop`, and takes at
some point of `(a, +∞)` a value greater than `l`, then `f` attains a maximum on `(a, +∞)`. -/
private lemma exists_isMaxOn_Ioi_of_tendsto (hfc : ContinuousOn f (Ioi a))
    (hfa : Tendsto f (𝓝[>] a) (𝓝 l)) (hftop : Tendsto f atTop (𝓝 l)) {c₀ : X} (hc₀ : a < c₀)
    (hlt : l < f c₀) : ∃ c ∈ Ioi a, IsMaxOn f (Ioi a) c := by
  obtain ⟨u, hu, hus⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset hc₀).1
    (hfa.eventually (gt_mem_nhds hlt))
  obtain ⟨p, hap, hpu⟩ := exists_between hu.1
  obtain ⟨q, hq⟩ := eventually_atTop.1 (hftop.eventually (gt_mem_nhds hlt))
  have hc₀q : c₀ < q := not_le.1 fun h => absurd (hq c₀ h) (lt_irrefl _)
  obtain ⟨c, hc, hcmax⟩ := exists_isMaxOn_of_forall_lt (p := p) (q := q) hfc
    (fun x hx => hap.trans_le hx.1) ⟨(hpu.trans_le hu.2).le, hc₀q.le⟩
    (fun x hx hxp => hus ⟨hx, hxp.trans_lt hpu⟩) fun x _ hqx => hq x hqx
  exact ⟨c, hap.trans hc.1, hcmax⟩

/-- If `f` is continuous on `(-∞, b)`, tends to `l` along `atBot` and at `𝓝[<] b`, and takes at
some point of `(-∞, b)` a value greater than `l`, then `f` attains a maximum on `(-∞, b)`. -/
private lemma exists_isMaxOn_Iio_of_tendsto (hfc : ContinuousOn f (Iio b))
    (hfbot : Tendsto f atBot (𝓝 l)) (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) {c₀ : X} (hc₀ : c₀ < b)
    (hlt : l < f c₀) : ∃ c ∈ Iio b, IsMaxOn f (Iio b) c := by
  obtain ⟨u, hu, hus⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hc₀).1
    (hfb.eventually (gt_mem_nhds hlt))
  obtain ⟨q, huq, hqb⟩ := exists_between hu.2
  obtain ⟨p, hp⟩ := eventually_atBot.1 (hfbot.eventually (gt_mem_nhds hlt))
  have hpc₀ : p < c₀ := not_le.1 fun h => absurd (hp c₀ h) (lt_irrefl _)
  obtain ⟨c, hc, hcmax⟩ := exists_isMaxOn_of_forall_lt (p := p) (q := q) hfc
    (fun x hx => hx.2.trans_lt hqb) ⟨hpc₀.le, (hu.1.trans_lt huq).le⟩
    (fun x _ hxp => hp x hxp) fun x hx hqx => hus ⟨huq.trans_le hqx, hx⟩
  exact ⟨c, hc.2.trans hqb, hcmax⟩

omit [DenselyOrdered X] in
/-- If `f` is continuous, tends to `l` along `atBot` and along `atTop`, and takes somewhere a value
greater than `l`, then `f` attains a global maximum. -/
private lemma exists_isMaxOn_univ_of_tendsto (hfc : Continuous f) (hfbot : Tendsto f atBot (𝓝 l))
    (hftop : Tendsto f atTop (𝓝 l)) {c₀ : X} (hlt : l < f c₀) : ∃ c, IsMaxOn f univ c := by
  obtain ⟨p, hp⟩ := eventually_atBot.1 (hfbot.eventually (gt_mem_nhds hlt))
  obtain ⟨q, hq⟩ := eventually_atTop.1 (hftop.eventually (gt_mem_nhds hlt))
  have hpc₀ : p < c₀ := not_le.1 fun h => absurd (hp c₀ h) (lt_irrefl _)
  have hc₀q : c₀ < q := not_le.1 fun h => absurd (hq c₀ h) (lt_irrefl _)
  obtain ⟨c, -, hcmax⟩ := exists_isMaxOn_of_forall_lt (p := p) (q := q) hfc.continuousOn
    (subset_univ _) ⟨hpc₀.le, hc₀q.le⟩ (fun x _ hxp => hp x hxp) fun x _ hqx => hq x hqx
  exact ⟨c, hcmax⟩

/-- If a function `f` is continuous on `(a, +∞)` and tends to the same value at `𝓝[>] a` and along
`atTop`, then it has an extremum on `(a, +∞)`. -/
lemma exists_isExtrOn_Ioi_of_tendsto [NoMaxOrder X] (hfc : ContinuousOn f (Ioi a))
    (hfa : Tendsto f (𝓝[>] a) (𝓝 l)) (hftop : Tendsto f atTop (𝓝 l)) :
    ∃ c ∈ Ioi a, IsExtrOn f (Ioi a) c := by
  by_cases! hconst : ∀ x ∈ Ioi a, f x = l
  · obtain ⟨c, hc⟩ := exists_gt a
    exact ⟨c, hc, Or.inl fun x hx => (hconst c hc).trans_le (hconst x hx).ge⟩
  · obtain ⟨c₀, hc₀, hne⟩ := hconst
    rcases lt_or_gt_of_ne hne with h | h
    · exact (exists_isMaxOn_Ioi_of_tendsto (Y := Yᵒᵈ) hfc hfa hftop hc₀ h).imp
        fun c hc => ⟨hc.1, Or.inl hc.2⟩
    · exact (exists_isMaxOn_Ioi_of_tendsto hfc hfa hftop hc₀ h).imp
        fun c hc => ⟨hc.1, Or.inr hc.2⟩

/-- If a function `f` is continuous on `(a, +∞)` and tends to the same value at `𝓝[>] a` and along
`atTop`, then it has a local extremum on `(a, +∞)`. -/
lemma exists_isLocalExtr_Ioi_of_tendsto [NoMaxOrder X] (hfc : ContinuousOn f (Ioi a))
    (hfa : Tendsto f (𝓝[>] a) (𝓝 l)) (hftop : Tendsto f atTop (𝓝 l)) :
    ∃ c ∈ Ioi a, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_isExtrOn_Ioi_of_tendsto hfc hfa hftop
  ⟨c, cmem, hc.isLocalExtr <| Ioi_mem_nhds cmem⟩

/-- If a function `f` is continuous on `(-∞, b)` and tends to the same value along `atBot` and at
`𝓝[<] b`, then it has an extremum on `(-∞, b)`. -/
lemma exists_isExtrOn_Iio_of_tendsto [NoMinOrder X] (hfc : ContinuousOn f (Iio b))
    (hfbot : Tendsto f atBot (𝓝 l)) (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    ∃ c ∈ Iio b, IsExtrOn f (Iio b) c := by
  by_cases! hconst : ∀ x ∈ Iio b, f x = l
  · obtain ⟨c, hc⟩ := exists_lt b
    exact ⟨c, hc, Or.inl fun x hx => (hconst c hc).trans_le (hconst x hx).ge⟩
  · obtain ⟨c₀, hc₀, hne⟩ := hconst
    rcases lt_or_gt_of_ne hne with h | h
    · exact (exists_isMaxOn_Iio_of_tendsto (Y := Yᵒᵈ) hfc hfbot hfb hc₀ h).imp
        fun c hc => ⟨hc.1, Or.inl hc.2⟩
    · exact (exists_isMaxOn_Iio_of_tendsto hfc hfbot hfb hc₀ h).imp
        fun c hc => ⟨hc.1, Or.inr hc.2⟩

/-- If a function `f` is continuous on `(-∞, b)` and tends to the same value along `atBot` and at
`𝓝[<] b`, then it has a local extremum on `(-∞, b)`. -/
lemma exists_isLocalExtr_Iio_of_tendsto [NoMinOrder X] (hfc : ContinuousOn f (Iio b))
    (hfbot : Tendsto f atBot (𝓝 l)) (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    ∃ c ∈ Iio b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_isExtrOn_Iio_of_tendsto hfc hfbot hfb
  ⟨c, cmem, hc.isLocalExtr <| Iio_mem_nhds cmem⟩

omit [DenselyOrdered X] in
/-- If a continuous function `f` tends to the same value along `atBot` and along `atTop`,
then it has a global extremum. -/
lemma exists_isExtrOn_univ_of_tendsto [Nonempty X] (hfc : Continuous f)
    (hfbot : Tendsto f atBot (𝓝 l)) (hftop : Tendsto f atTop (𝓝 l)) :
    ∃ c, IsExtrOn f univ c := by
  by_cases! hconst : ∀ x, f x = l
  · exact ⟨Classical.arbitrary X, Or.inl fun x _ => (hconst _).trans_le (hconst x).ge⟩
  · obtain ⟨c₀, hne⟩ := hconst
    rcases lt_or_gt_of_ne hne with h | h
    · exact (exists_isMaxOn_univ_of_tendsto (Y := Yᵒᵈ) hfc hfbot hftop h).imp fun c hc => Or.inl hc
    · exact (exists_isMaxOn_univ_of_tendsto hfc hfbot hftop h).imp fun c hc => Or.inr hc

omit [DenselyOrdered X] in
/-- If a continuous function `f` tends to the same value along `atBot` and along `atTop`,
then it has a local extremum. -/
lemma exists_isLocalExtr_of_tendsto [Nonempty X] (hfc : Continuous f)
    (hfbot : Tendsto f atBot (𝓝 l)) (hftop : Tendsto f atTop (𝓝 l)) : ∃ c, IsLocalExtr f c :=
  let ⟨c, hc⟩ := exists_isExtrOn_univ_of_tendsto hfc hfbot hftop
  ⟨c, hc.isLocalExtr univ_mem⟩

/-- A continuous function on an unordered closed interval with `f a = f b`
takes either its maximum or its minimum value at a point in the interior of the interval. -/
theorem exists_uIoo_isExtrOn_uIcc (hab : a ≠ b) (hfc : ContinuousOn f (uIcc a b))
    (hfI : f a = f b) :
    ∃ c ∈ uIoo a b, IsExtrOn f (uIcc a b) c :=
  exists_Ioo_extr_on_Icc (by simp [hab.symm]) hfc (by grind)

/-- A continuous function on a unordered closed interval with `f a = f b`
has a local extremum at some point of the corresponding unordered open interval. -/
theorem exists_isLocalExtr_uIoo (hab : a ≠ b) (hfc : ContinuousOn f (uIcc a b)) (hfI : f a = f b) :
    ∃ c ∈ uIoo a b, IsLocalExtr f c :=
  exists_isLocalExtr_Ioo (by simp [hab.symm]) hfc (by grind)

/-- If a function `f` is continuous on an unordered open interval
and tends to the same value at its endpoints,
then it has an extremum on this unordered open interval. -/
lemma exists_isExtrOn_uIoo_of_tendsto (hab : a ≠ b) (hfc : ContinuousOn f (uIoo a b))
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 l)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 l)) :
    ∃ c ∈ uIoo a b, IsExtrOn f (uIoo a b) c := by
  have h : EqOn (extendFrom (uIoo a b) f) f (uIoo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : ∃ c ∈ uIoo a b, IsExtrOn (extendFrom (uIoo a b) f) (uIcc a b) c :=
    exists_uIoo_isExtrOn_uIcc hab (continuousOn_uIcc_extendFrom_uIoo hfc ha hb)
      ((eq_lim_at_left_extendFrom_uIoo hab ha).trans (eq_lim_at_right_extendFrom_uIoo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset uIoo_subset_uIcc_self).congr h (h hc)⟩

/-- If a function `f` is continuous on an unordered open interval
and tends to the same value at its endpoints,
then it has a local extremum on this unordered open interval. -/
lemma exists_isLocalExtr_uIoo_of_tendsto (hab : a ≠ b) (hfc : ContinuousOn f (uIoo a b))
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 l)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 l)) :
    ∃ c ∈ uIoo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_isExtrOn_uIoo_of_tendsto hab hfc ha hb
  ⟨c, cmem, hc.isLocalExtr <| Ioo_mem_nhds cmem.1 cmem.2⟩
