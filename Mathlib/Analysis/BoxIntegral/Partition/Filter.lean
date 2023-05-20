/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.partition.filter
! leanprover-community/mathlib commit 92ca63f0fb391a9ca5f22d2409a6080e786d99f7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathbin.Analysis.BoxIntegral.Partition.Split

/-!
# Filters used in box-based integrals

First we define a structure `box_integral.integration_params`. This structure will be used as an
argument in the definition of `box_integral.integral` in order to use the same definition for a few
well-known definitions of integrals based on partitions of a rectangular box into subboxes (Riemann
integral, Henstock-Kurzweil integral, and McShane integral).

This structure holds three boolean values (see below), and encodes eight different sets of
parameters; only four of these values are used somewhere in `mathlib`. Three of them correspond to
the integration theories listed above, and one is a generalization of the one-dimensional
Henstock-Kurzweil integral such that the divergence theorem works without additional integrability
assumptions.

Finally, for each set of parameters `l : box_integral.integration_params` and a rectangular box
`I : box_integral.box ι`, we define several `filter`s that will be used either in the definition of
the corresponding integral, or in the proofs of its properties. We equip
`box_integral.integration_params` with a `bounded_order` structure such that larger
`integration_params` produce larger filters.

## Main definitions

### Integration parameters

The structure `box_integral.integration_params` has 3 boolean fields with the following meaning:

* `bRiemann`: the value `tt` means that the filter corresponds to a Riemann-style integral, i.e. in
  the definition of integrability we require a constant upper estimate `r` on the size of boxes of a
  tagged partition; the value `ff` means that the estimate may depend on the position of the tag.

* `bHenstock`: the value `tt` means that we require that each tag belongs to its own closed box; the
  value `ff` means that we only require that tags belong to the ambient box.

* `bDistortion`: the value `tt` means that `r` can depend on the maximal ratio of sides of the same
  box of a partition. Presence of this case make quite a few proofs harder but we can prove the
  divergence theorem only for the filter
  `box_integral.integration_params.GP = ⊥ = {bRiemann := ff, bHenstock := tt, bDistortion := tt}`.

### Well-known sets of parameters

Out of eight possible values of `box_integral.integration_params`, the following four are used in
the library.

* `box_integral.integration_params.Riemann` (`bRiemann = tt`, `bHenstock = tt`, `bDistortion = ff`):
  this value corresponds to the Riemann integral; in the corresponding filter, we require that the
  diameters of all boxes `J` of a tagged partition are bounded from above by a constant upper
  estimate that may not depend on the geometry of `J`, and each tag belongs to the corresponding
  closed box.

* `box_integral.integration_params.Henstock` (`bRiemann = ff`, `bHenstock = tt`,
  `bDistortion = ff`): this value corresponds to the most natural generalization of
  Henstock-Kurzweil integral to higher dimension; the only (but important!) difference between this
  theory and Riemann integral is that instead of a constant upper estimate on the size of all boxes
  of a partition, we require that the partition is *subordinate* to a possibly discontinuous
  function `r : (ι → ℝ) → {x : ℝ | 0 < x}`, i.e. each box `J` is included in a closed ball with
  center `π.tag J` and radius `r J`.

* `box_integral.integration_params.McShane` (`bRiemann = ff`, `bHenstock = ff`, `bDistortion = ff`):
  this value corresponds to the McShane integral; the only difference with the Henstock integral is
  that we allow tags to be outside of their boxes; the tags still have to be in the ambient closed
  box, and the partition still has to be subordinate to a function.

* `box_integral.integration_params.GP = ⊥` (`bRiemann = ff`, `bHenstock = tt`, `bDistortion = tt`):
  this is the least integration theory in our list, i.e., all functions integrable in any other
  theory is integrable in this one as well.  This is a non-standard generalization of the
  Henstock-Kurzweil integral to higher dimension.  In dimension one, it generates the same filter as
  `Henstock`. In higher dimension, this generalization defines an integration theory such that the
  divergence of any Fréchet differentiable function `f` is integrable, and its integral is equal to
  the sum of integrals of `f` over the faces of the box, taken with appropriate signs.

  A function `f` is `GP`-integrable if for any `ε > 0` and `c : ℝ≥0` there exists
  `r : (ι → ℝ) → {x : ℝ | 0 < x}` such that for any tagged partition `π` subordinate to `r`, if each
  tag belongs to the corresponding closed box and for each box `J ∈ π`, the maximal ratio of its
  sides is less than or equal to `c`, then the integral sum of `f` over `π` is `ε`-close to the
  integral.

### Filters and predicates on `tagged_prepartition I`

For each value of `integration_params` and a rectangular box `I`, we define a few filters on
`tagged_prepartition I`. First, we define a predicate

```
structure box_integral.integration_params.mem_base_set (l : box_integral.integration_params)
  (I : box_integral.box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
  (π : box_integral.tagged_prepartition I) : Prop :=
```

This predicate says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs to the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equal to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c` that covers
  exactly `I \ π.Union`.

The last condition is always true for `c > 1`, see TODO section for more details.

Then we define a predicate `box_integral.integration_params.r_cond` on functions
`r : (ι → ℝ) → {x : ℝ | 0 < x}`. If `l.bRiemann`, then this predicate requires `r` to be a constant
function, otherwise it imposes no restrictions on `r`. We introduce this definition to prove a few
dot-notation lemmas: e.g., `box_integral.integration_params.r_cond.min` says that the pointwise
minimum of two functions that satisfy this condition satisfies this condition as well.

Then we define four filters on `box_integral.tagged_prepartition I`.

* `box_integral.integration_params.to_filter_distortion`: an auxiliary filter that takes parameters
  `(l : box_integral.integration_params) (I : box_integral.box ι) (c : ℝ≥0)` and returns the
  filter generated by all sets `{π | mem_base_set l I c r π}`, where `r` is a function satisfying
  the predicate `box_integral.integration_params.r_cond l`;

* `box_integral.integration_params.to_filter l I`: the supremum of `l.to_filter_distortion I c`
  over all `c : ℝ≥0`;

* `box_integral.integration_params.to_filter_distortion_Union l I c π₀`, where `π₀` is a
  prepartition of `I`: the infimum of `l.to_filter_distortion I c` and the principal filter
  generated by `{π | π.Union = π₀.Union}`;

* `box_integral.integration_params.to_filter_Union l I π₀`: the supremum of
  `l.to_filter_distortion_Union l I c π₀` over all `c : ℝ≥0`. This is the filter (in the case
  `π₀ = ⊤` is the one-box partition of `I`) used in the definition of the integral of a function
  over a box.

## Implementation details

* Later we define the integral of a function over a rectangular box as the limit (if it exists) of
  the integral sums along `box_integral.integration_params.to_filter_Union l I ⊤`. While it is
  possible to define the integral with a general filter on `box_integral.tagged_prepartition I` as a
  parameter, many lemmas (e.g., Sacks-Henstock lemma and most results about integrability of
  functions) require the filter to have a predictable structure. So, instead of adding assumptions
  about the filter here and there, we define this auxiliary type that can encode all integration
  theories we need in practice.

* While the definition of the integral only uses the filter
  `box_integral.integration_params.to_filter_Union l I ⊤` and partitions of a box, some lemmas
  (e.g., the Henstock-Sacks lemmas) are best formulated in terms of the predicate `mem_base_set` and
  other filters defined above.

* We use `bool` instead of `Prop` for the fields of `integration_params` in order to have decidable
  equality and inequalities.

## TODO

Currently, `box_integral.integration_params.mem_base_set` explicitly requires that there exists a
partition of the complement `I \ π.Union` with distortion `≤ c`. For `c > 1`, this condition is
always true but the proof of this fact requires more API about
`box_integral.prepartition.split_many`. We should formalize this fact, then either require `c > 1`
everywhere, or replace `≤ c` with `< c` so that we automatically get `c > 1` for a non-trivial
prepartition (and consider the special case `π = ⊥` separately if needed).

## Tags

integral, rectangular box, partition, filter
-/


open Set Function Filter Metric Finset Bool

open Classical Topology Filter NNReal

noncomputable section

namespace BoxIntegral

variable {ι : Type _} [Fintype ι] {I J : Box ι} {c c₁ c₂ : ℝ≥0} {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}
  {π π₁ π₂ : TaggedPrepartition I}

open TaggedPrepartition

/-- An `integration_params` is a structure holding 3 boolean values used to define a filter to be
used in the definition of a box-integrable function.

* `bRiemann`: the value `tt` means that the filter corresponds to a Riemann-style integral, i.e. in
  the definition of integrability we require a constant upper estimate `r` on the size of boxes of a
  tagged partition; the value `ff` means that the estimate may depend on the position of the tag.

* `bHenstock`: the value `tt` means that we require that each tag belongs to its own closed box; the
  value `ff` means that we only require that tags belong to the ambient box.

* `bDistortion`: the value `tt` means that `r` can depend on the maximal ratio of sides of the same
  box of a partition. Presence of this case makes quite a few proofs harder but we can prove the
  divergence theorem only for the filter
  `box_integral.integration_params.GP = ⊥ = {bRiemann := ff, bHenstock := tt, bDistortion := tt}`.
-/
@[ext]
structure IntegrationParams : Type where
  (bRiemann bHenstock bDistortion : Bool)
#align box_integral.integration_params BoxIntegral.IntegrationParams

variable {l l₁ l₂ : IntegrationParams}

namespace IntegrationParams

/-- Auxiliary equivalence with a product type used to lift an order. -/
def equivProd : IntegrationParams ≃ Bool × Boolᵒᵈ × Boolᵒᵈ
    where
  toFun l := ⟨l.1, OrderDual.toDual l.2, OrderDual.toDual l.3⟩
  invFun l := ⟨l.1, OrderDual.ofDual l.2.1, OrderDual.ofDual l.2.2⟩
  left_inv := fun ⟨a, b, c⟩ => rfl
  right_inv := fun ⟨a, b, c⟩ => rfl
#align box_integral.integration_params.equiv_prod BoxIntegral.IntegrationParams.equivProd

instance : PartialOrder IntegrationParams :=
  PartialOrder.lift equivProd equivProd.Injective

/-- Auxiliary `order_iso` with a product type used to lift a `bounded_order` structure. -/
def isoProd : IntegrationParams ≃o Bool × Boolᵒᵈ × Boolᵒᵈ :=
  ⟨equivProd, fun ⟨x, y, z⟩ => Iff.rfl⟩
#align box_integral.integration_params.iso_prod BoxIntegral.IntegrationParams.isoProd

instance : BoundedOrder IntegrationParams :=
  isoProd.symm.toGaloisInsertion.liftBoundedOrder

/-- The value
`box_integral.integration_params.GP = ⊥` (`bRiemann = ff`, `bHenstock = tt`, `bDistortion = tt`)
corresponds to a generalization of the Henstock integral such that the Divergence theorem holds true
without additional integrability assumptions, see the module docstring for details. -/
instance : Inhabited IntegrationParams :=
  ⟨⊥⟩

instance : DecidableRel ((· ≤ ·) : IntegrationParams → IntegrationParams → Prop) := fun _ _ =>
  And.decidable

instance : DecidableEq IntegrationParams := fun x y => decidable_of_iff _ (ext_iff x y).symm

/-- The `box_integral.integration_params` corresponding to the Riemann integral. In the
corresponding filter, we require that the diameters of all boxes `J` of a tagged partition are
bounded from above by a constant upper estimate that may not depend on the geometry of `J`, and each
tag belongs to the corresponding closed box. -/
def riemann : IntegrationParams where
  bRiemann := true
  bHenstock := true
  bDistortion := false
#align box_integral.integration_params.Riemann BoxIntegral.IntegrationParams.riemann

/-- The `box_integral.integration_params` corresponding to the Henstock-Kurzweil integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r` and each tag belongs to the corresponding closed box. -/
def henstock : IntegrationParams :=
  ⟨false, true, false⟩
#align box_integral.integration_params.Henstock BoxIntegral.IntegrationParams.henstock

/-- The `box_integral.integration_params` corresponding to the McShane integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r`; the tags may be outside of the corresponding closed box
(but still inside the ambient closed box `I.Icc`). -/
def mcShane : IntegrationParams :=
  ⟨false, false, false⟩
#align box_integral.integration_params.McShane BoxIntegral.IntegrationParams.mcShane

/-- The `box_integral.integration_params` corresponding to the generalized Perron integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r` and each tag belongs to the corresponding closed box. We also
require an upper estimate on the distortion of all boxes of the partition. -/
def gP : IntegrationParams :=
  ⊥
#align box_integral.integration_params.GP BoxIntegral.IntegrationParams.gP

theorem henstock_le_riemann : henstock ≤ riemann := by decide
#align box_integral.integration_params.Henstock_le_Riemann BoxIntegral.IntegrationParams.henstock_le_riemann

theorem henstock_le_mcShane : henstock ≤ mcShane := by decide
#align box_integral.integration_params.Henstock_le_McShane BoxIntegral.IntegrationParams.henstock_le_mcShane

theorem gP_le : gP ≤ l :=
  bot_le
#align box_integral.integration_params.GP_le BoxIntegral.IntegrationParams.gP_le

/-- The predicate corresponding to a base set of the filter defined by an
`integration_params`. It says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs to the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equal to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c` that covers
  exactly `I \ π.Union`.

The last condition is automatically verified for partitions, and is used in the proof of the
Sacks-Henstock inequality to compare two prepartitions covering the same part of the box.

It is also automatically satisfied for any `c > 1`, see TODO section of the module docstring for
details. -/
@[protect_proj]
structure MemBaseSet (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
  (π : TaggedPrepartition I) : Prop where
  IsSubordinate : π.IsSubordinate r
  IsHenstock : l.bHenstock → π.IsHenstock
  distortion_le : l.bDistortion → π.distortion ≤ c
  exists_compl : l.bDistortion → ∃ π' : Prepartition I, π'.iUnion = I \ π.iUnion ∧ π'.distortion ≤ c
#align box_integral.integration_params.mem_base_set BoxIntegral.IntegrationParams.MemBaseSet

/-- A predicate saying that in case `l.bRiemann = tt`, the function `r` is a constant. -/
def RCond {ι : Type _} (l : IntegrationParams) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  l.bRiemann → ∀ x, r x = r 0
#align box_integral.integration_params.r_cond BoxIntegral.IntegrationParams.RCond

/-- A set `s : set (tagged_prepartition I)` belongs to `l.to_filter_distortion I c` if there exists
a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tt`) such that `s` contains each
prepartition `π` such that `l.mem_base_set I c r π`. -/
def toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) :
    Filter (TaggedPrepartition I) :=
  ⨅ (r : (ι → ℝ) → Ioi (0 : ℝ)) (hr : l.RCond r), 𝓟 { π | l.MemBaseSet I c r π }
#align box_integral.integration_params.to_filter_distortion BoxIntegral.IntegrationParams.toFilterDistortion

/-- A set `s : set (tagged_prepartition I)` belongs to `l.to_filter I` if for any `c : ℝ≥0` there
exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tt`) such that
`s` contains each prepartition `π` such that `l.mem_base_set I c r π`. -/
def toFilter (l : IntegrationParams) (I : Box ι) : Filter (TaggedPrepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortion I c
#align box_integral.integration_params.to_filter BoxIntegral.IntegrationParams.toFilter

/-- A set `s : set (tagged_prepartition I)` belongs to `l.to_filter_distortion_Union I c π₀` if
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tt`) such that `s`
contains each prepartition `π` such that `l.mem_base_set I c r π` and `π.Union = π₀.Union`. -/
def toFilterDistortionUnion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (π₀ : Prepartition I) :=
  l.toFilterDistortion I c ⊓ 𝓟 { π | π.iUnion = π₀.iUnion }
#align box_integral.integration_params.to_filter_distortion_Union BoxIntegral.IntegrationParams.toFilterDistortionUnion

/-- A set `s : set (tagged_prepartition I)` belongs to `l.to_filter_Union I π₀` if for any `c : ℝ≥0`
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tt`) such that `s`
contains each prepartition `π` such that `l.mem_base_set I c r π` and `π.Union = π₀.Union`. -/
def toFilterUnion (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortionUnion I c π₀
#align box_integral.integration_params.to_filter_Union BoxIntegral.IntegrationParams.toFilterUnion

theorem rCond_of_bRiemann_eq_false {ι} (l : IntegrationParams) (hl : l.bRiemann = false)
    {r : (ι → ℝ) → Ioi (0 : ℝ)} : l.RCond r := by simp [r_cond, hl]
#align box_integral.integration_params.r_cond_of_bRiemann_eq_ff BoxIntegral.IntegrationParams.rCond_of_bRiemann_eq_false

theorem toFilter_inf_iUnion_eq (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    l.toFilter I ⊓ 𝓟 { π | π.iUnion = π₀.iUnion } = l.toFilterUnion I π₀ :=
  (iSup_inf_principal _ _).symm
#align box_integral.integration_params.to_filter_inf_Union_eq BoxIntegral.IntegrationParams.toFilter_inf_iUnion_eq

theorem MemBaseSet.mono' (I : Box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) {π : TaggedPrepartition I}
    (hr : ∀ J ∈ π, r₁ (π.Tag J) ≤ r₂ (π.Tag J)) (hπ : l₁.MemBaseSet I c₁ r₁ π) :
    l₂.MemBaseSet I c₂ r₂ π :=
  ⟨hπ.1.mono' hr, fun h₂ => hπ.2 (le_iff_imp.1 h.2.1 h₂), fun hD =>
    (hπ.3 (le_iff_imp.1 h.2.2 hD)).trans hc, fun hD =>
    (hπ.4 (le_iff_imp.1 h.2.2 hD)).imp fun π hπ => ⟨hπ.1, hπ.2.trans hc⟩⟩
#align box_integral.integration_params.mem_base_set.mono' BoxIntegral.IntegrationParams.MemBaseSet.mono'

@[mono]
theorem MemBaseSet.mono (I : Box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) {π : TaggedPrepartition I}
    (hr : ∀ x ∈ I.Icc, r₁ x ≤ r₂ x) (hπ : l₁.MemBaseSet I c₁ r₁ π) : l₂.MemBaseSet I c₂ r₂ π :=
  hπ.mono' I h hc fun J hJ => hr _ <| π.tag_mem_Icc J
#align box_integral.integration_params.mem_base_set.mono BoxIntegral.IntegrationParams.MemBaseSet.mono

theorem MemBaseSet.exists_common_compl (h₁ : l.MemBaseSet I c₁ r₁ π₁) (h₂ : l.MemBaseSet I c₂ r₂ π₂)
    (hU : π₁.iUnion = π₂.iUnion) :
    ∃ π : Prepartition I,
      π.iUnion = I \ π₁.iUnion ∧
        (l.bDistortion → π.distortion ≤ c₁) ∧ (l.bDistortion → π.distortion ≤ c₂) :=
  by
  wlog hc : c₁ ≤ c₂
  · simpa [hU, and_comm'] using this h₂ h₁ hU.symm (le_of_not_le hc)
  by_cases hD : (l.bDistortion : Prop)
  · rcases h₁.4 hD with ⟨π, hπU, hπc⟩
    exact ⟨π, hπU, fun _ => hπc, fun _ => hπc.trans hc⟩
  ·
    exact
      ⟨π₁.to_prepartition.compl, π₁.to_prepartition.Union_compl, fun h => (hD h).elim, fun h =>
        (hD h).elim⟩
#align box_integral.integration_params.mem_base_set.exists_common_compl BoxIntegral.IntegrationParams.MemBaseSet.exists_common_compl

protected theorem MemBaseSet.unionComplToSubordinate (hπ₁ : l.MemBaseSet I c r₁ π₁)
    (hle : ∀ x ∈ I.Icc, r₂ x ≤ r₁ x) {π₂ : Prepartition I} (hU : π₂.iUnion = I \ π₁.iUnion)
    (hc : l.bDistortion → π₂.distortion ≤ c) :
    l.MemBaseSet I c r₁ (π₁.unionComplToSubordinate π₂ hU r₂) :=
  ⟨hπ₁.1.disjUnion ((π₂.isSubordinate_toSubordinate r₂).mono hle) _, fun h =>
    (hπ₁.2 h).disjUnion (π₂.isHenstock_toSubordinate _) _, fun h =>
    (distortion_unionComplToSubordinate _ _ _ _).trans_le (max_le (hπ₁.3 h) (hc h)), fun _ =>
    ⟨⊥, by simp⟩⟩
#align box_integral.integration_params.mem_base_set.union_compl_to_subordinate BoxIntegral.IntegrationParams.MemBaseSet.unionComplToSubordinate

protected theorem MemBaseSet.filter (hπ : l.MemBaseSet I c r π) (p : Box ι → Prop) :
    l.MemBaseSet I c r (π.filterₓ p) :=
  by
  refine'
    ⟨fun J hJ => hπ.1 J (π.mem_filter.1 hJ).1, fun hH J hJ => hπ.2 hH J (π.mem_filter.1 hJ).1,
      fun hD => (distortion_filter_le _ _).trans (hπ.3 hD), fun hD => _⟩
  rcases hπ.4 hD with ⟨π₁, hπ₁U, hc⟩
  set π₂ := π.filter fun J => ¬p J
  have : Disjoint π₁.Union π₂.Union := by
    simpa [π₂, hπ₁U] using disjoint_sdiff_self_left.mono_right sdiff_le
  refine' ⟨π₁.disj_union π₂.to_prepartition this, _, _⟩
  · suffices ↑I \ π.Union ∪ π.Union \ (π.filter p).iUnion = ↑I \ (π.filter p).iUnion by simpa [*]
    have : (π.filter p).iUnion ⊆ π.Union := bUnion_subset_bUnion_left (Finset.filter_subset _ _)
    ext x
    fconstructor
    · rintro (⟨hxI, hxπ⟩ | ⟨hxπ, hxp⟩)
      exacts[⟨hxI, mt (@this x) hxπ⟩, ⟨π.Union_subset hxπ, hxp⟩]
    · rintro ⟨hxI, hxp⟩
      by_cases hxπ : x ∈ π.Union
      exacts[Or.inr ⟨hxπ, hxp⟩, Or.inl ⟨hxI, hxπ⟩]
  · have : (π.filter fun J => ¬p J).distortion ≤ c := (distortion_filter_le _ _).trans (hπ.3 hD)
    simpa [hc]
#align box_integral.integration_params.mem_base_set.filter BoxIntegral.IntegrationParams.MemBaseSet.filter

theorem bUnionTaggedMemBaseSet {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J}
    (h : ∀ J ∈ π, l.MemBaseSet J c r (πi J)) (hp : ∀ J ∈ π, (πi J).IsPartition)
    (hc : l.bDistortion → π.compl.distortion ≤ c) : l.MemBaseSet I c r (π.biUnionTagged πi) :=
  by
  refine'
    ⟨tagged_prepartition.is_subordinate_bUnion_tagged.2 fun J hJ => (h J hJ).1, fun hH =>
      tagged_prepartition.is_Henstock_bUnion_tagged.2 fun J hJ => (h J hJ).2 hH, fun hD => _,
      fun hD => _⟩
  · rw [prepartition.distortion_bUnion_tagged, Finset.sup_le_iff]
    exact fun J hJ => (h J hJ).3 hD
  · refine' ⟨_, _, hc hD⟩
    rw [π.Union_compl, ← π.Union_bUnion_partition hp]
    rfl
#align box_integral.integration_params.bUnion_tagged_mem_base_set BoxIntegral.IntegrationParams.bUnionTaggedMemBaseSet

@[mono]
theorem RCond.mono {ι : Type _} {r : (ι → ℝ) → Ioi (0 : ℝ)} (h : l₁ ≤ l₂) (hr : l₂.RCond r) :
    l₁.RCond r := fun hR => hr (le_iff_imp.1 h.1 hR)
#align box_integral.integration_params.r_cond.mono BoxIntegral.IntegrationParams.RCond.mono

theorem RCond.min {ι : Type _} {r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)} (h₁ : l.RCond r₁) (h₂ : l.RCond r₂) :
    l.RCond fun x => min (r₁ x) (r₂ x) := fun hR x => congr_arg₂ min (h₁ hR x) (h₂ hR x)
#align box_integral.integration_params.r_cond.min BoxIntegral.IntegrationParams.RCond.min

@[mono]
theorem toFilterDistortion_mono (I : Box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) :
    l₁.toFilterDistortion I c₁ ≤ l₂.toFilterDistortion I c₂ :=
  iInf_mono fun r =>
    iInf_mono' fun hr =>
      ⟨hr.mono h, principal_mono.2 fun _ => MemBaseSet.mono I h hc fun _ _ => le_rfl⟩
#align box_integral.integration_params.to_filter_distortion_mono BoxIntegral.IntegrationParams.toFilterDistortion_mono

@[mono]
theorem toFilter_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ ≤ l₂) :
    l₁.toFilter I ≤ l₂.toFilter I :=
  iSup_mono fun c => toFilterDistortion_mono I h le_rfl
#align box_integral.integration_params.to_filter_mono BoxIntegral.IntegrationParams.toFilter_mono

@[mono]
theorem toFilterUnion_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ ≤ l₂)
    (π₀ : Prepartition I) : l₁.toFilterUnion I π₀ ≤ l₂.toFilterUnion I π₀ :=
  iSup_mono fun c => inf_le_inf_right _ <| toFilterDistortion_mono _ h le_rfl
#align box_integral.integration_params.to_filter_Union_mono BoxIntegral.IntegrationParams.toFilterUnion_mono

theorem toFilterUnion_congr (I : Box ι) (l : IntegrationParams) {π₁ π₂ : Prepartition I}
    (h : π₁.iUnion = π₂.iUnion) : l.toFilterUnion I π₁ = l.toFilterUnion I π₂ := by
  simp only [to_filter_Union, to_filter_distortion_Union, h]
#align box_integral.integration_params.to_filter_Union_congr BoxIntegral.IntegrationParams.toFilterUnion_congr

theorem hasBasis_toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) :
    (l.toFilterDistortion I c).HasBasis l.RCond fun r => { π | l.MemBaseSet I c r π } :=
  hasBasis_biInf_principal'
    (fun r₁ hr₁ r₂ hr₂ =>
      ⟨_, hr₁.min hr₂, fun _ => MemBaseSet.mono _ le_rfl le_rfl fun x hx => min_le_left _ _,
        fun _ => MemBaseSet.mono _ le_rfl le_rfl fun x hx => min_le_right _ _⟩)
    ⟨fun _ => ⟨1, zero_lt_one⟩, fun _ _ => rfl⟩
#align box_integral.integration_params.has_basis_to_filter_distortion BoxIntegral.IntegrationParams.hasBasis_toFilterDistortion

theorem hasBasis_toFilterDistortionUnion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0)
    (π₀ : Prepartition I) :
    (l.toFilterDistortionUnion I c π₀).HasBasis l.RCond fun r =>
      { π | l.MemBaseSet I c r π ∧ π.iUnion = π₀.iUnion } :=
  (l.hasBasis_toFilterDistortion I c).inf_principal _
#align box_integral.integration_params.has_basis_to_filter_distortion_Union BoxIntegral.IntegrationParams.hasBasis_toFilterDistortionUnion

theorem hasBasis_toFilterUnion (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilterUnion I π₀).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π ∧ π.iUnion = π₀.iUnion } :=
  by
  have := fun c => l.hasBasis_toFilterDistortionUnion I c π₀
  simpa only [set_of_and, set_of_exists] using has_basis_supr this
#align box_integral.integration_params.has_basis_to_filter_Union BoxIntegral.IntegrationParams.hasBasis_toFilterUnion

theorem hasBasis_toFilterUnion_top (l : IntegrationParams) (I : Box ι) :
    (l.toFilterUnion I ⊤).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π ∧ π.IsPartition } :=
  by
  simpa only [tagged_prepartition.is_partition_iff_Union_eq, prepartition.Union_top] using
    l.has_basis_to_filter_Union I ⊤
#align box_integral.integration_params.has_basis_to_filter_Union_top BoxIntegral.IntegrationParams.hasBasis_toFilterUnion_top

theorem hasBasis_toFilter (l : IntegrationParams) (I : Box ι) :
    (l.toFilter I).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c)) fun r =>
      { π | ∃ c, l.MemBaseSet I c (r c) π } :=
  by simpa only [set_of_exists] using has_basis_supr (l.has_basis_to_filter_distortion I)
#align box_integral.integration_params.has_basis_to_filter BoxIntegral.IntegrationParams.hasBasis_toFilter

theorem tendsto_embedBox_toFilterUnion_top (l : IntegrationParams) (h : I ≤ J) :
    Tendsto (TaggedPrepartition.embedBox I J h) (l.toFilterUnion I ⊤)
      (l.toFilterUnion J (Prepartition.single J I h)) :=
  by
  simp only [to_filter_Union, tendsto_supr]; intro c
  set π₀ := prepartition.single J I h
  refine' le_iSup_of_le (max c π₀.compl.distortion) _
  refine'
    ((l.has_basis_to_filter_distortion_Union I c ⊤).tendsto_iffₓ
          (l.has_basis_to_filter_distortion_Union J _ _)).2
      fun r hr => _
  refine' ⟨r, hr, fun π hπ => _⟩
  rw [mem_set_of_eq, prepartition.Union_top] at hπ
  refine' ⟨⟨hπ.1.1, hπ.1.2, fun hD => le_trans (hπ.1.3 hD) (le_max_left _ _), fun hD => _⟩, _⟩
  · refine' ⟨_, π₀.Union_compl.trans _, le_max_right _ _⟩
    congr 1
    exact (prepartition.Union_single h).trans hπ.2.symm
  · exact hπ.2.trans (prepartition.Union_single _).symm
#align box_integral.integration_params.tendsto_embed_box_to_filter_Union_top BoxIntegral.IntegrationParams.tendsto_embedBox_toFilterUnion_top

theorem exists_memBaseSet_le_iUnion_eq (l : IntegrationParams) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    ∃ π, l.MemBaseSet I c r π ∧ π.toPrepartition ≤ π₀ ∧ π.iUnion = π₀.iUnion :=
  by
  rcases π₀.exists_tagged_le_is_Henstock_is_subordinate_Union_eq r with ⟨π, hle, hH, hr, hd, hU⟩
  refine' ⟨π, ⟨hr, fun _ => hH, fun _ => hd.trans_le hc₁, fun hD => ⟨π₀.compl, _, hc₂⟩⟩, ⟨hle, hU⟩⟩
  exact prepartition.compl_congr hU ▸ π.to_prepartition.Union_compl
#align box_integral.integration_params.exists_mem_base_set_le_Union_eq BoxIntegral.IntegrationParams.exists_memBaseSet_le_iUnion_eq

theorem exists_memBaseSet_isPartition (l : IntegrationParams) (I : Box ι) (hc : I.distortion ≤ c)
    (r : (ι → ℝ) → Ioi (0 : ℝ)) : ∃ π, l.MemBaseSet I c r π ∧ π.IsPartition :=
  by
  rw [← prepartition.distortion_top] at hc
  have hc' : (⊤ : prepartition I).compl.distortion ≤ c := by simp
  simpa [is_partition_iff_Union_eq] using l.exists_mem_base_set_le_Union_eq ⊤ hc hc' r
#align box_integral.integration_params.exists_mem_base_set_is_partition BoxIntegral.IntegrationParams.exists_memBaseSet_isPartition

theorem toFilterDistortionUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) :
    (l.toFilterDistortionUnion I c π₀).ne_bot :=
  ((l.hasBasis_toFilterDistortion I _).inf_principal _).neBot_iff.2 fun r hr =>
    (l.exists_memBaseSet_le_iUnion_eq π₀ hc₁ hc₂ r).imp fun π hπ => ⟨hπ.1, hπ.2.2⟩
#align box_integral.integration_params.to_filter_distortion_Union_ne_bot BoxIntegral.IntegrationParams.toFilterDistortionUnion_neBot

instance toFilterDistortionUnion_ne_bot' (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilterDistortionUnion I (max π₀.distortion π₀.compl.distortion) π₀).ne_bot :=
  l.toFilterDistortionUnion_neBot I π₀ (le_max_left _ _) (le_max_right _ _)
#align box_integral.integration_params.to_filter_distortion_Union_ne_bot' BoxIntegral.IntegrationParams.toFilterDistortionUnion_ne_bot'

instance toFilterDistortion_neBot (l : IntegrationParams) (I : Box ι) :
    (l.toFilterDistortion I I.distortion).ne_bot := by
  simpa using (l.to_filter_distortion_Union_ne_bot' I ⊤).mono inf_le_left
#align box_integral.integration_params.to_filter_distortion_ne_bot BoxIntegral.IntegrationParams.toFilterDistortion_neBot

instance toFilter_neBot (l : IntegrationParams) (I : Box ι) : (l.toFilter I).ne_bot :=
  (l.toFilterDistortion_neBot I).mono <| le_iSup _ _
#align box_integral.integration_params.to_filter_ne_bot BoxIntegral.IntegrationParams.toFilter_neBot

instance toFilterUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilterUnion I π₀).ne_bot :=
  (l.toFilterDistortionUnion_ne_bot' I π₀).mono <|
    le_iSup (fun c => l.toFilterDistortionUnion I c π₀) _
#align box_integral.integration_params.to_filter_Union_ne_bot BoxIntegral.IntegrationParams.toFilterUnion_neBot

theorem eventually_isPartition (l : IntegrationParams) (I : Box ι) :
    ∀ᶠ π in l.toFilterUnion I ⊤, TaggedPrepartition.IsPartition π :=
  eventually_iSup.2 fun c =>
    eventually_inf_principal.2 <|
      eventually_of_forall fun π h =>
        π.isPartition_iff_iUnion_eq.2 (h.trans Prepartition.iUnion_top)
#align box_integral.integration_params.eventually_is_partition BoxIntegral.IntegrationParams.eventually_isPartition

end IntegrationParams

end BoxIntegral

