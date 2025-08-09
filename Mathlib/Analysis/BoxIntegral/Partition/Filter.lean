/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
import Mathlib.Analysis.BoxIntegral.Partition.Split

/-!
# Filters used in box-based integrals

First we define a structure `BoxIntegral.IntegrationParams`. This structure will be used as an
argument in the definition of `BoxIntegral.integral` in order to use the same definition for a few
well-known definitions of integrals based on partitions of a rectangular box into subboxes (Riemann
integral, Henstock-Kurzweil integral, and McShane integral).

This structure holds three boolean values (see below), and encodes eight different sets of
parameters; only four of these values are used somewhere in `mathlib4`. Three of them correspond to
the integration theories listed above, and one is a generalization of the one-dimensional
Henstock-Kurzweil integral such that the divergence theorem works without additional integrability
assumptions.

Finally, for each set of parameters `l : BoxIntegral.IntegrationParams` and a rectangular box
`I : BoxIntegral.Box ι`, we define several `Filter`s that will be used either in the definition of
the corresponding integral, or in the proofs of its properties. We equip
`BoxIntegral.IntegrationParams` with a `BoundedOrder` structure such that larger
`IntegrationParams` produce larger filters.

## Main definitions

### Integration parameters

The structure `BoxIntegral.IntegrationParams` has 3 boolean fields with the following meaning:

* `bRiemann`: the value `true` means that the filter corresponds to a Riemann-style integral, i.e.
  in the definition of integrability we require a constant upper estimate `r` on the size of boxes
  of a tagged partition; the value `false` means that the estimate may depend on the position of the
  tag.

* `bHenstock`: the value `true` means that we require that each tag belongs to its own closed box;
  the value `false` means that we only require that tags belong to the ambient box.

* `bDistortion`: the value `true` means that `r` can depend on the maximal ratio of sides of the
  same box of a partition. Presence of this case make quite a few proofs harder but we can prove the
  divergence theorem only for the filter `BoxIntegral.IntegrationParams.GP = ⊥ =
  {bRiemann := false, bHenstock := true, bDistortion := true}`.

### Well-known sets of parameters

Out of eight possible values of `BoxIntegral.IntegrationParams`, the following four are used in
the library.

* `BoxIntegral.IntegrationParams.Riemann` (`bRiemann = true`, `bHenstock = true`,
  `bDistortion = false`): this value corresponds to the Riemann integral; in the corresponding
  filter, we require that the diameters of all boxes `J` of a tagged partition are bounded from
  above by a constant upper estimate that may not depend on the geometry of `J`, and each tag
  belongs to the corresponding closed box.

* `BoxIntegral.IntegrationParams.Henstock` (`bRiemann = false`, `bHenstock = true`,
  `bDistortion = false`): this value corresponds to the most natural generalization of
  Henstock-Kurzweil integral to higher dimension; the only (but important!) difference between this
  theory and Riemann integral is that instead of a constant upper estimate on the size of all boxes
  of a partition, we require that the partition is *subordinate* to a possibly discontinuous
  function `r : (ι → ℝ) → {x : ℝ | 0 < x}`, i.e. each box `J` is included in a closed ball with
  center `π.tag J` and radius `r J`.

* `BoxIntegral.IntegrationParams.McShane` (`bRiemann = false`, `bHenstock = false`,
  `bDistortion = false`): this value corresponds to the McShane integral; the only difference with
  the Henstock integral is that we allow tags to be outside of their boxes; the tags still have to
  be in the ambient closed box, and the partition still has to be subordinate to a function.

* `BoxIntegral.IntegrationParams.GP = ⊥` (`bRiemann = false`, `bHenstock = true`,
  `bDistortion = true`): this is the least integration theory in our list, i.e., all functions
  integrable in any other theory is integrable in this one as well.  This is a non-standard
  generalization of the Henstock-Kurzweil integral to higher dimension.  In dimension one, it
  generates the same filter as `Henstock`. In higher dimension, this generalization defines an
  integration theory such that the divergence of any Fréchet differentiable function `f` is
  integrable, and its integral is equal to the sum of integrals of `f` over the faces of the box,
  taken with appropriate signs.

  A function `f` is `GP`-integrable if for any `ε > 0` and `c : ℝ≥0` there exists
  `r : (ι → ℝ) → {x : ℝ | 0 < x}` such that for any tagged partition `π` subordinate to `r`, if each
  tag belongs to the corresponding closed box and for each box `J ∈ π`, the maximal ratio of its
  sides is less than or equal to `c`, then the integral sum of `f` over `π` is `ε`-close to the
  integral.

### Filters and predicates on `TaggedPrepartition I`

For each value of `IntegrationParams` and a rectangular box `I`, we define a few filters on
`TaggedPrepartition I`. First, we define a predicate

```
structure BoxIntegral.IntegrationParams.MemBaseSet (l : BoxIntegral.IntegrationParams)
  (I : BoxIntegral.Box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
  (π : BoxIntegral.TaggedPrepartition I) : Prop where
```

This predicate says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs to the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equal to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c` that covers
  exactly `I \ π.iUnion`.

The last condition is always true for `c > 1`, see TODO section for more details.

Then we define a predicate `BoxIntegral.IntegrationParams.RCond` on functions
`r : (ι → ℝ) → {x : ℝ | 0 < x}`. If `l.bRiemann`, then this predicate requires `r` to be a constant
function, otherwise it imposes no restrictions on `r`. We introduce this definition to prove a few
dot-notation lemmas: e.g., `BoxIntegral.IntegrationParams.RCond.min` says that the pointwise
minimum of two functions that satisfy this condition satisfies this condition as well.

Then we define four filters on `BoxIntegral.TaggedPrepartition I`.

* `BoxIntegral.IntegrationParams.toFilterDistortion`: an auxiliary filter that takes parameters
  `(l : BoxIntegral.IntegrationParams) (I : BoxIntegral.Box ι) (c : ℝ≥0)` and returns the
  filter generated by all sets `{π | MemBaseSet l I c r π}`, where `r` is a function satisfying
  the predicate `BoxIntegral.IntegrationParams.RCond l`;

* `BoxIntegral.IntegrationParams.toFilter l I`: the supremum of `l.toFilterDistortion I c`
  over all `c : ℝ≥0`;

* `BoxIntegral.IntegrationParams.toFilterDistortioniUnion l I c π₀`, where `π₀` is a
  prepartition of `I`: the infimum of `l.toFilterDistortion I c` and the principal filter
  generated by `{π | π.iUnion = π₀.iUnion}`;

* `BoxIntegral.IntegrationParams.toFilteriUnion l I π₀`: the supremum of
  `l.toFilterDistortioniUnion l I c π₀` over all `c : ℝ≥0`. This is the filter (in the case
  `π₀ = ⊤` is the one-box partition of `I`) used in the definition of the integral of a function
  over a box.

## Implementation details

* Later we define the integral of a function over a rectangular box as the limit (if it exists) of
  the integral sums along `BoxIntegral.IntegrationParams.toFilteriUnion l I ⊤`. While it is
  possible to define the integral with a general filter on `BoxIntegral.TaggedPrepartition I` as a
  parameter, many lemmas (e.g., Sacks-Henstock lemma and most results about integrability of
  functions) require the filter to have a predictable structure. So, instead of adding assumptions
  about the filter here and there, we define this auxiliary type that can encode all integration
  theories we need in practice.

* While the definition of the integral only uses the filter
  `BoxIntegral.IntegrationParams.toFilteriUnion l I ⊤` and partitions of a box, some lemmas
  (e.g., the Henstock-Sacks lemmas) are best formulated in terms of the predicate `MemBaseSet` and
  other filters defined above.

* We use `Bool` instead of `Prop` for the fields of `IntegrationParams` in order to have decidable
  equality and inequalities.

## TODO

Currently, `BoxIntegral.IntegrationParams.MemBaseSet` explicitly requires that there exists a
partition of the complement `I \ π.iUnion` with distortion `≤ c`. For `c > 1`, this condition is
always true but the proof of this fact requires more API about
`BoxIntegral.Prepartition.splitMany`. We should formalize this fact, then either require `c > 1`
everywhere, or replace `≤ c` with `< c` so that we automatically get `c > 1` for a non-trivial
prepartition (and consider the special case `π = ⊥` separately if needed).

## Tags

integral, rectangular box, partition, filter
-/

open Set Function Filter Metric Finset Bool
open scoped Topology Filter NNReal

noncomputable section

namespace BoxIntegral

variable {ι : Type*} [Fintype ι] {I J : Box ι} {c c₁ c₂ : ℝ≥0}

open TaggedPrepartition

/-- An `IntegrationParams` is a structure holding 3 boolean values used to define a filter to be
used in the definition of a box-integrable function.

* `bRiemann`: the value `true` means that the filter corresponds to a Riemann-style integral, i.e.
  in the definition of integrability we require a constant upper estimate `r` on the size of boxes
  of a tagged partition; the value `false` means that the estimate may depend on the position of the
  tag.

* `bHenstock`: the value `true` means that we require that each tag belongs to its own closed box;
  the value `false` means that we only require that tags belong to the ambient box.

* `bDistortion`: the value `true` means that `r` can depend on the maximal ratio of sides of the
  same box of a partition. Presence of this case makes quite a few proofs harder but we can prove
  the divergence theorem only for the filter `BoxIntegral.IntegrationParams.GP = ⊥ =
  {bRiemann := false, bHenstock := true, bDistortion := true}`.
-/
@[ext]
structure IntegrationParams : Type where
  (bRiemann bHenstock bDistortion : Bool)

variable {l l₁ l₂ : IntegrationParams}

namespace IntegrationParams

/-- Auxiliary equivalence with a product type used to lift an order. -/
def equivProd : IntegrationParams ≃ Bool × Boolᵒᵈ × Boolᵒᵈ where
  toFun l := ⟨l.1, OrderDual.toDual l.2, OrderDual.toDual l.3⟩
  invFun l := ⟨l.1, OrderDual.ofDual l.2.1, OrderDual.ofDual l.2.2⟩

instance : PartialOrder IntegrationParams :=
  PartialOrder.lift equivProd equivProd.injective

/-- Auxiliary `OrderIso` with a product type used to lift a `BoundedOrder` structure. -/
def isoProd : IntegrationParams ≃o Bool × Boolᵒᵈ × Boolᵒᵈ :=
  ⟨equivProd, Iff.rfl⟩

instance : BoundedOrder IntegrationParams :=
  isoProd.symm.toGaloisInsertion.liftBoundedOrder

/-- The value `BoxIntegral.IntegrationParams.GP = ⊥`
(`bRiemann = false`, `bHenstock = true`, `bDistortion = true`)
corresponds to a generalization of the Henstock integral such that the Divergence theorem holds true
without additional integrability assumptions, see the module docstring for details. -/
instance : Inhabited IntegrationParams :=
  ⟨⊥⟩

instance : DecidableLE (IntegrationParams) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

instance : DecidableEq IntegrationParams :=
  fun _ _ => decidable_of_iff _ IntegrationParams.ext_iff.symm

/-- The `BoxIntegral.IntegrationParams` corresponding to the Riemann integral. In the
corresponding filter, we require that the diameters of all boxes `J` of a tagged partition are
bounded from above by a constant upper estimate that may not depend on the geometry of `J`, and each
tag belongs to the corresponding closed box. -/
def Riemann : IntegrationParams where
  bRiemann := true
  bHenstock := true
  bDistortion := false

/-- The `BoxIntegral.IntegrationParams` corresponding to the Henstock-Kurzweil integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r` and each tag belongs to the corresponding closed box. -/
def Henstock : IntegrationParams :=
  ⟨false, true, false⟩

/-- The `BoxIntegral.IntegrationParams` corresponding to the McShane integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r`; the tags may be outside of the corresponding closed box
(but still inside the ambient closed box `I.Icc`). -/
def McShane : IntegrationParams :=
  ⟨false, false, false⟩

/-- The `BoxIntegral.IntegrationParams` corresponding to the generalized Perron integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r` and each tag belongs to the corresponding closed box. We also
require an upper estimate on the distortion of all boxes of the partition. -/
def GP : IntegrationParams := ⊥

theorem henstock_le_riemann : Henstock ≤ Riemann := by trivial

theorem henstock_le_mcShane : Henstock ≤ McShane := by trivial

theorem gp_le : GP ≤ l :=
  bot_le

/-- The predicate corresponding to a base set of the filter defined by an
`IntegrationParams`. It says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs to the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equal to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c` that covers
  exactly `I \ π.iUnion`.

The last condition is automatically verified for partitions, and is used in the proof of the
Sacks-Henstock inequality to compare two prepartitions covering the same part of the box.

It is also automatically satisfied for any `c > 1`, see TODO section of the module docstring for
details. -/
structure MemBaseSet (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
    (π : TaggedPrepartition I) : Prop where
  protected isSubordinate : π.IsSubordinate r
  protected isHenstock : l.bHenstock → π.IsHenstock
  protected distortion_le : l.bDistortion → π.distortion ≤ c
  protected exists_compl : l.bDistortion → ∃ π' : Prepartition I,
    π'.iUnion = ↑I \ π.iUnion ∧ π'.distortion ≤ c

/-- A predicate saying that in case `l.bRiemann = true`, the function `r` is a constant. -/
def RCond {ι : Type*} (l : IntegrationParams) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  l.bRiemann → ∀ x, r x = r 0

/-- A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilterDistortion I c` if there exists
a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) such that `s` contains each
prepartition `π` such that `l.MemBaseSet I c r π`. -/
def toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) :
    Filter (TaggedPrepartition I) :=
  ⨅ (r : (ι → ℝ) → Ioi (0 : ℝ)) (_ : l.RCond r), 𝓟 { π | l.MemBaseSet I c r π }

/-- A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilter I` if for any `c : ℝ≥0` there
exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) such that
`s` contains each prepartition `π` such that `l.MemBaseSet I c r π`. -/
def toFilter (l : IntegrationParams) (I : Box ι) : Filter (TaggedPrepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortion I c

/-- A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilterDistortioniUnion I c π₀` if
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) such that `s`
contains each prepartition `π` such that `l.MemBaseSet I c r π` and `π.iUnion = π₀.iUnion`. -/
def toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (π₀ : Prepartition I) :=
  l.toFilterDistortion I c ⊓ 𝓟 { π | π.iUnion = π₀.iUnion }

/-- A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilteriUnion I π₀` if for any `c : ℝ≥0`
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) such that `s`
contains each prepartition `π` such that `l.MemBaseSet I c r π` and `π.iUnion = π₀.iUnion`. -/
def toFilteriUnion (I : Box ι) (π₀ : Prepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortioniUnion I c π₀

theorem rCond_of_bRiemann_eq_false {ι} (l : IntegrationParams) (hl : l.bRiemann = false)
    {r : (ι → ℝ) → Ioi (0 : ℝ)} : l.RCond r := by
  simp [RCond, hl]

theorem toFilter_inf_iUnion_eq (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    l.toFilter I ⊓ 𝓟 { π | π.iUnion = π₀.iUnion } = l.toFilteriUnion I π₀ :=
  (iSup_inf_principal _ _).symm

variable {r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)} {π π₁ π₂ : TaggedPrepartition I}

variable (I) in
theorem MemBaseSet.mono' (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂)
    (hr : ∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) (hπ : l₁.MemBaseSet I c₁ r₁ π) :
    l₂.MemBaseSet I c₂ r₂ π :=
  ⟨hπ.1.mono' hr, fun h₂ => hπ.2 (le_iff_imp.1 h.2.1 h₂),
    fun hD => (hπ.3 (le_iff_imp.1 h.2.2 hD)).trans hc,
    fun hD => (hπ.4 (le_iff_imp.1 h.2.2 hD)).imp fun _ hπ => ⟨hπ.1, hπ.2.trans hc⟩⟩

variable (I) in
@[mono]
theorem MemBaseSet.mono (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂)
    (hr : ∀ x ∈ Box.Icc I, r₁ x ≤ r₂ x) (hπ : l₁.MemBaseSet I c₁ r₁ π) : l₂.MemBaseSet I c₂ r₂ π :=
  hπ.mono' I h hc fun J _ => hr _ <| π.tag_mem_Icc J

theorem MemBaseSet.exists_common_compl
    (h₁ : l.MemBaseSet I c₁ r₁ π₁) (h₂ : l.MemBaseSet I c₂ r₂ π₂)
    (hU : π₁.iUnion = π₂.iUnion) :
    ∃ π : Prepartition I, π.iUnion = ↑I \ π₁.iUnion ∧
      (l.bDistortion → π.distortion ≤ c₁) ∧ (l.bDistortion → π.distortion ≤ c₂) := by
  wlog hc : c₁ ≤ c₂ with H
  · simpa [hU, _root_.and_comm] using
      @H _ _ I c₂ c₁ l r₂ r₁ π₂ π₁ h₂ h₁ hU.symm (le_of_not_ge hc)
  by_cases hD : (l.bDistortion : Prop)
  · rcases h₁.4 hD with ⟨π, hπU, hπc⟩
    exact ⟨π, hπU, fun _ => hπc, fun _ => hπc.trans hc⟩
  · exact ⟨π₁.toPrepartition.compl, π₁.toPrepartition.iUnion_compl,
      fun h => (hD h).elim, fun h => (hD h).elim⟩

protected theorem MemBaseSet.unionComplToSubordinate (hπ₁ : l.MemBaseSet I c r₁ π₁)
    (hle : ∀ x ∈ Box.Icc I, r₂ x ≤ r₁ x) {π₂ : Prepartition I} (hU : π₂.iUnion = ↑I \ π₁.iUnion)
    (hc : l.bDistortion → π₂.distortion ≤ c) :
    l.MemBaseSet I c r₁ (π₁.unionComplToSubordinate π₂ hU r₂) :=
  ⟨hπ₁.1.disjUnion ((π₂.isSubordinate_toSubordinate r₂).mono hle) _,
    fun h => (hπ₁.2 h).disjUnion (π₂.isHenstock_toSubordinate _) _,
    fun h => (distortion_unionComplToSubordinate _ _ _ _).trans_le (max_le (hπ₁.3 h) (hc h)),
    fun _ => ⟨⊥, by simp⟩⟩

variable {r : (ι → ℝ) → Ioi (0 : ℝ)}

protected theorem MemBaseSet.filter (hπ : l.MemBaseSet I c r π) (p : Box ι → Prop) :
    l.MemBaseSet I c r (π.filter p) := by
  classical
  refine ⟨fun J hJ => hπ.1 J (π.mem_filter.1 hJ).1, fun hH J hJ => hπ.2 hH J (π.mem_filter.1 hJ).1,
    fun hD => (distortion_filter_le _ _).trans (hπ.3 hD), fun hD => ?_⟩
  rcases hπ.4 hD with ⟨π₁, hπ₁U, hc⟩
  set π₂ := π.filter fun J => ¬p J
  have : Disjoint π₁.iUnion π₂.iUnion := by
    simpa [π₂, hπ₁U] using disjoint_sdiff_self_left.mono_right sdiff_le
  refine ⟨π₁.disjUnion π₂.toPrepartition this, ?_, ?_⟩
  · suffices ↑I \ π.iUnion ∪ π.iUnion \ (π.filter p).iUnion = ↑I \ (π.filter p).iUnion by
      simp [π₂, *]
    have h : (π.filter p).iUnion ⊆ π.iUnion :=
      biUnion_subset_biUnion_left (Finset.filter_subset _ _)
    ext x
    fconstructor
    · rintro (⟨hxI, hxπ⟩ | ⟨hxπ, hxp⟩)
      exacts [⟨hxI, mt (@h x) hxπ⟩, ⟨π.iUnion_subset hxπ, hxp⟩]
    · rintro ⟨hxI, hxp⟩
      by_cases hxπ : x ∈ π.iUnion
      exacts [Or.inr ⟨hxπ, hxp⟩, Or.inl ⟨hxI, hxπ⟩]
  · have : (π.filter fun J => ¬p J).distortion ≤ c := (distortion_filter_le _ _).trans (hπ.3 hD)
    simpa [hc]

theorem biUnionTagged_memBaseSet {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J}
    (h : ∀ J ∈ π, l.MemBaseSet J c r (πi J)) (hp : ∀ J ∈ π, (πi J).IsPartition)
    (hc : l.bDistortion → π.compl.distortion ≤ c) : l.MemBaseSet I c r (π.biUnionTagged πi) := by
  refine ⟨TaggedPrepartition.isSubordinate_biUnionTagged.2 fun J hJ => (h J hJ).1,
    fun hH => TaggedPrepartition.isHenstock_biUnionTagged.2 fun J hJ => (h J hJ).2 hH,
    fun hD => ?_, fun hD => ?_⟩
  · rw [Prepartition.distortion_biUnionTagged, Finset.sup_le_iff]
    exact fun J hJ => (h J hJ).3 hD
  · refine ⟨_, ?_, hc hD⟩
    rw [π.iUnion_compl, ← π.iUnion_biUnion_partition hp]
    rfl

@[mono]
theorem RCond.mono {ι : Type*} {r : (ι → ℝ) → Ioi (0 : ℝ)} (h : l₁ ≤ l₂) (hr : l₂.RCond r) :
    l₁.RCond r :=
  fun hR => hr (le_iff_imp.1 h.1 hR)

nonrec theorem RCond.min {ι : Type*} {r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)} (h₁ : l.RCond r₁)
    (h₂ : l.RCond r₂) : l.RCond fun x => min (r₁ x) (r₂ x) :=
  fun hR x => congr_arg₂ min (h₁ hR x) (h₂ hR x)

@[gcongr, mono]
theorem toFilterDistortion_mono (I : Box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) :
    l₁.toFilterDistortion I c₁ ≤ l₂.toFilterDistortion I c₂ :=
  iInf_mono fun _ =>
    iInf_mono' fun hr =>
      ⟨hr.mono h, principal_mono.2 fun _ => MemBaseSet.mono I h hc fun _ _ => le_rfl⟩

@[gcongr, mono]
theorem toFilter_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ ≤ l₂) :
    l₁.toFilter I ≤ l₂.toFilter I :=
  iSup_mono fun _ => toFilterDistortion_mono I h le_rfl

@[gcongr, mono]
theorem toFilteriUnion_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ ≤ l₂)
    (π₀ : Prepartition I) : l₁.toFilteriUnion I π₀ ≤ l₂.toFilteriUnion I π₀ :=
  iSup_mono fun _ => inf_le_inf_right _ <| toFilterDistortion_mono _ h le_rfl

theorem toFilteriUnion_congr (I : Box ι) (l : IntegrationParams) {π₁ π₂ : Prepartition I}
    (h : π₁.iUnion = π₂.iUnion) : l.toFilteriUnion I π₁ = l.toFilteriUnion I π₂ := by
  simp only [toFilteriUnion, toFilterDistortioniUnion, h]

theorem hasBasis_toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) :
    (l.toFilterDistortion I c).HasBasis l.RCond fun r => { π | l.MemBaseSet I c r π } :=
  hasBasis_biInf_principal'
    (fun _ hr₁ _ hr₂ =>
      ⟨_, hr₁.min hr₂, fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_left _ _,
        fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_right _ _⟩)
    ⟨fun _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩, fun _ _ => rfl⟩

theorem hasBasis_toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0)
    (π₀ : Prepartition I) :
    (l.toFilterDistortioniUnion I c π₀).HasBasis l.RCond fun r =>
      { π | l.MemBaseSet I c r π ∧ π.iUnion = π₀.iUnion } :=
  (l.hasBasis_toFilterDistortion I c).inf_principal _

theorem hasBasis_toFilteriUnion (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilteriUnion I π₀).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π ∧ π.iUnion = π₀.iUnion } := by
  have := fun c => l.hasBasis_toFilterDistortioniUnion I c π₀
  simpa only [setOf_and, setOf_exists] using hasBasis_iSup this

theorem hasBasis_toFilteriUnion_top (l : IntegrationParams) (I : Box ι) :
    (l.toFilteriUnion I ⊤).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π ∧ π.IsPartition } := by
  simpa only [TaggedPrepartition.isPartition_iff_iUnion_eq, Prepartition.iUnion_top] using
    l.hasBasis_toFilteriUnion I ⊤

theorem hasBasis_toFilter (l : IntegrationParams) (I : Box ι) :
    (l.toFilter I).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π } := by
  simpa only [setOf_exists] using hasBasis_iSup (l.hasBasis_toFilterDistortion I)

theorem tendsto_embedBox_toFilteriUnion_top (l : IntegrationParams) (h : I ≤ J) :
    Tendsto (TaggedPrepartition.embedBox I J h) (l.toFilteriUnion I ⊤)
      (l.toFilteriUnion J (Prepartition.single J I h)) := by
  simp only [toFilteriUnion, tendsto_iSup]; intro c
  set π₀ := Prepartition.single J I h
  refine le_iSup_of_le (max c π₀.compl.distortion) ?_
  refine ((l.hasBasis_toFilterDistortioniUnion I c ⊤).tendsto_iff
    (l.hasBasis_toFilterDistortioniUnion J _ _)).2 fun r hr => ?_
  refine ⟨r, hr, fun π hπ => ?_⟩
  rw [mem_setOf_eq, Prepartition.iUnion_top] at hπ
  refine ⟨⟨hπ.1.1, hπ.1.2, fun hD => le_trans (hπ.1.3 hD) (le_max_left _ _), fun _ => ?_⟩, ?_⟩
  · refine ⟨_, π₀.iUnion_compl.trans ?_, le_max_right _ _⟩
    congr 1
    exact (Prepartition.iUnion_single h).trans hπ.2.symm
  · exact hπ.2.trans (Prepartition.iUnion_single _).symm

theorem exists_memBaseSet_le_iUnion_eq (l : IntegrationParams) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    ∃ π, l.MemBaseSet I c r π ∧ π.toPrepartition ≤ π₀ ∧ π.iUnion = π₀.iUnion := by
  rcases π₀.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r with ⟨π, hle, hH, hr, hd, hU⟩
  refine ⟨π, ⟨hr, fun _ => hH, fun _ => hd.trans_le hc₁, fun _ => ⟨π₀.compl, ?_, hc₂⟩⟩, ⟨hle, hU⟩⟩
  exact Prepartition.compl_congr hU ▸ π.toPrepartition.iUnion_compl

theorem exists_memBaseSet_isPartition (l : IntegrationParams) (I : Box ι) (hc : I.distortion ≤ c)
    (r : (ι → ℝ) → Ioi (0 : ℝ)) : ∃ π, l.MemBaseSet I c r π ∧ π.IsPartition := by
  rw [← Prepartition.distortion_top] at hc
  have hc' : (⊤ : Prepartition I).compl.distortion ≤ c := by simp
  simpa [isPartition_iff_iUnion_eq] using l.exists_memBaseSet_le_iUnion_eq ⊤ hc hc' r

theorem toFilterDistortioniUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) :
    (l.toFilterDistortioniUnion I c π₀).NeBot :=
  ((l.hasBasis_toFilterDistortion I _).inf_principal _).neBot_iff.2
    fun {r} _ => (l.exists_memBaseSet_le_iUnion_eq π₀ hc₁ hc₂ r).imp fun _ hπ => ⟨hπ.1, hπ.2.2⟩

instance toFilterDistortioniUnion_neBot' (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilterDistortioniUnion I (max π₀.distortion π₀.compl.distortion) π₀).NeBot :=
  l.toFilterDistortioniUnion_neBot I π₀ (le_max_left _ _) (le_max_right _ _)

instance toFilterDistortion_neBot (l : IntegrationParams) (I : Box ι) :
    (l.toFilterDistortion I I.distortion).NeBot := by
  simpa using (l.toFilterDistortioniUnion_neBot' I ⊤).mono inf_le_left

instance toFilter_neBot (l : IntegrationParams) (I : Box ι) : (l.toFilter I).NeBot :=
  (l.toFilterDistortion_neBot I).mono <| le_iSup _ _

instance toFilteriUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilteriUnion I π₀).NeBot :=
  (l.toFilterDistortioniUnion_neBot' I π₀).mono <|
    le_iSup (fun c => l.toFilterDistortioniUnion I c π₀) _

theorem eventually_isPartition (l : IntegrationParams) (I : Box ι) :
    ∀ᶠ π in l.toFilteriUnion I ⊤, TaggedPrepartition.IsPartition π :=
  eventually_iSup.2 fun _ =>
    eventually_inf_principal.2 <|
      Eventually.of_forall fun π h =>
        π.isPartition_iff_iUnion_eq.2 (h.trans Prepartition.iUnion_top)

end IntegrationParams

end BoxIntegral
