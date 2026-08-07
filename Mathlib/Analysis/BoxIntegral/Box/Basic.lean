/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.Order.MonotoneConvergence
/-!
# Rectangular boxes in `ℝⁿ`

In this file we define rectangular boxes in `ℝⁿ`. As usual, we represent `ℝⁿ` as the type of
functions `ι → ℝ` (usually `ι = Fin n` for some `n`). When we need to interpret a box `[l, u]` as a
set, we use the product `{x | ∀ i, l i < x i ∧ x i ≤ u i}` of half-open intervals `(l i, u i]`. We
exclude `l i` because this way boxes of a partition are disjoint as sets in `ℝⁿ`.

Currently, the only use cases for these constructions are the definitions of Riemann-style integrals
(Riemann, Henstock-Kurzweil, McShane).

## Main definitions

We use the same structure `BoxIntegral.Box` both for ambient boxes and for elements of a partition.
Each box is stored as two points `lower upper : ι → ℝ` and a proof of `∀ i, lower i < upper i`. We
define instances `Membership (ι → ℝ) (Box ι)` and `CoeTC (Box ι) (Set <| ι → ℝ)` so that each box is
interpreted as the set `{x | ∀ i, x i ∈ Set.Ioc (I.lower i) (I.upper i)}`. This way boxes of a
partition are pairwise disjoint and their union is exactly the original box.

We require boxes to be nonempty, because this way coercion to sets is injective. The empty box can
be represented as `⊥ : WithBot (BoxIntegral.Box ι)`.

We define the following operations on boxes:

* coercion to `Set (ι → ℝ)` and `Membership (ι → ℝ) (BoxIntegral.Box ι)` as described above;
* `PartialOrder` and `SemilatticeSup` instances such that `I ≤ J` is equivalent to
  `(I : Set (ι → ℝ)) ⊆ J`;
* `Lattice` instances on `WithBot (BoxIntegral.Box ι)`;
* `BoxIntegral.Box.Icc`: the closed box `Set.Icc I.lower I.upper`; defined as a bundled monotone
  map from `Box ι` to `Set (ι → ℝ)`;
* `BoxIntegral.Box.face I i : Box (Fin n)`: a hyperface of `I : BoxIntegral.Box (Fin (n + 1))`;
* `BoxIntegral.Box.distortion`: the maximal ratio of two lengths of edges of a box; defined as the
  supremum of `nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`.

We also provide a convenience constructor `BoxIntegral.Box.mk' (l u : ι → ℝ) : WithBot (Box ι)`
that returns the box `⟨l, u, _⟩` if it is nonempty and `⊥` otherwise.

## Tags

rectangular box
-/

@[expose] public section

open Set Function Metric Filter

noncomputable section

open scoped NNReal Topology

namespace BoxIntegral

variable {ι : Type*}

/-!
### Rectangular box: definition and partial order
-/


/-- A nontrivial rectangular box in `ι → ℝ` with corners `lower` and `upper`. Represents the product
of half-open intervals `(lower i, upper i]`. -/
structure Box (ι : Type*) where
  /-- coordinates of the lower and upper corners of the box -/
  (lower upper : ι → ℝ)
  /-- Each lower coordinate is less than its upper coordinate: i.e., the box is non-empty -/
  lower_lt_upper : ∀ i, lower i < upper i

attribute [simp] Box.lower_lt_upper

namespace Box

variable (I J : Box ι) {x y : ι → ℝ}

instance : Inhabited (Box ι) :=
  ⟨⟨0, 1, fun _ ↦ zero_lt_one⟩⟩

theorem lower_le_upper : I.lower ≤ I.upper :=
  fun i ↦ (I.lower_lt_upper i).le

theorem lower_ne_upper (i) : I.lower i ≠ I.upper i :=
  (I.lower_lt_upper i).ne

instance : Membership (ι → ℝ) (Box ι) :=
  ⟨fun I x ↦ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)⟩

/-- The set of points in this box: this is the product of half-open intervals `(lower i, upper i]`,
where `lower` and `upper` are this box' corners. -/
@[coe]
def toSet (I : Box ι) : Set (ι → ℝ) := { x | x ∈ I }

instance : CoeTC (Box ι) (Set <| ι → ℝ) :=
  ⟨toSet⟩

@[simp]
theorem mem_mk {l u x : ι → ℝ} {H} : x ∈ mk l u H ↔ ∀ i, x i ∈ Ioc (l i) (u i) := Iff.rfl

@[simp, norm_cast]
theorem mem_coe : x ∈ (I : Set (ι → ℝ)) ↔ x ∈ I := Iff.rfl

theorem mem_def : x ∈ I ↔ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i) := Iff.rfl

theorem mem_univ_Ioc {I : Box ι} : (x ∈ pi univ fun i ↦ Ioc (I.lower i) (I.upper i)) ↔ x ∈ I :=
  mem_univ_pi

theorem coe_eq_pi : (I : Set (ι → ℝ)) = pi univ fun i ↦ Ioc (I.lower i) (I.upper i) :=
  Set.ext fun _ ↦ mem_univ_Ioc.symm

@[simp]
theorem upper_mem : I.upper ∈ I :=
  fun i ↦ right_mem_Ioc.2 <| I.lower_lt_upper i

theorem exists_mem : ∃ x, x ∈ I :=
  ⟨_, I.upper_mem⟩

theorem nonempty_coe : Set.Nonempty (I : Set (ι → ℝ)) :=
  I.exists_mem

@[simp]
theorem coe_ne_empty : (I : Set (ι → ℝ)) ≠ ∅ :=
  I.nonempty_coe.ne_empty

@[simp]
theorem empty_ne_coe : ∅ ≠ (I : Set (ι → ℝ)) :=
  I.coe_ne_empty.symm

instance : LE (Box ι) :=
  ⟨fun I J ↦ ∀ ⦃x⦄, x ∈ I → x ∈ J⟩

theorem le_def : I ≤ J ↔ ∀ x ∈ I, x ∈ J := Iff.rfl

theorem le_TFAE : List.TFAE [I ≤ J, (I : Set (ι → ℝ)) ⊆ J,
    Icc I.lower I.upper ⊆ Icc J.lower J.upper, J.lower ≤ I.lower ∧ I.upper ≤ J.upper] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 → 3
  | h => by simpa [coe_eq_pi, closure_pi_set, lower_ne_upper] using closure_mono h
  tfae_have 3 ↔ 4 := Icc_subset_Icc_iff I.lower_le_upper
  tfae_have 4 → 2
  | h, x, hx, i => Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i)
  tfae_finish

variable {I J}

@[simp, norm_cast]
theorem coe_subset_coe : (I : Set (ι → ℝ)) ⊆ J ↔ I ≤ J := Iff.rfl

theorem le_iff_bounds : I ≤ J ↔ J.lower ≤ I.lower ∧ I.upper ≤ J.upper :=
  (le_TFAE I J).out 0 3

theorem injective_coe : Injective ((↑) : Box ι → Set (ι → ℝ)) := by
  rintro ⟨l₁, u₁, h₁⟩ ⟨l₂, u₂, h₂⟩ h
  simp only [Subset.antisymm_iff, coe_subset_coe, le_iff_bounds] at h
  congr
  exacts [le_antisymm h.2.1 h.1.1, le_antisymm h.1.2 h.2.2]

@[simp, norm_cast]
theorem coe_inj : (I : Set (ι → ℝ)) = J ↔ I = J :=
  injective_coe.eq_iff

@[ext]
theorem ext (H : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  injective_coe <| Set.ext H

theorem ne_of_disjoint_coe (h : Disjoint (I : Set (ι → ℝ)) J) : I ≠ J :=
  mt coe_inj.2 <| h.ne I.coe_ne_empty

instance : PartialOrder (Box ι) :=
  { PartialOrder.lift ((↑) : Box ι → Set (ι → ℝ)) injective_coe with le := (· ≤ ·) }

/-- Closed box corresponding to `I : BoxIntegral.Box ι`. -/
protected def Icc : Box ι ↪o Set (ι → ℝ) :=
  OrderEmbedding.ofMapLEIff (fun I : Box ι ↦ Icc I.lower I.upper) fun I J ↦ (le_TFAE I J).out 2 0

theorem Icc_def : Box.Icc I = Icc I.lower I.upper := rfl

@[simp]
theorem upper_mem_Icc (I : Box ι) : I.upper ∈ Box.Icc I :=
  right_mem_Icc.2 I.lower_le_upper

@[simp]
theorem lower_mem_Icc (I : Box ι) : I.lower ∈ Box.Icc I :=
  left_mem_Icc.2 I.lower_le_upper

protected theorem isCompact_Icc (I : Box ι) : IsCompact (Box.Icc I) :=
  isCompact_Icc

theorem Icc_eq_pi : Box.Icc I = pi univ fun i ↦ Icc (I.lower i) (I.upper i) :=
  (pi_univ_Icc _ _).symm

theorem le_iff_Icc : I ≤ J ↔ Box.Icc I ⊆ Box.Icc J :=
  (le_TFAE I J).out 0 2

theorem antitone_lower : Antitone fun I : Box ι ↦ I.lower :=
  fun _ _ H ↦ (le_iff_bounds.1 H).1

theorem monotone_upper : Monotone fun I : Box ι ↦ I.upper :=
  fun _ _ H ↦ (le_iff_bounds.1 H).2

theorem coe_subset_Icc : ↑I ⊆ Box.Icc I :=
  fun _ hx ↦ ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2⟩

theorem isBounded_Icc [Finite ι] (I : Box ι) : Bornology.IsBounded (Box.Icc I) := by
  cases nonempty_fintype ι
  exact Metric.isBounded_Icc _ _

theorem isBounded [Finite ι] (I : Box ι) : Bornology.IsBounded I.toSet :=
  Bornology.IsBounded.subset I.isBounded_Icc coe_subset_Icc

/-!
### Supremum of two boxes
-/


/-- `I ⊔ J` is the least box that includes both `I` and `J`. Since `↑I ∪ ↑J` is usually not a box,
`↑(I ⊔ J)` is larger than `↑I ∪ ↑J`. -/
instance : SemilatticeSup (Box ι) :=
  { sup := fun I J ↦ ⟨I.lower ⊓ J.lower, I.upper ⊔ J.upper,
    fun i ↦ (min_le_left _ _).trans_lt <| (I.lower_lt_upper i).trans_le (le_max_left _ _)⟩
    le_sup_left := fun _ _ ↦ le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩
    le_sup_right := fun _ _ ↦ le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩
    sup_le := fun _ _ _ h₁ h₂ ↦ le_iff_bounds.2
      ⟨le_inf (antitone_lower h₁) (antitone_lower h₂),
        sup_le (monotone_upper h₁) (monotone_upper h₂)⟩ }

/-!
### `WithBot (Box ι)`

In this section we define coercion from `WithBot (Box ι)` to `Set (ι → ℝ)` by sending `⊥` to `∅`.
-/

/-- The set underlying this box: `⊥` is mapped to `∅`. -/
@[coe]
def withBotToSet (o : WithBot (Box ι)) : Set (ι → ℝ) := o.elim ∅ (↑)

instance withBotCoe : CoeTC (WithBot (Box ι)) (Set (ι → ℝ)) :=
  ⟨withBotToSet⟩

@[simp, norm_cast]
theorem coe_bot : ((⊥ : WithBot (Box ι)) : Set (ι → ℝ)) = ∅ := rfl

@[simp, norm_cast]
theorem coe_coe : ((I : WithBot (Box ι)) : Set (ι → ℝ)) = I := rfl

theorem isSome_iff : ∀ {I : WithBot (Box ι)}, I.isSome ↔ (I : Set (ι → ℝ)).Nonempty
  | ⊥ => by
    unfold Option.isSome
    simp
  | (I : Box ι) => by
    unfold Option.isSome
    simp [I.nonempty_coe]

theorem biUnion_coe_eq_coe (I : WithBot (Box ι)) :
    ⋃ (J : Box ι) (_ : ↑J = I), (J : Set (ι → ℝ)) = I := by
  induction I <;> simp

@[simp, norm_cast]
theorem withBotCoe_subset_iff {I J : WithBot (Box ι)} : (I : Set (ι → ℝ)) ⊆ J ↔ I ≤ J := by
  induction I; · simp
  induction J; · simp [subset_empty_iff]
  simp [le_def]

@[simp, norm_cast]
theorem withBotCoe_inj {I J : WithBot (Box ι)} : (I : Set (ι → ℝ)) = J ↔ I = J := by
  simp only [Subset.antisymm_iff, ← le_antisymm_iff, withBotCoe_subset_iff]

open scoped Classical in
/-- Make a `WithBot (Box ι)` from a pair of corners `l u : ι → ℝ`. If `l i < u i` for all `i`,
then the result is `⟨l, u, _⟩ : Box ι`, otherwise it is `⊥`. In any case, the result interpreted
as a set in `ι → ℝ` is the set `{x : ι → ℝ | ∀ i, x i ∈ Ioc (l i) (u i)}`. -/
def mk' (l u : ι → ℝ) : WithBot (Box ι) :=
  if h : ∀ i, l i < u i then ↑(⟨l, u, h⟩ : Box ι) else ⊥

@[simp]
theorem mk'_eq_bot {l u : ι → ℝ} : mk' l u = ⊥ ↔ ∃ i, u i ≤ l i := by
  rw [mk']
  split_ifs with h <;> simpa using h

@[simp]
theorem mk'_eq_coe {l u : ι → ℝ} : mk' l u = I ↔ l = I.lower ∧ u = I.upper := by
  obtain ⟨lI, uI, hI⟩ := I; rw [mk']; split_ifs with h
  · simp
  · suffices l = lI → u ≠ uI by simpa
    rintro rfl rfl
    exact h hI

@[simp]
theorem coe_mk' (l u : ι → ℝ) : (mk' l u : Set (ι → ℝ)) = pi univ fun i ↦ Ioc (l i) (u i) := by
  rw [mk']; split_ifs with h
  · exact coe_eq_pi _
  · rcases not_forall.mp h with ⟨i, hi⟩
    rw [coe_bot, univ_pi_eq_empty]
    exact Ioc_eq_empty hi

instance WithBot.inf : Min (WithBot (Box ι)) :=
  ⟨fun I ↦
    WithBot.recBotCoe (fun _ ↦ ⊥)
      (fun I J ↦ WithBot.recBotCoe ⊥ (fun J ↦ mk' (I.lower ⊔ J.lower) (I.upper ⊓ J.upper)) J) I⟩

@[simp]
theorem coe_inf (I J : WithBot (Box ι)) : (↑(I ⊓ J) : Set (ι → ℝ)) = (I : Set _) ∩ J := by
  induction I
  · change ∅ = _
    simp
  induction J
  · change ∅ = _
    simp
  change ((mk' _ _ : WithBot (Box ι)) : Set (ι → ℝ)) = _
  simp only [coe_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, Pi.sup_apply, Pi.inf_apply, coe_mk',
    coe_coe]

instance : Lattice (WithBot (Box ι)) :=
  { inf := min
    inf_le_left := fun I J ↦ by
      rw [← withBotCoe_subset_iff, coe_inf]
      exact inter_subset_left
    inf_le_right := fun I J ↦ by
      rw [← withBotCoe_subset_iff, coe_inf]
      exact inter_subset_right
    le_inf := fun I J₁ J₂ h₁ h₂ ↦ by
      simp only [← withBotCoe_subset_iff, coe_inf] at *
      exact subset_inter h₁ h₂ }

@[simp, norm_cast]
theorem disjoint_withBotCoe {I J : WithBot (Box ι)} :
    Disjoint (I : Set (ι → ℝ)) J ↔ Disjoint I J := by
  simp only [disjoint_iff_inf_le, ← withBotCoe_subset_iff, coe_inf]
  rfl

theorem disjoint_coe : Disjoint (I : WithBot (Box ι)) J ↔ Disjoint (I : Set (ι → ℝ)) J :=
  disjoint_withBotCoe.symm

theorem not_disjoint_coe_iff_nonempty_inter :
    ¬Disjoint (I : WithBot (Box ι)) J ↔ (I ∩ J : Set (ι → ℝ)).Nonempty := by
  rw [disjoint_coe, Set.not_disjoint_iff_nonempty_inter]

/-!
### Hyperface of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`
-/


/-- Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at
`I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`. -/
@[simps +simpRhs]
def face {n} (I : Box (Fin (n + 1))) (i : Fin (n + 1)) : Box (Fin n) :=
  ⟨I.lower ∘ Fin.succAbove i, I.upper ∘ Fin.succAbove i, fun _ ↦ I.lower_lt_upper _⟩

@[simp]
theorem face_mk {n} (l u : Fin (n + 1) → ℝ) (h : ∀ i, l i < u i) (i : Fin (n + 1)) :
    face ⟨l, u, h⟩ i = ⟨l ∘ Fin.succAbove i, u ∘ Fin.succAbove i, fun _ ↦ h _⟩ := rfl

@[gcongr, mono]
theorem face_mono {n} {I J : Box (Fin (n + 1))} (h : I ≤ J) (i : Fin (n + 1)) :
    face I i ≤ face J i :=
  fun _ hx _ ↦ Ioc_subset_Ioc ((le_iff_bounds.1 h).1 _) ((le_iff_bounds.1 h).2 _) (hx _)

theorem monotone_face {n} (i : Fin (n + 1)) : Monotone fun I ↦ face I i :=
  fun _ _ h ↦ face_mono h i

theorem mapsTo_insertNth_face_Icc {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ Icc (I.lower i) (I.upper i)) :
    MapsTo (i.insertNth x) (Box.Icc (I.face i)) (Box.Icc I) :=
  fun _ hy ↦ Fin.insertNth_mem_Icc.2 ⟨hx, hy⟩

theorem mapsTo_insertNth_face {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ Ioc (I.lower i) (I.upper i)) :
    MapsTo (i.insertNth x) (I.face i : Set (_ → _)) (I : Set (_ → _)) := by
  intro y hy
  simp_rw [mem_coe, mem_def, i.forall_iff_succAbove, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact ⟨hx, hy⟩

theorem continuousOn_face_Icc {X} [TopologicalSpace X] {n} {f : (Fin (n + 1) → ℝ) → X}
    {I : Box (Fin (n + 1))} (h : ContinuousOn f (Box.Icc I)) {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ Icc (I.lower i) (I.upper i)) :
    ContinuousOn (f ∘ i.insertNth x) (Box.Icc (I.face i)) :=
  h.comp (continuousOn_const.finInsertNth i continuousOn_id) (I.mapsTo_insertNth_face_Icc hx)

/-!
### Covering of the interior of a box by a monotone sequence of smaller boxes
-/


/-- The interior of a box. -/
protected def Ioo : Box ι →o Set (ι → ℝ) where
  toFun I := pi univ fun i ↦ Ioo (I.lower i) (I.upper i)
  monotone' _ _ h :=
    pi_mono fun i _ ↦ Ioo_subset_Ioo ((le_iff_bounds.1 h).1 i) ((le_iff_bounds.1 h).2 i)

theorem Ioo_subset_coe (I : Box ι) : Box.Ioo I ⊆ I :=
  fun _ hx i ↦ Ioo_subset_Ioc_self (hx i trivial)

protected theorem Ioo_subset_Icc (I : Box ι) : Box.Ioo I ⊆ Box.Icc I :=
  I.Ioo_subset_coe.trans coe_subset_Icc

theorem iUnion_Ioo_of_tendsto [Finite ι] {I : Box ι} {J : ℕ → Box ι} (hJ : Monotone J)
    (hl : Tendsto (lower ∘ J) atTop (𝓝 I.lower)) (hu : Tendsto (upper ∘ J) atTop (𝓝 I.upper)) :
    ⋃ n, Box.Ioo (J n) = Box.Ioo I :=
  have hl' : ∀ i, Antitone fun n ↦ (J n).lower i :=
    fun i ↦ (monotone_eval (α := fun _ ↦ ℝ) i).comp_antitone (antitone_lower.comp_monotone hJ)
  have hu' : ∀ i, Monotone fun n ↦ (J n).upper i :=
    fun i ↦ (monotone_eval (α := fun _ ↦ ℝ) i).comp (monotone_upper.comp hJ)
  calc
    ⋃ n, Box.Ioo (J n) = pi univ fun i ↦ ⋃ n, Ioo ((J n).lower i) ((J n).upper i) :=
      iUnion_univ_pi_of_monotone fun i ↦ (hl' i).Ioo (hu' i)
    _ = Box.Ioo I :=
      pi_congr rfl fun i _ ↦
        iUnion_Ioo_of_mono_of_isGLB_of_isLUB (hl' i) (hu' i)
          (isGLB_of_tendsto_atTop (hl' i) (tendsto_pi_nhds.1 hl _))
          (isLUB_of_tendsto_atTop (hu' i) (tendsto_pi_nhds.1 hu _))

theorem exists_seq_mono_tendsto (I : Box ι) :
    ∃ J : ℕ →o Box ι,
      (∀ n, Box.Icc (J n) ⊆ Box.Ioo I) ∧
        Tendsto (lower ∘ J) atTop (𝓝 I.lower) ∧ Tendsto (upper ∘ J) atTop (𝓝 I.upper) := by
  choose a b ha_anti hb_mono ha_mem hb_mem hab ha_tendsto hb_tendsto using
    fun i ↦ exists_seq_strictAnti_strictMono_tendsto (I.lower_lt_upper i)
  exact
    ⟨⟨fun k ↦ ⟨flip a k, flip b k, fun i ↦ hab _ _ _⟩, fun k l hkl ↦
        le_iff_bounds.2 ⟨fun i ↦ (ha_anti i).antitone hkl, fun i ↦ (hb_mono i).monotone hkl⟩⟩,
      fun n x hx i _ ↦ ⟨(ha_mem _ _).1.trans_le (hx.1 _), (hx.2 _).trans_lt (hb_mem _ _).2⟩,
      tendsto_pi_nhds.2 ha_tendsto, tendsto_pi_nhds.2 hb_tendsto⟩

section Distortion

variable [Fintype ι]

/-- The distortion of a box `I` is the maximum of the ratios of the lengths of its edges.
It is defined as the maximum of the ratios
`nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`. -/
def distortion (I : Box ι) : ℝ≥0 :=
  Finset.univ.sup fun i : ι ↦ nndist I.lower I.upper / nndist (I.lower i) (I.upper i)

theorem distortion_eq_of_sub_eq_div {I J : Box ι} {r : ℝ}
    (h : ∀ i, I.upper i - I.lower i = (J.upper i - J.lower i) / r) :
    distortion I = distortion J := by
  simp only [distortion, nndist_pi_def, Real.nndist_eq', h, map_div₀]
  congr 1 with i
  have : 0 < r := by
    by_contra hr
    have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 <| J.lower_le_upper i) (not_lt.1 hr)
    rw [← h] at this
    exact this.not_gt (sub_pos.2 <| I.lower_lt_upper i)
  have hn0 := (map_ne_zero Real.nnabs).2 this.ne'
  simp_rw [NNReal.finset_sup_div, div_div_div_cancel_right₀ hn0]

theorem nndist_le_distortion_mul (I : Box ι) (i : ι) :
    nndist I.lower I.upper ≤ I.distortion * nndist (I.lower i) (I.upper i) :=
  calc
    nndist I.lower I.upper =
        nndist I.lower I.upper / nndist (I.lower i) (I.upper i) * nndist (I.lower i) (I.upper i) :=
      (div_mul_cancel₀ _ <| mt nndist_eq_zero.1 (I.lower_lt_upper i).ne).symm
    _ ≤ I.distortion * nndist (I.lower i) (I.upper i) := by
      grw [distortion, ← Finset.le_sup (Finset.mem_univ i)]

theorem dist_le_distortion_mul (I : Box ι) (i : ι) :
    dist I.lower I.upper ≤ I.distortion * (I.upper i - I.lower i) := by
  have A : I.lower i - I.upper i < 0 := sub_neg.2 (I.lower_lt_upper i)
  simpa only [← NNReal.coe_le_coe, ← dist_nndist, NNReal.coe_mul, Real.dist_eq, abs_of_neg A,
    neg_sub] using I.nndist_le_distortion_mul i

theorem diam_Icc_le_of_distortion_le (I : Box ι) (i : ι) {c : ℝ≥0} (h : I.distortion ≤ c) :
    diam (Box.Icc I) ≤ c * (I.upper i - I.lower i) :=
  have : (0 : ℝ) ≤ c * (I.upper i - I.lower i) :=
    mul_nonneg c.coe_nonneg (sub_nonneg.2 <| I.lower_le_upper _)
  diam_le_of_forall_dist_le this fun x hx y hy ↦
    calc
      dist x y ≤ dist I.lower I.upper := Real.dist_le_of_mem_pi_Icc hx hy
      _ ≤ I.distortion * (I.upper i - I.lower i) := I.dist_le_distortion_mul i
      _ ≤ c * (I.upper i - I.lower i) := by gcongr; exact sub_nonneg.2 (I.lower_le_upper i)

end Distortion

end Box

end BoxIntegral
