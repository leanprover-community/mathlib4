/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Set.Intervals.Monotone
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.TFAE
import Mathlib.Topology.Algebra.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Basic

#align_import analysis.box_integral.box.basic from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"
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


open Set Function Metric Filter

noncomputable section

open NNReal Classical Topology

namespace BoxIntegral

variable {ι : Type*}

/-!
### Rectangular box: definition and partial order
-/


/-- A nontrivial rectangular box in `ι → ℝ` with corners `lower` and `upper`. Represents the product
of half-open intervals `(lower i, upper i]`. -/
structure Box (ι : Type*) where
  (lower upper : ι → ℝ)
  lower_lt_upper : ∀ i, lower i < upper i
#align box_integral.box BoxIntegral.Box

attribute [simp] Box.lower_lt_upper

namespace Box

variable (I J : Box ι) {x y : ι → ℝ}

instance : Inhabited (Box ι) :=
  ⟨⟨0, 1, fun _ ↦ zero_lt_one⟩⟩

theorem lower_le_upper : I.lower ≤ I.upper :=
  fun i ↦ (I.lower_lt_upper i).le
#align box_integral.box.lower_le_upper BoxIntegral.Box.lower_le_upper

theorem lower_ne_upper (i) : I.lower i ≠ I.upper i :=
  (I.lower_lt_upper i).ne
#align box_integral.box.lower_ne_upper BoxIntegral.Box.lower_ne_upper

instance : Membership (ι → ℝ) (Box ι) :=
  ⟨fun x I ↦ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)⟩

-- Porting note: added
@[coe]
def toSet (I : Box ι) : Set (ι → ℝ) := { x | x ∈ I }

instance : CoeTC (Box ι) (Set <| ι → ℝ) :=
  ⟨toSet⟩

@[simp]
theorem mem_mk {l u x : ι → ℝ} {H} : x ∈ mk l u H ↔ ∀ i, x i ∈ Ioc (l i) (u i) := Iff.rfl
#align box_integral.box.mem_mk BoxIntegral.Box.mem_mk

@[simp, norm_cast]
theorem mem_coe : x ∈ (I : Set (ι → ℝ)) ↔ x ∈ I := Iff.rfl
#align box_integral.box.mem_coe BoxIntegral.Box.mem_coe

theorem mem_def : x ∈ I ↔ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i) := Iff.rfl
#align box_integral.box.mem_def BoxIntegral.Box.mem_def

theorem mem_univ_Ioc {I : Box ι} : (x ∈ pi univ fun i ↦ Ioc (I.lower i) (I.upper i)) ↔ x ∈ I :=
  mem_univ_pi
#align box_integral.box.mem_univ_Ioc BoxIntegral.Box.mem_univ_Ioc

theorem coe_eq_pi : (I : Set (ι → ℝ)) = pi univ fun i ↦ Ioc (I.lower i) (I.upper i) :=
  Set.ext fun _ ↦ mem_univ_Ioc.symm
#align box_integral.box.coe_eq_pi BoxIntegral.Box.coe_eq_pi

@[simp]
theorem upper_mem : I.upper ∈ I :=
  fun i ↦ right_mem_Ioc.2 <| I.lower_lt_upper i
#align box_integral.box.upper_mem BoxIntegral.Box.upper_mem

theorem exists_mem : ∃ x, x ∈ I :=
  ⟨_, I.upper_mem⟩
#align box_integral.box.exists_mem BoxIntegral.Box.exists_mem

theorem nonempty_coe : Set.Nonempty (I : Set (ι → ℝ)) :=
  I.exists_mem
#align box_integral.box.nonempty_coe BoxIntegral.Box.nonempty_coe

@[simp]
theorem coe_ne_empty : (I : Set (ι → ℝ)) ≠ ∅ :=
  I.nonempty_coe.ne_empty
#align box_integral.box.coe_ne_empty BoxIntegral.Box.coe_ne_empty

@[simp]
theorem empty_ne_coe : ∅ ≠ (I : Set (ι → ℝ)) :=
  I.coe_ne_empty.symm
#align box_integral.box.empty_ne_coe BoxIntegral.Box.empty_ne_coe

instance : LE (Box ι) :=
  ⟨fun I J ↦ ∀ ⦃x⦄, x ∈ I → x ∈ J⟩

theorem le_def : I ≤ J ↔ ∀ x ∈ I, x ∈ J := Iff.rfl
#align box_integral.box.le_def BoxIntegral.Box.le_def

theorem le_TFAE : List.TFAE [I ≤ J, (I : Set (ι → ℝ)) ⊆ J,
    Icc I.lower I.upper ⊆ Icc J.lower J.upper, J.lower ≤ I.lower ∧ I.upper ≤ J.upper] := by
  tfae_have 1 ↔ 2; exact Iff.rfl
  -- ⊢ I ≤ J ↔ ↑I ⊆ ↑J
                   -- ⊢ List.TFAE [I ≤ J, ↑I ⊆ ↑J, Icc I.lower I.upper ⊆ Icc J.lower J.upper, J.lowe …
  tfae_have 2 → 3
  -- ⊢ ↑I ⊆ ↑J → Icc I.lower I.upper ⊆ Icc J.lower J.upper
  · intro h
    -- ⊢ Icc I.lower I.upper ⊆ Icc J.lower J.upper
    simpa [coe_eq_pi, closure_pi_set, lower_ne_upper] using closure_mono h
    -- 🎉 no goals
  tfae_have 3 ↔ 4; exact Icc_subset_Icc_iff I.lower_le_upper
  -- ⊢ Icc I.lower I.upper ⊆ Icc J.lower J.upper ↔ J.lower ≤ I.lower ∧ I.upper ≤ J. …
                   -- ⊢ List.TFAE [I ≤ J, ↑I ⊆ ↑J, Icc I.lower I.upper ⊆ Icc J.lower J.upper, J.lowe …
  tfae_have 4 → 2; exact fun h x hx i ↦ Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i)
  -- ⊢ J.lower ≤ I.lower ∧ I.upper ≤ J.upper → ↑I ⊆ ↑J
                   -- ⊢ List.TFAE [I ≤ J, ↑I ⊆ ↑J, Icc I.lower I.upper ⊆ Icc J.lower J.upper, J.lowe …
  tfae_finish
  -- 🎉 no goals
#align box_integral.box.le_tfae BoxIntegral.Box.le_TFAE

variable {I J}

@[simp, norm_cast]
theorem coe_subset_coe : (I : Set (ι → ℝ)) ⊆ J ↔ I ≤ J := Iff.rfl
#align box_integral.box.coe_subset_coe BoxIntegral.Box.coe_subset_coe

theorem le_iff_bounds : I ≤ J ↔ J.lower ≤ I.lower ∧ I.upper ≤ J.upper :=
  (le_TFAE I J).out 0 3
#align box_integral.box.le_iff_bounds BoxIntegral.Box.le_iff_bounds

theorem injective_coe : Injective ((↑) : Box ι → Set (ι → ℝ)) := by
  rintro ⟨l₁, u₁, h₁⟩ ⟨l₂, u₂, h₂⟩ h
  -- ⊢ { lower := l₁, upper := u₁, lower_lt_upper := h₁ } = { lower := l₂, upper := …
  simp only [Subset.antisymm_iff, coe_subset_coe, le_iff_bounds] at h
  -- ⊢ { lower := l₁, upper := u₁, lower_lt_upper := h₁ } = { lower := l₂, upper := …
  congr
  -- ⊢ l₁ = l₂
  exacts [le_antisymm h.2.1 h.1.1, le_antisymm h.1.2 h.2.2]
  -- 🎉 no goals
#align box_integral.box.injective_coe BoxIntegral.Box.injective_coe

@[simp, norm_cast]
theorem coe_inj : (I : Set (ι → ℝ)) = J ↔ I = J :=
  injective_coe.eq_iff
#align box_integral.box.coe_inj BoxIntegral.Box.coe_inj

@[ext]
theorem ext (H : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  injective_coe <| Set.ext H
#align box_integral.box.ext BoxIntegral.Box.ext

theorem ne_of_disjoint_coe (h : Disjoint (I : Set (ι → ℝ)) J) : I ≠ J :=
  mt coe_inj.2 <| h.ne I.coe_ne_empty
#align box_integral.box.ne_of_disjoint_coe BoxIntegral.Box.ne_of_disjoint_coe

instance : PartialOrder (Box ι) :=
  { PartialOrder.lift ((↑) : Box ι → Set (ι → ℝ)) injective_coe with le := (· ≤ ·) }

/-- Closed box corresponding to `I : BoxIntegral.Box ι`. -/
protected def Icc : Box ι ↪o Set (ι → ℝ) :=
  OrderEmbedding.ofMapLEIff (fun I : Box ι ↦ Icc I.lower I.upper) fun I J ↦ (le_TFAE I J).out 2 0
#align box_integral.box.Icc BoxIntegral.Box.Icc

theorem Icc_def : Box.Icc I = Icc I.lower I.upper := rfl
#align box_integral.box.Icc_def BoxIntegral.Box.Icc_def

@[simp]
theorem upper_mem_Icc (I : Box ι) : I.upper ∈ Box.Icc I :=
  right_mem_Icc.2 I.lower_le_upper
#align box_integral.box.upper_mem_Icc BoxIntegral.Box.upper_mem_Icc

@[simp]
theorem lower_mem_Icc (I : Box ι) : I.lower ∈ Box.Icc I :=
  left_mem_Icc.2 I.lower_le_upper
#align box_integral.box.lower_mem_Icc BoxIntegral.Box.lower_mem_Icc

protected theorem isCompact_Icc (I : Box ι) : IsCompact (Box.Icc I) :=
  isCompact_Icc
#align box_integral.box.is_compact_Icc BoxIntegral.Box.isCompact_Icc

theorem Icc_eq_pi : Box.Icc I = pi univ fun i ↦ Icc (I.lower i) (I.upper i) :=
  (pi_univ_Icc _ _).symm
#align box_integral.box.Icc_eq_pi BoxIntegral.Box.Icc_eq_pi

theorem le_iff_Icc : I ≤ J ↔ Box.Icc I ⊆ Box.Icc J :=
  (le_TFAE I J).out 0 2
#align box_integral.box.le_iff_Icc BoxIntegral.Box.le_iff_Icc

theorem antitone_lower : Antitone fun I : Box ι ↦ I.lower :=
  fun _ _ H ↦ (le_iff_bounds.1 H).1
#align box_integral.box.antitone_lower BoxIntegral.Box.antitone_lower

theorem monotone_upper : Monotone fun I : Box ι ↦ I.upper :=
  fun _ _ H ↦ (le_iff_bounds.1 H).2
#align box_integral.box.monotone_upper BoxIntegral.Box.monotone_upper

theorem coe_subset_Icc : ↑I ⊆ Box.Icc I :=
  fun _ hx ↦ ⟨fun i ↦ (hx i).1.le, fun i ↦ (hx i).2⟩
#align box_integral.box.coe_subset_Icc BoxIntegral.Box.coe_subset_Icc

/-!
### Supremum of two boxes
-/


/-- `I ⊔ J` is the least box that includes both `I` and `J`. Since `↑I ∪ ↑J` is usually not a box,
`↑(I ⊔ J)` is larger than `↑I ∪ ↑J`. -/
instance : Sup (Box ι) :=
  ⟨fun I J ↦ ⟨I.lower ⊓ J.lower, I.upper ⊔ J.upper,
    fun i ↦ (min_le_left _ _).trans_lt <| (I.lower_lt_upper i).trans_le (le_max_left _ _)⟩⟩

instance : SemilatticeSup (Box ι) :=
  { (inferInstance : PartialOrder (Box ι)),
    (inferInstance : Sup (Box ι)) with
    le_sup_left := fun _ _ ↦ le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩
    le_sup_right := fun _ _ ↦ le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩
    sup_le := fun _ _ _ h₁ h₂ ↦ le_iff_bounds.2
      ⟨le_inf (antitone_lower h₁) (antitone_lower h₂),
        sup_le (monotone_upper h₁) (monotone_upper h₂)⟩ }

/-!
### `WithBot (Box ι)`

In this section we define coercion from `WithBot (Box ι)` to `Set (ι → ℝ)` by sending `⊥` to `∅`.
-/

-- Porting note: added
@[coe]
def withBotToSet (o : WithBot (Box ι)) : Set (ι → ℝ) := o.elim ∅ (↑)

instance withBotCoe : CoeTC (WithBot (Box ι)) (Set (ι → ℝ)) :=
  ⟨withBotToSet⟩
#align box_integral.box.with_bot_coe BoxIntegral.Box.withBotCoe

@[simp, norm_cast]
theorem coe_bot : ((⊥ : WithBot (Box ι)) : Set (ι → ℝ)) = ∅ := rfl
#align box_integral.box.coe_bot BoxIntegral.Box.coe_bot

@[simp, norm_cast]
theorem coe_coe : ((I : WithBot (Box ι)) : Set (ι → ℝ)) = I := rfl
#align box_integral.box.coe_coe BoxIntegral.Box.coe_coe

theorem isSome_iff : ∀ {I : WithBot (Box ι)}, I.isSome ↔ (I : Set (ι → ℝ)).Nonempty
  | ⊥ => by
    erw [Option.isSome]
    -- ⊢ (match ⊥ with
    simp
    -- 🎉 no goals
  | (I : Box ι) => by
    erw [Option.isSome]
    -- ⊢ (match ↑I with
    simp [I.nonempty_coe]
    -- 🎉 no goals
#align box_integral.box.is_some_iff BoxIntegral.Box.isSome_iff

theorem biUnion_coe_eq_coe (I : WithBot (Box ι)) :
    ⋃ (J : Box ι) (_ : ↑J = I), (J : Set (ι → ℝ)) = I := by
  induction I using WithBot.recBotCoe <;> simp [WithBot.coe_eq_coe]
  -- ⊢ ⋃ (J : Box ι) (_ : ↑J = ⊥), ↑J = ↑⊥
                                          -- 🎉 no goals
                                          -- 🎉 no goals
#align box_integral.box.bUnion_coe_eq_coe BoxIntegral.Box.biUnion_coe_eq_coe

@[simp, norm_cast]
theorem withBotCoe_subset_iff {I J : WithBot (Box ι)} : (I : Set (ι → ℝ)) ⊆ J ↔ I ≤ J := by
  induction I using WithBot.recBotCoe; · simp
  -- ⊢ ↑⊥ ⊆ ↑J ↔ ⊥ ≤ J
                                         -- 🎉 no goals
  induction J using WithBot.recBotCoe; · simp [subset_empty_iff]
  -- ⊢ ↑↑a✝ ⊆ ↑⊥ ↔ ↑a✝ ≤ ⊥
                                         -- 🎉 no goals
  simp [le_def]
  -- 🎉 no goals
#align box_integral.box.with_bot_coe_subset_iff BoxIntegral.Box.withBotCoe_subset_iff

@[simp, norm_cast]
theorem withBotCoe_inj {I J : WithBot (Box ι)} : (I : Set (ι → ℝ)) = J ↔ I = J := by
  simp only [Subset.antisymm_iff, ← le_antisymm_iff, withBotCoe_subset_iff]
  -- 🎉 no goals
#align box_integral.box.with_bot_coe_inj BoxIntegral.Box.withBotCoe_inj

/-- Make a `WithBot (Box ι)` from a pair of corners `l u : ι → ℝ`. If `l i < u i` for all `i`,
then the result is `⟨l, u, _⟩ : Box ι`, otherwise it is `⊥`. In any case, the result interpreted
as a set in `ι → ℝ` is the set `{x : ι → ℝ | ∀ i, x i ∈ Ioc (l i) (u i)}`.  -/
def mk' (l u : ι → ℝ) : WithBot (Box ι) :=
  if h : ∀ i, l i < u i then ↑(⟨l, u, h⟩ : Box ι) else ⊥
#align box_integral.box.mk' BoxIntegral.Box.mk'

@[simp]
theorem mk'_eq_bot {l u : ι → ℝ} : mk' l u = ⊥ ↔ ∃ i, u i ≤ l i := by
  rw [mk']
  -- ⊢ (if h : ∀ (i : ι), l i < u i then ↑{ lower := l, upper := u, lower_lt_upper  …
  split_ifs with h <;> simpa using h
  -- ⊢ ↑{ lower := l, upper := u, lower_lt_upper := h } = ⊥ ↔ ∃ i, u i ≤ l i
                       -- 🎉 no goals
                       -- 🎉 no goals
#align box_integral.box.mk'_eq_bot BoxIntegral.Box.mk'_eq_bot

@[simp]
theorem mk'_eq_coe {l u : ι → ℝ} : mk' l u = I ↔ l = I.lower ∧ u = I.upper := by
  cases' I with lI uI hI; rw [mk']; split_ifs with h
  -- ⊢ mk' l u = ↑{ lower := lI, upper := uI, lower_lt_upper := hI } ↔ l = { lower  …
                          -- ⊢ (if h : ∀ (i : ι), l i < u i then ↑{ lower := l, upper := u, lower_lt_upper  …
                                    -- ⊢ ↑{ lower := l, upper := u, lower_lt_upper := h } = ↑{ lower := lI, upper :=  …
  · simp [WithBot.coe_eq_coe]
    -- 🎉 no goals
  · suffices l = lI → u ≠ uI by simpa
    -- ⊢ l = lI → u ≠ uI
    rintro rfl rfl
    -- ⊢ False
    exact h hI
    -- 🎉 no goals
#align box_integral.box.mk'_eq_coe BoxIntegral.Box.mk'_eq_coe

@[simp]
theorem coe_mk' (l u : ι → ℝ) : (mk' l u : Set (ι → ℝ)) = pi univ fun i ↦ Ioc (l i) (u i) := by
  rw [mk']; split_ifs with h
  -- ⊢ ↑(if h : ∀ (i : ι), l i < u i then ↑{ lower := l, upper := u, lower_lt_upper …
            -- ⊢ ↑↑{ lower := l, upper := u, lower_lt_upper := h } = Set.pi univ fun i => Ioc …
  · exact coe_eq_pi _
    -- 🎉 no goals
  · rcases not_forall.mp h with ⟨i, hi⟩
    -- ⊢ ↑⊥ = Set.pi univ fun i => Ioc (l i) (u i)
    rw [coe_bot, univ_pi_eq_empty]
    -- ⊢ Ioc (l ?m.301759) (u ?m.301759) = ∅
    exact Ioc_eq_empty hi
    -- 🎉 no goals
#align box_integral.box.coe_mk' BoxIntegral.Box.coe_mk'

instance WithBot.inf : Inf (WithBot (Box ι)) :=
  ⟨fun I ↦
    WithBot.recBotCoe (fun _ ↦ ⊥)
      (fun I J ↦ WithBot.recBotCoe ⊥ (fun J ↦ mk' (I.lower ⊔ J.lower) (I.upper ⊓ J.upper)) J) I⟩

@[simp]
theorem coe_inf (I J : WithBot (Box ι)) : (↑(I ⊓ J) : Set (ι → ℝ)) = (I : Set _) ∩ J := by
  induction I using WithBot.recBotCoe
  -- ⊢ ↑(⊥ ⊓ J) = ↑⊥ ∩ ↑J
  · change ∅ = _
    -- ⊢ ∅ = ↑⊥ ∩ ↑J
    simp
    -- 🎉 no goals
  induction J using WithBot.recBotCoe
  -- ⊢ ↑(↑a✝ ⊓ ⊥) = ↑↑a✝ ∩ ↑⊥
  · change ∅ = _
    -- ⊢ ∅ = ↑↑a✝ ∩ ↑⊥
    simp
    -- 🎉 no goals
  change ((mk' _ _ : WithBot (Box ι)) : Set (ι → ℝ)) = _
  -- ⊢ ↑(mk' (fun i => (a✝¹.lower ⊔ a✝.lower) i) fun i => (a✝¹.upper ⊓ a✝.upper) i) …
  simp only [coe_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, Pi.sup_apply, Pi.inf_apply, coe_mk',
    coe_coe]
#align box_integral.box.coe_inf BoxIntegral.Box.coe_inf

instance : Lattice (WithBot (Box ι)) :=
  { WithBot.semilatticeSup,
    Box.WithBot.inf with
    inf_le_left := fun I J ↦ by
      rw [← withBotCoe_subset_iff, coe_inf]
      -- ⊢ ↑I ∩ ↑J ⊆ ↑I
      exact inter_subset_left _ _
      -- 🎉 no goals
    inf_le_right := fun I J ↦ by
      rw [← withBotCoe_subset_iff, coe_inf]
      -- ⊢ ↑I ∩ ↑J ⊆ ↑J
      exact inter_subset_right _ _
      -- 🎉 no goals
    le_inf := fun I J₁ J₂ h₁ h₂ ↦ by
      simp only [← withBotCoe_subset_iff, coe_inf] at *
      -- ⊢ ↑I ⊆ ↑J₁ ∩ ↑J₂
      exact subset_inter h₁ h₂ }
      -- 🎉 no goals

@[simp, norm_cast]
theorem disjoint_withBotCoe {I J : WithBot (Box ι)} :
    Disjoint (I : Set (ι → ℝ)) J ↔ Disjoint I J := by
  simp only [disjoint_iff_inf_le, ← withBotCoe_subset_iff, coe_inf]
  -- ⊢ ↑I ⊓ ↑J ≤ ⊥ ↔ ↑I ∩ ↑J ⊆ ↑⊥
  rfl
  -- 🎉 no goals
#align box_integral.box.disjoint_with_bot_coe BoxIntegral.Box.disjoint_withBotCoe

theorem disjoint_coe : Disjoint (I : WithBot (Box ι)) J ↔ Disjoint (I : Set (ι → ℝ)) J :=
  disjoint_withBotCoe.symm
#align box_integral.box.disjoint_coe BoxIntegral.Box.disjoint_coe

theorem not_disjoint_coe_iff_nonempty_inter :
    ¬Disjoint (I : WithBot (Box ι)) J ↔ (I ∩ J : Set (ι → ℝ)).Nonempty := by
  rw [disjoint_coe, Set.not_disjoint_iff_nonempty_inter]
  -- 🎉 no goals
#align box_integral.box.not_disjoint_coe_iff_nonempty_inter BoxIntegral.Box.not_disjoint_coe_iff_nonempty_inter

/-!
### Hyperface of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`
-/


/-- Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at
`I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`. -/
@[simps (config := { simpRhs := true })]
def face {n} (I : Box (Fin (n + 1))) (i : Fin (n + 1)) : Box (Fin n) :=
  ⟨I.lower ∘ Fin.succAbove i, I.upper ∘ Fin.succAbove i, fun _ ↦ I.lower_lt_upper _⟩
#align box_integral.box.face BoxIntegral.Box.face

@[simp]
theorem face_mk {n} (l u : Fin (n + 1) → ℝ) (h : ∀ i, l i < u i) (i : Fin (n + 1)) :
    face ⟨l, u, h⟩ i = ⟨l ∘ Fin.succAbove i, u ∘ Fin.succAbove i, fun _ ↦ h _⟩ := rfl
#align box_integral.box.face_mk BoxIntegral.Box.face_mk

@[mono]
theorem face_mono {n} {I J : Box (Fin (n + 1))} (h : I ≤ J) (i : Fin (n + 1)) :
    face I i ≤ face J i :=
  fun _ hx _ ↦ Ioc_subset_Ioc ((le_iff_bounds.1 h).1 _) ((le_iff_bounds.1 h).2 _) (hx _)
#align box_integral.box.face_mono BoxIntegral.Box.face_mono

theorem monotone_face {n} (i : Fin (n + 1)) : Monotone fun I ↦ face I i :=
  fun _ _ h ↦ face_mono h i
#align box_integral.box.monotone_face BoxIntegral.Box.monotone_face

theorem mapsTo_insertNth_face_Icc {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ Icc (I.lower i) (I.upper i)) :
    MapsTo (i.insertNth x) (Box.Icc (I.face i)) (Box.Icc I) :=
  fun _ hy ↦ Fin.insertNth_mem_Icc.2 ⟨hx, hy⟩
#align box_integral.box.maps_to_insert_nth_face_Icc BoxIntegral.Box.mapsTo_insertNth_face_Icc

theorem mapsTo_insertNth_face {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ Ioc (I.lower i) (I.upper i)) :
    MapsTo (i.insertNth x) (I.face i : Set (_ → _)) (I : Set (_ → _)) := by
  intro y hy
  -- ⊢ Fin.insertNth i x y ∈ ↑I
  simp_rw [mem_coe, mem_def, i.forall_iff_succAbove, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact ⟨hx, hy⟩
  -- 🎉 no goals
#align box_integral.box.maps_to_insert_nth_face BoxIntegral.Box.mapsTo_insertNth_face

theorem continuousOn_face_Icc {X} [TopologicalSpace X] {n} {f : (Fin (n + 1) → ℝ) → X}
    {I : Box (Fin (n + 1))} (h : ContinuousOn f (Box.Icc I)) {i : Fin (n + 1)} {x : ℝ}
    (hx : x ∈ Icc (I.lower i) (I.upper i)) :
    ContinuousOn (f ∘ i.insertNth x) (Box.Icc (I.face i)) :=
  h.comp (continuousOn_const.fin_insertNth i continuousOn_id) (I.mapsTo_insertNth_face_Icc hx)
#align box_integral.box.continuous_on_face_Icc BoxIntegral.Box.continuousOn_face_Icc

/-!
### Covering of the interior of a box by a monotone sequence of smaller boxes
-/


/-- The interior of a box. -/
protected def Ioo : Box ι →o Set (ι → ℝ) where
  toFun I := pi univ fun i ↦ Ioo (I.lower i) (I.upper i)
  monotone' _ _ h :=
    pi_mono fun i _ ↦ Ioo_subset_Ioo ((le_iff_bounds.1 h).1 i) ((le_iff_bounds.1 h).2 i)
#align box_integral.box.Ioo BoxIntegral.Box.Ioo

theorem Ioo_subset_coe (I : Box ι) : Box.Ioo I ⊆ I :=
  fun _ hx i ↦ Ioo_subset_Ioc_self (hx i trivial)
#align box_integral.box.Ioo_subset_coe BoxIntegral.Box.Ioo_subset_coe

protected theorem Ioo_subset_Icc (I : Box ι) : Box.Ioo I ⊆ Box.Icc I :=
  I.Ioo_subset_coe.trans coe_subset_Icc
#align box_integral.box.Ioo_subset_Icc BoxIntegral.Box.Ioo_subset_Icc

theorem iUnion_Ioo_of_tendsto [Finite ι] {I : Box ι} {J : ℕ → Box ι} (hJ : Monotone J)
    (hl : Tendsto (lower ∘ J) atTop (𝓝 I.lower)) (hu : Tendsto (upper ∘ J) atTop (𝓝 I.upper)) :
    ⋃ n, Box.Ioo (J n) = Box.Ioo I :=
  have hl' : ∀ i, Antitone fun n ↦ (J n).lower i :=
    fun i ↦ (monotone_eval i).comp_antitone (antitone_lower.comp_monotone hJ)
  have hu' : ∀ i, Monotone fun n ↦ (J n).upper i :=
    fun i ↦ (monotone_eval i).comp (monotone_upper.comp hJ)
  calc
    ⋃ n, Box.Ioo (J n) = pi univ fun i ↦ ⋃ n, Ioo ((J n).lower i) ((J n).upper i) :=
      iUnion_univ_pi_of_monotone fun i ↦ (hl' i).Ioo (hu' i)
    _ = Box.Ioo I :=
      pi_congr rfl fun i _ ↦
        iUnion_Ioo_of_mono_of_isGLB_of_isLUB (hl' i) (hu' i)
          (isGLB_of_tendsto_atTop (hl' i) (tendsto_pi_nhds.1 hl _))
          (isLUB_of_tendsto_atTop (hu' i) (tendsto_pi_nhds.1 hu _))
#align box_integral.box.Union_Ioo_of_tendsto BoxIntegral.Box.iUnion_Ioo_of_tendsto

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
#align box_integral.box.exists_seq_mono_tendsto BoxIntegral.Box.exists_seq_mono_tendsto

section Distortion

variable [Fintype ι]

/-- The distortion of a box `I` is the maximum of the ratios of the lengths of its edges.
It is defined as the maximum of the ratios
`nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`. -/
def distortion (I : Box ι) : ℝ≥0 :=
  Finset.univ.sup fun i : ι ↦ nndist I.lower I.upper / nndist (I.lower i) (I.upper i)
#align box_integral.box.distortion BoxIntegral.Box.distortion

theorem distortion_eq_of_sub_eq_div {I J : Box ι} {r : ℝ}
    (h : ∀ i, I.upper i - I.lower i = (J.upper i - J.lower i) / r) :
    distortion I = distortion J := by
  simp only [distortion, nndist_pi_def, Real.nndist_eq', h, map_div₀]
  -- ⊢ (Finset.sup Finset.univ fun i => (Finset.sup Finset.univ fun b => ↑Real.nnab …
  congr 1 with i
  -- ⊢ ↑((Finset.sup Finset.univ fun b => ↑Real.nnabs (upper J b - lower J b) / ↑Re …
  have : 0 < r := by
    by_contra hr
    have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 <| J.lower_le_upper i) (not_lt.1 hr)
    rw [← h] at this
    exact this.not_lt (sub_pos.2 <| I.lower_lt_upper i)
  have hn0 := (map_ne_zero Real.nnabs).2 this.ne'
  -- ⊢ ↑((Finset.sup Finset.univ fun b => ↑Real.nnabs (upper J b - lower J b) / ↑Re …
  simp_rw [NNReal.finset_sup_div, div_div_div_cancel_right _ hn0]
  -- 🎉 no goals
#align box_integral.box.distortion_eq_of_sub_eq_div BoxIntegral.Box.distortion_eq_of_sub_eq_div

theorem nndist_le_distortion_mul (I : Box ι) (i : ι) :
    nndist I.lower I.upper ≤ I.distortion * nndist (I.lower i) (I.upper i) :=
  calc
    nndist I.lower I.upper =
        nndist I.lower I.upper / nndist (I.lower i) (I.upper i) * nndist (I.lower i) (I.upper i) :=
      (div_mul_cancel _ <| mt nndist_eq_zero.1 (I.lower_lt_upper i).ne).symm
    _ ≤ I.distortion * nndist (I.lower i) (I.upper i) := by
      apply mul_le_mul_right'
      -- ⊢ nndist I.lower I.upper / nndist (lower I i) (upper I i) ≤ distortion I
      apply Finset.le_sup (Finset.mem_univ i)
      -- 🎉 no goals
#align box_integral.box.nndist_le_distortion_mul BoxIntegral.Box.nndist_le_distortion_mul

theorem dist_le_distortion_mul (I : Box ι) (i : ι) :
    dist I.lower I.upper ≤ I.distortion * (I.upper i - I.lower i) := by
  have A : I.lower i - I.upper i < 0 := sub_neg.2 (I.lower_lt_upper i)
  -- ⊢ dist I.lower I.upper ≤ ↑(distortion I) * (upper I i - lower I i)
  simpa only [← NNReal.coe_le_coe, ← dist_nndist, NNReal.coe_mul, Real.dist_eq, abs_of_neg A,
    neg_sub] using I.nndist_le_distortion_mul i
#align box_integral.box.dist_le_distortion_mul BoxIntegral.Box.dist_le_distortion_mul

theorem diam_Icc_le_of_distortion_le (I : Box ι) (i : ι) {c : ℝ≥0} (h : I.distortion ≤ c) :
    diam (Box.Icc I) ≤ c * (I.upper i - I.lower i) :=
  have : (0 : ℝ) ≤ c * (I.upper i - I.lower i) :=
    mul_nonneg c.coe_nonneg (sub_nonneg.2 <| I.lower_le_upper _)
  diam_le_of_forall_dist_le this fun x hx y hy ↦
    calc
      dist x y ≤ dist I.lower I.upper := Real.dist_le_of_mem_pi_Icc hx hy
      _ ≤ I.distortion * (I.upper i - I.lower i) := (I.dist_le_distortion_mul i)
      _ ≤ c * (I.upper i - I.lower i) := by gcongr; exact sub_nonneg.2 (I.lower_le_upper i)
                                            -- ⊢ 0 ≤ upper I i - lower I i
                                                    -- 🎉 no goals
#align box_integral.box.diam_Icc_le_of_distortion_le BoxIntegral.Box.diam_Icc_le_of_distortion_le

end Distortion

end Box

end BoxIntegral
