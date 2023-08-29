/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.BoxIntegral.Partition.Split
import Mathlib.Analysis.NormedSpace.OperatorNorm

#align_import analysis.box_integral.partition.additive from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Box additive functions

We say that a function `f : Box ι → M` from boxes in `ℝⁿ` to a commutative additive monoid `M` is
*box additive* on subboxes of `I₀ : WithTop (Box ι)` if for any box `J`, `↑J ≤ I₀`, and a partition
`π` of `J`, `f J = ∑ J' in π.boxes, f J'`. We use `I₀ : WithTop (Box ι)` instead of `I₀ : Box ι` to
use the same definition for functions box additive on subboxes of a box and for functions box
additive on all boxes.

Examples of box-additive functions include the measure of a box and the integral of a fixed
integrable function over a box.

In this file we define box-additive functions and prove that a function such that
`f J = f (J ∩ {x | x i < y}) + f (J ∩ {x | y ≤ x i})` is box-additive.

### Tags

rectangular box, additive function
-/


noncomputable section

open Classical BigOperators Function Set

namespace BoxIntegral

variable {ι M : Type*} {n : ℕ}

/-- A function on `Box ι` is called box additive if for every box `J` and a partition `π` of `J`
we have `f J = ∑ Ji in π.boxes, f Ji`. A function is called box additive on subboxes of `I : Box ι`
if the same property holds for `J ≤ I`. We formalize these two notions in the same definition
using `I : WithBot (Box ι)`: the value `I = ⊤` corresponds to functions box additive on the whole
space. -/
structure BoxAdditiveMap (ι M : Type*) [AddCommMonoid M] (I : WithTop (Box ι)) where
  toFun : Box ι → M
  sum_partition_boxes' : ∀ J : Box ι, ↑J ≤ I → ∀ π : Prepartition J, π.IsPartition →
    ∑ Ji in π.boxes, toFun Ji = toFun J
#align box_integral.box_additive_map BoxIntegral.BoxAdditiveMap

scoped notation:25 ι " →ᵇᵃ " M => BoxIntegral.BoxAdditiveMap ι M ⊤
scoped notation:25 ι " →ᵇᵃ[" I "] " M => BoxIntegral.BoxAdditiveMap ι M I

namespace BoxAdditiveMap

open Box Prepartition Finset

variable {N : Type*} [AddCommMonoid M] [AddCommMonoid N] {I₀ : WithTop (Box ι)} {I J : Box ι}
  {i : ι}

instance : FunLike (ι →ᵇᵃ[I₀] M) (Box ι) (fun _ ↦ M) where
  coe := toFun
  coe_injective' f g h := by cases f; cases g; congr
                             -- ⊢ { toFun := toFun✝, sum_partition_boxes' := sum_partition_boxes'✝ } = g
                                      -- ⊢ { toFun := toFun✝¹, sum_partition_boxes' := sum_partition_boxes'✝¹ } = { toF …
                                               -- 🎉 no goals

initialize_simps_projections BoxIntegral.BoxAdditiveMap (toFun → apply)

#noalign box_integral.box_additive_map.to_fun_eq_coe

@[simp]
theorem coe_mk (f h) : ⇑(mk f h : ι →ᵇᵃ[I₀] M) = f := rfl
#align box_integral.box_additive_map.coe_mk BoxIntegral.BoxAdditiveMap.coe_mk

theorem coe_injective : Injective fun (f : ι →ᵇᵃ[I₀] M) x => f x :=
  FunLike.coe_injective
#align box_integral.box_additive_map.coe_injective BoxIntegral.BoxAdditiveMap.coe_injective

-- porting note: was @[simp], now can be proved by `simp`
theorem coe_inj {f g : ι →ᵇᵃ[I₀] M} : (f : Box ι → M) = g ↔ f = g := FunLike.coe_fn_eq
#align box_integral.box_additive_map.coe_inj BoxIntegral.BoxAdditiveMap.coe_inj

theorem sum_partition_boxes (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π : Prepartition I}
    (h : π.IsPartition) : ∑ J in π.boxes, f J = f I :=
  f.sum_partition_boxes' I hI π h
#align box_integral.box_additive_map.sum_partition_boxes BoxIntegral.BoxAdditiveMap.sum_partition_boxes

@[simps (config := { fullyApplied := false })]
instance : Zero (ι →ᵇᵃ[I₀] M) :=
  ⟨⟨0, fun _ _ _ _ => sum_const_zero⟩⟩

instance : Inhabited (ι →ᵇᵃ[I₀] M) :=
  ⟨0⟩

instance : Add (ι →ᵇᵃ[I₀] M) :=
  ⟨fun f g =>
    ⟨f + g, fun I hI π hπ => by
      simp only [Pi.add_apply, sum_add_distrib, sum_partition_boxes _ hI hπ]⟩⟩
      -- 🎉 no goals

instance {R} [Monoid R] [DistribMulAction R M] : SMul R (ι →ᵇᵃ[I₀] M) :=
  ⟨fun r f =>
    ⟨r • (f : Box ι → M), fun I hI π hπ => by
      simp only [Pi.smul_apply, ← smul_sum, sum_partition_boxes _ hI hπ]⟩⟩
      -- 🎉 no goals

instance : AddCommMonoid (ι →ᵇᵃ[I₀] M) :=
  Function.Injective.addCommMonoid _ coe_injective rfl (fun _ _ => rfl) fun _ _ => rfl

@[simp]
theorem map_split_add (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) (i : ι) (x : ℝ) :
    (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f = f I := by
  rw [← f.sum_partition_boxes hI (isPartitionSplit I i x), sum_split_boxes]
  -- 🎉 no goals
#align box_integral.box_additive_map.map_split_add BoxIntegral.BoxAdditiveMap.map_split_add

/-- If `f` is box-additive on subboxes of `I₀`, then it is box-additive on subboxes of any
`I ≤ I₀`. -/
@[simps]
def restrict (f : ι →ᵇᵃ[I₀] M) (I : WithTop (Box ι)) (hI : I ≤ I₀) : ι →ᵇᵃ[I] M :=
  ⟨f, fun J hJ => f.2 J (hJ.trans hI)⟩
#align box_integral.box_additive_map.restrict BoxIntegral.BoxAdditiveMap.restrict

/-- If `f : Box ι → M` is box additive on partitions of the form `split I i x`, then it is box
additive. -/
def ofMapSplitAdd [Fintype ι] (f : Box ι → M) (I₀ : WithTop (Box ι))
    (hf : ∀ I : Box ι, ↑I ≤ I₀ → ∀ {i x}, x ∈ Ioo (I.lower i) (I.upper i) →
      (I.splitLower i x).elim' 0 f + (I.splitUpper i x).elim' 0 f = f I) :
    ι →ᵇᵃ[I₀] M := by
  refine' ⟨f, _⟩
  -- ⊢ ∀ (J : Box ι), ↑J ≤ I₀ → ∀ (π : Prepartition J), IsPartition π → ∑ Ji in π.b …
  replace hf : ∀ I : Box ι, ↑I ≤ I₀ → ∀ s, (∑ J in (splitMany I s).boxes, f J) = f I
  -- ⊢ ∀ (I : Box ι), ↑I ≤ I₀ → ∀ (s : Finset (ι × ℝ)), ∑ J in (splitMany I s).boxe …
  · intro I hI s
    -- ⊢ ∑ J in (splitMany I s).boxes, f J = f I
    induction' s using Finset.induction_on with a s _ ihs
    -- ⊢ ∑ J in (splitMany I ∅).boxes, f J = f I
    · simp
      -- 🎉 no goals
    rw [splitMany_insert, inf_split, ← ihs, biUnion_boxes, sum_biUnion_boxes]
    -- ⊢ ∑ J in (splitMany I s).boxes, ∑ J' in (split J a.fst a.snd).boxes, f J' = ∑  …
    refine' Finset.sum_congr rfl fun J' hJ' => _
    -- ⊢ ∑ J' in (split J' a.fst a.snd).boxes, f J' = f J'
    by_cases h : a.2 ∈ Ioo (J'.lower a.1) (J'.upper a.1)
    -- ⊢ ∑ J' in (split J' a.fst a.snd).boxes, f J' = f J'
    · rw [sum_split_boxes]
      -- ⊢ Option.elim' 0 (fun J' => f J') (splitLower J' a.fst a.snd) + Option.elim' 0 …
      exact hf _ ((WithTop.coe_le_coe.2 <| le_of_mem _ hJ').trans hI) h
      -- 🎉 no goals
    · rw [split_of_not_mem_Ioo h, top_boxes, Finset.sum_singleton]
      -- 🎉 no goals
  intro I hI π hπ
  -- ⊢ ∑ Ji in π.boxes, f Ji = f I
  have Hle : ∀ J ∈ π, ↑J ≤ I₀ := fun J hJ => (WithTop.coe_le_coe.2 <| π.le_of_mem hJ).trans hI
  -- ⊢ ∑ Ji in π.boxes, f Ji = f I
  rcases hπ.exists_splitMany_le with ⟨s, hs⟩
  -- ⊢ ∑ Ji in π.boxes, f Ji = f I
  rw [← hf _ hI, ← inf_of_le_right hs, inf_splitMany, biUnion_boxes, sum_biUnion_boxes]
  -- ⊢ ∑ Ji in π.boxes, f Ji = ∑ J in π.boxes, ∑ J' in (splitMany J s).boxes, f J'
  exact Finset.sum_congr rfl fun J hJ => (hf _ (Hle _ hJ) _).symm
  -- 🎉 no goals
#align box_integral.box_additive_map.of_map_split_add BoxIntegral.BoxAdditiveMap.ofMapSplitAdd

/-- If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is a box additive
map. -/
@[simps (config := { fullyApplied := false })]
def map (f : ι →ᵇᵃ[I₀] M) (g : M →+ N) : ι →ᵇᵃ[I₀] N where
  toFun := g ∘ f
  sum_partition_boxes' I hI π hπ := by simp_rw [comp, ← g.map_sum, f.sum_partition_boxes hI hπ]
                                       -- 🎉 no goals
#align box_integral.box_additive_map.map BoxIntegral.BoxAdditiveMap.map

/-- If `f` is a box additive function on subboxes of `I` and `π₁`, `π₂` are two prepartitions of
`I` that cover the same part of `I`, then `∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J`. -/
theorem sum_boxes_congr [Finite ι] (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π₁ π₂ : Prepartition I}
    (h : π₁.iUnion = π₂.iUnion) : ∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J := by
  rcases exists_splitMany_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _) with
    ⟨s, hs⟩
  simp only [inf_splitMany] at hs
  -- ⊢ ∑ J in π₁.boxes, ↑f J = ∑ J in π₂.boxes, ↑f J
  rcases hs _ (Or.inl rfl), hs _ (Or.inr rfl) with ⟨h₁, h₂⟩; clear hs
  -- ⊢ ∑ J in π₁.boxes, ↑f J = ∑ J in π₂.boxes, ↑f J
                                                             -- ⊢ ∑ J in π₁.boxes, ↑f J = ∑ J in π₂.boxes, ↑f J
  rw [h] at h₁
  -- ⊢ ∑ J in π₁.boxes, ↑f J = ∑ J in π₂.boxes, ↑f J
  calc
    ∑ J in π₁.boxes, f J = ∑ J in π₁.boxes, ∑ J' in (splitMany J s).boxes, f J' :=
      Finset.sum_congr rfl fun J hJ => (f.sum_partition_boxes ?_ (isPartition_splitMany _ _)).symm
    _ = ∑ J in (π₁.biUnion fun J => splitMany J s).boxes, f J := (sum_biUnion_boxes _ _ _).symm
    _ = ∑ J in (π₂.biUnion fun J => splitMany J s).boxes, f J := by rw [h₁, h₂]
    _ = ∑ J in π₂.boxes, ∑ J' in (splitMany J s).boxes, f J' := (sum_biUnion_boxes _ _ _)
    _ = ∑ J in π₂.boxes, f J :=
      Finset.sum_congr rfl fun J hJ => f.sum_partition_boxes ?_ (isPartition_splitMany _ _)
  exacts [(WithTop.coe_le_coe.2 <| π₁.le_of_mem hJ).trans hI,
    (WithTop.coe_le_coe.2 <| π₂.le_of_mem hJ).trans hI]
#align box_integral.box_additive_map.sum_boxes_congr BoxIntegral.BoxAdditiveMap.sum_boxes_congr

section ToSMul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `f` is a box-additive map, then so is the map sending `I` to the scalar multiplication
by `f I` as a continuous linear map from `E` to itself. -/
def toSMul (f : ι →ᵇᵃ[I₀] ℝ) : ι →ᵇᵃ[I₀] E →L[ℝ] E :=
  f.map (ContinuousLinearMap.lsmul ℝ ℝ).toLinearMap.toAddMonoidHom
#align box_integral.box_additive_map.to_smul BoxIntegral.BoxAdditiveMap.toSMul

@[simp]
theorem toSMul_apply (f : ι →ᵇᵃ[I₀] ℝ) (I : Box ι) (x : E) : f.toSMul I x = f I • x := rfl
#align box_integral.box_additive_map.to_smul_apply BoxIntegral.BoxAdditiveMap.toSMul_apply

end ToSMul

/-- Given a box `I₀` in `ℝⁿ⁺¹`, `f x : Box (Fin n) → G` is a family of functions indexed by a real
`x` and for `x ∈ [I₀.lower i, I₀.upper i]`, `f x` is box-additive on subboxes of the `i`-th face of
`I₀`, then `fun J ↦ f (J.upper i) (J.face i) - f (J.lower i) (J.face i)` is box-additive on subboxes
of `I₀`. -/
@[simps!]
def upperSubLower.{u} {G : Type u} [AddCommGroup G] (I₀ : Box (Fin (n + 1))) (i : Fin (n + 1))
    (f : ℝ → Box (Fin n) → G) (fb : Icc (I₀.lower i) (I₀.upper i) → Fin n →ᵇᵃ[I₀.face i] G)
    (hf : ∀ (x) (hx : x ∈ Icc (I₀.lower i) (I₀.upper i)) (J), f x J = fb ⟨x, hx⟩ J) :
    Fin (n + 1) →ᵇᵃ[I₀] G :=
  ofMapSplitAdd (fun J : Box (Fin (n + 1)) => f (J.upper i) (J.face i) - f (J.lower i) (J.face i))
    I₀
    (by
      intro J hJ j x
      -- ⊢ x ∈ Set.Ioo (lower J j) (upper J j) → Option.elim' 0 (fun J => f (upper J i) …
      rw [WithTop.coe_le_coe] at hJ
      -- ⊢ x ∈ Set.Ioo (lower J j) (upper J j) → Option.elim' 0 (fun J => f (upper J i) …
      refine' i.succAboveCases (fun hx => _) (fun j hx => _) j
      -- ⊢ Option.elim' 0 (fun J => f (upper J i) (face J i) - f (lower J i) (face J i) …
      · simp only [Box.splitLower_def hx, Box.splitUpper_def hx, update_same, ← WithBot.some_eq_coe,
          Option.elim', Box.face, (· ∘ ·), update_noteq (Fin.succAbove_ne _ _)]
        abel
        -- 🎉 no goals
        -- 🎉 no goals
      · have : (J.face i : WithTop (Box (Fin n))) ≤ I₀.face i :=
          WithTop.coe_le_coe.2 (face_mono hJ i)
        rw [le_iff_Icc, @Box.Icc_eq_pi _ I₀] at hJ
        -- ⊢ Option.elim' 0 (fun J => f (upper J i) (face J i) - f (lower J i) (face J i) …
        simp only
        -- ⊢ Option.elim' 0 (fun J => f (upper J i) (face J i) - f (lower J i) (face J i) …
        rw [hf _ (hJ J.upper_mem_Icc _ trivial), hf _ (hJ J.lower_mem_Icc _ trivial),
          ← (fb _).map_split_add this j x, ← (fb _).map_split_add this j x]
        have hx' : x ∈ Ioo ((J.face i).lower j) ((J.face i).upper j) := hx
        -- ⊢ Option.elim' 0 (fun J => f (upper J i) (face J i) - f (lower J i) (face J i) …
        simp only [Box.splitLower_def hx, Box.splitUpper_def hx, Box.splitLower_def hx',
          Box.splitUpper_def hx', ← WithBot.some_eq_coe, Option.elim', Box.face_mk,
          update_noteq (Fin.succAbove_ne _ _).symm, sub_add_sub_comm,
          update_comp_eq_of_injective _ (Fin.strictMono_succAbove i).injective j x, ← hf]
        simp only [Box.face])
        -- 🎉 no goals
#align box_integral.box_additive_map.upper_sub_lower BoxIntegral.BoxAdditiveMap.upperSubLower

end BoxAdditiveMap

end BoxIntegral
