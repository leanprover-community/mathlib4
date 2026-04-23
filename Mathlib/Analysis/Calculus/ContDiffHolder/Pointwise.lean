/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.IsBounded
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Continuously `k` times differentiable functions with pointwise Hölder continuous derivatives

We say that a function is of class $C^{k+(α)}$ at a point `a`,
where `k` is a natural number and `0 ≤ α ≤ 1`, if

- it is of class $C^k$ at `a` in the sense of `ContDiffAt`;
- its `k`th derivative satisfies $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`.

Note that the Hölder condition used in this definition fixes one of the points at `a`.
In different sources, it is called *pointwise*, *local*, or *weak* Hölder condition,
though the term "local" may also mean a stronger condition
saying that a function is Hölder continuous on a neighborhood of `a`.

The immediate reason for adding this definition to the library
is its use in [Moreira2001], where Moreira proves a version of the Morse-Sard theorem
for functions that satisfy this condition on their critical set.

In this file, we define `ContDiffPointwiseHolderAt` to be the predicate
saying that a function is $C^{k+(α)}$ in the sense described above
and prove basic properties of this predicate.

## Implementation notes

In Moreira's paper, `k` is assumed to be a strictly positive number.
We define the predicate for any `k : ℕ`, then assume `k ≠ 0` whenever it is necessary.
-/

@[expose] public section

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k l m : ℕ} {α β : I} {f : E → F} {a : E}

/-- A map `f` is said to be $C^{k+(α)}$ at `a`, where `k` is a natural number and `0 ≤ α ≤ 1`,
if it is $C^k$ at this point and $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`.

When naming lemmas about this predicate, `k` is called "order", and `α` is called "exponent". -/
@[mk_iff]
structure ContDiffPointwiseHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  /-- A $C^{k+(α)}$ map is a $C^k$ map. -/
  contDiffAt : ContDiffAt ℝ k f a
  /-- A $C^{k+(α)}$ map satisfies $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`. -/
  isBigO : (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

/-- A $C^n$ map is a $C^{k+(α)}$ map for any `k < n`. -/
theorem ContDiffAt.contDiffPointwiseHolderAt {n : WithTop ℕ∞} (h : ContDiffAt ℝ n f a) (hk : k < n)
    (α : I) : ContDiffPointwiseHolderAt k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) <| tendsto_norm_sub_self_nhdsGE a

namespace ContDiffPointwiseHolderAt

theorem continuousAt (h : ContDiffPointwiseHolderAt k α f a) : ContinuousAt f a :=
  h.contDiffAt.continuousAt

theorem differentiableAt (h : ContDiffPointwiseHolderAt k α f a) (hk : k ≠ 0) :
    DifferentiableAt ℝ f a :=
  h.contDiffAt.differentiableAt <| mod_cast hk

/-- A function is $C^{k+(0)}$ at a point if and only if it is $C^k$ at the point. -/
@[simp]
theorem zero_exponent_iff : ContDiffPointwiseHolderAt k 0 f a ↔ ContDiffAt ℝ k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

/-- A function is $C^{0+(α)}$ at a point if and only if
it is $C^0$ at the point (i.e., it is continuous on a neighborhood of the point)
and $f(x) - f(a) = O(‖x - a‖ ^ α)$. -/
theorem zero_order_iff :
    ContDiffPointwiseHolderAt 0 α f a ↔
      ContDiffAt ℝ 0 f a ∧ (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) := by
  simp only [contDiffPointwiseHolderAt_iff, Nat.cast_zero, and_congr_right_iff]
  intro hfc
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub]
  rw [← isBigO_norm_left]
  simp_rw [LinearIsometryEquiv.norm_map, isBigO_norm_left]

theorem of_exponent_le (hf : ContDiffPointwiseHolderAt k α f a) (hle : β ≤ α) :
    ContDiffPointwiseHolderAt k β f a where
  contDiffAt := hf.contDiffAt
  isBigO := hf.isBigO.trans <| by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le_of_imp hle fun hα ↦ ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a

theorem of_order_lt (hf : ContDiffPointwiseHolderAt k α f a) (hlt : l < k) :
    ContDiffPointwiseHolderAt l β f a :=
  hf.contDiffAt.contDiffPointwiseHolderAt (mod_cast hlt) _

theorem of_toLex_le (hf : ContDiffPointwiseHolderAt k α f a) (hle : toLex (l, β) ≤ toLex (k, α)) :
    ContDiffPointwiseHolderAt l β f a :=
  (Prod.Lex.le_iff.mp hle).elim hf.of_order_lt <| by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

theorem of_order_le (hf : ContDiffPointwiseHolderAt k α f a) (hl : l ≤ k) :
    ContDiffPointwiseHolderAt l α f a :=
  hf.of_toLex_le <| Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

/-- If a function is $C^{k+α}$ on a neighborhood of a point `a`,
i.e., it is $C^k$ on this neighborhood and $D^k f$ is Hölder continuous on it,
then the function is $C^{k+(α)}$ at `a`. -/
theorem of_contDiffOn_holderOnWith {s : Set E} {C : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv ℝ k f) s) :
    ContDiffPointwiseHolderAt k α f a where
  contDiffAt := hf.contDiffAt hs
  isBigO := .of_bound C <| mem_of_superset hs fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using hd.dist_le hx (mem_of_mem_nhds hs)

theorem fst {a : E × F} : ContDiffPointwiseHolderAt k α Prod.fst a :=
  contDiffAt_fst.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

theorem snd {a : E × F} : ContDiffPointwiseHolderAt k α Prod.snd a :=
  contDiffAt_snd.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

theorem prodMk {g : E → G} (hf : ContDiffPointwiseHolderAt k α f a)
    (hg : ContDiffPointwiseHolderAt k α g a) :
    ContDiffPointwiseHolderAt k α (fun x ↦ (f x, g x)) a where
  contDiffAt := hf.contDiffAt.prodMk hg.contDiffAt
  isBigO := calc
    _ =ᶠ[𝓝 a] (fun x ↦ (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f a).prod
                (iteratedFDeriv ℝ k g x - iteratedFDeriv ℝ k g a)) := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hg.contDiffAt.eventually (by simp)] with x hfx hgx
      apply DFunLike.ext
      rw [iteratedFDeriv_prodMk _ _ le_rfl, iteratedFDeriv_prodMk _ _ le_rfl] <;>
        simp [hfx, hgx, hf.contDiffAt, hg.contDiffAt]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      refine .of_norm_left ?_
      simp only [ContinuousMultilinearMap.opNorm_prod, ← Prod.norm_mk]
      exact (hf.isBigO.prod_left hg.isBigO).norm_left

variable (a) in
/-- Composition of two $C^{k+(α)}$ functions is a $C^{k+(α)}$ function,
provided that one of them is differentiable.

The latter condition follows automatically from the functions being $C^{k+(α)}$,
if `k ≠ 0`, see `comp` below. -/
theorem comp_of_differentiableAt {g : F → G} (hg : ContDiffPointwiseHolderAt k α g (f a))
    (hf : ContDiffPointwiseHolderAt k α f a)
    (hd : DifferentiableAt ℝ g (f a) ∨ DifferentiableAt ℝ f a) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a where
  contDiffAt := hg.contDiffAt.comp a hf.contDiffAt
  isBigO := calc
    (iteratedFDeriv ℝ k (g ∘ f) · - iteratedFDeriv ℝ k (g ∘ f) a)
      =ᶠ[𝓝 a] fun x ↦ (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) k -
        (ftaylorSeries ℝ g (f a)).taylorComp (ftaylorSeries ℝ f a) k := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hf.continuousAt.eventually (hg.contDiffAt.eventually (by simp))] with x hfx hgx
      rw [iteratedFDeriv_comp hgx hfx le_rfl,
        iteratedFDeriv_comp hg.contDiffAt hf.contDiffAt le_rfl]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO <;> intro i hi
      · exact ((hg.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).comp hf.continuousAt)
          |>.norm.isBoundedUnder_le
      · by_cases hfd : DifferentiableAt ℝ f a
        · refine ((hg.of_order_le hi).isBigO.comp_tendsto hf.continuousAt).trans ?_
          refine .rpow α.2.1 (.of_forall fun _ ↦ norm_nonneg _) <| .norm_norm ?_
          exact hfd.isBigO_sub
        · obtain rfl : k = 0 := by
            contrapose! hfd
            exact hf.differentiableAt hfd
          obtain rfl : i = 0 := by rwa [nonpos_iff_eq_zero] at hi
          refine .of_norm_left ?_
          simp only [ftaylorSeries, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
            LinearIsometryEquiv.norm_map, isBigO_norm_left]
          refine ((hd.resolve_right hfd).isBigO_sub.comp_tendsto hf.continuousAt).trans ?_
          exact (zero_order_iff.mp hf).2
      · exact (hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).norm.isBoundedUnder_le
      · exact isBoundedUnder_const
      · exact (hf.of_order_le hi).isBigO

variable (a) in
/-- Composition of two $C^{k+(α)}$ functions, `k ≠ 0`, is a $C^{k+(α)}$ function. -/
theorem comp {g : F → G} (hg : ContDiffPointwiseHolderAt k α g (f a))
    (hf : ContDiffPointwiseHolderAt k α f a) (hk : k ≠ 0) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a :=
  hg.comp_of_differentiableAt a hf (.inl <| hg.differentiableAt hk)

variable (a) in
theorem comp₂_of_differentiableAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : F × G → H} {f₁ : E → F} {f₂ : E → G} (hg : ContDiffPointwiseHolderAt k α g (f₁ a, f₂ a))
    (hf₁ : ContDiffPointwiseHolderAt k α f₁ a) (hf₂ : ContDiffPointwiseHolderAt k α f₂ a)
    (hdiff : DifferentiableAt ℝ g (f₁ a, f₂ a) ∨
      DifferentiableAt ℝ f₁ a ∧ DifferentiableAt ℝ f₂ a) :
    ContDiffPointwiseHolderAt k α (fun x ↦ g (f₁ x, f₂ x)) a :=
  hg.comp_of_differentiableAt a (hf₁.prodMk hf₂) <| hdiff.imp_right fun h ↦
    h.left.prodMk h.right

theorem _root_.ContinuousLinearMap.contDiffPointwiseHolderAt (f : E →L[ℝ] F) :
    ContDiffPointwiseHolderAt k α f a :=
  f.contDiff.contDiffAt.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _

theorem _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt (f : E ≃L[ℝ] F) :
    ContDiffPointwiseHolderAt k α f a :=
  f.toContinuousLinearMap.contDiffPointwiseHolderAt

theorem continuousLinearMap_comp (hf : ContDiffPointwiseHolderAt k α f a) (g : F →L[ℝ] G) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a :=
  g.contDiffPointwiseHolderAt.comp_of_differentiableAt a hf <| .inl g.differentiableAt

@[simp]
theorem _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp (g : F ≃L[ℝ] G) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a ↔ ContDiffPointwiseHolderAt k α f a :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.continuousLinearMap_comp (g.symm : G →L[ℝ] F),
    fun h ↦ h.continuousLinearMap_comp (g : F →L[ℝ] G)⟩

@[simp]
theorem _root_.LinearIsometryEquiv.contDiffPointwiseHolderAt_left_comp (g : F ≃ₗᵢ[ℝ] G) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a ↔ ContDiffPointwiseHolderAt k α f a :=
  g.toContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp

protected theorem id : ContDiffPointwiseHolderAt k α id a :=
  ContinuousLinearMap.id ℝ E |>.contDiffPointwiseHolderAt

protected theorem const {b : F} : ContDiffPointwiseHolderAt k α (Function.const E b) a :=
  contDiffAt_const.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

/-- The derivative of a $C^{k + (α)}$ function is a $C^{l + (α)}$ function, if `l < k`. -/
protected theorem fderiv (hf : ContDiffPointwiseHolderAt k α f a) (hl : l < k) :
    ContDiffPointwiseHolderAt l α (fderiv ℝ f) a where
  contDiffAt := hf.contDiffAt.fderiv_right (mod_cast hl)
  isBigO := .of_norm_left <| by
    simpa [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, ← dist_eq_norm_sub]
      using hf.of_order_le (Nat.add_one_le_iff.mpr hl) |>.isBigO |>.norm_left

/-- If `f` is a $C^{k+(α)}$ function and `l + m ≤ k`, then $D^mf$ is a $C^{l + (α)}$ function. -/
protected theorem iteratedFDeriv (hf : ContDiffPointwiseHolderAt k α f a) (hl : l + m ≤ k) :
    ContDiffPointwiseHolderAt l α (iteratedFDeriv ℝ m f) a := by
  induction m generalizing l with
  | zero =>
    simpa +unfoldPartialApp [iteratedFDeriv_zero_eq_comp] using hf.of_order_le hl
  | succ m ihm =>
    rw [← add_assoc, add_right_comm] at hl
    simpa +unfoldPartialApp [iteratedFDeriv_succ_eq_comp_left] using (ihm hl).fderiv l.lt_add_one

theorem congr_of_eventuallyEq {g : E → F} (hf : ContDiffPointwiseHolderAt k α f a)
    (hfg : f =ᶠ[𝓝 a] g) :
    ContDiffPointwiseHolderAt k α g a where
  contDiffAt := hf.contDiffAt.congr_of_eventuallyEq hfg.symm
  isBigO := by
    refine EventuallyEq.trans_isBigO (.sub ?_ ?_) hf.isBigO
    · exact hfg.symm.iteratedFDeriv ℝ _
    · rw [hfg.symm.iteratedFDeriv ℝ _ |>.self_of_nhds]

theorem clm_apply {f : E → F →L[ℝ] G} {g : E → F} (hf : ContDiffPointwiseHolderAt k α f a)
    (hg : ContDiffPointwiseHolderAt k α g a) :
    ContDiffPointwiseHolderAt k α (fun x ↦ f x (g x)) a :=
  (contDiffAt_fst.clm_apply contDiffAt_snd).contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _
    |>.comp₂_of_differentiableAt a hf hg <| .inl (by fun_prop)

end ContDiffPointwiseHolderAt
