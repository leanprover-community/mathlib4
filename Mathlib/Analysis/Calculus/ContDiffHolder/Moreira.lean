/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.MetricSpace.Holder

/-!
# `C^{k+(α)}` functions in the sense of Moreira

In [Moreira2001], Moreira proves a version of the Morse-Sard theorem
for a carefully chosen class of maps he calls $C^{k+(α)}$ maps.
Namely, a map `f` is said to be $C^{k+(α)}$ at `a`,
where `k` is a natural number and `0 ≤ α ≤ 1`,
if it is $C^k$ at this point and $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`.

The main theorem of [Moreira2001] only assumes
that a function is $C^{k+(α)}$ at all points of a set `s`
and the rank of the Fréchet derivative at these points is at most a given number `p`,
which is strictly less than the dimension of the domain.
Then it provides an upper estimate on the Hausdorff dimension of the image of `s` under `f`.

In this file, we define `ContDiffMoreiraHolderAt` to be the predicate
saying that a function is $C^{k+(α)}$ in the sense described above
and prove basic properties of this predicate.

## Implementation notes

In the original paper, `k` is assumed to be a strictly positive number.
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
if it is $C^k$ at this point and $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ k)$ as `x → a`. -/
@[mk_iff]
structure ContDiffMoreiraHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  /-- A $C^{k+(α)}$ map is a $C^k$ map. -/
  contDiffAt : ContDiffAt ℝ k f a
  /-- A $C^{k+(α)}$ map satisfies $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ k)$ as `x → a`. -/
  isBigO : (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

/-- A $C^n$ map is a $C^{k+(α)}$ map with any `k < n`. -/
theorem ContDiffAt.contDiffMoreiraHolderAt {n : WithTop ℕ∞} (h : ContDiffAt ℝ n f a) (hk : k < n)
    (α : I) : ContDiffMoreiraHolderAt k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) <| tendsto_norm_sub_self_nhdsGE a

namespace ContDiffMoreiraHolderAt

theorem continuousAt (h : ContDiffMoreiraHolderAt k α f a) : ContinuousAt f a :=
  h.contDiffAt.continuousAt

theorem differentiableAt (h : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) :
    DifferentiableAt ℝ f a :=
  h.contDiffAt.differentiableAt <| mod_cast hk

/-- A function is $C^{k+(0)}$ at a point if and only if it is $C^k$ at the point. -/
@[simp]
theorem zero_exponent_iff : ContDiffMoreiraHolderAt k 0 f a ↔ ContDiffAt ℝ k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

/-- A function is $C^{0+(α)}$ at a point if and only if
it is $C^0$ at the point (i.e., it is continuous on a neighborhood of the point)
and $f(x) - f(a) = O(‖x - a‖ ^ α)$. -/
theorem zero_left_iff :
    ContDiffMoreiraHolderAt 0 α f a ↔
      ContDiffAt ℝ 0 f a ∧ (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) := by
  simp only [contDiffMoreiraHolderAt_iff, Nat.cast_zero, and_congr_right_iff]
  intro hfc
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub]
  rw [← isBigO_norm_left]
  simp_rw [LinearIsometryEquiv.norm_map, isBigO_norm_left]

theorem of_exponent_le (hf : ContDiffMoreiraHolderAt k α f a) (hle : β ≤ α) :
    ContDiffMoreiraHolderAt k β f a where
  contDiffAt := hf.contDiffAt
  isBigO := hf.isBigO.trans <| by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le_of_imp hle fun hα ↦ ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a

theorem of_lt (hf : ContDiffMoreiraHolderAt k α f a) (hlt : l < k) :
    ContDiffMoreiraHolderAt l β f a :=
  hf.contDiffAt.contDiffMoreiraHolderAt (mod_cast hlt) _

theorem of_toLex_le (hf : ContDiffMoreiraHolderAt k α f a) (hle : toLex (l, β) ≤ toLex (k, α)) :
    ContDiffMoreiraHolderAt l β f a :=
  (Prod.Lex.le_iff.mp hle).elim hf.of_lt <| by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle

theorem of_le (hf : ContDiffMoreiraHolderAt k α f a) (hl : l ≤ k) :
    ContDiffMoreiraHolderAt l α f a :=
  hf.of_toLex_le <| Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

/-- If a function is $C^{k+α}$ on a neighborhood of a point `a`,
i.e., it is $C^k$ on this neighborhood and $D^k f$ is Hölder continuous on it,
then the function is $C^{k+(α)}$ at `a`. -/
theorem of_contDiffOn_holderWith {s : Set E} {C : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv ℝ k f) s) :
    ContDiffMoreiraHolderAt k α f a where
  contDiffAt := hf.contDiffAt hs
  isBigO := .of_bound C <| mem_of_superset hs fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using hd.dist_le hx (mem_of_mem_nhds hs)

theorem fst {a : E × F} : ContDiffMoreiraHolderAt k α Prod.fst a :=
  contDiffAt_fst.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

theorem snd {a : E × F} : ContDiffMoreiraHolderAt k α Prod.snd a :=
  contDiffAt_snd.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

theorem prodMk {g : E → G} (hf : ContDiffMoreiraHolderAt k α f a)
    (hg : ContDiffMoreiraHolderAt k α g a) :
    ContDiffMoreiraHolderAt k α (fun x ↦ (f x, g x)) a where
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

/-- Composition of two $C^{k+(α)}$ functions is a $C^{k+(α)}$ function,
provided that one of them is differentiable.

The latter condition follows automatically from the functions being $C^{k+(α)}$,
if `k ≠ 0`, see `comp` below. -/
theorem comp_of_differentiableAt {g : F → G} (hg : ContDiffMoreiraHolderAt k α g (f a))
    (hf : ContDiffMoreiraHolderAt k α f a)
    (hd : DifferentiableAt ℝ g (f a) ∨ DifferentiableAt ℝ f a) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a where
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
      apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO
      · intro i hi
        exact ((hg.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).comp hf.continuousAt)
          |>.norm.isBoundedUnder_le
      · intro i hi
        by_cases hfd : DifferentiableAt ℝ f a
        · refine ((hg.of_le hi).isBigO.comp_tendsto hf.continuousAt).trans ?_
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
          refine .trans (.of_norm_right ?_) hf.isBigO
          simp [iteratedFDeriv_zero_eq_comp, ← map_sub, Function.comp_def, isBigO_refl]
      · intro i hi
        exact (hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).norm.isBoundedUnder_le
      · exact fun _ _ ↦ isBoundedUnder_const
      · exact fun i hi ↦ (hf.of_le hi).isBigO

/-- Composition of two $C^{k+(α)}$ functions, `k ≠ 0`, is a $C^{k+(α)}$ function. -/
theorem comp {g : F → G} (hg : ContDiffMoreiraHolderAt k α g (f a))
    (hf : ContDiffMoreiraHolderAt k α f a) (hk : k ≠ 0) : ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  hg.comp_of_differentiableAt hf (.inl <| hg.differentiableAt hk)

theorem _root_.ContinuousLinearMap.contDiffMoreiraHolderAt (f : E →L[ℝ] F) :
    ContDiffMoreiraHolderAt k α f a :=
  f.contDiff.contDiffAt.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) _

theorem _root_.ContinuousLinearEquiv.contDiffMoreiraHolderAt (f : E ≃L[ℝ] F) :
    ContDiffMoreiraHolderAt k α f a :=
  f.toContinuousLinearMap.contDiffMoreiraHolderAt

theorem continuousLinearMap_comp (hf : ContDiffMoreiraHolderAt k α f a) (g : F →L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a :=
  g.contDiffMoreiraHolderAt.comp_of_differentiableAt hf <| .inl g.differentiableAt

@[simp]
theorem _root_.ContinuousLinearEquiv.contDiffMoreiraHolderAt_left_comp (g : F ≃L[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.continuousLinearMap_comp (g.symm : G →L[ℝ] F),
    fun h ↦ h.continuousLinearMap_comp (g : F →L[ℝ] G)⟩

@[simp]
theorem _root_.LinearIsometryEquiv.contDiffMoreiraHolderAt_left_comp (g : F ≃ₗᵢ[ℝ] G) :
    ContDiffMoreiraHolderAt k α (g ∘ f) a ↔ ContDiffMoreiraHolderAt k α f a :=
  g.toContinuousLinearEquiv.contDiffMoreiraHolderAt_left_comp

protected theorem id : ContDiffMoreiraHolderAt k α id a :=
  ContinuousLinearMap.id ℝ E |>.contDiffMoreiraHolderAt

protected theorem const {b : F} : ContDiffMoreiraHolderAt k α (Function.const E b) a :=
  contDiffAt_const.contDiffMoreiraHolderAt (WithTop.coe_lt_top _) α

/-- The derivative of a $C^{k + (α)}$ function is a $C^{l + (α)}$ function, if `l < k`. -/
protected theorem fderiv (hf : ContDiffMoreiraHolderAt k α f a) (hl : l < k) :
    ContDiffMoreiraHolderAt l α (fderiv ℝ f) a where
  contDiffAt := hf.contDiffAt.fderiv_right (mod_cast hl)
  isBigO := .of_norm_left <| by
    simpa [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, ← dist_eq_norm_sub]
      using hf.of_le (Nat.add_one_le_iff.mpr hl) |>.isBigO |>.norm_left

/-- If `f` is a $C^{k+(α)}$ function and `l + m ≤ k`, then $D^mf$ is a $C^{l + (α)}$ function. -/
protected theorem iteratedFDeriv (hf : ContDiffMoreiraHolderAt k α f a) (hl : l + m ≤ k) :
    ContDiffMoreiraHolderAt l α (iteratedFDeriv ℝ m f) a := by
  induction m generalizing l with
  | zero =>
    simpa +unfoldPartialApp [iteratedFDeriv_zero_eq_comp] using hf.of_le hl
  | succ m ihm =>
    rw [← add_assoc, add_right_comm] at hl
    simpa +unfoldPartialApp [iteratedFDeriv_succ_eq_comp_left] using (ihm hl).fderiv l.lt_add_one

theorem congr_eventuallyEq {g : E → F} (hf : ContDiffMoreiraHolderAt k α f a) (hfg : f =ᶠ[𝓝 a] g) :
    ContDiffMoreiraHolderAt k α g a where
  contDiffAt := hf.contDiffAt.congr_of_eventuallyEq hfg.symm
  isBigO := by
    refine EventuallyEq.trans_isBigO (.sub ?_ ?_) hf.isBigO
    · exact hfg.symm.iteratedFDeriv ℝ _
    · rw [hfg.symm.iteratedFDeriv ℝ _ |>.self_of_nhds]

theorem clm_apply {f : E → F →L[ℝ] G} {g : E → F} (hf : ContDiffMoreiraHolderAt k α f a)
    (hg : ContDiffMoreiraHolderAt k α g a) : ContDiffMoreiraHolderAt k α (fun x ↦ f x (g x)) a :=
  (contDiffAt_fst.clm_apply contDiffAt_snd).contDiffMoreiraHolderAt (WithTop.coe_lt_top _) _
    |>.comp_of_differentiableAt (hf.prodMk hg) <| .inl (by fun_prop)

end ContDiffMoreiraHolderAt
