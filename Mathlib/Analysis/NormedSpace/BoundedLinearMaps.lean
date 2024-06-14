/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.Analysis.NormedSpace.Multilinear.Basic
import Mathlib.Analysis.NormedSpace.Units
import Mathlib.Analysis.NormedSpace.OperatorNorm.Completeness
import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul


#align_import analysis.normed_space.bounded_linear_maps from "leanprover-community/mathlib"@"ce11c3c2a285bbe6937e26d9792fda4e51f3fe1a"

/-!
# Bounded linear maps

This file defines a class stating that a map between normed vector spaces is (bi)linear and
continuous.
Instead of asking for continuity, the definition takes the equivalent condition (because the space
is normed) that `‖f x‖` is bounded by a multiple of `‖x‖`. Hence the "bounded" in the name refers to
`‖f x‖/‖x‖` rather than `‖f x‖` itself.

## Main definitions

* `IsBoundedLinearMap`: Class stating that a map `f : E → F` is linear and has `‖f x‖` bounded
  by a multiple of `‖x‖`.
* `IsBoundedBilinearMap`: Class stating that a map `f : E × F → G` is bilinear and continuous,
  but through the simpler to provide statement that `‖f (x, y)‖` is bounded by a multiple of
  `‖x‖ * ‖y‖`
* `IsBoundedBilinearMap.linearDeriv`: Derivative of a continuous bilinear map as a linear map.
* `IsBoundedBilinearMap.deriv`: Derivative of a continuous bilinear map as a continuous linear
  map. The proof that it is indeed the derivative is `IsBoundedBilinearMap.hasFDerivAt` in
  `Analysis.Calculus.FDeriv`.

## Main theorems

* `IsBoundedBilinearMap.continuous`: A bounded bilinear map is continuous.
* `ContinuousLinearEquiv.isOpen`: The continuous linear equivalences are an open subset of the
  set of continuous linear maps between a pair of Banach spaces.  Placed in this file because its
  proof uses `IsBoundedBilinearMap.continuous`.

## Notes

The main use of this file is `IsBoundedBilinearMap`.
The file `Analysis.NormedSpace.Multilinear.Basic`
already expounds the theory of multilinear maps,
but the `2`-variables case is sufficiently simpler to currently deserve its own treatment.

`IsBoundedLinearMap` is effectively an unbundled version of `ContinuousLinearMap` (defined
in `Topology.Algebra.Module.Basic`, theory over normed spaces developed in
`Analysis.NormedSpace.OperatorNorm`), albeit the name disparity. A bundled
`ContinuousLinearMap` is to be preferred over an `IsBoundedLinearMap` hypothesis. Historical
artifact, really.
-/


noncomputable section

open Topology

open Filter (Tendsto)

open Metric ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A function `f` satisfies `IsBoundedLinearMap 𝕜 f` if it is linear and satisfies the
inequality `‖f x‖ ≤ M * ‖x‖` for some positive constant `M`. -/
structure IsBoundedLinearMap (𝕜 : Type*) [NormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E → F) extends
  IsLinearMap 𝕜 f : Prop where
  bound : ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖
#align is_bounded_linear_map IsBoundedLinearMap

theorem IsLinearMap.with_bound {f : E → F} (hf : IsLinearMap 𝕜 f) (M : ℝ)
    (h : ∀ x : E, ‖f x‖ ≤ M * ‖x‖) : IsBoundedLinearMap 𝕜 f :=
  ⟨hf,
    by_cases
      (fun (this : M ≤ 0) =>
        ⟨1, zero_lt_one, fun x =>
          (h x).trans <| mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
      fun (this : ¬M ≤ 0) => ⟨M, lt_of_not_ge this, h⟩⟩
#align is_linear_map.with_bound IsLinearMap.with_bound

/-- A continuous linear map satisfies `IsBoundedLinearMap` -/
theorem ContinuousLinearMap.isBoundedLinearMap (f : E →L[𝕜] F) : IsBoundedLinearMap 𝕜 f :=
  { f.toLinearMap.isLinear with bound := f.bound }
#align continuous_linear_map.is_bounded_linear_map ContinuousLinearMap.isBoundedLinearMap

namespace IsBoundedLinearMap

/-- Construct a linear map from a function `f` satisfying `IsBoundedLinearMap 𝕜 f`. -/
def toLinearMap (f : E → F) (h : IsBoundedLinearMap 𝕜 f) : E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.toIsLinearMap
#align is_bounded_linear_map.to_linear_map IsBoundedLinearMap.toLinearMap

/-- Construct a continuous linear map from `IsBoundedLinearMap`. -/
def toContinuousLinearMap {f : E → F} (hf : IsBoundedLinearMap 𝕜 f) : E →L[𝕜] F :=
  { toLinearMap f hf with
    cont :=
      let ⟨C, _, hC⟩ := hf.bound
      AddMonoidHomClass.continuous_of_bound (toLinearMap f hf) C hC }
#align is_bounded_linear_map.to_continuous_linear_map IsBoundedLinearMap.toContinuousLinearMap

theorem zero : IsBoundedLinearMap 𝕜 fun _ : E => (0 : F) :=
  (0 : E →ₗ[𝕜] F).isLinear.with_bound 0 <| by simp [le_refl]
#align is_bounded_linear_map.zero IsBoundedLinearMap.zero

theorem id : IsBoundedLinearMap 𝕜 fun x : E => x :=
  LinearMap.id.isLinear.with_bound 1 <| by simp [le_refl]
#align is_bounded_linear_map.id IsBoundedLinearMap.id

theorem fst : IsBoundedLinearMap 𝕜 fun x : E × F => x.1 := by
  refine (LinearMap.fst 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_left _ _
#align is_bounded_linear_map.fst IsBoundedLinearMap.fst

theorem snd : IsBoundedLinearMap 𝕜 fun x : E × F => x.2 := by
  refine (LinearMap.snd 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_right _ _
#align is_bounded_linear_map.snd IsBoundedLinearMap.snd

variable {f g : E → F}

theorem smul (c : 𝕜) (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 (c • f) :=
  let ⟨hlf, M, _, hM⟩ := hf
  (c • hlf.mk' f).isLinear.with_bound (‖c‖ * M) fun x =>
    calc
      ‖c • f x‖ = ‖c‖ * ‖f x‖ := norm_smul c (f x)
      _ ≤ ‖c‖ * (M * ‖x‖) := mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ = ‖c‖ * M * ‖x‖ := (mul_assoc _ _ _).symm

#align is_bounded_linear_map.smul IsBoundedLinearMap.smul

theorem neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 fun e => -f e := by
  rw [show (fun e => -f e) = fun e => (-1 : 𝕜) • f e by funext; simp]
  exact smul (-1) hf
#align is_bounded_linear_map.neg IsBoundedLinearMap.neg

theorem add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e + g e :=
  let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
  (hlf.mk' _ + hlg.mk' _).isLinear.with_bound (Mf + Mg) fun x =>
    calc
      ‖f x + g x‖ ≤ Mf * ‖x‖ + Mg * ‖x‖ := norm_add_le_of_le (hMf x) (hMg x)
      _ ≤ (Mf + Mg) * ‖x‖ := by rw [add_mul]

#align is_bounded_linear_map.add IsBoundedLinearMap.add

theorem sub (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e - g e := by simpa [sub_eq_add_neg] using add hf (neg hg)
#align is_bounded_linear_map.sub IsBoundedLinearMap.sub

theorem comp {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 (g ∘ f) :=
  (hg.toContinuousLinearMap.comp hf.toContinuousLinearMap).isBoundedLinearMap
#align is_bounded_linear_map.comp IsBoundedLinearMap.comp

protected theorem tendsto (x : E) (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  let ⟨hf, M, _, hM⟩ := hf
  tendsto_iff_norm_sub_tendsto_zero.2 <|
    squeeze_zero (fun e => norm_nonneg _)
      (fun e =>
        calc
          ‖f e - f x‖ = ‖hf.mk' f (e - x)‖ := by rw [(hf.mk' _).map_sub e x]; rfl
          _ ≤ M * ‖e - x‖ := hM (e - x)
          )
      (suffices Tendsto (fun e : E => M * ‖e - x‖) (𝓝 x) (𝓝 (M * 0)) by simpa
      tendsto_const_nhds.mul (tendsto_norm_sub_self _))
#align is_bounded_linear_map.tendsto IsBoundedLinearMap.tendsto

theorem continuous (hf : IsBoundedLinearMap 𝕜 f) : Continuous f :=
  continuous_iff_continuousAt.2 fun _ => hf.tendsto _
#align is_bounded_linear_map.continuous IsBoundedLinearMap.continuous

theorem lim_zero_bounded_linear_map (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 0) (𝓝 0) :=
  (hf.1.mk' _).map_zero ▸ continuous_iff_continuousAt.1 hf.continuous 0
#align is_bounded_linear_map.lim_zero_bounded_linear_map IsBoundedLinearMap.lim_zero_bounded_linear_map

section

open Asymptotics Filter

theorem isBigO_id {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) : f =O[l] fun x => x :=
  let ⟨_, _, hM⟩ := h.bound
  IsBigO.of_bound _ (mem_of_superset univ_mem fun x _ => hM x)
set_option linter.uppercaseLean3 false in
#align is_bounded_linear_map.is_O_id IsBoundedLinearMap.isBigO_id

theorem isBigO_comp {E : Type*} {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) {f : E → F}
    (l : Filter E) : (fun x' => g (f x')) =O[l] f :=
  (hg.isBigO_id ⊤).comp_tendsto le_top
set_option linter.uppercaseLean3 false in
#align is_bounded_linear_map.is_O_comp IsBoundedLinearMap.isBigO_comp

theorem isBigO_sub {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  isBigO_comp h l
set_option linter.uppercaseLean3 false in
#align is_bounded_linear_map.is_O_sub IsBoundedLinearMap.isBigO_sub

end

end IsBoundedLinearMap

section

variable {ι : Type*} [Fintype ι]

/-- Taking the cartesian product of two continuous multilinear maps is a bounded linear
operation. -/
theorem isBoundedLinearMap_prod_multilinear {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedLinearMap 𝕜 fun p : ContinuousMultilinearMap 𝕜 E F × ContinuousMultilinearMap 𝕜 E G =>
      p.1.prod p.2 where
  map_add p₁ p₂ := by ext : 1; rfl
  map_smul c p := by ext : 1; rfl
  bound := by
    refine ⟨1, zero_lt_one, fun p ↦ ?_⟩
    rw [one_mul]
    apply ContinuousMultilinearMap.opNorm_le_bound _ (norm_nonneg _) _
    intro m
    rw [ContinuousMultilinearMap.prod_apply, norm_prod_le_iff]
    constructor
    · exact (p.1.le_opNorm m).trans (mul_le_mul_of_nonneg_right (norm_fst_le p) <| by positivity)
    · exact (p.2.le_opNorm m).trans (mul_le_mul_of_nonneg_right (norm_snd_le p) <| by positivity)
#align is_bounded_linear_map_prod_multilinear isBoundedLinearMap_prod_multilinear

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
theorem isBoundedLinearMap_continuousMultilinearMap_comp_linear (g : G →L[𝕜] E) :
    IsBoundedLinearMap 𝕜 fun f : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F =>
      f.compContinuousLinearMap fun _ => g := by
  refine
    IsLinearMap.with_bound
      ⟨fun f₁ f₂ => by ext; rfl,
        fun c f => by ext; rfl⟩
      (‖g‖ ^ Fintype.card ι) fun f => ?_
  apply ContinuousMultilinearMap.opNorm_le_bound _ _ _
  · apply_rules [mul_nonneg, pow_nonneg, norm_nonneg]
  intro m
  calc
    ‖f (g ∘ m)‖ ≤ ‖f‖ * ∏ i, ‖g (m i)‖ := f.le_opNorm _
    _ ≤ ‖f‖ * ∏ i, ‖g‖ * ‖m i‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => g.le_opNorm _
    _ = ‖g‖ ^ Fintype.card ι * ‖f‖ * ∏ i, ‖m i‖ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      ring

#align is_bounded_linear_map_continuous_multilinear_map_comp_linear isBoundedLinearMap_continuousMultilinearMap_comp_linear

end

section BilinearMap

namespace ContinuousLinearMap

/-! We prove some computation rules for continuous (semi-)bilinear maps in their first argument.
  If `f` is a continuous bilinear map, to use the corresponding rules for the second argument, use
  `(f _).map_add` and similar.

We have to assume that `F` and `G` are normed spaces in this section, to use
`ContinuousLinearMap.toNormedAddCommGroup`, but we don't need to assume this for the first
argument of `f`.
-/


variable {R : Type*}
variable {𝕜₂ 𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜₂]
variable {M : Type*} [TopologicalSpace M]
variable {σ₁₂ : 𝕜 →+* 𝕜₂}
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜₂ G'] [NormedSpace 𝕜' G']
variable [SMulCommClass 𝕜₂ 𝕜' G']

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] {ρ₁₂ : R →+* 𝕜'}

theorem map_add₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x x' : M) (y : F) :
    f (x + x') y = f x y + f x' y := by rw [f.map_add, add_apply]
#align continuous_linear_map.map_add₂ ContinuousLinearMap.map_add₂

theorem map_zero₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (y : F) : f 0 y = 0 := by
  rw [f.map_zero, zero_apply]
#align continuous_linear_map.map_zero₂ ContinuousLinearMap.map_zero₂

theorem map_smulₛₗ₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (c : R) (x : M) (y : F) :
    f (c • x) y = ρ₁₂ c • f x y := by rw [f.map_smulₛₗ, smul_apply]
#align continuous_linear_map.map_smulₛₗ₂ ContinuousLinearMap.map_smulₛₗ₂

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] {ρ₁₂ : R →+* 𝕜'}

theorem map_sub₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x x' : M) (y : F) :
    f (x - x') y = f x y - f x' y := by rw [f.map_sub, sub_apply]
#align continuous_linear_map.map_sub₂ ContinuousLinearMap.map_sub₂

theorem map_neg₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x : M) (y : F) : f (-x) y = -f x y := by
  rw [f.map_neg, neg_apply]
#align continuous_linear_map.map_neg₂ ContinuousLinearMap.map_neg₂

end Ring

theorem map_smul₂ (f : E →L[𝕜] F →L[𝕜] G) (c : 𝕜) (x : E) (y : F) : f (c • x) y = c • f x y := by
  rw [f.map_smul, smul_apply]
#align continuous_linear_map.map_smul₂ ContinuousLinearMap.map_smul₂

end ContinuousLinearMap

variable (𝕜)

/-- A map `f : E × F → G` satisfies `IsBoundedBilinearMap 𝕜 f` if it is bilinear and
continuous. -/
structure IsBoundedBilinearMap (f : E × F → G) : Prop where
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
  smul_left : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
  add_right : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
  smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
  bound : ∃ C > 0, ∀ (x : E) (y : F), ‖f (x, y)‖ ≤ C * ‖x‖ * ‖y‖
#align is_bounded_bilinear_map IsBoundedBilinearMap

variable {𝕜}
variable {f : E × F → G}

theorem ContinuousLinearMap.isBoundedBilinearMap (f : E →L[𝕜] F →L[𝕜] G) :
    IsBoundedBilinearMap 𝕜 fun x : E × F => f x.1 x.2 :=
  { add_left := f.map_add₂
    smul_left := f.map_smul₂
    add_right := fun x => (f x).map_add
    smul_right := fun c x => (f x).map_smul c
    bound :=
      ⟨max ‖f‖ 1, zero_lt_one.trans_le (le_max_right _ _), fun x y =>
        (f.le_opNorm₂ x y).trans <| by
          apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, le_max_left] ⟩ }
#align continuous_linear_map.is_bounded_bilinear_map ContinuousLinearMap.isBoundedBilinearMap

-- Porting note (#11445): new definition
/-- A bounded bilinear map `f : E × F → G` defines a continuous linear map
`f : E →L[𝕜] F →L[𝕜] G`. -/
def IsBoundedBilinearMap.toContinuousLinearMap (hf : IsBoundedBilinearMap 𝕜 f) :
    E →L[𝕜] F →L[𝕜] G :=
  LinearMap.mkContinuousOfExistsBound₂
    (LinearMap.mk₂ _ f.curry hf.add_left hf.smul_left hf.add_right hf.smul_right) <|
    hf.bound.imp fun _ ↦ And.right

protected theorem IsBoundedBilinearMap.isBigO (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p.1‖ * ‖p.2‖ :=
  let ⟨C, Cpos, hC⟩ := h.bound
  Asymptotics.IsBigO.of_bound _ <|
    Filter.eventually_of_forall fun ⟨x, y⟩ => by simpa [mul_assoc] using hC x y
set_option linter.uppercaseLean3 false in
#align is_bounded_bilinear_map.is_O IsBoundedBilinearMap.isBigO

theorem IsBoundedBilinearMap.isBigO_comp {α : Type*} (H : IsBoundedBilinearMap 𝕜 f) {g : α → E}
    {h : α → F} {l : Filter α} : (fun x => f (g x, h x)) =O[l] fun x => ‖g x‖ * ‖h x‖ :=
  H.isBigO.comp_tendsto le_top
set_option linter.uppercaseLean3 false in
#align is_bounded_bilinear_map.is_O_comp IsBoundedBilinearMap.isBigO_comp

protected theorem IsBoundedBilinearMap.isBigO' (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p‖ * ‖p‖ :=
  h.isBigO.trans <|
    (@Asymptotics.isBigO_fst_prod' _ E F _ _ _ _).norm_norm.mul
      (@Asymptotics.isBigO_snd_prod' _ E F _ _ _ _).norm_norm
set_option linter.uppercaseLean3 false in
#align is_bounded_bilinear_map.is_O' IsBoundedBilinearMap.isBigO'

theorem IsBoundedBilinearMap.map_sub_left (h : IsBoundedBilinearMap 𝕜 f) {x y : E} {z : F} :
    f (x - y, z) = f (x, z) - f (y, z) :=
  (h.toContinuousLinearMap.flip z).map_sub x y
#align is_bounded_bilinear_map.map_sub_left IsBoundedBilinearMap.map_sub_left

theorem IsBoundedBilinearMap.map_sub_right (h : IsBoundedBilinearMap 𝕜 f) {x : E} {y z : F} :
    f (x, y - z) = f (x, y) - f (x, z) :=
  (h.toContinuousLinearMap x).map_sub y z
#align is_bounded_bilinear_map.map_sub_right IsBoundedBilinearMap.map_sub_right

open Asymptotics in
/-- Useful to use together with `Continuous.comp₂`. -/
theorem IsBoundedBilinearMap.continuous (h : IsBoundedBilinearMap 𝕜 f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x ↦ tendsto_sub_nhds_zero_iff.1 ?_
  suffices Tendsto (fun y : E × F ↦ f (y.1 - x.1, y.2) + f (x.1, y.2 - x.2)) (𝓝 x) (𝓝 (0 + 0)) by
    simpa only [h.map_sub_left, h.map_sub_right, sub_add_sub_cancel, zero_add] using this
  apply Tendsto.add
  · rw [← isLittleO_one_iff ℝ, ← one_mul 1]
    refine h.isBigO_comp.trans_isLittleO ?_
    refine (IsLittleO.norm_left ?_).mul_isBigO (IsBigO.norm_left ?_)
    · exact (isLittleO_one_iff _).2 (tendsto_sub_nhds_zero_iff.2 (continuous_fst.tendsto _))
    · exact (continuous_snd.tendsto _).isBigO_one ℝ
  · refine Continuous.tendsto' ?_ _ _ (by rw [h.map_sub_right, sub_self])
    exact ((h.toContinuousLinearMap x.1).continuous).comp (continuous_snd.sub continuous_const)
#align is_bounded_bilinear_map.continuous IsBoundedBilinearMap.continuous

theorem IsBoundedBilinearMap.continuous_left (h : IsBoundedBilinearMap 𝕜 f) {e₂ : F} :
    Continuous fun e₁ => f (e₁, e₂) :=
  h.continuous.comp (continuous_id.prod_mk continuous_const)
#align is_bounded_bilinear_map.continuous_left IsBoundedBilinearMap.continuous_left

theorem IsBoundedBilinearMap.continuous_right (h : IsBoundedBilinearMap 𝕜 f) {e₁ : E} :
    Continuous fun e₂ => f (e₁, e₂) :=
  h.continuous.comp (continuous_const.prod_mk continuous_id)
#align is_bounded_bilinear_map.continuous_right IsBoundedBilinearMap.continuous_right

/-- Useful to use together with `Continuous.comp₂`. -/
theorem ContinuousLinearMap.continuous₂ (f : E →L[𝕜] F →L[𝕜] G) :
    Continuous (Function.uncurry fun x y => f x y) :=
  f.isBoundedBilinearMap.continuous
#align continuous_linear_map.continuous₂ ContinuousLinearMap.continuous₂

theorem IsBoundedBilinearMap.isBoundedLinearMap_left (h : IsBoundedBilinearMap 𝕜 f) (y : F) :
    IsBoundedLinearMap 𝕜 fun x => f (x, y) :=
  (h.toContinuousLinearMap.flip y).isBoundedLinearMap
#align is_bounded_bilinear_map.is_bounded_linear_map_left IsBoundedBilinearMap.isBoundedLinearMap_left

theorem IsBoundedBilinearMap.isBoundedLinearMap_right (h : IsBoundedBilinearMap 𝕜 f) (x : E) :
    IsBoundedLinearMap 𝕜 fun y => f (x, y) :=
  (h.toContinuousLinearMap x).isBoundedLinearMap
#align is_bounded_bilinear_map.is_bounded_linear_map_right IsBoundedBilinearMap.isBoundedLinearMap_right

theorem isBoundedBilinearMap_smul {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    IsBoundedBilinearMap 𝕜 fun p : 𝕜' × E => p.1 • p.2 :=
  (lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E).isBoundedBilinearMap
#align is_bounded_bilinear_map_smul isBoundedBilinearMap_smul

theorem isBoundedBilinearMap_mul : IsBoundedBilinearMap 𝕜 fun p : 𝕜 × 𝕜 => p.1 * p.2 := by
  simp_rw [← smul_eq_mul]
  exact isBoundedBilinearMap_smul
#align is_bounded_bilinear_map_mul isBoundedBilinearMap_mul

theorem isBoundedBilinearMap_comp :
    IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × (E →L[𝕜] F) => p.1.comp p.2 :=
  (compL 𝕜 E F G).isBoundedBilinearMap
#align is_bounded_bilinear_map_comp isBoundedBilinearMap_comp

theorem ContinuousLinearMap.isBoundedLinearMap_comp_left (g : F →L[𝕜] G) :
    IsBoundedLinearMap 𝕜 fun f : E →L[𝕜] F => ContinuousLinearMap.comp g f :=
  isBoundedBilinearMap_comp.isBoundedLinearMap_right _
#align continuous_linear_map.is_bounded_linear_map_comp_left ContinuousLinearMap.isBoundedLinearMap_comp_left

theorem ContinuousLinearMap.isBoundedLinearMap_comp_right (f : E →L[𝕜] F) :
    IsBoundedLinearMap 𝕜 fun g : F →L[𝕜] G => ContinuousLinearMap.comp g f :=
  isBoundedBilinearMap_comp.isBoundedLinearMap_left _
#align continuous_linear_map.is_bounded_linear_map_comp_right ContinuousLinearMap.isBoundedLinearMap_comp_right

theorem isBoundedBilinearMap_apply : IsBoundedBilinearMap 𝕜 fun p : (E →L[𝕜] F) × E => p.1 p.2 :=
  (ContinuousLinearMap.flip (apply 𝕜 F : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F)).isBoundedBilinearMap
#align is_bounded_bilinear_map_apply isBoundedBilinearMap_apply

/-- The function `ContinuousLinearMap.smulRight`, associating to a continuous linear map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
theorem isBoundedBilinearMap_smulRight :
    IsBoundedBilinearMap 𝕜 fun p =>
      (ContinuousLinearMap.smulRight : (E →L[𝕜] 𝕜) → F → E →L[𝕜] F) p.1 p.2 :=
  (smulRightL 𝕜 E F).isBoundedBilinearMap
#align is_bounded_bilinear_map_smul_right isBoundedBilinearMap_smulRight

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
theorem isBoundedBilinearMap_compMultilinear {ι : Type*} {E : ι → Type*} [Fintype ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × ContinuousMultilinearMap 𝕜 E F =>
      p.1.compContinuousMultilinearMap p.2 :=
  (compContinuousMultilinearMapL 𝕜 E F G).isBoundedBilinearMap
#align is_bounded_bilinear_map_comp_multilinear isBoundedBilinearMap_compMultilinear

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here as a linear map `E × F →ₗ[𝕜] G`, then `IsBoundedBilinearMap.deriv`
strengthens it to a continuous linear map `E × F →L[𝕜] G`.
-/
def IsBoundedBilinearMap.linearDeriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →ₗ[𝕜] G :=
  (h.toContinuousLinearMap.deriv₂ p).toLinearMap
#align is_bounded_bilinear_map.linear_deriv IsBoundedBilinearMap.linearDeriv

/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. The statement that this is indeed the derivative of `f` is
`IsBoundedBilinearMap.hasFDerivAt` in `Analysis.Calculus.FDeriv`. -/
def IsBoundedBilinearMap.deriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →L[𝕜] G :=
  h.toContinuousLinearMap.deriv₂ p
#align is_bounded_bilinear_map.deriv IsBoundedBilinearMap.deriv

@[simp]
theorem IsBoundedBilinearMap.deriv_apply (h : IsBoundedBilinearMap 𝕜 f) (p q : E × F) :
    h.deriv p q = f (p.1, q.2) + f (q.1, p.2) :=
  rfl
#align is_bounded_bilinear_map_deriv_coe IsBoundedBilinearMap.deriv_apply

variable (𝕜)

/-- The function `ContinuousLinearMap.mulLeftRight : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded
bilinear map. -/
theorem ContinuousLinearMap.mulLeftRight_isBoundedBilinear (𝕜' : Type*) [NormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] :
    IsBoundedBilinearMap 𝕜 fun p : 𝕜' × 𝕜' => ContinuousLinearMap.mulLeftRight 𝕜 𝕜' p.1 p.2 :=
  (ContinuousLinearMap.mulLeftRight 𝕜 𝕜').isBoundedBilinearMap
#align continuous_linear_map.mul_left_right_is_bounded_bilinear ContinuousLinearMap.mulLeftRight_isBoundedBilinear

variable {𝕜}

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
theorem IsBoundedBilinearMap.isBoundedLinearMap_deriv (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 fun p : E × F => h.deriv p :=
  h.toContinuousLinearMap.deriv₂.isBoundedLinearMap
#align is_bounded_bilinear_map.is_bounded_linear_map_deriv IsBoundedBilinearMap.isBoundedLinearMap_deriv

end BilinearMap

@[continuity]
theorem Continuous.clm_comp {X} [TopologicalSpace X] {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    (hg : Continuous g) (hf : Continuous f) : Continuous fun x => (g x).comp (f x) :=
  (compL 𝕜 E F G).continuous₂.comp₂ hg hf
#align continuous.clm_comp Continuous.clm_comp

theorem ContinuousOn.clm_comp {X} [TopologicalSpace X] {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    {s : Set X} (hg : ContinuousOn g s) (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (g x).comp (f x)) s :=
  (compL 𝕜 E F G).continuous₂.comp_continuousOn (hg.prod hf)
#align continuous_on.clm_comp ContinuousOn.clm_comp

@[continuity]
theorem Continuous.clm_apply {X} [TopologicalSpace X] {f : X → (E →L[𝕜] F)} {g : X → E}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x ↦ (f x) (g x)) :=
  isBoundedBilinearMap_apply.continuous.comp₂ hf hg

theorem ContinuousOn.clm_apply {X} [TopologicalSpace X] {f : X → (E →L[𝕜] F)} {g : X → E}
    {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x ↦ f x (g x)) s :=
  isBoundedBilinearMap_apply.continuous.comp_continuousOn (hf.prod hg)

namespace ContinuousLinearEquiv

open Set

/-!
### The set of continuous linear equivalences between two Banach spaces is open

In this section we establish that the set of continuous linear equivalences between two Banach
spaces is an open subset of the space of linear maps between them.
-/

protected theorem isOpen [CompleteSpace E] : IsOpen (range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F)) := by
  rw [isOpen_iff_mem_nhds, forall_mem_range]
  refine fun e => IsOpen.mem_nhds ?_ (mem_range_self _)
  let O : (E →L[𝕜] F) → E →L[𝕜] E := fun f => (e.symm : F →L[𝕜] E).comp f
  have h_O : Continuous O := isBoundedBilinearMap_comp.continuous_right
  convert show IsOpen (O ⁻¹' { x | IsUnit x }) from Units.isOpen.preimage h_O using 1
  ext f'
  constructor
  · rintro ⟨e', rfl⟩
    exact ⟨(e'.trans e.symm).toUnit, rfl⟩
  · rintro ⟨w, hw⟩
    use (unitsEquiv 𝕜 E w).trans e
    ext x
    simp [O, hw]
#align continuous_linear_equiv.is_open ContinuousLinearEquiv.isOpen

protected theorem nhds [CompleteSpace E] (e : E ≃L[𝕜] F) :
    range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (e : E →L[𝕜] F) :=
  IsOpen.mem_nhds ContinuousLinearEquiv.isOpen (by simp)
#align continuous_linear_equiv.nhds ContinuousLinearEquiv.nhds

end ContinuousLinearEquiv
