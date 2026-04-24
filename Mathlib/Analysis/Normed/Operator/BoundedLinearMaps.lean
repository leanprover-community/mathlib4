/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Operator.Mul

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
The file `Mathlib/Analysis/NormedSpace/Multilinear/Basic.lean`
already expounds the theory of multilinear maps,
but the `2`-variables case is sufficiently simpler to currently deserve its own treatment.

`IsBoundedLinearMap` is effectively an unbundled version of `ContinuousLinearMap` (defined
in `Topology.Algebra.Module.Basic`, theory over normed spaces developed in
`Analysis.NormedSpace.OperatorNorm`), albeit the name disparity. A bundled
`ContinuousLinearMap` is to be preferred over an `IsBoundedLinearMap` hypothesis. Historical
artifact, really.
-/

@[expose] public section


noncomputable section

open Topology

open Filter (Tendsto)

open Metric ContinuousLinearMap

section Semiring

variable {𝕜 E F G : Type*} [Semiring 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E]
    [SeminormedAddCommGroup F] [Module 𝕜 F]
    [SeminormedAddCommGroup G] [Module 𝕜 G]
    {f g : E → F}

variable (𝕜 f) in
/-- A function `f` satisfies `IsBoundedLinearMap 𝕜 f` if it is linear and satisfies the
inequality `‖f x‖ ≤ M * ‖x‖` for some positive constant `M`.

(We put only the typeclasses strictly necessary for the definition, although the main case of
interest is when `𝕜` itself is a normed ring and `E, F` are normed modules.) -/
structure IsBoundedLinearMap : Prop
    extends IsLinearMap 𝕜 f where
  bound : ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖

lemma isBoundedLinearMap_iff {f : E → F} :
    IsBoundedLinearMap 𝕜 f ↔ IsLinearMap 𝕜 f ∧ ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖ :=
  ⟨fun hf ↦ ⟨hf.toIsLinearMap, hf.bound⟩, fun ⟨hl, hm⟩ ↦ ⟨hl, hm⟩⟩

theorem IsLinearMap.with_bound {f : E → F} (hf : IsLinearMap 𝕜 f) (M : ℝ)
    (h : ∀ x : E, ‖f x‖ ≤ M * ‖x‖) : IsBoundedLinearMap 𝕜 f :=
  ⟨hf,
    by_cases
      (fun (this : M ≤ 0) =>
        ⟨1, zero_lt_one, fun x =>
          (h x).trans <| mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
      fun (this : ¬M ≤ 0) => ⟨M, lt_of_not_ge this, h⟩⟩

namespace IsBoundedLinearMap

/-- Construct a linear map from a function `f` satisfying `IsBoundedLinearMap 𝕜 f`. -/
def toLinearMap (f : E → F) (h : IsBoundedLinearMap 𝕜 f) : E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.toIsLinearMap

/-- Construct a continuous linear map from `IsBoundedLinearMap`. -/
def toContinuousLinearMap (f : E → F) (hf : IsBoundedLinearMap 𝕜 f) : E →L[𝕜] F :=
  { toLinearMap f hf with
    cont :=
      let ⟨C, _, hC⟩ := hf.bound
      AddMonoidHomClass.continuous_of_bound (toLinearMap f hf) C hC }

theorem zero : IsBoundedLinearMap 𝕜 fun _ : E => (0 : F) :=
  (0 : E →ₗ[𝕜] F).isLinear.with_bound 0 <| by simp

theorem id : IsBoundedLinearMap 𝕜 fun x : E => x :=
  LinearMap.id.isLinear.with_bound 1 <| by simp

theorem fst : IsBoundedLinearMap 𝕜 fun x : E × F => x.1 := by
  refine (LinearMap.fst 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_left _ _

theorem snd : IsBoundedLinearMap 𝕜 fun x : E × F => x.2 := by
  refine (LinearMap.snd 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_right _ _

theorem smul {𝕜' : Type*} (c : 𝕜') [SeminormedRing 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
    [SMulCommClass 𝕜 𝕜' F] (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 (c • f) :=
  let ⟨hlf, M, _, hM⟩ := hf
  (c • hlf.mk' f).isLinear.with_bound (‖c‖ * M) fun x =>
    calc
      ‖c • f x‖ ≤ ‖c‖ * ‖f x‖ := norm_smul_le c (f x)
      _ ≤ ‖c‖ * (M * ‖x‖) := by grw [hM]
      _ = ‖c‖ * M * ‖x‖ := (mul_assoc _ _ _).symm

theorem neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 fun e => -f e :=
  ⟨(-hf.1.mk' _).isLinear, by simpa using hf.2⟩

theorem add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e + g e :=
  let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
  (hlf.mk' _ + hlg.mk' _).isLinear.with_bound (Mf + Mg) fun x =>
    calc
      ‖f x + g x‖ ≤ Mf * ‖x‖ + Mg * ‖x‖ := norm_add_le_of_le (hMf x) (hMg x)
      _ ≤ (Mf + Mg) * ‖x‖ := by rw [add_mul]

theorem sub (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e - g e := by simpa [sub_eq_add_neg] using add hf (neg hg)

theorem comp {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 (g ∘ f) :=
  let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
  (hg.1.mk' _).comp (hf.1.mk' _) |>.isLinear.with_bound (Mg * Mf) fun x ↦
    show ‖g (f x)‖ ≤ _ by grw [hMg, hMf, mul_assoc]

protected theorem tendsto (x : E) (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  hf.toContinuousLinearMap.continuous.tendsto x

theorem continuous (hf : IsBoundedLinearMap 𝕜 f) : Continuous f :=
  hf.toContinuousLinearMap.continuous

theorem lim_zero_bounded_linear_map (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 0) (𝓝 0) :=
  (hf.1.mk' _).map_zero ▸ hf.tendsto 0

section

open Asymptotics Filter

theorem isBigO_id (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) : f =O[l] fun x => x :=
  let ⟨_, _, hM⟩ := h.bound
  IsBigO.of_bound _ (mem_of_superset univ_mem fun x _ => hM x)

theorem isBigO_comp {E : Type*} {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) {f : E → F}
    (l : Filter E) : (fun x' => g (f x')) =O[l] f :=
  (hg.isBigO_id ⊤).comp_tendsto le_top

theorem isBigO_sub {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  isBigO_comp h l

end

end IsBoundedLinearMap

variable (𝕜) in
/-- A map `f : E × F → G` satisfies `IsBoundedBilinearMap 𝕜 f` if it is bilinear and
continuous. -/
structure IsBoundedBilinearMap (f : E × F → G) : Prop where
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
  smul_left : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
  add_right : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
  smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
  bound : ∃ C > 0, ∀ (x : E) (y : F), ‖f (x, y)‖ ≤ C * ‖x‖ * ‖y‖

namespace IsBoundedBilinearMap

variable {f : E × F → G}

lemma symm (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedBilinearMap 𝕜 (fun p ↦ f (p.2, p.1)) where
  add_left x₁ x₂ y := h.add_right _ _ _
  smul_left c x y := h.smul_right _ _ _
  add_right x y₁ y₂ := h.add_left _ _ _
  smul_right c x y := h.smul_left _ _ _
  bound := by
    obtain ⟨C, hC_pos, hC⟩ := h.bound
    exact ⟨C, hC_pos, fun x y ↦ (hC y x).trans_eq (by ring)⟩

lemma isBoundedLinearMap_right (h : IsBoundedBilinearMap 𝕜 f) (x : E) :
    IsBoundedLinearMap 𝕜 (fun y ↦ f (x, y)) where
  map_add := h.add_right x
  map_smul := (h.smul_right · x ·)
  bound := by
    let ⟨C, hC_pos, hC⟩ := h.bound
    -- Using `C * ‖x‖` is tempting but `x` might be 0 and the constant must be positive!
    refine ⟨C * max ‖x‖ 1, by positivity, fun y ↦ (hC x y).trans ?_⟩
    rcases max_cases ‖x‖ 1 with hx | hx
    · grw [hx.1]
    · grw [hx.1, hx.2.le]

lemma isBoundedLinearMap_left (h : IsBoundedBilinearMap 𝕜 f) (y : F) :
    IsBoundedLinearMap 𝕜 (fun x ↦ f (x, y)) :=
  h.symm.isBoundedLinearMap_right y

theorem map_sub_left (h : IsBoundedBilinearMap 𝕜 f) {x y : E} {z : F} :
    f (x - y, z) = f (x, z) - f (y, z) :=
  (h.isBoundedLinearMap_left z).map_sub x y

theorem map_sub_right (h : IsBoundedBilinearMap 𝕜 f) {x : E} {y z : F} :
    f (x, y - z) = f (x, y) - f (x, z) :=
  (h.isBoundedLinearMap_right x).map_sub y z

protected theorem isBigO (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p.1‖ * ‖p.2‖ :=
  let ⟨C, _, hC⟩ := h.bound
  Asymptotics.IsBigO.of_bound C <|
    Filter.Eventually.of_forall fun ⟨x, y⟩ => by simpa [mul_assoc] using hC x y

theorem isBigO_comp {α : Type*} (H : IsBoundedBilinearMap 𝕜 f) {g : α → E}
    {h : α → F} {l : Filter α} : (fun x => f (g x, h x)) =O[l] fun x => ‖g x‖ * ‖h x‖ :=
  H.isBigO.comp_tendsto le_top

protected theorem isBigO' (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p‖ * ‖p‖ :=
  h.isBigO.trans <|
    (@Asymptotics.isBigO_fst_prod' _ E F _ _ _ _).norm_norm.mul
      (@Asymptotics.isBigO_snd_prod' _ E F _ _ _ _).norm_norm

open Asymptotics in
/-- Useful to use together with `Continuous.comp₂`. -/
theorem continuous (h : IsBoundedBilinearMap 𝕜 f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x ↦ tendsto_sub_nhds_zero_iff.1 ?_
  suffices Tendsto (fun y : E × F ↦ f (y.1 - x.1, y.2) + f (x.1, y.2 - x.2)) (𝓝 x) (𝓝 (0 + 0)) by
    simpa only [h.map_sub_left, h.map_sub_right, sub_add_sub_cancel, zero_add] using this
  apply Tendsto.add
  · rw [← isLittleO_one_iff ℝ, ← one_mul 1]
    refine h.isBigO_comp.trans_isLittleO ?_
    refine (IsLittleO.norm_left ?_).mul_isBigO (IsBigO.norm_left ?_)
    · exact (isLittleO_one_iff _).2 (tendsto_sub_nhds_zero_iff.2 (continuous_fst.tendsto _))
    · exact (continuous_snd.tendsto _).isBigO_one ℝ
  · rw [← isLittleO_one_iff ℝ]
    refine h.isBigO_comp.trans_isLittleO ?_
    apply IsLittleO.const_mul_left
    rw [isLittleO_norm_left, isLittleO_one_iff, ← sub_self x.2]
    exact continuous_snd.continuousAt.sub tendsto_const_nhds

theorem continuous_left (h : IsBoundedBilinearMap 𝕜 f) {e₂ : F} :
    Continuous fun e₁ => f (e₁, e₂) :=
  h.continuous.comp (by fun_prop)

theorem continuous_right (h : IsBoundedBilinearMap 𝕜 f) {e₁ : E} :
    Continuous fun e₂ => f (e₁, e₂) :=
  h.continuous.comp (by fun_prop)

end IsBoundedBilinearMap

end Semiring

section CommSemiring

variable {𝕜 A : Type*} [CommSemiring 𝕜] [SeminormedRing A] [Algebra 𝕜 A]

/-- Scalar multiplication (for a normed `𝕜`-algebra acting on a normed `𝕜`-module) as a bounded
bilinear map. -/
theorem isBoundedBilinearMap_smul {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E]
    [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] :
    IsBoundedBilinearMap 𝕜 fun p : A × E ↦ p.1 • p.2 where
  add_left := add_smul
  add_right := smul_add
  smul_left := smul_assoc
  smul_right c x := smul_comm x c
  bound := ⟨1, one_pos, fun x y ↦ by grw [one_mul, norm_smul_le]⟩

/-- Multiplication in a normed `𝕜`-algebra as a bounded bilinear map. -/
theorem isBoundedBilinearMap_mul :
    IsBoundedBilinearMap 𝕜 fun p : A × A ↦ p.1 * p.2 :=
  isBoundedBilinearMap_smul

end CommSemiring

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A continuous linear map satisfies `IsBoundedLinearMap` -/
theorem ContinuousLinearMap.isBoundedLinearMap (f : E →L[𝕜] F) : IsBoundedLinearMap 𝕜 f :=
  { f.toLinearMap.isLinear with bound := f.bound }

namespace IsBoundedLinearMap

variable {f g : E → F}

/-- A map between normed spaces is linear and continuous if and only if it is bounded. -/
theorem isLinearMap_and_continuous_iff_isBoundedLinearMap (f : E → F) :
    IsLinearMap 𝕜 f ∧ Continuous f ↔ IsBoundedLinearMap 𝕜 f where
  mp | ⟨hlin, hcont⟩ => ContinuousLinearMap.isBoundedLinearMap ⟨hlin.mk' _, hcont⟩
  mpr h_bdd := ⟨h_bdd.toIsLinearMap, h_bdd.continuous⟩

end IsBoundedLinearMap

section

variable {ι : Type*} [Fintype ι]

/-- Taking the Cartesian product of two continuous multilinear maps is a bounded linear
operation. -/
theorem isBoundedLinearMap_prod_multilinear {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedLinearMap 𝕜 fun p : ContinuousMultilinearMap 𝕜 E F × ContinuousMultilinearMap 𝕜 E G =>
      p.1.prod p.2 :=
  (ContinuousMultilinearMap.prodL 𝕜 E F G).toContinuousLinearEquiv
    |>.toContinuousLinearMap.isBoundedLinearMap

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
theorem isBoundedLinearMap_continuousMultilinearMap_comp_linear (g : G →L[𝕜] E) :
    IsBoundedLinearMap 𝕜 fun f : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F =>
      f.compContinuousLinearMap fun _ => g :=
  (ContinuousMultilinearMap.compContinuousLinearMapL (ι := ι) (F := F) (fun _ ↦ g))
    |>.isBoundedLinearMap

end

section BilinearMap

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
          gcongr; apply le_max_left ⟩ }

/-- A bounded bilinear map `f : E × F → G` defines a continuous linear map
`f : E →L[𝕜] F →L[𝕜] G`. -/
def IsBoundedBilinearMap.toContinuousLinearMap (hf : IsBoundedBilinearMap 𝕜 f) :
    E →L[𝕜] F →L[𝕜] G :=
  LinearMap.mkContinuousOfExistsBound₂
    (LinearMap.mk₂ _ f.curry hf.add_left hf.smul_left hf.add_right hf.smul_right) <|
    hf.bound.imp fun _ ↦ And.right

@[simp]
lemma IsBoundedBilinearMap.toContinuousLinearMap_apply (hf : IsBoundedBilinearMap 𝕜 f)
    (x : E) (y : F) : hf.toContinuousLinearMap x y = f (x, y) := rfl

/-- Useful to use together with `Continuous.comp₂`. -/
theorem ContinuousLinearMap.continuous₂ (f : E →L[𝕜] F →L[𝕜] G) :
    Continuous (Function.uncurry fun x y => f x y) :=
  f.isBoundedBilinearMap.continuous

theorem isBoundedBilinearMap_comp :
    IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × (E →L[𝕜] F) => p.1.comp p.2 :=
  (compL 𝕜 E F G).isBoundedBilinearMap

theorem ContinuousLinearMap.isBoundedLinearMap_comp_left (g : F →L[𝕜] G) :
    IsBoundedLinearMap 𝕜 fun f : E →L[𝕜] F => ContinuousLinearMap.comp g f :=
  isBoundedBilinearMap_comp.isBoundedLinearMap_right g

theorem ContinuousLinearMap.isBoundedLinearMap_comp_right (f : E →L[𝕜] F) :
    IsBoundedLinearMap 𝕜 fun g : F →L[𝕜] G => ContinuousLinearMap.comp g f :=
  (isBoundedBilinearMap_comp (G := G)).isBoundedLinearMap_left f

theorem isBoundedBilinearMap_apply : IsBoundedBilinearMap 𝕜 fun p : (E →L[𝕜] F) × E => p.1 p.2 :=
  (ContinuousLinearMap.flip (apply 𝕜 F : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F)).isBoundedBilinearMap

/-- The function `ContinuousLinearMap.smulRight`, associating to a continuous linear map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
theorem isBoundedBilinearMap_smulRight :
    IsBoundedBilinearMap 𝕜 fun p =>
      (ContinuousLinearMap.smulRight : StrongDual 𝕜 E → F → E →L[𝕜] F) p.1 p.2 :=
  (smulRightL 𝕜 E F).isBoundedBilinearMap

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
theorem isBoundedBilinearMap_compMultilinear {ι : Type*} {E : ι → Type*} [Fintype ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × ContinuousMultilinearMap 𝕜 E F =>
      p.1.compContinuousMultilinearMap p.2 :=
  (compContinuousMultilinearMapL 𝕜 E F G).isBoundedBilinearMap

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here as a linear map `E × F →ₗ[𝕜] G`, then `IsBoundedBilinearMap.deriv`
strengthens it to a continuous linear map `E × F →L[𝕜] G`.
-/
def IsBoundedBilinearMap.linearDeriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →ₗ[𝕜] G :=
  (h.toContinuousLinearMap.deriv₂ p).toLinearMap

/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. The statement that this is indeed the derivative of `f` is
`IsBoundedBilinearMap.hasFDerivAt` in `Analysis.Calculus.FDeriv`. -/
def IsBoundedBilinearMap.deriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →L[𝕜] G :=
  h.toContinuousLinearMap.deriv₂ p

@[simp]
theorem IsBoundedBilinearMap.deriv_apply (h : IsBoundedBilinearMap 𝕜 f) (p q : E × F) :
    h.deriv p q = f (p.1, q.2) + f (q.1, p.2) :=
  rfl

variable (𝕜) in
/-- The function `ContinuousLinearMap.mulLeftRight : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded
bilinear map. -/
theorem ContinuousLinearMap.mulLeftRight_isBoundedBilinear (𝕜' : Type*) [SeminormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] :
    IsBoundedBilinearMap 𝕜 fun p : 𝕜' × 𝕜' => ContinuousLinearMap.mulLeftRight 𝕜 𝕜' p.1 p.2 :=
  (ContinuousLinearMap.mulLeftRight 𝕜 𝕜').isBoundedBilinearMap

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
theorem IsBoundedBilinearMap.isBoundedLinearMap_deriv (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 fun p : E × F => h.deriv p :=
  h.toContinuousLinearMap.deriv₂.isBoundedLinearMap

end BilinearMap

variable {X : Type*} [TopologicalSpace X]

@[continuity, fun_prop]
theorem Continuous.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    (hg : Continuous g) (hf : Continuous f) : Continuous fun x => (g x).comp (f x) :=
  (compL 𝕜 E F G).continuous₂.comp₂ hg hf

@[fun_prop]
theorem ContinuousOn.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    {s : Set X} (hg : ContinuousOn g s) (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (g x).comp (f x)) s :=
  (compL 𝕜 E F G).continuous₂.comp_continuousOn (hg.prodMk hf)

@[fun_prop]
theorem ContinuousAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    {x : X} (hg : ContinuousAt g x) (hf : ContinuousAt f x) :
    ContinuousAt (fun x => (g x).comp (f x)) x :=
  (compL 𝕜 E F G).continuous₂.continuousAt.comp (hg.prodMk hf)

@[fun_prop]
theorem ContinuousWithinAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    {s : Set X} {x : X} (hg : ContinuousWithinAt g s x) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (g x).comp (f x)) s x :=
  (compL 𝕜 E F G).continuous₂.continuousAt.comp_continuousWithinAt (hg.prodMk hf)

@[continuity, fun_prop]
theorem Continuous.clm_apply {f : X → E →L[𝕜] F} {g : X → E}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x ↦ f x (g x)) :=
  isBoundedBilinearMap_apply.continuous.comp₂ hf hg

@[fun_prop]
theorem ContinuousOn.clm_apply {f : X → E →L[𝕜] F} {g : X → E}
    {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x ↦ f x (g x)) s :=
  (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.comp_continuousOn (hf.prodMk hg)

@[continuity, fun_prop]
theorem ContinuousAt.clm_apply {X} [TopologicalSpace X] {f : X → E →L[𝕜] F} {g : X → E} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x ↦ f x (g x)) x :=
  isBoundedBilinearMap_apply.continuous.continuousAt.comp₂ hf hg

@[continuity, fun_prop]
theorem ContinuousWithinAt.clm_apply {X} [TopologicalSpace X] {f : X → E →L[𝕜] F} {g : X → E}
    {s : Set X} {x : X} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x ↦ f x (g x)) s x :=
  (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.continuousAt.comp_continuousWithinAt
    (hf.prodMk hg)

@[fun_prop]
theorem ContinuousWithinAt.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {s : Set X} {x : X}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => (f x).coprod (g x)) s x := by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]
theorem ContinuousAt.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => (f x).coprod (g x)) x := by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]
theorem ContinuousOn.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).coprod (g x)) s := by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]
theorem Continuous.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (f x).coprod (g x)) := by
  apply continuousOn_univ.mp
  fun_prop

theorem ContinuousWithinAt.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {s : Set X} {x : X}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun y => (f y).coprod (g y)) s x := by
  simp only [← comp_fst_add_comp_snd]
  exact (hf.clm_comp continuousWithinAt_const).add (hg.clm_comp continuousWithinAt_const)

theorem ContinuousAt.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun y => (f y).coprod (g y)) x :=
  (hf.continuousWithinAt.continuousLinearMapCoprod
    hg.continuousWithinAt).continuousAt Filter.univ_mem

end

namespace ContinuousLinearEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open Set
open scoped Topology

/-!
### The set of continuous linear equivalences between two Banach spaces is open

In this section we establish that the set of continuous linear equivalences between two Banach
spaces is an open subset of the space of linear maps between them.
-/

protected theorem isOpen [CompleteSpace E] : IsOpen (range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F)) := by
  rw [isOpen_iff_mem_nhds, forall_mem_range]
  refine fun e => IsOpen.mem_nhds ?_ (mem_range_self _)
  let O : (E →L[𝕜] F) → E →L[𝕜] E := fun f => (e.symm : F →L[𝕜] E).comp f
  have h_O : Continuous O := (isBoundedBilinearMap_comp (𝕜 := 𝕜) (F := F) (G := E)).continuous_right
  convert show IsOpen (O ⁻¹' { x | IsUnit x }) from Units.isOpen.preimage h_O using 1
  ext f'
  constructor
  · rintro ⟨e', rfl⟩
    exact ⟨(e'.trans e.symm).toUnit, rfl⟩
  · rintro ⟨w, hw⟩
    use (unitsEquiv 𝕜 E w).trans e
    ext x
    simp [O, hw]

protected theorem nhds [CompleteSpace E] (e : E ≃L[𝕜] F) :
    range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (e : E →L[𝕜] F) :=
  IsOpen.mem_nhds ContinuousLinearEquiv.isOpen (by simp)

end ContinuousLinearEquiv
