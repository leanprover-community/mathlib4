/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Group.ZeroAtInfty
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Topology.Algebra.UniformFilterBasis
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Schwartz space

This file defines the Schwartz space. Usually, the Schwartz space is defined as the set of smooth
functions $f : ℝ^n → ℂ$ such that there exists $C_{αβ} > 0$ with $$|x^α ∂^β f(x)| < C_{αβ}$$ for
all $x ∈ ℝ^n$ and for all multiindices $α, β$.
In mathlib, we use a slightly different approach and define the Schwartz space as all
smooth functions `f : E → F`, where `E` and `F` are real normed vector spaces such that for all
natural numbers `k` and `n` we have uniform bounds `‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ < C`.
This approach completely avoids using partial derivatives as well as polynomials.
We construct the topology on the Schwartz space by a family of seminorms, which are the best
constants in the above estimates. The abstract theory of topological vector spaces developed in
`SeminormFamily.moduleFilterBasis` and `WithSeminorms.toLocallyConvexSpace` turns the
Schwartz space into a locally convex topological vector space.

## Main definitions

* `SchwartzMap`: The Schwartz space is the space of smooth functions such that all derivatives
  decay faster than any power of `‖x‖`.
* `SchwartzMap.seminorm`: The family of seminorms as described above
* `SchwartzMap.compCLM`: Composition with a function on the right as a continuous linear map
  `𝓢(E, F) →L[𝕜] 𝓢(D, F)`, provided that the function is temperate and grows polynomially near
  infinity
* `SchwartzMap.integralCLM`: Integration as a continuous linear map `𝓢(ℝ, F) →L[ℝ] F`

## Main statements

* `SchwartzMap.instIsUniformAddGroup` and `SchwartzMap.instLocallyConvexSpace`: The Schwartz space
  is a locally convex topological vector space.
* `SchwartzMap.one_add_le_sup_seminorm_apply`: For a Schwartz function `f` there is a uniform bound
  on `(1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖`.

## Implementation details

The implementation of the seminorms is taken almost literally from `ContinuousLinearMap.opNorm`.

## Notation

* `𝓢(E, F)`: The Schwartz space `SchwartzMap E F` localized in `SchwartzSpace`

## Tags

Schwartz space, tempered distributions
-/

@[expose] public noncomputable section

open scoped Nat NNReal ContDiff

variable {ι 𝕜 𝕜' D E F G H V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (E F) in
/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of `‖x‖`. -/
structure SchwartzMap where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : E → F
  smooth' : ContDiff ℝ ∞ toFun
  decay' : ∀ k n : ℕ, ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n toFun x‖ ≤ C

/-- A function is a Schwartz function if it is smooth and all derivatives decay faster than
  any power of `‖x‖`. -/
scoped[SchwartzMap] notation "𝓢(" E ", " F ")" => SchwartzMap E F

namespace SchwartzMap

instance instFunLike : FunLike 𝓢(E, F) E F where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- All derivatives of a Schwartz function are rapidly decaying. -/
theorem decay (f : 𝓢(E, F)) (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  rcases f.decay' k n with ⟨C, hC⟩
  exact ⟨max C 1, by positivity, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Every Schwartz function is smooth. -/
@[fun_prop]
theorem smooth (f : 𝓢(E, F)) (n : ℕ∞) : ContDiff ℝ n f :=
  f.smooth'.of_le (mod_cast le_top)

/-- Every Schwartz function is smooth at any point. -/
@[fun_prop]
theorem contDiffAt (f : 𝓢(E, F)) (n : ℕ∞) {x : E} : ContDiffAt ℝ n f x :=
  (f.smooth n).contDiffAt

/-- Every Schwartz function is continuous. -/
@[continuity, fun_prop]
protected theorem continuous (f : 𝓢(E, F)) : Continuous f :=
  (f.smooth 0).continuous

instance instContinuousMapClass : ContinuousMapClass 𝓢(E, F) E F where
  map_continuous := SchwartzMap.continuous

/-- Every Schwartz function is differentiable. -/
@[fun_prop]
protected theorem differentiable (f : 𝓢(E, F)) : Differentiable ℝ f :=
  (f.smooth 1).differentiable one_ne_zero

/-- Every Schwartz function is differentiable at any point. -/
@[fun_prop]
protected theorem differentiableAt (f : 𝓢(E, F)) {x : E} : DifferentiableAt ℝ f x :=
  f.differentiable.differentiableAt

@[ext]
theorem ext {f g : 𝓢(E, F)} (h : ∀ x, (f : E → F) x = g x) : f = g :=
  DFunLike.ext f g h

section IsBigO

open Asymptotics Filter

variable (f : 𝓢(E, F))

/-- Auxiliary lemma, used in proving the more general result `isBigO_cocompact_rpow`. -/
theorem isBigO_cocompact_zpow_neg_nat (k : ℕ) :
    f =O[cocompact E] (‖·‖ ^ (-k : ℤ)) := by
  obtain ⟨d, _, hd'⟩ := f.decay k 0
  simp only [norm_iteratedFDeriv_zero] at hd'
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine ⟨d, Filter.Eventually.filter_mono Filter.cocompact_le_cofinite ?_⟩
  refine (Filter.eventually_cofinite_ne 0).mono fun x hx ↦ ?_
  rw [Real.norm_of_nonneg (by positivity), zpow_neg, ← div_eq_mul_inv, le_div_iff₀' (by positivity)]
  exact hd' x

theorem isBigO_cocompact_rpow [ProperSpace E] (s : ℝ) :
    f =O[cocompact E] (‖·‖ ^ s) := by
  let k := ⌈-s⌉₊
  have hk : -(k : ℝ) ≤ s := neg_le.mp (Nat.le_ceil (-s))
  refine (isBigO_cocompact_zpow_neg_nat f k).trans ?_
  suffices (fun x : ℝ ↦ x ^ (-k : ℤ)) =O[atTop] fun x : ℝ ↦ x ^ s
    from this.comp_tendsto tendsto_norm_cocompact_atTop
  simp_rw [Asymptotics.IsBigO, Asymptotics.IsBigOWith]
  refine ⟨1, (Filter.eventually_ge_atTop 1).mono fun x hx ↦ ?_⟩
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
    ← Real.rpow_intCast, Int.cast_neg, Int.cast_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hx hk

theorem isBigO_cocompact_zpow [ProperSpace E] (k : ℤ) :
    f =O[cocompact E] (‖·‖ ^ k) := by
  simpa only [Real.rpow_intCast] using isBigO_cocompact_rpow f k

end IsBigO

section Aux

theorem bounds_nonempty (k n : ℕ) (f : 𝓢(E, F)) :
    ∃ c : ℝ, c ∈ { c : ℝ | 0 ≤ c ∧ ∀ x : E, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ c } :=
  let ⟨M, hMp, hMb⟩ := f.decay k n
  ⟨M, le_of_lt hMp, hMb⟩

theorem bounds_bddBelow (k n : ℕ) (f : 𝓢(E, F)) :
    BddBelow { c | 0 ≤ c ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ c } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

theorem decay_add_le_aux (k n : ℕ) (f g : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ((f : E → F) + (g : E → F)) x‖ ≤
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ + ‖x‖ ^ k * ‖iteratedFDeriv ℝ n g x‖ := by
  rw [← mul_add]
  gcongr _ * ?_
  rw [iteratedFDeriv_add_apply (f.smooth _).contDiffAt (g.smooth _).contDiffAt]
  exact norm_add_le _ _

theorem decay_neg_aux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (-f : E → F) x‖ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by
  rw [iteratedFDeriv_neg_apply, norm_neg]

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

theorem decay_smul_aux (k n : ℕ) (f : 𝓢(E, F)) (c : 𝕜) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (c • (f : E → F)) x‖ =
      ‖c‖ * ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by
  rw [mul_comm ‖c‖, mul_assoc, iteratedFDeriv_const_smul_apply (f.smooth _).contDiffAt,
    norm_smul c (iteratedFDeriv ℝ n (⇑f) x)]

end Aux

section SeminormAux

/-- Helper definition for the seminorms of the Schwartz space. -/
protected def seminormAux (k n : ℕ) (f : 𝓢(E, F)) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ c }

theorem seminormAux_nonneg (k n : ℕ) (f : 𝓢(E, F)) : 0 ≤ f.seminormAux k n :=
  le_csInf (bounds_nonempty k n f) fun _ ⟨hx, _⟩ => hx

theorem le_seminormAux (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ f.seminormAux k n :=
  le_csInf (bounds_nonempty k n f) fun _ ⟨_, h⟩ => h x

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
theorem seminormAux_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ M) : f.seminormAux k n ≤ M :=
  csInf_le (bounds_bddBelow k n f) ⟨hMp, hM⟩

end SeminormAux

/-! ### Algebraic properties -/

section SMul

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] [NormedField 𝕜'] [NormedSpace 𝕜' F]
  [SMulCommClass ℝ 𝕜' F]

instance instSMul : SMul 𝕜 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • (f : E → F)
      smooth' := (f.smooth _).const_smul c
      decay' k n := .intro (f.seminormAux k n * ‖c‖) fun x ↦ calc
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (c • ⇑f) x‖ = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ * ‖c‖ := by
          rw [mul_comm _ ‖c‖, ← mul_assoc]
          exact decay_smul_aux k n f c x
        _ ≤ SchwartzMap.seminormAux k n f * ‖c‖ := by
          gcongr
          apply f.le_seminormAux }⟩

@[simp]
theorem smul_apply {f : 𝓢(E, F)} {c : 𝕜} {x : E} : (c • f) x = c • f x :=
  rfl

instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' F] : IsScalarTower 𝕜 𝕜' 𝓢(E, F) :=
  ⟨fun a b f => ext fun x => smul_assoc a b (f x)⟩

instance instSMulCommClass [SMulCommClass 𝕜 𝕜' F] : SMulCommClass 𝕜 𝕜' 𝓢(E, F) :=
  ⟨fun a b f => ext fun x => smul_comm a b (f x)⟩

theorem seminormAux_smul_le (k n : ℕ) (c : 𝕜) (f : 𝓢(E, F)) :
    (c • f).seminormAux k n ≤ ‖c‖ * f.seminormAux k n := by
  refine (c • f).seminormAux_le_bound k n (mul_nonneg (norm_nonneg _) (seminormAux_nonneg _ _ _))
      fun x => (decay_smul_aux k n f c x).trans_le ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (f.le_seminormAux k n x) (norm_nonneg _)

instance instNSMul : SMul ℕ 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • (f : E → F)
      smooth' := (f.smooth _).const_smul c
      decay' := by simpa [← Nat.cast_smul_eq_nsmul ℝ] using ((c : ℝ) • f).decay' }⟩

instance instZSMul : SMul ℤ 𝓢(E, F) :=
  ⟨fun c f =>
    { toFun := c • (f : E → F)
      smooth' := (f.smooth _).const_smul c
      decay' := by simpa [← Int.cast_smul_eq_zsmul ℝ] using ((c : ℝ) • f).decay' }⟩

end SMul

section Zero

instance instZero : Zero 𝓢(E, F) :=
  ⟨{  toFun := fun _ => 0
      smooth' := contDiff_const
      decay' := fun _ _ => ⟨1, fun _ => by simp⟩ }⟩

instance instInhabited : Inhabited 𝓢(E, F) :=
  ⟨0⟩

theorem coe_zero : DFunLike.coe (0 : 𝓢(E, F)) = (0 : E → F) :=
  rfl

@[simp]
theorem coeFn_zero : ⇑(0 : 𝓢(E, F)) = (0 : E → F) :=
  rfl

@[simp]
theorem zero_apply {x : E} : (0 : 𝓢(E, F)) x = 0 :=
  rfl

theorem seminormAux_zero (k n : ℕ) : (0 : 𝓢(E, F)).seminormAux k n = 0 :=
  le_antisymm (seminormAux_le_bound k n _ rfl.le fun _ => by simp [Pi.zero_def])
    (seminormAux_nonneg _ _ _)

end Zero

section Neg

instance instNeg : Neg 𝓢(E, F) :=
  ⟨fun f =>
    ⟨-f, (f.smooth _).neg, fun k n =>
      ⟨f.seminormAux k n, fun x => (decay_neg_aux k n f x).le.trans (f.le_seminormAux k n x)⟩⟩⟩

@[simp]
theorem neg_apply (f : 𝓢(E, F)) (x : E) : (-f) x = - (f x) := rfl

end Neg

section Add

instance instAdd : Add 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f + g, (f.smooth _).add (g.smooth _), fun k n =>
      ⟨f.seminormAux k n + g.seminormAux k n, fun x =>
        (decay_add_le_aux k n f g x).trans
          (add_le_add (f.le_seminormAux k n x) (g.le_seminormAux k n x))⟩⟩⟩

@[simp]
theorem add_apply {f g : 𝓢(E, F)} {x : E} : (f + g) x = f x + g x :=
  rfl

theorem seminormAux_add_le (k n : ℕ) (f g : 𝓢(E, F)) :
    (f + g).seminormAux k n ≤ f.seminormAux k n + g.seminormAux k n :=
  (f + g).seminormAux_le_bound k n
    (add_nonneg (seminormAux_nonneg _ _ _) (seminormAux_nonneg _ _ _)) fun x =>
    (decay_add_le_aux k n f g x).trans <|
      add_le_add (f.le_seminormAux k n x) (g.le_seminormAux k n x)

end Add

section Sub

instance instSub : Sub 𝓢(E, F) :=
  ⟨fun f g =>
    ⟨f - g, (f.smooth _).sub (g.smooth _), by
      intro k n
      refine ⟨f.seminormAux k n + g.seminormAux k n, fun x => ?_⟩
      grw [← f.le_seminormAux k n x, ← g.le_seminormAux k n x]
      rw [sub_eq_add_neg]
      rw [← decay_neg_aux k n g x]
      exact decay_add_le_aux k n f (-g) x⟩⟩

@[simp]
theorem sub_apply {f g : 𝓢(E, F)} {x : E} : (f - g) x = f x - g x :=
  rfl

end Sub

section AddCommGroup

instance instAddCommGroup : AddCommGroup 𝓢(E, F) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

open Classical in
@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → 𝓢(E, F)) (x : E) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h => simp [his, h]

variable (E F)

/-- Coercion as an additive homomorphism. -/
def coeHom : 𝓢(E, F) →+ E → F where
  toFun f := f
  map_zero' := coe_zero
  map_add' _ _ := rfl

variable {E F}

theorem coe_coeHom : (coeHom E F : 𝓢(E, F) → E → F) = DFunLike.coe :=
  rfl

theorem coeHom_injective : Function.Injective (coeHom E F) := by
  rw [coe_coeHom]
  exact DFunLike.coe_injective

end AddCommGroup

section Module

variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

instance instModule : Module 𝕜 𝓢(E, F) :=
  coeHom_injective.module 𝕜 (coeHom E F) fun _ _ => rfl

end Module

section Seminorms

/-! ### Seminorms on Schwartz space -/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
variable (𝕜)

/-- The seminorms of the Schwartz space given by the best constants in the definition of
`𝓢(E, F)`. -/
protected def seminorm (k n : ℕ) : Seminorm 𝕜 𝓢(E, F) :=
  Seminorm.ofSMulLE (SchwartzMap.seminormAux k n) (seminormAux_zero k n) (seminormAux_add_le k n)
    (seminormAux_smul_le k n)

/-- If one controls the seminorm for every `x`, then one controls the seminorm. -/
theorem seminorm_le_bound (k n : ℕ) (f : 𝓢(E, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ M) : SchwartzMap.seminorm 𝕜 k n f ≤ M :=
  f.seminormAux_le_bound k n hMp hM

/-- If one controls the seminorm for every `x`, then one controls the seminorm.

Variant for functions `𝓢(ℝ, F)`. -/
theorem seminorm_le_bound' (k n : ℕ) (f : 𝓢(ℝ, F)) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ x, |x| ^ k * ‖iteratedDeriv n f x‖ ≤ M) : SchwartzMap.seminorm 𝕜 k n f ≤ M := by
  refine seminorm_le_bound 𝕜 k n f hMp ?_
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]

/-- The seminorm controls the Schwartz estimate for any fixed `x`. -/
theorem le_seminorm (k n : ℕ) (f : 𝓢(E, F)) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ SchwartzMap.seminorm 𝕜 k n f :=
  f.le_seminormAux k n x

/-- The seminorm controls the Schwartz estimate for any fixed `x`.

Variant for functions `𝓢(ℝ, F)`. -/
theorem le_seminorm' (k n : ℕ) (f : 𝓢(ℝ, F)) (x : ℝ) :
    |x| ^ k * ‖iteratedDeriv n f x‖ ≤ SchwartzMap.seminorm 𝕜 k n f := by
  have := le_seminorm 𝕜 k n f x
  rwa [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]

theorem norm_iteratedFDeriv_le_seminorm (f : 𝓢(E, F)) (n : ℕ) (x₀ : E) :
    ‖iteratedFDeriv ℝ n f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 0 n) f := by
  have := SchwartzMap.le_seminorm 𝕜 0 n f x₀
  rwa [pow_zero, one_mul] at this

theorem norm_pow_mul_le_seminorm (f : 𝓢(E, F)) (k : ℕ) (x₀ : E) :
    ‖x₀‖ ^ k * ‖f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 k 0) f := by
  have := SchwartzMap.le_seminorm 𝕜 k 0 f x₀
  rwa [norm_iteratedFDeriv_zero] at this

theorem norm_le_seminorm (f : 𝓢(E, F)) (x₀ : E) : ‖f x₀‖ ≤ (SchwartzMap.seminorm 𝕜 0 0) f := by
  have := norm_pow_mul_le_seminorm 𝕜 f 0 x₀
  rwa [pow_zero, one_mul] at this

variable (E F)

/-- The family of Schwartz seminorms. -/
def _root_.schwartzSeminormFamily : SeminormFamily 𝕜 𝓢(E, F) (ℕ × ℕ) :=
  fun m => SchwartzMap.seminorm 𝕜 m.1 m.2

@[simp]
theorem schwartzSeminormFamily_apply (n k : ℕ) :
    schwartzSeminormFamily 𝕜 E F (n, k) = SchwartzMap.seminorm 𝕜 n k :=
  rfl

@[simp]
theorem schwartzSeminormFamily_apply_zero :
    schwartzSeminormFamily 𝕜 E F 0 = SchwartzMap.seminorm 𝕜 0 0 :=
  rfl

variable {𝕜 E F}

/-- A more convenient version of `le_sup_seminorm_apply`.

The set `Finset.Iic m` is the set of all pairs `(k', n')` with `k' ≤ m.1` and `n' ≤ m.2`.
Note that the constant is far from optimal. -/
theorem one_add_le_sup_seminorm_apply {m : ℕ × ℕ} {k n : ℕ} (hk : k ≤ m.1) (hn : n ≤ m.2)
    (f : 𝓢(E, F)) (x : E) :
    (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
      2 ^ m.1 * (Finset.Iic m).sup (fun m => SchwartzMap.seminorm 𝕜 m.1 m.2) f := by
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one, Finset.sum_mul]
  norm_cast
  rw [← Nat.sum_range_choose m.1]
  push_cast
  rw [Finset.sum_mul]
  have hk' : Finset.range (k + 1) ⊆ Finset.range (m.1 + 1) := by grind
  grw [hk']
  gcongr ∑ _i ∈ Finset.range (m.1 + 1), ?_ with i hi
  move_mul [(Nat.choose k i : ℝ), (Nat.choose m.1 i : ℝ)]
  gcongr
  grw [le_seminorm 𝕜 i n f x]
  apply Seminorm.le_def.1
  exact Finset.le_sup_of_le (Finset.mem_Iic.2 <|
    Prod.mk_le_mk.2 ⟨Finset.mem_range_succ_iff.mp hi, hn⟩) le_rfl

end Seminorms

section Topology

/-! ### The topology on the Schwartz space -/


variable [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
variable (𝕜 E F)

instance instTopologicalSpace : TopologicalSpace 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).moduleFilterBasis.topology'

theorem _root_.schwartz_withSeminorms : WithSeminorms (schwartzSeminormFamily 𝕜 E F) := by
  have A : WithSeminorms (schwartzSeminormFamily ℝ E F) := ⟨rfl⟩
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at A ⊢
  rw [A]
  rfl

variable {𝕜 E F}

instance instContinuousSMul : ContinuousSMul 𝕜 𝓢(E, F) := by
  rw [(schwartz_withSeminorms 𝕜 E F).withSeminorms_eq]
  exact (schwartzSeminormFamily 𝕜 E F).moduleFilterBasis.continuousSMul

instance instIsTopologicalAddGroup : IsTopologicalAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).addGroupFilterBasis.isTopologicalAddGroup

instance instUniformSpace : UniformSpace 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).addGroupFilterBasis.uniformSpace

instance instIsUniformAddGroup : IsUniformAddGroup 𝓢(E, F) :=
  (schwartzSeminormFamily ℝ E F).addGroupFilterBasis.isUniformAddGroup

instance instLocallyConvexSpace : LocallyConvexSpace ℝ 𝓢(E, F) :=
  (schwartz_withSeminorms ℝ E F).toLocallyConvexSpace

instance instFirstCountableTopology : FirstCountableTopology 𝓢(E, F) :=
  (schwartz_withSeminorms ℝ E F).firstCountableTopology

end Topology

@[fun_prop]
theorem hasTemperateGrowth (f : 𝓢(E, F)) : Function.HasTemperateGrowth f := by
  refine ⟨smooth f ⊤, fun n => ?_⟩
  rcases f.decay 0 n with ⟨C, Cpos, hC⟩
  exact ⟨0, C, by simpa using hC⟩

section HasCompactSupport

/-- A smooth compactly supported function is a Schwartz function. -/
@[simps]
def _root_.HasCompactSupport.toSchwartzMap {f : E → F} (h₁ : HasCompactSupport f)
    (h₂ : ContDiff ℝ ∞ f) : 𝓢(E, F) where
  toFun := f
  smooth' := h₂
  decay' k n := by
    set g := fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
    have hg₁ : Continuous g := by
      apply Continuous.mul (by fun_prop)
      exact (h₂.of_le (mod_cast le_top)).continuous_iteratedFDeriv'.norm
    have hg₂ : HasCompactSupport g := (h₁.iteratedFDeriv _).norm.mul_left
    obtain ⟨x₀, hx₀⟩ := hg₁.exists_forall_ge_of_hasCompactSupport hg₂
    exact ⟨g x₀, hx₀⟩

end HasCompactSupport

section CLM

/-! ### Construction of continuous linear maps between Schwartz spaces -/


variable [NormedField 𝕜] [NormedField 𝕜']
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜' G] [SMulCommClass ℝ 𝕜' G]
variable {σ : 𝕜 →+* 𝕜'}

/-- Create a semilinear map between Schwartz spaces.

Note: This is a helper definition for `mkCLM`. -/
def mkLM (A : 𝓢(D, E) → F → G) (hadd : ∀ (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
    (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x)
    (hsmooth : ∀ f : 𝓢(D, E), ContDiff ℝ ∞ (A f))
    (hbound : ∀ n : ℕ × ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(D, E)) (x : F),
      ‖x‖ ^ n.fst * ‖iteratedFDeriv ℝ n.snd (A f) x‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) →ₛₗ[σ] 𝓢(F, G) where
  toFun f :=
    { toFun := A f
      smooth' := hsmooth f
      decay' := by
        intro k n
        rcases hbound ⟨k, n⟩ with ⟨s, C, _, h⟩
        exact ⟨C * (s.sup (schwartzSeminormFamily 𝕜 D E)) f, h f⟩ }
  map_add' f g := ext (hadd f g)
  map_smul' a f := ext (hsmul a f)

/-- Create a continuous semilinear map between Schwartz spaces.

For an example of using this definition, see `fderivCLM`. -/
def mkCLM [RingHomIsometric σ] (A : 𝓢(D, E) → F → G)
    (hadd : ∀ (f g : 𝓢(D, E)) (x), A (f + g) x = A f x + A g x)
    (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)) (x), A (a • f) x = σ a • A f x)
    (hsmooth : ∀ f : 𝓢(D, E), ContDiff ℝ ∞ (A f))
    (hbound : ∀ n : ℕ × ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(D, E)) (x : F),
      ‖x‖ ^ n.fst * ‖iteratedFDeriv ℝ n.snd (A f) x‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) →SL[σ] 𝓢(F, G) where
  cont := by
    change Continuous (mkLM A hadd hsmul hsmooth hbound : 𝓢(D, E) →ₛₗ[σ] 𝓢(F, G))
    refine
      Seminorm.continuous_from_bounded (schwartz_withSeminorms 𝕜 D E)
        (schwartz_withSeminorms 𝕜' F G) _ fun n => ?_
    rcases hbound n with ⟨s, C, hC, h⟩
    refine ⟨s, ⟨C, hC⟩, fun f => ?_⟩
    exact (mkLM A hadd hsmul hsmooth hbound f).seminorm_le_bound 𝕜' n.1 n.2 (by positivity) (h f)
  toLinearMap := mkLM A hadd hsmul hsmooth hbound

/-- Define a continuous semilinear map from Schwartz space to a normed space. -/
def mkCLMtoNormedSpace [RingHomIsometric σ] (A : 𝓢(D, E) → G)
    (hadd : ∀ (f g : 𝓢(D, E)), A (f + g) = A f + A g)
    (hsmul : ∀ (a : 𝕜) (f : 𝓢(D, E)), A (a • f) = σ a • A f)
    (hbound : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓢(D, E)),
      ‖A f‖ ≤ C * s.sup (schwartzSeminormFamily 𝕜 D E) f) :
    𝓢(D, E) →SL[σ] G :=
  letI f : 𝓢(D, E) →ₛₗ[σ] G :=
    { toFun := (A ·)
      map_add' := hadd
      map_smul' := hsmul }
  { toLinearMap := f
    cont := by
      change Continuous (LinearMap.mk _ _)
      apply Seminorm.cont_withSeminorms_normedSpace G (schwartz_withSeminorms 𝕜 D E)
      rcases hbound with ⟨s, C, hC, h⟩
      exact ⟨s, ⟨C, hC⟩, h⟩ }

end CLM

section EvalCLM

variable [NormedField 𝕜]
variable [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedSpace 𝕜 G] [SMulCommClass ℝ 𝕜 G]

variable (𝕜 E G) in
/-- The map applying a vector to Hom-valued Schwartz function as a continuous linear map. -/
protected def evalCLM (m : F) : 𝓢(E, F →L[ℝ] G) →L[𝕜] 𝓢(E, G) :=
  mkCLM (fun f x => f x m) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun f => ContDiff.clm_apply f.2 contDiff_const) <| by
  rintro ⟨k, n⟩
  use {(k, n)}, ‖m‖, norm_nonneg _
  intro f x
  simp only [Finset.sup_singleton, schwartzSeminormFamily_apply]
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (f · m) x‖ ≤ ‖x‖ ^ k * (‖m‖ * ‖iteratedFDeriv ℝ n f x‖) := by
      gcongr
      exact norm_iteratedFDeriv_clm_apply_const (f.smooth _).contDiffAt le_rfl
    _ ≤ ‖m‖ * SchwartzMap.seminorm 𝕜 k n f := by
      move_mul [‖m‖]
      gcongr
      apply le_seminorm

@[simp]
theorem evalCLM_apply_apply (f : 𝓢(E, F →L[ℝ] G)) (m : F) (x : E) :
    SchwartzMap.evalCLM 𝕜 E G m f x = f x m := rfl

end EvalCLM

section Multiplication

variable [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedSpace 𝕜 F]

section bilin

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]

/-- The map `f ↦ (x ↦ B (f x) (g x))` as a continuous `𝕜`-linear map on Schwartz space,
where `B` is a continuous `𝕜`-linear map and `g` is a function of temperate growth. -/
def bilinLeftCLM (B : E →L[𝕜] F →L[𝕜] G) {g : D → F} (hg : g.HasTemperateGrowth) :
    𝓢(D, E) →L[𝕜] 𝓢(D, G) := by
  refine mkCLM (fun f x => B (f x) (g x))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun f => (B.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp
      ((f.smooth ⊤).prodMk hg.1)) ?_
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  use
    Finset.Iic (l + k, n), ‖B‖ * ((n : ℝ) + (1 : ℝ)) * n.choose (n / 2) * (C * 2 ^ (l + k)),
    by positivity
  intro f x
  have hxk : 0 ≤ ‖x‖ ^ k := by positivity
  simp_rw [← ContinuousLinearMap.bilinearRestrictScalars_apply_apply ℝ B]
  have hnorm_mul :=
    ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (B.bilinearRestrictScalars ℝ)
    (f.smooth ⊤) hg.1 x (n := n) (mod_cast le_top)
  grw [hnorm_mul]
  rw [ContinuousLinearMap.norm_bilinearRestrictScalars]
  move_mul [← ‖B‖]
  simp_rw [mul_assoc ‖B‖]
  gcongr _ * ?_
  rw [Finset.mul_sum]
  have : (∑ _x ∈ Finset.range (n + 1), (1 : ℝ)) = n + 1 := by simp
  simp_rw [mul_assoc ((n : ℝ) + 1)]
  rw [← this, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  simp only [one_mul]
  move_mul [(Nat.choose n i : ℝ), (Nat.choose n (n / 2) : ℝ)]
  gcongr ?_ * ?_
  swap
  · norm_cast
    exact i.choose_le_middle n
  specialize hgrowth (n - i) (by simp only [tsub_le_self]) x
  grw [hgrowth]
  move_mul [C]
  gcongr ?_ * C
  rw [Finset.mem_range_succ_iff] at hi
  change i ≤ (l + k, n).snd at hi
  refine le_trans ?_ (one_add_le_sup_seminorm_apply le_rfl hi f x)
  rw [pow_add]
  move_mul [(1 + ‖x‖) ^ l]
  gcongr
  simp

@[simp]
theorem bilinLeftCLM_apply (B : E →L[𝕜] F →L[𝕜] G) {g : D → F} (hg : g.HasTemperateGrowth)
    (f : 𝓢(D, E)) : bilinLeftCLM B hg f = fun x => B (f x) (g x) := rfl

end bilin

section smul

variable (F) in
open Classical in
/-- The map `f ↦ (x ↦ g x • f x)` as a continuous `𝕜`-linear map on Schwartz space,
where `g` is a function of temperate growth. -/
def smulLeftCLM (g : E → 𝕜) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  if hg : g.HasTemperateGrowth then
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul 𝕜 𝕜).flip hg
  else 0

theorem smulLeftCLM_apply {g : E → 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F g f = fun x ↦ g x • f x := by
  simp [smulLeftCLM, hg]

@[simp]
theorem smulLeftCLM_apply_apply {g : E → 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) :
    smulLeftCLM F g f x = g x • f x := by
  simp [smulLeftCLM_apply hg]

@[simp]
theorem smulLeftCLM_const (c : 𝕜) :
    smulLeftCLM F (fun (_ : E) ↦ c) = c • ContinuousLinearMap.id 𝕜 _ := by
  ext f x
  have : (fun (_ : E) ↦ c).HasTemperateGrowth := by fun_prop
  simp [this]

@[simp]
theorem smulLeftCLM_smulLeftCLM_apply {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F g₁ (smulLeftCLM F g₂ f) = smulLeftCLM F (g₁ * g₂) f := by
  ext x
  simp [smul_smul, hg₁, hg₂, hg₁.mul hg₂]

theorem smulLeftCLM_compL_smulLeftCLM {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F g₁ ∘L smulLeftCLM F g₂ = smulLeftCLM F (g₁ * g₂) := by
  ext1 f
  exact smulLeftCLM_smulLeftCLM_apply hg₁ hg₂ f

theorem smulLeftCLM_smul {g : E → 𝕜} (hg : g.HasTemperateGrowth) (c : 𝕜) :
    smulLeftCLM F (c • g) = c • smulLeftCLM F g := by
  have : (fun (_ : E) ↦ c).HasTemperateGrowth := by fun_prop
  convert (smulLeftCLM_compL_smulLeftCLM this hg).symm using 1
  simp

theorem smulLeftCLM_add {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ + g₂) = smulLeftCLM F g₁ + smulLeftCLM F g₂ := by
  ext f x
  simp [hg₁, hg₂, hg₁.add hg₂, add_smul]

theorem smulLeftCLM_sub {g₁ g₂ : E → 𝕜} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) :
    smulLeftCLM F (g₁ - g₂) = smulLeftCLM F g₁ - smulLeftCLM F g₂ := by
  ext f x
  simp [hg₁, hg₂, hg₁.sub hg₂, sub_smul]

theorem smulLeftCLM_neg {g : E → 𝕜} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F (-g) = -smulLeftCLM F g := by
  ext f x
  simp [hg, hg.neg, neg_smul]

theorem smulLeftCLM_fun_neg {g : E → 𝕜} (hg : g.HasTemperateGrowth) :
    smulLeftCLM F (fun x ↦ -g x) = -smulLeftCLM F g :=
  smulLeftCLM_neg hg

theorem smulLeftCLM_sum {g : ι → E → 𝕜} {s : Finset ι} (hg : ∀ i ∈ s, (g i).HasTemperateGrowth) :
    smulLeftCLM F (fun x ↦ ∑ i ∈ s, g i x) = ∑ i ∈ s, smulLeftCLM F (g i) := by
  ext f x
  simp +contextual [Function.HasTemperateGrowth.sum hg, Finset.sum_smul, hg]

variable {𝕜' : Type*} [RCLike 𝕜'] [NormedSpace 𝕜' F]

variable (𝕜') in
theorem smulLeftCLM_ofReal {g : E → ℝ} (hg : g.HasTemperateGrowth) (f : 𝓢(E, F)) :
    smulLeftCLM F (fun x ↦ RCLike.ofReal (K := 𝕜') (g x)) f = smulLeftCLM F g f := by
  ext x
  rw [smulLeftCLM_apply_apply (by fun_prop), smulLeftCLM_apply_apply (by fun_prop),
    algebraMap_smul]

theorem smulLeftCLM_real_smul {g : E → 𝕜'} (hg : g.HasTemperateGrowth) (c : ℝ) :
    smulLeftCLM F (c • g) = c • smulLeftCLM F g := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜') c, smulLeftCLM_smul hg,
    ← RCLike.real_smul_eq_coe_smul c]

theorem tsupport_smulLeftCLM_subset_left (g : E → 𝕜) (f : 𝓢(E, F)) :
    tsupport (smulLeftCLM F g f) ⊆ tsupport g := by
  by_cases hg : g.HasTemperateGrowth
  · rw [smulLeftCLM_apply hg]
    apply tsupport_smul_subset_left
  · unfold smulLeftCLM
    simp [hg]

theorem tsupport_smulLeftCLM_subset_right (g : E → 𝕜) (f : 𝓢(E, F)) :
    tsupport (smulLeftCLM F g f) ⊆ tsupport f := by
  by_cases hg : g.HasTemperateGrowth
  · rw [smulLeftCLM_apply hg]
    apply tsupport_smul_subset_right
  · unfold smulLeftCLM
    simp [hg]

end smul

section pairing

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 G]

/-- The bilinear pairing of Schwartz functions.

The continuity in the left argument is provided in `SchwartzMap.pairing_continuous_left`. -/
def pairing (B : E →L[𝕜] F →L[𝕜] G) : 𝓢(D, E) →ₗ[𝕜] 𝓢(D, F) →L[𝕜] 𝓢(D, G) where
  toFun f := bilinLeftCLM B.flip f.hasTemperateGrowth
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem pairing_apply (B : E →L[𝕜] F →L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) :
    pairing B f g = fun x ↦ B (f x) (g x) := rfl

@[simp]
theorem pairing_apply_apply (B : E →L[𝕜] F →L[𝕜] G) (f : 𝓢(D, E)) (g : 𝓢(D, F)) (x : D) :
    pairing B f g x = B (f x) (g x) := rfl

/-- The pairing is continuous in the left argument.

Note that since `𝓢(E, F)` is not a normed space, uncurried and curried continuity do not
coincide. -/
theorem pairing_continuous_left (B : E →L[𝕜] F →L[𝕜] G) (g : 𝓢(D, F)) :
    Continuous (pairing B · g) := (pairing B.flip g).continuous

end pairing

open ContinuousLinearMap

variable (𝕜 F) in
/-- Scalar multiplication with a continuous linear map as a continuous linear map on Schwartz
functions. -/
def smulRightCLM (L : E →L[ℝ] G →L[ℝ] ℝ) : 𝓢(E, F) →L[𝕜] 𝓢(E, G →L[ℝ] F) :=
  mkCLM (fun f x ↦ (L x).smulRight (f x)) (by intros; ext; simp)
    (by intro c g x; ext v; simpa using smul_comm (L x v) c (g x))
    (by fun_prop) <| by
      intro ⟨k, n⟩
      use {(k + 1, n), (k, n - 1)}, 2 * ‖L‖ * (max 1 n), by positivity
      intro f x
      calc
        _ ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i) *
            ‖iteratedFDeriv ℝ i L x‖ * ‖iteratedFDeriv ℝ (n - i) f x‖ := by
          gcongr 1
          exact norm_iteratedFDeriv_le_of_bilinear_of_le_one (smulRightL ℝ G F)
            (by fun_prop) (f.smooth ⊤) x (mod_cast le_top) norm_smulRightL_le
        _ ≤ ‖x‖ ^ k *
            (‖L x‖ * ‖iteratedFDeriv ℝ n f x‖ + n * ‖L‖ * ‖iteratedFDeriv ℝ (n - 1) f x‖) := by
          gcongr 1
          rw [Finset.sum_range_succ', add_comm]
          cases n with
          | zero => simp
          | succ n =>
            have : ∑ k ∈ Finset.range n,
                (((n + 1).choose (k + 1 + 1)) : ℝ) * ‖iteratedFDeriv ℝ (k + 1 + 1) L x‖ *
                ‖iteratedFDeriv ℝ (n + 1 - (k + 1 + 1)) f x‖ = 0 := by
              apply Finset.sum_eq_zero
              simp [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_const]
            simp [Finset.sum_range_succ', this]
        _ = ‖x‖ ^ k * ‖L x‖ * ‖iteratedFDeriv ℝ n f x‖ +
              ‖x‖ ^ k * n * ‖L‖ * ‖iteratedFDeriv ℝ (n - 1) f x‖ := by ring
        _ ≤ ‖L‖ * 1 * (SchwartzMap.seminorm 𝕜 (k + 1) n) f +
              ‖L‖ * n * (SchwartzMap.seminorm 𝕜 k (n - 1) f) := by
          grw [le_opNorm, ← le_seminorm 𝕜 (k + 1) n f x, ← le_seminorm 𝕜 k (n - 1) f x]
          apply le_of_eq
          ring
        _ ≤ ‖L‖ * max 1 n *
            max ((SchwartzMap.seminorm 𝕜 (k + 1) n) f) ((SchwartzMap.seminorm 𝕜 k (n - 1)) f) +
            ‖L‖ * max 1 n *
            max ((SchwartzMap.seminorm 𝕜 (k + 1) n) f) ((SchwartzMap.seminorm 𝕜 k (n - 1)) f) := by
          gcongr <;> simp
        _ = _ := by
          simp only [Finset.sup_insert, schwartzSeminormFamily_apply, Finset.sup_singleton,
            Seminorm.coe_sup, Pi.sup_apply]
          ring

@[simp]
theorem smulRightCLM_apply_apply (L : E →L[ℝ] G →L[ℝ] ℝ) (f : 𝓢(E, F)) (x : E) :
    smulRightCLM 𝕜 F L f x = (L x).smulRight (f x) := rfl

end Multiplication

section Comp

variable (𝕜)
variable [RCLike 𝕜]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- Composition with a function on the right is a continuous linear map on Schwartz space
provided that the function is temperate and growths polynomially near infinity. -/
def compCLM {g : D → E} (hg : g.HasTemperateGrowth)
    (hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k) : 𝓢(E, F) →L[𝕜] 𝓢(D, F) := by
  refine mkCLM (fun f => f ∘ g) (fun _ _ _ => by simp) (fun _ _ _ => rfl)
    (fun f => (f.smooth ⊤).comp hg.1) ?_
  rintro ⟨k, n⟩
  rcases hg.norm_iteratedFDeriv_le_uniform n with ⟨l, C, hC, hgrowth⟩
  rcases hg_upper with ⟨kg, Cg, hg_upper'⟩
  have hCg : 1 ≤ 1 + Cg := by
    refine le_add_of_nonneg_right ?_
    specialize hg_upper' 0
    rw [norm_zero] at hg_upper'
    exact nonneg_of_mul_nonneg_left hg_upper' (by positivity)
  let k' := kg * (k + l * n)
  use Finset.Iic (k', n), (1 + Cg) ^ (k + l * n) * ((C + 1) ^ n * n ! * 2 ^ k'), by positivity
  intro f x
  let seminorm_f := ((Finset.Iic (k', n)).sup (schwartzSeminormFamily 𝕜 _ _)) f
  have hg_upper'' : (1 + ‖x‖) ^ (k + l * n) ≤ (1 + Cg) ^ (k + l * n) * (1 + ‖g x‖) ^ k' := by
    rw [pow_mul, ← mul_pow]
    gcongr
    rw [add_mul]
    refine add_le_add ?_ (hg_upper' x)
    nth_rw 1 [← one_mul (1 : ℝ)]
    gcongr
    apply one_le_pow₀
    simp only [le_add_iff_nonneg_right, norm_nonneg]
  have hbound (i) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i f (g x)‖ ≤ 2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k' := by
    have hpos : 0 < (1 + ‖g x‖) ^ k' := by positivity
    rw [le_div_iff₀' hpos]
    change i ≤ (k', n).snd at hi
    exact one_add_le_sup_seminorm_apply le_rfl hi _ _
  have hgrowth' (N : ℕ) (hN₁ : 1 ≤ N) (hN₂ : N ≤ n) :
      ‖iteratedFDeriv ℝ N g x‖ ≤ ((C + 1) * (1 + ‖x‖) ^ l) ^ N := by
    refine (hgrowth N hN₂ x).trans ?_
    rw [mul_pow]
    have hN₁' := (lt_of_lt_of_le zero_lt_one hN₁).ne'
    gcongr
    · exact le_trans (by simp) (le_self_pow₀ (by simp [hC]) hN₁')
    · refine le_self_pow₀ (one_le_pow₀ ?_) hN₁'
      simp only [le_add_iff_nonneg_right, norm_nonneg]
  have := norm_iteratedFDeriv_comp_le (f.smooth ⊤) hg.1 (mod_cast le_top) x hbound hgrowth'
  have hxk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (by simp only [zero_le_one, le_add_iff_nonneg_left]) _
  grw [hxk, this]
  have rearrange :
    (1 + ‖x‖) ^ k *
        (n ! * (2 ^ k' * seminorm_f / (1 + ‖g x‖) ^ k') * ((C + 1) * (1 + ‖x‖) ^ l) ^ n) =
      (1 + ‖x‖) ^ (k + l * n) / (1 + ‖g x‖) ^ k' *
        ((C + 1) ^ n * n ! * 2 ^ k' * seminorm_f) := by
    rw [mul_pow, pow_add, ← pow_mul]
    ring
  rw [rearrange]
  have hgxk' : 0 < (1 + ‖g x‖) ^ k' := by positivity
  rw [← div_le_iff₀ hgxk'] at hg_upper''
  grw [hg_upper'', ← mul_assoc]

@[simp] lemma compCLM_apply {g : D → E} (hg : g.HasTemperateGrowth)
    (hg_upper : ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖g x‖) ^ k) (f : 𝓢(E, F)) :
    compCLM 𝕜 hg hg_upper f = f ∘ g := rfl

/-- Composition with a function on the right is a continuous linear map on Schwartz space
provided that the function is temperate and antilipschitz. -/
def compCLMOfAntilipschitz {K : ℝ≥0} {g : D → E}
    (hg : g.HasTemperateGrowth) (h'g : AntilipschitzWith K g) :
    𝓢(E, F) →L[𝕜] 𝓢(D, F) := by
  refine compCLM 𝕜 hg ⟨1, K * max 1 ‖g 0‖, fun x ↦ ?_⟩
  calc
  ‖x‖ ≤ K * ‖g x - g 0‖ := by
    rw [← dist_zero_right, ← dist_eq_norm]
    apply h'g.le_mul_dist
  _ ≤ K * (‖g x‖ + ‖g 0‖) := by
    gcongr
    exact norm_sub_le _ _
  _ ≤ K * (‖g x‖ + max 1 ‖g 0‖) := by
    gcongr
    exact le_max_right _ _
  _ ≤ (K * max 1 ‖g 0‖ : ℝ) * (1 + ‖g x‖) ^ 1 := by
    simp only [mul_add, add_comm (K * ‖g x‖), pow_one, mul_one, add_le_add_iff_left]
    gcongr
    exact le_mul_of_one_le_right (by positivity) (le_max_left _ _)

@[simp] lemma compCLMOfAntilipschitz_apply {K : ℝ≥0} {g : D → E} (hg : g.HasTemperateGrowth)
    (h'g : AntilipschitzWith K g) (f : 𝓢(E, F)) :
    compCLMOfAntilipschitz 𝕜 hg h'g f = f ∘ g := rfl

/-- Composition with a continuous linear equiv on the right is a continuous linear map on
Schwartz space. -/
def compCLMOfContinuousLinearEquiv (g : D ≃L[ℝ] E) :
    𝓢(E, F) →L[𝕜] 𝓢(D, F) :=
  compCLMOfAntilipschitz 𝕜 (g.toContinuousLinearMap.hasTemperateGrowth) g.antilipschitz

@[simp] lemma compCLMOfContinuousLinearEquiv_apply (g : D ≃L[ℝ] E) (f : 𝓢(E, F)) :
    compCLMOfContinuousLinearEquiv 𝕜 g f = f ∘ g := rfl

variable [NontriviallyNormedField 𝕜'] [NormedAlgebra ℝ 𝕜'] [NormedSpace 𝕜' F]

theorem smulLeftCLM_compCLMOfContinuousLinearEquiv {u : D → 𝕜'} (hu : u.HasTemperateGrowth)
    (g : D ≃L[ℝ] E) (f : 𝓢(E, F)) :
    smulLeftCLM F u (compCLMOfContinuousLinearEquiv 𝕜 g f) =
    compCLMOfContinuousLinearEquiv 𝕜 g (smulLeftCLM F (u ∘ g.symm) f) := by
  ext x
  have hu' : (u ∘ g.symm).HasTemperateGrowth := by fun_prop
  simp [smulLeftCLM_apply_apply hu, smulLeftCLM_apply_apply hu']

end Comp

section Integration

/-! ### Integration -/


open Real Complex Filter MeasureTheory MeasureTheory.Measure Module

variable [RCLike 𝕜]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V]
variable [MeasurableSpace D]

variable {μ : Measure D} [hμ : HasTemperateGrowth μ]

attribute [local instance 101] secondCountableTopologyEither_of_left

variable (𝕜 μ) in
lemma integral_pow_mul_iteratedFDeriv_le (f : 𝓢(D, V)) (k n : ℕ) :
    ∫ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ∂μ ≤ 2 ^ μ.integrablePower *
      (∫ x, (1 + ‖x‖) ^ (- (μ.integrablePower : ℝ)) ∂μ) *
        (SchwartzMap.seminorm 𝕜 0 n f + SchwartzMap.seminorm 𝕜 (k + μ.integrablePower) n f) :=
  integral_pow_mul_le_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm ℝ _ _)
    (le_seminorm ℝ _ _ _)

variable [BorelSpace D] [SecondCountableTopology D]

variable (μ) in
lemma integrable_pow_mul_iteratedFDeriv
    (f : 𝓢(D, V))
    (k n : ℕ) : Integrable (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) μ :=
  integrable_of_le_of_pow_mul_le (norm_iteratedFDeriv_le_seminorm ℝ _ _) (le_seminorm ℝ _ _ _)
    ((f.smooth ⊤).continuous_iteratedFDeriv (mod_cast le_top)).aestronglyMeasurable

variable (μ) in
lemma integrable_pow_mul (f : 𝓢(D, V))
    (k : ℕ) : Integrable (fun x ↦ ‖x‖ ^ k * ‖f x‖) μ := by
  convert integrable_pow_mul_iteratedFDeriv μ f k 0 with x
  simp

lemma integrable (f : 𝓢(D, V)) : Integrable f μ :=
  (f.integrable_pow_mul μ 0).mono f.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun _ ↦ by simp))

variable (𝕜 μ) in
/-- The integral as a continuous linear map from Schwartz space to the codomain. -/
def integralCLM : 𝓢(D, V) →L[𝕜] V := by
  refine mkCLMtoNormedSpace (∫ x, · x ∂μ)
    (fun f g ↦ integral_add f.integrable g.integrable) (integral_smul · ·) ?_
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, 2 ^ n * ∫ x : D, (1 + ‖x‖) ^ (- (n : ℝ)) ∂μ
  refine ⟨by positivity, fun f ↦ (norm_integral_le_integral_norm f).trans ?_⟩
  have h' : ∀ x, ‖f x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
      (2 ^ n * ((Finset.Iic m).sup (fun m' => SchwartzMap.seminorm 𝕜 m'.1 m'.2) f)) := by
    intro x
    rw [rpow_neg (by positivity), ← div_eq_inv_mul, le_div_iff₀' (by positivity), rpow_natCast]
    simpa using one_add_le_sup_seminorm_apply (m := m) (k := n) (n := 0) le_rfl le_rfl f x
  apply (integral_mono (by simpa using f.integrable_pow_mul μ 0) _ h').trans
  · unfold schwartzSeminormFamily
    rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]
  apply h.mul_const

variable (𝕜) in
@[simp]
lemma integralCLM_apply (f : 𝓢(D, V)) : integralCLM 𝕜 μ f = ∫ x, f x ∂μ := by rfl

end Integration

section BoundedContinuousFunction

/-! ### Inclusion into the space of bounded continuous functions -/


open scoped BoundedContinuousFunction

instance instBoundedContinuousMapClass : BoundedContinuousMapClass 𝓢(E, F) E F where
  __ := instContinuousMapClass
  map_bounded := fun f ↦ ⟨2 * (SchwartzMap.seminorm ℝ 0 0) f,
    (BoundedContinuousFunction.dist_le_two_norm' (norm_le_seminorm ℝ f))⟩

/-- Schwartz functions as bounded continuous functions -/
def toBoundedContinuousFunction (f : 𝓢(E, F)) : E →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup f (SchwartzMap.continuous f)
    (SchwartzMap.seminorm ℝ 0 0 f) (norm_le_seminorm ℝ f)

@[simp]
theorem toBoundedContinuousFunction_apply (f : 𝓢(E, F)) (x : E) :
    f.toBoundedContinuousFunction x = f x :=
  rfl

/-- Schwartz functions as continuous functions -/
def toContinuousMap (f : 𝓢(E, F)) : C(E, F) :=
  f.toBoundedContinuousFunction.toContinuousMap

variable (𝕜 E F)
variable [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The inclusion map from Schwartz functions to bounded continuous functions as a continuous linear
map. -/
def toBoundedContinuousFunctionCLM : 𝓢(E, F) →L[𝕜] E →ᵇ F :=
  mkCLMtoNormedSpace toBoundedContinuousFunction (by intro f g; ext; exact add_apply)
    (by intro a f; ext; exact smul_apply)
    (⟨{0}, 1, zero_le_one, by
      simpa [BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)

@[simp]
theorem toBoundedContinuousFunctionCLM_apply (f : 𝓢(E, F)) (x : E) :
    toBoundedContinuousFunctionCLM 𝕜 E F f x = f x :=
  rfl

end BoundedContinuousFunction

section ZeroAtInfty

open scoped ZeroAtInfty

variable [ProperSpace E]

instance instZeroAtInftyContinuousMapClass : ZeroAtInftyContinuousMapClass 𝓢(E, F) E F where
  __ := instContinuousMapClass
  zero_at_infty := by
    intro f
    apply zero_at_infty_of_norm_le
    intro ε hε
    use (SchwartzMap.seminorm ℝ 1 0) f / ε
    intro x hx
    rw [div_lt_iff₀ hε] at hx
    have hxpos : 0 < ‖x‖ := by
      rw [norm_pos_iff]
      intro hxzero
      simp only [hxzero, norm_zero, zero_mul, ← not_le] at hx
      exact hx (apply_nonneg (SchwartzMap.seminorm ℝ 1 0) f)
    have := norm_pow_mul_le_seminorm ℝ f 1 x
    rw [pow_one, ← le_div_iff₀' hxpos] at this
    apply lt_of_le_of_lt this
    rwa [div_lt_iff₀' hxpos]

/-- Schwartz functions as continuous functions vanishing at infinity. -/
def toZeroAtInfty (f : 𝓢(E, F)) : C₀(E, F) where
  toFun := f
  zero_at_infty' := zero_at_infty f

@[simp] theorem toZeroAtInfty_apply (f : 𝓢(E, F)) (x : E) : f.toZeroAtInfty x = f x :=
  rfl

@[simp] theorem toZeroAtInfty_toBCF (f : 𝓢(E, F)) :
    f.toZeroAtInfty.toBCF = f.toBoundedContinuousFunction :=
  rfl

variable (𝕜 E F)
variable [RCLike 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The inclusion map from Schwartz functions to continuous functions vanishing at infinity as a
continuous linear map. -/
def toZeroAtInftyCLM : 𝓢(E, F) →L[𝕜] C₀(E, F) :=
  mkCLMtoNormedSpace toZeroAtInfty (by intro f g; ext; exact add_apply)
    (by intro a f; ext; exact smul_apply)
    (⟨{0}, 1, zero_le_one, by simpa [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_le (apply_nonneg _ _)] using norm_le_seminorm 𝕜 ⟩)

@[simp] theorem toZeroAtInftyCLM_apply (f : 𝓢(E, F)) (x : E) : toZeroAtInftyCLM 𝕜 E F f x = f x :=
  rfl

end ZeroAtInfty

section Lp

/-! ### Inclusion into L^p space -/

open MeasureTheory
open scoped NNReal ENNReal

variable [NormedAddCommGroup D] [MeasurableSpace D] [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

variable (𝕜 F) in
/-- The `L^p` norm of a Schwartz function is controlled by a finite family of Schwartz seminorms.

The maximum index `k` and the constant `C` depend on `p` and `μ`.
-/
theorem eLpNorm_le_seminorm (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] :
    ∃ (k : ℕ) (C : ℝ≥0), ∀ (f : 𝓢(E, F)), eLpNorm f p μ ≤
      C * ENNReal.ofReal ((Finset.Iic (k, 0)).sup (schwartzSeminormFamily 𝕜 E F) f) := by
  -- Apply Hölder's inequality `‖f‖_p ≤ ‖f₁‖_p * ‖f₂‖_∞` to obtain the `L^p` norm of `f = f₁ • f₂`
  -- using `f₁ = (1 + ‖x‖) ^ (-k)` and `f₂ = (1 + ‖x‖) ^ k • f x`.
  rcases hμ.exists_eLpNorm_lt_top p with ⟨k, hk⟩
  refine ⟨k, (eLpNorm (fun x ↦ (1 + ‖x‖) ^ (-k : ℝ)) p μ).toNNReal * 2 ^ k, fun f ↦ ?_⟩
  have h_one_add (x : E) : 0 < 1 + ‖x‖ := lt_add_of_pos_of_le zero_lt_one (norm_nonneg x)
  calc eLpNorm (⇑f) p μ
  _ = eLpNorm ((fun x : E ↦ (1 + ‖x‖) ^ (-k : ℝ)) • fun x ↦ (1 + ‖x‖) ^ k • f x) p μ := by
    refine congrArg (eLpNorm · p μ) (funext fun x ↦ ?_)
    simp [(h_one_add x).ne']
  _ ≤ eLpNorm (fun x ↦ (1 + ‖x‖) ^ (-k : ℝ)) p μ * eLpNorm (fun x ↦ (1 + ‖x‖) ^ k • f x) ⊤ μ := by
    refine eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top p _ ?_
    refine Continuous.aestronglyMeasurable ?_
    exact .rpow_const (by fun_prop) fun x ↦ .inl (h_one_add x).ne'
  _ ≤ eLpNorm (fun x ↦ (1 + ‖x‖) ^ (-k : ℝ)) p μ *
      (2 ^ k * ENNReal.ofReal (((Finset.Iic (k, 0)).sup (schwartzSeminormFamily 𝕜 E F)) f)) := by
    gcongr
    refine eLpNormEssSup_le_of_ae_nnnorm_bound (ae_of_all μ fun x ↦ ?_)
    rw [← norm_toNNReal, Real.toNNReal_le_iff_le_coe]
    simpa [norm_smul, abs_of_nonneg (h_one_add x).le] using
      one_add_le_sup_seminorm_apply (m := (k, 0)) (le_refl k) (le_refl 0) f x
  _ = _ := by
    rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hk.ne]
    simp only [ENNReal.coe_pow, ENNReal.coe_ofNat]
    ring

/-- The `L^p` norm of a Schwartz function is finite. -/
theorem eLpNorm_lt_top (f : 𝓢(E, F)) (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : eLpNorm f p μ < ⊤ := by
  rcases eLpNorm_le_seminorm ℝ F p μ with ⟨k, C, hC⟩
  exact lt_of_le_of_lt (hC f) (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top)

variable [SecondCountableTopologyEither E F]

/-- Schwartz functions are in `L^∞`; does not require `hμ.HasTemperateGrowth`. -/
theorem memLp_top (f : 𝓢(E, F)) (μ : Measure E := by volume_tac) : MemLp f ⊤ μ := by
  rcases f.decay 0 0 with ⟨C, _, hC⟩
  refine memLp_top_of_bound f.continuous.aestronglyMeasurable C (ae_of_all μ fun x ↦ ?_)
  simpa using hC x

/-- Schwartz functions are in `L^p` for any `p`. -/
theorem memLp (f : 𝓢(E, F)) (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : MemLp f p μ :=
  ⟨f.continuous.aestronglyMeasurable, f.eLpNorm_lt_top p μ⟩

/-- Map a Schwartz function to an `Lp` function for any `p`. -/
def toLp (f : 𝓢(E, F)) (p : ℝ≥0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth] :
    Lp F p μ := (f.memLp p μ).toLp

theorem coeFn_toLp (f : 𝓢(E, F)) (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : f.toLp p μ =ᵐ[μ] f := (f.memLp p μ).coeFn_toLp

theorem norm_toLp {f : 𝓢(E, F)} {p : ℝ≥0∞} {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    ‖f.toLp p μ‖ = ENNReal.toReal (eLpNorm f p μ) := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_toLp f p μ)]

theorem injective_toLp (p : ℝ≥0∞) (μ : Measure E := by volume_tac) [hμ : μ.HasTemperateGrowth]
    [μ.IsOpenPosMeasure] : Function.Injective (fun f : 𝓢(E, F) ↦ f.toLp p μ) :=
  fun f g ↦ by simpa [toLp] using (Continuous.ae_eq_iff_eq μ f.continuous g.continuous).mp

variable (𝕜 F) in
theorem norm_toLp_le_seminorm (p : ℝ≥0∞) (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] :
    ∃ k C, 0 ≤ C ∧ ∀ (f : 𝓢(E, F)), ‖f.toLp p μ‖ ≤
      C * (Finset.Iic (k, 0)).sup (schwartzSeminormFamily 𝕜 E F) f := by
  rcases eLpNorm_le_seminorm 𝕜 F p μ with ⟨k, C, hC⟩
  refine ⟨k, C, C.coe_nonneg, fun f ↦ ?_⟩
  rw [norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by simp [mul_nonneg]) ?_
  rw [ENNReal.ofReal_mul NNReal.zero_le_coe]
  simpa using hC f

variable (𝕜 F) in
/-- Continuous linear map from Schwartz functions to `L^p`. -/
def toLpCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (μ : Measure E := by volume_tac)
    [hμ : μ.HasTemperateGrowth] : 𝓢(E, F) →L[𝕜] Lp F p μ :=
  mkCLMtoNormedSpace (fun f ↦ f.toLp p μ) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) <| by
    rcases norm_toLp_le_seminorm 𝕜 F p μ with ⟨k, C, hC_pos, hC⟩
    exact ⟨Finset.Iic (k, 0), C, hC_pos, hC⟩

@[simp] theorem toLpCLM_apply {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth]
    {f : 𝓢(E, F)} : toLpCLM 𝕜 F p μ f = f.toLp p μ := rfl

@[fun_prop]
theorem continuous_toLp {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth] :
    Continuous (fun f : 𝓢(E, F) ↦ f.toLp p μ) := (toLpCLM ℝ F p μ).continuous

/-- Schwartz functions are dense in `Lp`. -/
theorem denseRange_toLpCLM [FiniteDimensional ℝ E] [BorelSpace E] {p : ℝ≥0∞} (hp : p ≠ ⊤)
    [hp' : Fact (1 ≤ p)] {μ : Measure E} [hμ : μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ] :
    DenseRange (SchwartzMap.toLpCLM ℝ F p μ) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := MemLp.exist_eLpNorm_sub_le hp hp'.out (Lp.memLp f) hε
  use (hg₁.toSchwartzMap hg₂).toLp p μ
  have : (f : E → F) - ((hg₁.toSchwartzMap hg₂).toLp p μ : E → F) =ᶠ[ae μ] (f : E → F) - g := by
    filter_upwards [(hg₁.toSchwartzMap hg₂).coeFn_toLp p μ]
    simp
  simp only [Set.mem_range, toLpCLM_apply, exists_apply_eq_apply, Metric.mem_closedBall', true_and,
    Lp.dist_def, eLpNorm_congr_ae this]
  grw [hg₃, ENNReal.toReal_ofReal hε.le]
  simp

end Lp

section L2

open MeasureTheory

variable [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

@[simp]
theorem inner_toL2_toL2_eq (f g : 𝓢(H, V)) (μ : Measure H := by volume_tac) [μ.HasTemperateGrowth] :
    inner ℂ (f.toLp 2 μ) (g.toLp 2 μ) = ∫ x, inner ℂ (f x) (g x) ∂μ := by
  apply integral_congr_ae
  have hf_ae := f.coeFn_toLp 2 μ
  have hg_ae := g.coeFn_toLp 2 μ
  filter_upwards [hf_ae, hg_ae] with _ hf hg
  rw [hf, hg]

end L2

end SchwartzMap
