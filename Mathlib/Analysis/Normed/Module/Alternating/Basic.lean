/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov, Heather Macbeth, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Module.Alternating.Topology
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Operator norm on the space of continuous alternating maps

In this file we show that continuous alternating maps
from a seminormed space to a (semi)normed space form a (semi)normed space.
We also prove basic facts about this norm
and define bundled versions of some operations on continuous alternating maps.

Most proofs just invoke the corresponding fact about continuous multilinear maps.
-/

@[expose] public section

noncomputable section

open scoped NNReal
open Finset Metric

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a nontrivially normed field;
* `ι`: a finite index type;
* `E`, `F`, `G`: (semi)normed vector spaces over `𝕜`.
-/

/-- Applying a continuous alternating map to a vector is continuous
in the pair (map, vector).

Continuity in the vector holds by definition
and continuity in the map holds if both the domain and the codomain are topological vector spaces.
However, continuity in the pair (map, vector) needs the domain to be a locally bounded TVS.
We have no typeclass for a locally bounded TVS,
so we require it to be a seminormed space instead. -/
instance ContinuousAlternatingMap.instContinuousEval {𝕜 ι E F : Type*}
    [NormedField 𝕜] [Finite ι] [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [Module 𝕜 F] :
    ContinuousEval (E [⋀^ι]→L[𝕜] F) (ι → E) F :=
  .of_continuous_forget continuous_toContinuousMultilinearMap

section Seminorm

universe u wE wF wG v
variable {𝕜 : Type u} {n : ℕ} {E : Type wE} {F : Type wF} {G : Type wG} {ι : Type v}
  [NontriviallyNormedField 𝕜]
  [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E]
  [NormPseudoMetric F] [AddCommGroup F] [IsNormedAddGroup F] [NormedSpace 𝕜 F]
  [NormPseudoMetric G] [AddCommGroup G] [IsNormedAddGroup G] [NormedSpace 𝕜 G]

/-!
### Continuity properties of alternating maps

We relate continuity of alternating maps to the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, in
both directions. Along the way, we prove useful bounds on the difference `‖f m₁ - f m₂‖`.
-/
namespace AlternatingMap

/-- If `f` is a continuous alternating map on `E`
and `m` is an element of `ι → E` such that one of the `m i` has norm `0`, then `f m` has norm `0`.

Note that we cannot drop the continuity assumption.
Indeed, let `ℝ₀` be a copy or `ℝ` with zero norm and indiscrete topology.
Then `f : (Unit → ℝ₀) → ℝ` given by `f x = x ()`
sends vector `1` with zero norm to number `1` with nonzero norm. -/
theorem norm_map_coord_zero (f : E [⋀^ι]→ₗ[𝕜] F) (hf : Continuous f)
    {m : ι → E} {i : ι} (hi : ‖m i‖ = 0) : ‖f m‖ = 0 :=
  f.1.norm_map_coord_zero hf hi

variable [Fintype ι]

/-- If an alternating map in finitely many variables on seminormed spaces
sends vectors with a component of norm zero to vectors of norm zero
and satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i`
for some positive numbers `ε i` and elements `c i : 𝕜`, `1 < ‖c i‖`,
then it satisfies this inequality for all `m`.

The first assumption is automatically satisfied on normed spaces, see `bound_of_shell` below.
For seminormed spaces, it follows from continuity of `f`,
see lemma `bound_of_shell_of_continuous` below. -/
theorem bound_of_shell_of_norm_map_coord_zero (f : E [⋀^ι]→ₗ[𝕜] F)
    (hf₀ : ∀ {m i}, ‖m i‖ = 0 → ‖f m‖ = 0)
    {ε : ι → ℝ} {C : ℝ} (hε : ∀ i, 0 < ε i) {c : ι → 𝕜} (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ι → E, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ι → E) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell_of_norm_map_coord_zero hf₀ hε hc hf m

/-- If a continuous alternating map in finitely many variables on normed spaces
satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`
on a shell `ε / ‖c‖ < ‖m i‖ < ε` for some positive number `ε` and an elements `c : 𝕜`, `1 < ‖c‖`,
then it satisfies this inequality for all `m`.

If the domain is a Hausdorff space, then the continuity assumption is redundant,
see `bound_of_shell` below. -/
theorem bound_of_shell_of_continuous (f : E [⋀^ι]→ₗ[𝕜] F) (hfc : Continuous f)
    {ε : ℝ} {C : ℝ} (hε : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ m : ι → E, (∀ i, ε / ‖c‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ι → E) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell_of_continuous hfc (fun _ ↦ hε) (fun _ ↦ hc) hf m

/-- If an alternating map in finitely many variables on a seminormed space is continuous,
then it satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`,
for some `C` which can be chosen to be positive. -/
theorem exists_bound_of_continuous (f : E [⋀^ι]→ₗ[𝕜] F) (hf : Continuous f) :
    ∃ (C : ℝ), 0 < C ∧ (∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :=
  f.1.exists_bound_of_continuous hf

/-- If an alternating map `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a precise but hard to use version.
See `AlternatingMap.norm_image_sub_le_of_bound` for a less precise but more usable version.
The bound reads
`‖f m - f m'‖ ≤
  C * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
theorem norm_image_sub_le_of_bound' [DecidableEq ι] (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound' hC H m₁ m₂

/-- If an alternating map `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a usable but not very precise version.
See `AlternatingMap.norm_image_sub_le_of_bound'` for a more precise but less usable version.
The bound is `‖f m - f m'‖ ≤ C * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
theorem norm_image_sub_le_of_bound (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ C * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound hC H m₁ m₂

/-- If an alternating map satisfies an inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`,
then it is continuous. -/
theorem continuous_of_bound (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    Continuous f :=
  f.toMultilinearMap.continuous_of_bound C H

/-- Construct a continuous alternating map
from an alternating map satisfying a boundedness condition. -/
def mkContinuous (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : E [⋀^ι]→L[𝕜] F :=
  { f with cont := f.continuous_of_bound C H }

@[simp] theorem coe_mkContinuous (f : E [⋀^ι]→ₗ[𝕜] F) (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    (f.mkContinuous C H : (ι → E) → F) = f :=
  rfl

end AlternatingMap

/-!
### Continuous alternating maps

We define the norm `‖f‖` of a continuous alternating map `f` in finitely many variables
as the smallest nonnegative number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`.
We show that this defines a normed space structure on `E [⋀^ι]→L[𝕜] F`.
-/

namespace ContinuousAlternatingMap

variable [Fintype ι] {f : E [⋀^ι]→L[𝕜] F} {m : ι → E}

theorem bound (f : E [⋀^ι]→L[𝕜] F) : ∃ (C : ℝ), 0 < C ∧ (∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :=
  f.toContinuousMultilinearMap.bound

instance instNormPseudoMetric : NormPseudoMetric (E [⋀^ι]→L[𝕜] F) where
  toPseudoMetricSpace := .induced toContinuousMultilinearMap inferInstance
  norm f := ‖f.toContinuousMultilinearMap‖

/-- Continuous alternating maps form a seminormed additive commutative group.
We override projection to `PseudoMetricSpace` to ensure that instances commute
in `with_reducible_and_instances`. -/
instance instIsNormedAddGroup : IsNormedAddGroup (E [⋀^ι]→L[𝕜] F) :=
  .induced _ _ (toMultilinearAddHom : E [⋀^ι]→L[𝕜] F →+ _)

@[simp] theorem norm_toContinuousMultilinearMap (f : E [⋀^ι]→L[𝕜] F) : ‖f.1‖ = ‖f‖ := rfl
@[simp] theorem nnnorm_toContinuousMultilinearMap (f : E [⋀^ι]→L[𝕜] F) : ‖f.1‖₊ = ‖f‖₊ := rfl
@[simp] theorem enorm_toContinuousMultilinearMap (f : E [⋀^ι]→L[𝕜] F) : ‖f.1‖ₑ = ‖f‖ₑ := rfl

/-- The inclusion of `E [⋀^ι]→L[𝕜] F` into `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F`
as a linear isometry. -/
@[simps!]
def toContinuousMultilinearMapLI :
    E [⋀^ι]→L[𝕜] F →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F where
  toLinearMap := toContinuousMultilinearMapLinear
  norm_map' _ := rfl

theorem norm_def (f : E [⋀^ι]→L[𝕜] F) :
    ‖f‖ = sInf {c : ℝ | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
  rfl

theorem bounds_nonempty :
    ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
  ContinuousMultilinearMap.bounds_nonempty

theorem bounds_bddBelow {f : E [⋀^ι]→L[𝕜] F} :
    BddBelow {c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
  ContinuousMultilinearMap.bounds_bddBelow

theorem isLeast_opNorm (f : E [⋀^ι]→L[𝕜] F) :
    IsLeast {c : ℝ | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} ‖f‖ :=
  f.1.isLeast_opNorm

/-- The fundamental property of the operator norm of a continuous alternating map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`. -/
theorem le_opNorm (f : E [⋀^ι]→L[𝕜] F) (m : ι → E) : ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ := f.1.le_opNorm m

theorem le_mul_prod_of_opNorm_le_of_le
    {m : ι → E} {C : ℝ} {b : ι → ℝ} (hC : ‖f‖ ≤ C) (hm : ∀ i, ‖m i‖ ≤ b i) :
    ‖f m‖ ≤ C * ∏ i, b i :=
  f.1.le_mul_prod_of_opNorm_le_of_le hC hm

theorem le_opNorm_mul_prod_of_le (f : E [⋀^ι]→L[𝕜] F) {b : ι → ℝ} (hm : ∀ i, ‖m i‖ ≤ b i) :
    ‖f m‖ ≤ ‖f‖ * ∏ i, b i :=
  f.1.le_opNorm_mul_prod_of_le hm

theorem le_opNorm_mul_pow_card_of_le (f : E [⋀^ι]→L[𝕜] F) {m b} (hm : ‖m‖ ≤ b) :
    ‖f m‖ ≤ ‖f‖ * b ^ Fintype.card ι :=
  f.1.le_opNorm_mul_pow_card_of_le hm

theorem le_opNorm_mul_pow_of_le {n} (f : E [⋀^Fin n]→L[𝕜] F) {m b} (hm : ‖m‖ ≤ b) :
    ‖f m‖ ≤ ‖f‖ * b ^ n :=
  f.1.le_opNorm_mul_pow_of_le hm

theorem le_of_opNorm_le {C : ℝ} (h : ‖f‖ ≤ C) (m : ι → E) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.le_of_opNorm_le h m

theorem ratio_le_opNorm (f : E [⋀^ι]→L[𝕜] F) (m : ι → E) : ‖f m‖ / ∏ i, ‖m i‖ ≤ ‖f‖ :=
  f.1.ratio_le_opNorm m

/-- The image of the unit ball under a continuous alternating map is bounded. -/
theorem unit_le_opNorm (f : E [⋀^ι]→L[𝕜] F) (h : ‖m‖ ≤ 1) : ‖f m‖ ≤ ‖f‖ := f.1.unit_le_opNorm h

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
theorem opNorm_le_bound (f : E [⋀^ι]→L[𝕜] F) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ m, ‖f m‖ ≤ M * ∏ i, ‖m i‖) : ‖f‖ ≤ M :=
  f.1.opNorm_le_bound hMp hM

theorem opNorm_le_iff {C : ℝ} (hC : 0 ≤ C) : ‖f‖ ≤ C ↔ ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.opNorm_le_iff hC

/-- The fundamental property of the operator norm of a continuous alternating map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`, `nnnorm` version. -/
theorem le_opNNNorm (f : E [⋀^ι]→L[𝕜] F) (m : ι → E) : ‖f m‖₊ ≤ ‖f‖₊ * ∏ i, ‖m i‖₊ :=
  f.1.le_opNNNorm m

theorem le_of_opNNNorm_le {C : ℝ≥0} (h : ‖f‖₊ ≤ C) (m : ι → E) : ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ :=
  f.1.le_of_opNNNorm_le h m

theorem opNNNorm_le_iff {C : ℝ≥0} : ‖f‖₊ ≤ C ↔ ∀ m, ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ :=
  f.1.opNNNorm_le_iff

theorem isLeast_opNNNorm (f : E [⋀^ι]→L[𝕜] F) :
    IsLeast {C : ℝ≥0 | ∀ m, ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊} ‖f‖₊ :=
  f.1.isLeast_opNNNorm

theorem opNNNorm_prod (f : E [⋀^ι]→L[𝕜] F) (g : E [⋀^ι]→L[𝕜] G) :
    ‖f.prod g‖₊ = max (‖f‖₊) (‖g‖₊) :=
  f.1.opNNNorm_prod g.1

theorem opNorm_prod (f : E [⋀^ι]→L[𝕜] F) (g : E [⋀^ι]→L[𝕜] G) : ‖f.prod g‖ = max (‖f‖) (‖g‖) :=
  f.1.opNorm_prod g.1

theorem opNNNorm_pi {ι' : Type*} [Fintype ι'] {F : ι' → Type*} [∀ i', NormPseudoMetric (F i')] [∀ i', AddCommGroup (F i')] [∀ i', IsNormedAddGroup (F i')]
    [∀ i', NormedSpace 𝕜 (F i')] (f : ∀ i', E [⋀^ι]→L[𝕜] F i') : ‖pi f‖₊ = ‖f‖₊ :=
  ContinuousMultilinearMap.opNNNorm_pi fun i ↦ (f i).1

theorem opNorm_pi {ι' : Type*} [Fintype ι'] {F : ι' → Type*} [∀ i', NormPseudoMetric (F i')] [∀ i', AddCommGroup (F i')] [∀ i', IsNormedAddGroup (F i')]
    [∀ i', NormedSpace 𝕜 (F i')] (f : ∀ i', E [⋀^ι]→L[𝕜] F i') : ‖pi f‖ = ‖f‖ :=
  ContinuousMultilinearMap.opNorm_pi fun i ↦ (f i).1

instance instNormedSpace {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass 𝕜 𝕜' F] :
    NormedSpace 𝕜' (E [⋀^ι]→L[𝕜] F) :=
  ⟨fun c f ↦ f.1.opNorm_smul_le c⟩

section

@[simp] theorem norm_ofSubsingleton [Subsingleton ι] (i : ι) (f : E →L[𝕜] F) :
    ‖ofSubsingleton 𝕜 E F i f‖ = ‖f‖ :=
  ContinuousMultilinearMap.norm_ofSubsingleton i f

@[simp] theorem nnnorm_ofSubsingleton [Subsingleton ι] (i : ι) (f : E →L[𝕜] F) :
    ‖ofSubsingleton 𝕜 E F i f‖₊ = ‖f‖₊ :=
  NNReal.eq <| norm_ofSubsingleton i f

/-- `ContinuousAlternatingMap.ofSubsingleton` as a linear isometry. -/
@[simps +simpRhs]
def ofSubsingletonLIE [Subsingleton ι] (i : ι) : (E →L[𝕜] F) ≃ₗᵢ[𝕜] (E [⋀^ι]→L[𝕜] F) where
  __ := ofSubsingleton 𝕜 E F i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := norm_ofSubsingleton i

theorem norm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 E E i (.id _ _)‖ ≤ 1 :=
  ContinuousMultilinearMap.norm_ofSubsingleton_id_le ..

theorem nnnorm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 E E i (.id _ _)‖₊ ≤ 1 :=
  ContinuousMultilinearMap.nnnorm_ofSubsingleton_id_le ..

variable (𝕜 E)

@[simp] theorem norm_constOfIsEmpty [IsEmpty ι] (x : F) : ‖constOfIsEmpty 𝕜 E ι x‖ = ‖x‖ :=
  ContinuousMultilinearMap.norm_constOfIsEmpty _ _ _

@[simp] theorem nnnorm_constOfIsEmpty [IsEmpty ι] (x : F) : ‖constOfIsEmpty 𝕜 E ι x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_constOfIsEmpty _ _ _

variable (ι F) in
/-- `constOfIsEmpty` as a linear isometry equivalence. -/
@[simps]
def constOfIsEmptyLIE [IsEmpty ι] : F ≃ₗᵢ[𝕜] (E [⋀^ι]→L[𝕜] F) where
  toFun := constOfIsEmpty _ _ _
  invFun f := f 0
  left_inv x := by simp
  right_inv f := by ext x; simp [Subsingleton.allEq x 0]
  map_add' f g := rfl
  map_smul' c f := rfl
  norm_map' := norm_constOfIsEmpty _ _

end

variable (𝕜 E F G) in
/-- `ContinuousAlternatingMap.prod` as a `LinearIsometryEquiv`. -/
@[simps]
def prodLIE : (E [⋀^ι]→L[𝕜] F) × (E [⋀^ι]→L[𝕜] G) ≃ₗᵢ[𝕜] (E [⋀^ι]→L[𝕜] (F × G)) where
  toFun f := f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst 𝕜 F G).compContinuousAlternatingMap f,
    (ContinuousLinearMap.snd 𝕜 F G).compContinuousAlternatingMap f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' f := opNorm_prod f.1 f.2

variable (𝕜 E) in
/-- `ContinuousAlternatingMap.pi` as a `LinearIsometryEquiv`. -/
@[simps!]
def piLIE {ι' : Type*} [Fintype ι'] {F : ι' → Type*} [∀ i', NormPseudoMetric (F i')] [∀ i', AddCommGroup (F i')] [∀ i', IsNormedAddGroup (F i')]
    [∀ i', NormedSpace 𝕜 (F i')] :
    (∀ i', E [⋀^ι]→L[𝕜] F i') ≃ₗᵢ[𝕜] (E [⋀^ι]→L[𝕜] (∀ i, F i)) where
  toLinearEquiv := piLinearEquiv
  norm_map' := opNorm_pi

section restrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' F] [IsScalarTower 𝕜' 𝕜 F]
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]

@[simp] theorem norm_restrictScalars : ‖f.restrictScalars 𝕜'‖ = ‖f‖ := rfl

variable (𝕜')

/-- `ContinuousAlternatingMap.restrictScalars` as a `LinearIsometry`. -/
@[simps]
def restrictScalarsLI : E [⋀^ι]→L[𝕜] F →ₗᵢ[𝕜'] E [⋀^ι]→L[𝕜'] F where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

end restrictScalars

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, precise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound reads
`‖f m - f m'‖ ≤
  ‖f‖ * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
theorem norm_image_sub_le' [DecidableEq ι] (f : E [⋀^ι]→L[𝕜] F) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.1.norm_image_sub_le' m₁ m₂

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`,
less precise version.
For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `‖f m - f m'‖ ≤ ‖f‖ * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
theorem norm_image_sub_le (f : E [⋀^ι]→L[𝕜] F) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.1.norm_image_sub_le m₁ m₂

end ContinuousAlternatingMap

variable [Fintype ι]

/-- If a continuous alternating map is constructed from an alternating map via the constructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem AlternatingMap.mkContinuous_norm_le (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ C :=
  f.toMultilinearMap.mkContinuous_norm_le hC H

/-- If a continuous alternating map is constructed from an alternating map via the constructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem AlternatingMap.mkContinuous_norm_le' (f : E [⋀^ι]→ₗ[𝕜] F) {C : ℝ}
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ max C 0 :=
  ContinuousMultilinearMap.opNorm_le_bound (le_max_right _ _) fun m ↦ (H m).trans <| by
    gcongr
    apply le_max_left

namespace ContinuousLinearMap

theorem norm_compContinuousAlternatingMap_le (g : F →L[𝕜] G) (f : E [⋀^ι]→L[𝕜] F) :
    ‖g.compContinuousAlternatingMap f‖ ≤ ‖g‖ * ‖f‖ :=
  g.norm_compContinuousMultilinearMap_le f.1

/-- Flip arguments in `f : F →L[𝕜] E [⋀^ι]→L[𝕜] G` to get `⋀^ι⟮𝕜; E; F →L[𝕜] G⟯` -/
@[simps! apply_apply]
def flipAlternating (f : F →L[𝕜] (E [⋀^ι]→L[𝕜] G)) : E [⋀^ι]→L[𝕜] (F →L[𝕜] G) where
  toContinuousMultilinearMap :=
    ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜).comp f).flipMultilinear
  map_eq_zero_of_eq' v i j hv hne := by ext x; simp [(f x).map_eq_zero_of_eq v hv hne]

end ContinuousLinearMap

theorem LinearIsometry.norm_compContinuousAlternatingMap (g : F →ₗᵢ[𝕜] G) (f : E [⋀^ι]→L[𝕜] F) :
    ‖g.toContinuousLinearMap.compContinuousAlternatingMap f‖ = ‖f‖ :=
  g.norm_compContinuousMultilinearMap f.1

open ContinuousAlternatingMap

section

namespace ContinuousAlternatingMap

theorem norm_compContinuousLinearMap_le (f : F [⋀^ι]→L[𝕜] G)
    (g : E →L[𝕜] F) : ‖f.compContinuousLinearMap g‖ ≤ ‖f‖ * (‖g‖ ^ Fintype.card ι) :=
  (f.1.norm_compContinuousLinearMap_le _).trans_eq <| by simp

omit [Fintype ι] in
theorem continuous_compContinuousLinearMapCLM [Finite ι] :
    Continuous
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) := by
  rcases nonempty_fintype ι
  refine UniformConvergenceCLM.isUniformInducing_postcomp (.id 𝕜)
    (toContinuousMultilinearMapCLM 𝕜 : (E [⋀^ι]→L[𝕜] G) →L[𝕜] _)
    isUniformEmbedding_toContinuousMultilinearMap.isUniformInducing _ |>.isInducing
    |>.continuous_iff |>.mpr ?_
  change Continuous <|
    (toContinuousMultilinearMapCLM 𝕜 : (F [⋀^ι]→L[𝕜] G) →L[𝕜] _).precomp _ ∘
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
        (fun _ : ι ↦ E) (fun _ ↦ F) G ∘
      (fun f _ ↦ f)
  fun_prop

variable [DecidableEq ι]

/-- Fréchet derivative of `compContinuousLinearMap f g` with respect to `g`.

Recall that `compContinuousLinearMap f g` is the pullback of `f : F [⋀^ι]→L[𝕜] G`
along `g : E →L[𝕜] F`.

This function is linear in `f`, so its derivative with respect to `f`
is given by `compContinuousLinearMapCLM f g`.

The derivative with respect to `g` is given by
`f.fderivCompContinuousLinearMap g dg v = ∑ i, f fun j ↦ Function.update (fun _ ↦ g) i dg j (v j)`,
see `fderivCompContinuousLinearMap_apply` below.
-/
def fderivCompContinuousLinearMap (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F) :
    (E →L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] G) :=
  liftCLM (f.1.fderivCompContinuousLinearMap (fun _ : ι ↦ g) ∘L .pi fun _ ↦ .id _ _) <| by
    intro dg v a b heq hne
    trans ∑ i, f fun j ↦ Function.update (fun _ ↦ g) i dg j (v j)
    · simp
    · rw [← Finset.sum_add_sum_compl {a, b}, Finset.sum_pair hne, Finset.sum_eq_zero, add_zero]
      · convert f.map_add_swap _ hne with i
        rcases eq_or_ne i a with rfl | hia
        · simp [heq, hne, hne.symm]
        · rcases eq_or_ne i b with rfl | hib
          · simp [Function.update_apply, heq]
          · simp [Function.update_apply, Equiv.swap_apply_of_ne_of_ne, *]
      · simp only [mem_compl, mem_insert, mem_singleton, not_or, and_imp]
        intro i hia hib
        apply f.map_eq_zero_of_eq _ _ hne
        simp [*, Ne.symm]

@[simp]
lemma toContinuousMultilinearMapCLM_comp_fderivCompContinuousLinearMap
    (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F) :
    toContinuousMultilinearMapCLM 𝕜 ∘L f.fderivCompContinuousLinearMap g =
      f.1.fderivCompContinuousLinearMap (fun _ : ι ↦ g) ∘L .pi fun _ ↦ .id _ _ :=
  rfl

@[simp]
lemma fderivCompContinuousLinearMap_apply (f : F [⋀^ι]→L[𝕜] G) (g dg : E →L[𝕜] F) (v : ι → E) :
    f.fderivCompContinuousLinearMap g dg v =
      ∑ i, f fun j ↦ Function.update (fun _ ↦ g) i dg j (v j) := by
  simp [fderivCompContinuousLinearMap]

@[nontriviality]
lemma fderivCompContinuousLinearMap_of_isEmpty [IsEmpty ι] :
    fderivCompContinuousLinearMap (ι := ι) (𝕜 := 𝕜) (E := E) (F := F) (G := G) = 0 := by
  ext; simp

variable (G) in
/-- `fderivCompContinuousLinearMap` as a continuous linear map -/
def fderivCompContinuousLinearMapCLM (g : E →L[𝕜] F) :
    (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E →L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] G) :=
  LinearMap.mkContinuous
    { toFun := (fderivCompContinuousLinearMap · g)
      map_add' f₁ f₂ := by ext; simp [Finset.sum_add_distrib]
      map_smul' c f := by ext; simp [Finset.smul_sum] }
    (Fintype.card ι * ‖g‖ ^ (Fintype.card ι - 1))
    fun f ↦ by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun dg ↦ ?_
      refine opNorm_le_bound _ (by positivity) fun v ↦ ?_
      simp? [mul_assoc] says
        simp only [LinearMap.coe_mk, AddHom.coe_mk, fderivCompContinuousLinearMap_apply, mul_assoc]
      refine (norm_sum_le _ _).trans ?_
      grw [← nsmul_eq_mul]
      apply Finset.sum_le_card_nsmul
      rintro i -
      grw [le_opNorm]
      simp only [Fintype.prod_eq_mul_prod_compl i, Function.update_self, mul_left_comm (‖g‖ ^ _)]
      grw [dg.le_opNorm, mul_assoc]
      gcongr
      rw [← Finset.card_singleton i, ← Finset.card_compl, ← Finset.prod_const,
        ← Finset.prod_mul_distrib]
      gcongr with j hj
      simpa [Function.update_of_ne (by simpa using hj)] using g.le_opNorm _

@[simp]
lemma fderivCompContinuousLinearMapCLM_apply (f : F [⋀^ι]→L[𝕜] G) (g : E →L[𝕜] F) :
    fderivCompContinuousLinearMapCLM G g f = fderivCompContinuousLinearMap f g :=
  rfl

end ContinuousAlternatingMap

end

open ContinuousAlternatingMap

namespace AlternatingMap

/-- Given a map `f : F →ₗ[𝕜] E [⋀^ι]→ₗ[𝕜] G` and an estimate
`H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖`, construct a continuous linear
map from `F` to `E [⋀^ι]→L[𝕜] G`.

In order to lift, e.g., a map `f : (E [⋀^ι]→ₗ[𝕜] F) →ₗ[𝕜] E' [⋀^ι]→ₗ[𝕜] G`
to a map `(E [⋀^ι]→L[𝕜] F) →L[𝕜] E' [⋀^ι]→L[𝕜] G`,
one can apply this construction to `f.comp ContinuousAlternatingMap.toAlternatingMapLinear`
which is a linear map from `E [⋀^ι]→L[𝕜] F` to `E' [⋀^ι]→ₗ[𝕜] G`. -/
def mkContinuousLinear (f : F →ₗ[𝕜] E [⋀^ι]→ₗ[𝕜] G) (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : F →L[𝕜] E [⋀^ι]→L[𝕜] G :=
  LinearMap.mkContinuous
    { toFun x := (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' x y := by ext1; simp
      map_smul' c x := by ext1; simp }
    (max C 0) fun x ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact (mkContinuous_norm_le' _ _).trans_eq <| by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

theorem mkContinuousLinear_norm_le_max (f : F →ₗ[𝕜] E [⋀^ι]→ₗ[𝕜] G) (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ max C 0 :=
  LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

theorem mkContinuousLinear_norm_le (f : F →ₗ[𝕜] E [⋀^ι]→ₗ[𝕜] G) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ C :=
  (mkContinuousLinear_norm_le_max f C H).trans_eq (max_eq_left hC)

variable {ι' : Type*} [Fintype ι']

/-- Given a map `f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G)` and an estimate
`H : ∀ m m', ‖f m m'‖ ≤ C * ∏ i, ‖m i‖ * ∏ i, ‖m' i‖`, upgrade all `AlternatingMap`s in the type
to `ContinuousAlternatingMap`s. -/
def mkContinuousAlternating (f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G))
    (C : ℝ) (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    E [⋀^ι]→L[𝕜] (F [⋀^ι']→L[𝕜] G) :=
  mkContinuous
    { toFun m := mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_update_add' m i x y := by ext1; simp
      map_update_smul' m i c x := by ext1; simp
      map_eq_zero_of_eq' v i j hv hij := by
        ext v'
        have : f v = 0 := by simpa using f.map_eq_zero_of_eq' v i j hv hij
        simp [this] }
    (max C 0) fun m => by
      simp only [coe_mk, MultilinearMap.coe_mk]
      refine ((f m).mkContinuous_norm_le' _).trans_eq ?_
      rw [max_mul_of_nonneg, zero_mul]
      positivity

@[simp]
theorem mkContinuousAlternating_apply (f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G)) {C : ℝ}
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : ι → E) :
    ⇑(mkContinuousAlternating f C H m) = f m :=
  rfl

theorem mkContinuousAlternating_norm_le_max (f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G)) {C : ℝ}
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousAlternating f C H‖ ≤ max C 0 := by
  dsimp only [mkContinuousAlternating]
  exact mkContinuous_norm_le _ (le_max_right _ _) _

theorem mkContinuousAlternating_norm_le (f : E [⋀^ι]→ₗ[𝕜] (F [⋀^ι']→ₗ[𝕜] G)) {C : ℝ}
    (hC : 0 ≤ C) (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousAlternating f C H‖ ≤ C :=
  (mkContinuousAlternating_norm_le_max f H).trans_eq (max_eq_left hC)

end AlternatingMap

end Seminorm

section Norm

/-! Results that are only true if the target space is a `NormedAddCommGroup`
(and not just a `SeminormedAddCommGroup`). -/

universe u wE wF v
variable {𝕜 : Type u} {n : ℕ} {E : Type wE} {F : Type wF} {ι : Type v}
  [Fintype ι]
  [NontriviallyNormedField 𝕜]
  [NormPseudoMetric E] [AddCommGroup E] [IsNormedAddGroup E] [NormedSpace 𝕜 E]
  [NormMetric F] [AddCommGroup F] [IsNormedAddGroup F] [NormedSpace 𝕜 F]

namespace ContinuousAlternatingMap

instance instNormMetric : NormMetric (E [⋀^ι]→L[𝕜] F) :=
  NormMetric.ofAddSeparation fun _f hf ↦ toContinuousMultilinearMap_injective <| norm_eq_zero.mp hf

/-- Continuous alternating maps themselves form a normed group with respect to the operator norm. -/
example : NormedAddCommGroup (E [⋀^ι]→L[𝕜] F) where

variable (𝕜 F) in
theorem norm_ofSubsingleton_id [Subsingleton ι] [Nontrivial F] (i : ι) :
    ‖ofSubsingleton 𝕜 F F i (.id _ _)‖ = 1 :=
  ContinuousMultilinearMap.norm_ofSubsingleton_id 𝕜 F i

variable (𝕜 F) in
theorem nnnorm_ofSubsingleton_id [Subsingleton ι] [Nontrivial F] (i : ι) :
    ‖ofSubsingleton 𝕜 F F i (.id _ _)‖₊ = 1 :=
  NNReal.eq <| norm_ofSubsingleton_id ..

end ContinuousAlternatingMap

namespace AlternatingMap

/-- If an alternating map in finitely many variables on a normed space satisfies the inequality
`‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` for some positive numbers `ε i`
and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequality for all `m`. -/
theorem bound_of_shell (f : F [⋀^ι]→ₗ[𝕜] E) {ε : ι → ℝ} {C : ℝ} {c : ι → 𝕜}
    (hε : ∀ i, 0 < ε i) (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ι → F, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ι → F) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.bound_of_shell hε hc hf m

end AlternatingMap

end Norm
