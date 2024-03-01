/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov, Heather Macbeth, Patrick Massot
-/
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.NormedSpace.Multilinear.Basic

/-!
# Operator norm on the space of continuous alternating maps

-/

noncomputable section

open scoped BigOperators NNReal
open Finset Metric

/-!
### Type variables

We use the following type variables in this file:

* `𝕜` : a `NontriviallyNormedField`;
* `ι`, `ι'` : finite index types with decidable equality;
* `E`, `E₁` : families of normed vector spaces over `𝕜` indexed by `i : ι`;
* `E'` : a family of normed vector spaces over `𝕜` indexed by `i' : ι'`;
* `Ei` : a family of normed vector spaces over `𝕜` indexed by `i : Fin (Nat.succ n)`;
* `G`, `G'` : normed vector spaces over `𝕜`.
-/

universe u v v' wE wE₁ wE' wEi wG wG'
variable {𝕜 : Type u} {n : ℕ}
  {E : Type wE} {E₁ : Type wE₁} {E' : Type wE'} {Ei : Type wEi}
  {G : Type wG} {G' : Type wG'} {ι : Type v} {ι' : Type v'}
  [Fintype ι] [Fintype ι'] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup Ei] [NormedSpace 𝕜 Ei]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-!
### Continuity properties of alternating maps

We relate continuity of alternating maps to the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, in
both directions. Along the way, we prove useful bounds on the difference `‖f m₁ - f m₂‖`.
-/
namespace AlternatingMap

variable (f : E [Λ^ι]→ₗ[𝕜] G)

/-- If an alternating map in finitely many variables on normed spaces satisfies the inequality
`‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε / ‖c‖ < ‖m i‖ < ε` for some positive number `ε`
and an elements `c : 𝕜`, `1 < ‖c‖`, then it satisfies this inequality for all `m`. -/
lemma bound_of_shell {ε : ℝ} {C : ℝ} (hε : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ m : ι → E, (∀ i, ε / ‖c‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ι → E) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.toMultilinearMap.bound_of_shell (fun _ ↦ hε) (fun _ ↦ hc) hf m

/-- If a alternating map in finitely many variables on normed spaces is continuous,
then it satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`,
for some `C` which can be chosen to be positive. -/
theorem exists_bound_of_continuous (hf : Continuous f) :
    ∃ (C : ℝ), 0 < C ∧ (∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :=
  f.toMultilinearMap.exists_bound_of_continuous hf

/-- If `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a precise but hard to use version.
See `AlternatingMap.norm_image_sub_le_of_bound` for a less precise but more usable version.
The bound reads
`‖f m - f m'‖ ≤
  C * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
lemma norm_image_sub_le_of_bound' [DecidableEq ι] {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound' hC H m₁ m₂

/-- If `f` satisfies a boundedness property around `0`,
one can deduce a bound on `f m₁ - f m₂` using the multilinearity.
Here, we give a usable but not very precise version.
See `AlternatingMap.norm_image_sub_le_of_bound'` for a more precise but less usable version.
The bound is `‖f m - f m'‖ ≤ C * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
lemma norm_image_sub_le_of_bound {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ C * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound hC H m₁ m₂

/-- If an alternating map satisfies an inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`,
then it is continuous. -/
theorem continuous_of_bound (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    Continuous f :=
  f.toMultilinearMap.continuous_of_bound C H

/-- Constructing a continuous alternating map from a alternating map
satisfying a boundedness condition. -/
def mkContinuous (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : E [Λ^ι]→L[𝕜] G :=
  { f with cont := f.continuous_of_bound C H }

@[simp] lemma coe_mk_continuous (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :
    (f.mkContinuous C H : (ι → E) → G) = f :=
  rfl

end AlternatingMap

/-!
### Continuous alternating maps

We define the norm `‖f‖` of a continuous alternating map `f` in finitely many variables as the
smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`. We show that this
defines a normed space structure on `ContinuousMultilinearMap 𝕜 E G`.
-/

namespace ContinuousAlternatingMap

variable (c : 𝕜) (f g : E [Λ^ι]→L[𝕜] G) (m : ι → E)

theorem bound : ∃ (C : ℝ), 0 < C ∧ (∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) :=
  f.toContinuousMultilinearMap.bound

instance : NormedAddCommGroup (E [Λ^ι]→L[𝕜] G) :=
  NormedAddCommGroup.induced _ _
    (toMultilinearAddHom : E [Λ^ι]→L[𝕜] G →+ _)
    toContinuousMultilinearMap_injective

@[simp] lemma norm_toContinuousMultilinearMap : ‖f.1‖ = ‖f‖ := rfl

/-- The inclusion of `E [Λ^ι]→L[𝕜] G` into `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G`
as a linear isometry. -/
@[simps!] def toContinuousMultilinearMapLinearIsometry :
    E [Λ^ι]→L[𝕜] G →ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G :=
  { (toContinuousMultilinearMapLinear :
      E [Λ^ι]→L[𝕜] G →ₗ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G) with
    norm_map' := fun _ ↦ rfl }

lemma embedding_toContinuousMultilinearMap :
    Embedding (toContinuousMultilinearMap : E [Λ^ι]→L[𝕜] G →
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G) :=
  toContinuousMultilinearMap_injective.embedding_induced

lemma uniformEmbedding_toContinuousMultilinearMap :
    UniformEmbedding (toContinuousMultilinearMap : E [Λ^ι]→L[𝕜] G →
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G) :=
  ⟨⟨rfl⟩, toContinuousMultilinearMap_injective⟩

lemma isClosed_range_toContinuousMultilinearMap :
    IsClosed (Set.range (toContinuousMultilinearMap : E [Λ^ι]→L[𝕜] G →
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G)) := by
  simp only [range_toContinuousMultilinearMap, Set.setOf_forall]
  repeat apply isClosed_iInter; intro
  exact isClosed_singleton.preimage (ContinuousMultilinearMap.continuous_eval_left _)

lemma closedEmbedding_toContinuousMultilinearMap :
    ClosedEmbedding (toContinuousMultilinearMap : E [Λ^ι]→L[𝕜] G →
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G) :=
  ⟨embedding_toContinuousMultilinearMap, isClosed_range_toContinuousMultilinearMap⟩

lemma continuous_toContinuousMultilinearMap :
    Continuous (toContinuousMultilinearMap : E [Λ^ι]→L[𝕜] G →
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G) :=
  embedding_toContinuousMultilinearMap.continuous

lemma norm_def : ‖f‖ = sInf {c | 0 ≤ (c : ℝ) ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} := rfl

-- So that invocations of `le_cInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : E [Λ^ι]→L[𝕜] G} :
    ∃ c, c ∈ {c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
  ContinuousMultilinearMap.bounds_nonempty

lemma bounds_bddBelow {f : E [Λ^ι]→L[𝕜] G} :
    BddBelow {c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} :=
  ContinuousMultilinearMap.bounds_bddBelow

/-- The fundamental property of the operator norm of a continuous alternating map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`. -/
theorem le_op_norm : ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ := f.1.le_op_norm m

theorem le_of_op_norm_le {C : ℝ} (h : ‖f‖ ≤ C) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.1.le_of_op_norm_le m h

theorem le_op_norm_of_le {C : ι → ℝ} (h : ∀ i, ‖m i‖ ≤ C i) : ‖f m‖ ≤ ‖f‖ * ∏ i, C i :=
  f.1.le_op_norm_mul_prod_of_le h

lemma ratio_le_op_norm : ‖f m‖ / ∏ i, ‖m i‖ ≤ ‖f‖ := f.1.ratio_le_op_norm m

/-- The image of the unit ball under a continuous alternating map is bounded. -/
lemma unit_le_op_norm (h : ‖m‖ ≤ 1) : ‖f m‖ ≤ ‖f‖ := f.1.unit_le_op_norm m h

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
lemma op_norm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ m, ‖f m‖ ≤ M * ∏ i, ‖m i‖) :
    ‖f‖ ≤ M :=
  f.1.op_norm_le_bound hMp hM

section

variable {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]

instance instNormedSpace : NormedSpace 𝕜' (E [Λ^ι]→L[𝕜] G) :=
  ⟨fun c f ↦ f.1.op_norm_smul_le c⟩

variable (𝕜')

/-- The inclusion of *alternating* continuous multi-linear maps into continuous multi-linear maps
as a continuous linear map. -/
@[simps!]
def toContinuousMultilinearMapL :
    E [Λ^ι]→L[𝕜] G →L[𝕜'] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) G :=
  ⟨toContinuousMultilinearMapLinear, continuous_induced_dom⟩

variable {𝕜'}

theorem le_op_norm_mul_prod_of_le {b : ι → ℝ} (hm : ∀ i, ‖m i‖ ≤ b i) : ‖f m‖ ≤ ‖f‖ * ∏ i, b i :=
  f.1.le_op_norm_mul_prod_of_le hm

theorem le_op_norm_mul_pow_card_of_le {b : ℝ} (hm : ‖m‖ ≤ b) : ‖f m‖ ≤ ‖f‖ * b ^ Fintype.card ι :=
  f.1.le_op_norm_mul_pow_card_of_le hm

theorem le_op_norm_mul_pow_of_le (f : E [Λ^Fin n]→L[𝕜] G) (m : Fin n → E) {b : ℝ} (hm : ‖m‖ ≤ b) :
    ‖f m‖ ≤ ‖f‖ * b ^ n :=
  f.1.le_op_norm_mul_pow_of_le hm

/-- The fundamental property of the operator norm of a continuous alternating map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`, `nnnorm` version. -/
theorem le_op_nnnorm : ‖f m‖₊ ≤ ‖f‖₊ * ∏ i, ‖m i‖₊ := f.1.le_op_nnnorm m

theorem le_of_op_nnnorm_le {C : ℝ≥0} (h : ‖f‖₊ ≤ C) : ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ :=
  f.1.le_of_op_nnnorm_le m h

lemma op_norm_prod (f : E [Λ^ι]→L[𝕜] G) (g : E [Λ^ι]→L[𝕜] G') :
    ‖f.prod g‖ = max (‖f‖) (‖g‖) :=
  f.1.op_norm_prod g.1

lemma op_norm_pi {ι' : Type v'} [Fintype ι'] {E' : ι' → Type wE'} [∀ i', NormedAddCommGroup (E' i')]
    [∀ i', NormedSpace 𝕜 (E' i')] (f : ∀ i', ContinuousAlternatingMap 𝕜 E (E' i') ι) :
    ‖pi f‖ = ‖f‖ :=
  ContinuousMultilinearMap.op_norm_pi fun i ↦ (f i).1

section

@[simp] lemma norm_of_subsingleton [Subsingleton ι] (i : ι) (f : E →L[𝕜] G) :
    ‖ofSubsingleton 𝕜 E G i f‖ = ‖f‖ :=
  ContinuousMultilinearMap.norm_ofSubsingleton i f

@[simp] lemma nnnorm_of_subsingleton [Subsingleton ι] (i : ι) (f : E →L[𝕜] G) :
    ‖ofSubsingleton 𝕜 E G i f‖₊ = ‖f‖₊ :=
  NNReal.eq <| norm_of_subsingleton i f

variable (𝕜 E)

@[simp] lemma norm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E ι x‖ = ‖x‖ :=
  ContinuousMultilinearMap.norm_constOfIsEmpty _ _ _

@[simp] lemma nnnorm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E ι x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_constOfIsEmpty _ _ _

end

section

variable (𝕜 E E' G G')

/-- `ContinuousMultilinearMap.prod` as a `LinearIsometryEquiv`. -/
def prodₗᵢ :
    (E [Λ^ι]→L[𝕜] G) × (E [Λ^ι]→L[𝕜] G') ≃ₗᵢ[𝕜]
      ContinuousAlternatingMap 𝕜 E (G × G') ι where
  toFun f := f.1.prod f.2
  invFun f := ((ContinuousLinearMap.fst 𝕜 G G').compContinuousAlternatingMap f,
    (ContinuousLinearMap.snd 𝕜 G G').compContinuousAlternatingMap f)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' f := op_norm_prod f.1 f.2

/-- `ContinuousMultilinearMap.pi` as a `LinearIsometryEquiv`. -/
def piₗᵢ {ι' : Type v'} [Fintype ι'] {G : ι' → Type wE'} [∀ i', NormedAddCommGroup (G i')]
    [∀ i', NormedSpace 𝕜 (G i')] :
    (∀ i', E [Λ^ι]→L[𝕜] G i') ≃ₗᵢ[𝕜] (E [Λ^ι]→L[𝕜] (∀ i, G i)) where
  toLinearEquiv := piLinearEquiv
  norm_map' := op_norm_pi

end

end

section restrict_scalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' G] [IsScalarTower 𝕜' 𝕜 G]
variable [NormedSpace 𝕜' E] [IsScalarTower 𝕜' 𝕜 E]

@[simp] lemma norm_restrict_scalars : ‖f.restrictScalars 𝕜'‖ = ‖f‖ := rfl

variable (𝕜')

/-- `ContinuousMultilinearMap.restrict_scalars` as a `linear_isometry`. -/
def restrictScalarsₗᵢ : E [Λ^ι]→L[𝕜] G →ₗᵢ[𝕜'] E [Λ^ι]→L[𝕜'] G where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

variable {𝕜'}

lemma continuous_restrictScalars :
    Continuous (restrictScalars 𝕜' : E [Λ^ι]→L[𝕜] G → E [Λ^ι]→L[𝕜'] G) :=
  (restrictScalarsₗᵢ 𝕜').continuous

end restrict_scalars

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, precise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound reads
`‖f m - f m'‖ ≤
  ‖f‖ * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`.-/
lemma norm_image_sub_le' [DecidableEq ι] (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.1.norm_image_sub_le' m₁ m₂

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, less precise
version. For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `‖f m - f m'‖ ≤ ‖f‖ * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`.-/
lemma norm_image_sub_le (m₁ m₂ : ι → E) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * (Fintype.card ι) * (max ‖m₁‖ ‖m₂‖) ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.1.norm_image_sub_le m₁ m₂

/-- Applying a alternating map to a vector is continuous in both coordinates. -/
lemma continuous_eval :
    Continuous (fun p : E [Λ^ι]→L[𝕜] G × (ι → E) ↦ p.1 p.2) :=
  (@ContinuousMultilinearMap.continuous_eval 𝕜 ι (fun _ ↦ E) G _ _ _ _ _ _).comp
    (continuous_toContinuousMultilinearMap.prod_map continuous_id)

lemma continuous_eval_left (m : ι → E) : Continuous fun p : E [Λ^ι]→L[𝕜] G ↦ p m :=
  continuous_eval.comp₂ continuous_id continuous_const

lemma hasSum_eval {α : Type*} {p : α → E [Λ^ι]→L[𝕜] G} {q : E [Λ^ι]→L[𝕜] G}
    (h : HasSum p q) (m : ι → E) : HasSum (p · m) (q m) := by
  dsimp only [HasSum] at h ⊢
  convert ((continuous_eval_left m).tendsto _).comp h
  simp

lemma tsum_eval {α : Type*} {p : α → E [Λ^ι]→L[𝕜] G} (hp : Summable p)
    (m : ι → E) : (∑' a, p a) m = ∑' a, p a m :=
  (hasSum_eval hp.hasSum m).tsum_eq.symm

open scoped Topology
open filter

/-- If the target space is complete, the space of continuous alternating maps with its norm is also
complete. -/
instance [CompleteSpace G] : CompleteSpace (E [Λ^ι]→L[𝕜] G) :=
  (completeSpace_iff_isComplete_range uniformEmbedding_toContinuousMultilinearMap.1).2
    isClosed_range_toContinuousMultilinearMap.isComplete

end ContinuousAlternatingMap

/-- If a continuous alternating map is constructed from a alternating map via the constructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
lemma AlternatingMap.mkContinuous_norm_le (f : E [Λ^ι]→ₗ[𝕜] G) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ C :=
  f.toMultilinearMap.mkContinuous_norm_le hC H

/-- If a continuous alternating map is constructed from a alternating map via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
lemma AlternatingMap.mkContinuous_norm_le' (f : E [Λ^ι]→ₗ[𝕜] G) {C : ℝ}
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ max C 0 :=
  ContinuousMultilinearMap.op_norm_le_bound _ (le_max_right _ _) fun m ↦ (H m).trans <| by
    gcongr
    · apply prod_nonneg; intros; apply norm_nonneg
    · apply le_max_left

namespace ContinuousLinearMap

lemma norm_compContinuousAlternatingMap_le (g : G →L[𝕜] G') (f : E [Λ^ι]→L[𝕜] G) :
    ‖g.compContinuousAlternatingMap f‖ ≤ ‖g‖ * ‖f‖ :=
  g.norm_compContinuousMultilinearMap_le f.1

variable (𝕜 E G G')

/-- `continuous_linear_map.comp_ContinuousAlternatingMap` as a bundled continuous bilinear map. -/
def compContinuousAlternatingMapL : (G →L[𝕜] G') →L[𝕜] E [Λ^ι]→L[𝕜] G →L[𝕜] (E [Λ^ι]→L[𝕜] G') :=
  LinearMap.mkContinuous₂ (compContinuousAlternatingMapₗ 𝕜 E G G') 1 fun f g ↦ by
    simpa using f.norm_compContinuousAlternatingMap_le g

variable {𝕜 G G'}

/-- `ContinuousLinearMap.compContinuousAlternatingMap` as a bundled continuous linear equiv. -/
nonrec def _root_.ContinuousLinearEquiv.compContinuousAlternatingMapL (g : G ≃L[𝕜] G') :
    (E [Λ^ι]→L[𝕜] G) ≃L[𝕜] (E [Λ^ι]→L[𝕜] G') :=
  { g.compContinuousAlternatingMap,
      compContinuousAlternatingMapL 𝕜 E G G' g.toContinuousLinearMap with
    invFun := compContinuousAlternatingMapL 𝕜 E G' G g.symm.toContinuousLinearMap
    continuous_toFun :=
      (compContinuousAlternatingMapL 𝕜 E G G' g.toContinuousLinearMap).continuous
    continuous_invFun :=
      (compContinuousAlternatingMapL 𝕜 E G' G g.symm.toContinuousLinearMap).continuous }

@[simp]
lemma _root_.ContinuousLinearEquiv.compContinuousAlternatingMapL_symm (g : G ≃L[𝕜] G') :
    (g.compContinuousAlternatingMapL (ι := ι) E).symm = g.symm.compContinuousAlternatingMapL E :=
  rfl

variable {E}

@[simp]
lemma _root_.continuous_linear_equiv.comp_ContinuousAlternatingMapL_apply
    (g : G ≃L[𝕜] G') (f : E [Λ^ι]→L[𝕜] G) :
    g.compContinuousAlternatingMapL E f = (g : G →L[𝕜] G').compContinuousAlternatingMap f :=
  rfl

/-- Flip arguments in `f : G →L[𝕜] E [Λ^ι]→L[𝕜] G'` to get `Λ^ι⟮𝕜; E; G →L[𝕜] G'⟯` -/
def flipAlternating (f : G →L[𝕜] (E [Λ^ι]→L[𝕜] G')) : E [Λ^ι]→L[𝕜] (G →L[𝕜] G') where
  toContinuousMultilinearMap :=
    ((ContinuousAlternatingMap.toContinuousMultilinearMapL 𝕜).comp f).flipMultilinear
  map_eq_zero_of_eq' v i j hv hne := by ext x; simp [(f x).map_eq_zero_of_eq v hv hne]

end ContinuousLinearMap

lemma LinearIsometry.norm_compContinuousAlternatingMap (g : G →ₗᵢ[𝕜] G') (f : E [Λ^ι]→L[𝕜] G) :
    ‖g.toContinuousLinearMap.compContinuousAlternatingMap f‖ = ‖f‖ :=
  g.norm_compContinuousMultilinearMap f.1

open ContinuousAlternatingMap

section

lemma ContinuousAlternatingMap.norm_compContinuousLinearMap_le (f : E' [Λ^ι]→L[𝕜] G)
    (g : E →L[𝕜] E') : ‖f.compContinuousLinearMap g‖ ≤ ‖f‖ * (‖g‖ ^ Fintype.card ι) :=
  (f.1.norm_compContinuousLinearMap_le _).trans_eq <| by simp [Fintype.card]

def ContinuousAlternatingMap.compContinuousLinearMapL (f : E →L[𝕜] E') :
    (E' [Λ^ι]→L[𝕜] G) →L[𝕜] (E [Λ^ι]→L[𝕜] G) :=
  LinearMap.mkContinuous
    (ContinuousAlternatingMap.compContinuousLinearMapₗ f) (‖f‖ ^ Fintype.card ι) fun g ↦
      (g.norm_compContinuousLinearMap_le f).trans_eq (mul_comm _ _)

def ContinuousAlternatingMap.compContinuousLinearEquivL (f : E ≃L[𝕜] E') :
    E [Λ^ι]→L[𝕜] G ≃L[𝕜] (E' [Λ^ι]→L[𝕜] G) :=
  { f.continuousAlternatingMapComp,
      ContinuousAlternatingMap.compContinuousLinearMapL (f.symm : E' →L[𝕜] E) with
    continuous_invFun :=
      (ContinuousAlternatingMap.compContinuousLinearMapL (f : E →L[𝕜] E')).cont
    continuous_toFun :=
      (ContinuousAlternatingMap.compContinuousLinearMapL (f.symm : E' →L[𝕜] E)).cont }

def ContinuousLinearEquiv.continuousAlternatingMapCongrL (e : E ≃L[𝕜] E') (e' : G ≃L[𝕜] G') :
    (E [Λ^ι]→L[𝕜] G) ≃L[𝕜] (E' [Λ^ι]→L[𝕜] G') :=
  (ContinuousAlternatingMap.compContinuousLinearEquivL e).trans <|
    e'.compContinuousAlternatingMapL E'

@[simp]
lemma ContinuousLinearEquiv.continuousAlternatingMapCongrL_apply (e : E ≃L[𝕜] E')
    (e' : G ≃L[𝕜] G') (f : E [Λ^ι]→L[𝕜] G) :
    e.continuousAlternatingMapCongrL e' f =
      e'.compContinuousAlternatingMap (f.compContinuousLinearMap ↑e.symm) :=
  rfl

end

open ContinuousAlternatingMap

namespace AlternatingMap

/-- Given a map `f : G →ₗ[𝕜] E [Λ^ι]→ₗ[𝕜] G'` and an estimate
`H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖`, construct a continuous linear
map from `G` to `E [Λ^ι]→L[𝕜] G'`.

In order to lift, e.g., a map `f : (E [Λ^ι]→ₗ[𝕜] G) →ₗ[𝕜] E' [Λ^ι]→ₗ[𝕜] G'`
to a map `(E [Λ^ι]→L[𝕜] G) →L[𝕜] E' [Λ^ι]→L[𝕜] G'`,
one can apply this construction to `f.comp ContinuousAlternatingMap.toAlternatingMapLinear`
which is a linear map from `E [Λ^ι]→L[𝕜] G` to `E' [Λ^ι]→ₗ[𝕜] G'`. -/
def mkContinuousLinear (f : G →ₗ[𝕜] E [Λ^ι]→ₗ[𝕜] G') (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : G →L[𝕜] E [Λ^ι]→L[𝕜] G' :=
  LinearMap.mkContinuous
    { toFun := fun x => (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' := fun x y => by
        ext1
        simp only [_root_.map_add]
        rfl
      map_smul' := fun c x => by
        ext1
        simp only [SMulHomClass.map_smul]
        rfl }
    (max C 0) fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk]
      exact (mkContinuous_norm_le' _ _).trans_eq <| by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

theorem mkContinuousLinear_norm_le' (f : G →ₗ[𝕜] E [Λ^ι]→ₗ[𝕜] G') (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ max C 0 :=
  LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

theorem mkContinuousLinear_norm_le (f : G →ₗ[𝕜] E [Λ^ι]→ₗ[𝕜] G') {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ C :=
  (mkContinuousLinear_norm_le' f C H).trans_eq (max_eq_left hC)

/-- Given a map `f : E [Λ^ι]→ₗ[𝕜] (E' [Λ^ι']→ₗ[𝕜] G)` and an estimate
`H : ∀ m m', ‖f m m'‖ ≤ C * ∏ i, ‖m i‖ * ∏ i, ‖m' i‖`, upgrade all `AlternatingMap`s in the type to
`ContinuousAlternatingMap`s. -/
def mkContinuousAlternating (f : E [Λ^ι]→ₗ[𝕜] (E' [Λ^ι']→ₗ[𝕜] G)) (C : ℝ)
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    E [Λ^ι]→L[𝕜] (E' [Λ^ι']→L[𝕜] G)  :=
  mkContinuous
    { toFun := fun m => mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_add' := fun m i x y => by
        ext1
        simp
      map_smul' := fun m i c x => by
        ext1
        simp
      map_eq_zero_of_eq' := by
        intros v i j hv hij
        ext v'
        have : f v = 0 := by simpa using f.map_eq_zero_of_eq' v i j hv hij
        simp [this] }
    (max C 0) fun m => by
      simp only [coe_mk, MultilinearMap.coe_mk, ge_iff_le]
      refine ((f m).mkContinuous_norm_le' _).trans_eq ?_
      rw [max_mul_of_nonneg, zero_mul]
      exact prod_nonneg fun _ _ => norm_nonneg _

@[simp]
theorem mkContinuousAlternating_apply (f : E [Λ^ι]→ₗ[𝕜] (E' [Λ^ι']→ₗ[𝕜] G)) {C : ℝ}
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : ι → E) :
    ⇑(mkContinuousAlternating f C H m) = f m :=
  rfl

theorem mkContinuousAlternating_norm_le' (f : E [Λ^ι]→ₗ[𝕜]  (E' [Λ^ι']→ₗ[𝕜] G)) (C : ℝ)
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousAlternating f C H‖ ≤ max C 0 := by
  dsimp only [mkContinuousAlternating]
  exact mkContinuous_norm_le _ (le_max_right _ _) _

theorem mkContinuousAlternating_norm_le (f : E [Λ^ι]→ₗ[𝕜] (E' [Λ^ι']→ₗ[𝕜] G)) {C : ℝ}
    (hC : 0 ≤ C) (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousAlternating f C H‖ ≤ C :=
  (mkContinuousAlternating_norm_le' f C H).trans_eq (max_eq_left hC)

end AlternatingMap

section Smul

variable {R : Type*} [Semiring R] [Module R G] [SMulCommClass 𝕜 R G] [ContinuousConstSMul R G]

instance ContinuousAlternatingMap.continuousConstSMul :
    ContinuousConstSMul R (E [Λ^ι]→L[𝕜] G) :=
  ⟨fun c =>
    (ContinuousLinearMap.compContinuousAlternatingMapL 𝕜 E G G (c • ContinuousLinearMap.id 𝕜 G)).2⟩

end Smul
