/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Topology.Algebra.Module.Alternating
import Mathlib.Analysis.NormedSpace.Multilinear

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

variable (f : AlternatingMap 𝕜 E G ι)

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

lemma op_norm_prod (f : E [Λ^ι]→L[𝕜] G) (g : ContinuousAlternatingMap 𝕜 E G' ι) :
    ‖f.prod g‖ = max (‖f‖) (‖g‖) :=
  f.1.op_norm_prod g.1

lemma op_norm_pi {ι' : Type v'} [Fintype ι'] {E' : ι' → Type wE'} [∀ i', NormedAddCommGroup (E' i')]
    [∀ i', NormedSpace 𝕜 (E' i')] (f : ∀ i', ContinuousAlternatingMap 𝕜 E (E' i') ι) :
    ‖pi f‖ = ‖f‖ :=
  ContinuousMultilinearMap.op_norm_pi fun i ↦ (f i).1

section
variable (𝕜 G)

lemma norm_of_subsingleton_le [Subsingleton ι] (i' : ι) : ‖ofSubsingleton 𝕜 G i'‖ ≤ 1 :=
  ContinuousMultilinearMap.norm_ofSubsingleton_le 𝕜 G i'

@[simp] lemma norm_of_subsingleton [Subsingleton ι] [Nontrivial G] (i' : ι) :
    ‖ofSubsingleton 𝕜 G i'‖ = 1 :=
  ContinuousMultilinearMap.norm_ofSubsingleton 𝕜 G i'

lemma nnnorm_of_subsingleton_le [Subsingleton ι] (i' : ι) : ‖ofSubsingleton 𝕜 G i'‖₊ ≤ 1 :=
  norm_of_subsingleton_le _ _ _

@[simp] lemma nnnorm_of_subsingleton [Subsingleton ι] [Nontrivial G] (i' : ι) :
    ‖ofSubsingleton 𝕜 G i'‖₊ = 1 :=
  NNReal.eq <| norm_of_subsingleton _ _ _

variable {G} (E)

@[simp] lemma norm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E ι x‖ = ‖x‖ :=
  ContinuousMultilinearMap.norm_constOfIsEmpty _ _ _

@[simp] lemma nnnorm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E ι x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_constOfIsEmpty _ _ _

end

section

variable (𝕜 E E' G G')

/-- `ContinuousMultilinearMap.prod` as a `LinearIsometryEquiv`. -/
def prodₗᵢ :
    (E [Λ^ι]→L[𝕜] G) × (ContinuousAlternatingMap 𝕜 E G' ι) ≃ₗᵢ[𝕜]
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
lemma AlternatingMap.mkContinuous_norm_le (f : E [Λ^ι]→L[𝕜] G) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ C :=
  f.toMultilinearMap.mkContinuous_norm_le hC H

/-- If a continuous alternating map is constructed from a alternating map via the constructor
`mk_continuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
lemma AlternatingMap.mkContinuous_norm_le' (f : E [Λ^ι]→L[𝕜] G) {C : ℝ}
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

/-

namespace multilinear_map

/-- Given a map `f : G →ₗ[𝕜] alternating_map 𝕜 E G ι'` and an estimate
`H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖`, construct a continuous linear
map from `G` to `E [Λ^ι]→L[𝕜] G'`.

In order to lift, e.g., a map `f : (alternating_map 𝕜 E G ι) →ₗ[𝕜] multilinear_map 𝕜 E' G'`
to a map `(E [Λ^ι]→L[𝕜] G) →L[𝕜] ContinuousAlternatingMap 𝕜 E' G'`,
one can apply this construction to `f.comp ContinuousAlternatingMap.to_alternating_map_linear`
which is a linear map from `E [Λ^ι]→L[𝕜] G` to `multilinear_map 𝕜 E' G'`. -/
def mk_continuous_linear (f : G →ₗ[𝕜] alternating_map 𝕜 E G ι') (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) :
  G →L[𝕜] E [Λ^ι]→L[𝕜] G' :=
linear_map.mk_continuous
  { to_fun := λ x, (f x).mk_continuous (C * ‖x‖) $ H x,
    map_add' := λ x y, by { ext1, simp only [_root_.map_add], refl },
    map_smul' := λ c x, by { ext1, simp only [smul_hom_class.map_smul], refl } }
  (max C 0) $ λ x, ((f x).mk_continuous_norm_le' _).trans_eq $
    by rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

lemma mk_continuous_linear_norm_le' (f : G →ₗ[𝕜] alternating_map 𝕜 E G ι') (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) :
  ‖mk_continuous_linear f C H‖ ≤ max C 0 :=
begin
  dunfold mk_continuous_linear,
  exact linear_map.mk_continuous_norm_le _ (le_max_right _ _) _
end

lemma mk_continuous_linear_norm_le (f : G →ₗ[𝕜] alternating_map 𝕜 E G ι') {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) :
  ‖mk_continuous_linear f C H‖ ≤ C :=
(mk_continuous_linear_norm_le' f C H).trans_eq (max_eq_left hC)

/-- Given a map `f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G)` and an estimate
`H : ∀ m m', ‖f m m'‖ ≤ C * ∏ i, ‖m i‖ * ∏ i, ‖m' i‖`, upgrade all `multilinear_map`s in the type to
`ContinuousAlternatingMap`s. -/
def mk_continuous_alternating (f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G)) (C : ℝ)
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ C * (∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
  ContinuousAlternatingMap 𝕜 E (ContinuousAlternatingMap 𝕜 E' G) :=
mk_continuous
  { to_fun := λ m, mk_continuous (f m) (C * ∏ i, ‖m i‖) $ H m,
    map_add' := λ _ m i x y, by { ext1, simp },
    map_smul' := λ _ m i c x, by { ext1, simp } }
  (max C 0) $ λ m, ((f m).mk_continuous_norm_le' _).trans_eq $
    by { rw [max_mul_of_nonneg, zero_mul], exact prod_nonneg (λ _ _, norm_nonneg _) }

@[simp] lemma mk_continuous_alternating_apply (f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G))
  {C : ℝ} (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ C * (∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : ι → E) :
  ⇑(mk_continuous_alternating f C H m) = f m :=
rfl

lemma mk_continuous_alternating_norm_le' (f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G)) (C : ℝ)
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ C * (∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
  ‖mk_continuous_alternating f C H‖ ≤ max C 0 :=
begin
  dunfold mk_continuous_alternating,
  exact mk_continuous_norm_le _ (le_max_right _ _) _
end

lemma mk_continuous_alternating_norm_le (f : multilinear_map 𝕜 E (multilinear_map 𝕜 E' G)) {C : ℝ}
    (hC : 0 ≤ C) (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ C * (∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
  ‖mk_continuous_alternating f C H‖ ≤ C :=
(mk_continuous_alternating_norm_le' f C H).trans_eq (max_eq_left hC)

end multilinear_map

namespace ContinuousAlternatingMap

lemma norm_comp_continuous_linear_le (g : ContinuousAlternatingMap 𝕜 E₁ G)
    (f : ι → E →L[𝕜] E₁ i) :
  ‖g.comp_continuous_linear_map f‖ ≤ ‖g‖ * ∏ i, ‖f i‖ :=
op_norm_le_bound _ (mul_nonneg (norm_nonneg _) $ prod_nonneg $ λ i hi, norm_nonneg _) $ λ m,
calc ‖g (λ i, f i (m i))‖ ≤ ‖g‖ * ∏ i, ‖f i (m i)‖ : g.le_op_norm _
... ≤ ‖g‖ * ∏ i, (‖f i‖ * ‖m i‖) :
  mul_le_mul_of_nonneg_left
    (prod_le_prod (λ _ _, norm_nonneg _) (λ i hi, (f i).le_op_norm (m i))) (norm_nonneg g)
... = (‖g‖ * ∏ i, ‖f i‖) * ∏ i, ‖m i‖ : by rw [prod_mul_distrib, mul_assoc]

lemma norm_comp_continuous_linear_isometry_le (g : ContinuousAlternatingMap 𝕜 E₁ G)
    (f : ι → E →ₗᵢ[𝕜] E₁ i) :
  ‖g.comp_continuous_linear_map (λ i, (f i).to_continuous_linear_map)‖ ≤ ‖g‖ :=
begin
  apply op_norm_le_bound _ (norm_nonneg _) (λ m, _),
  apply (g.le_op_norm _).trans _,
  simp only [continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe,
    linear_isometry.coe_to_continuous_linear_map, linear_isometry.norm_map]
end

lemma norm_comp_continuous_linear_isometry_equiv (g : ContinuousAlternatingMap 𝕜 E₁ G)
    (f : ι → E ≃ₗᵢ[𝕜] E₁ i) :
  ‖g.comp_continuous_linear_map (λ i, (f i : E i →L[𝕜] E₁ i))‖ = ‖g‖ :=
begin
  apply le_antisymm (g.norm_comp_continuous_linear_isometry_le (λ i, (f i).to_linear_isometry)),
  have : g = (g.comp_continuous_linear_map (λ i, (f i : E i →L[𝕜] E₁ i)))
    .comp_continuous_linear_map (λ i, ((f i).symm : E₁ i →L[𝕜] E i)),
  { ext1 m,
    simp only [comp_continuous_linear_map_apply, linear_isometry_equiv.coe_coe'',
      linear_isometry_equiv.apply_symm_apply] },
  conv_lhs { rw this },
  apply (g.comp_continuous_linear_map (λ i, (f i : E i →L[𝕜] E₁ i)))
    .norm_comp_continuous_linear_isometry_le (λ i, (f i).symm.to_linear_isometry),
end

/-- `ContinuousAlternatingMap.comp_continuous_linear_map` as a bundled continuous linear map.
This implementation fixes `f : ι → E →L[𝕜] E₁ i`.

TODO: Actually, the map is multilinear in `f` but an attempt to formalize this failed because of
issues with class instances. -/
def comp_continuous_linear_mapL (f : ι → E →L[𝕜] E₁ i) :
    ContinuousAlternatingMap 𝕜 E₁ G →L[𝕜] E [Λ^ι]→L[𝕜] G :=
linear_map.mk_continuous
  { to_fun := λ g, g.comp_continuous_linear_map f,
    map_add' := λ g₁ g₂, rfl,
    map_smul' := λ c g, rfl }
  (∏ i, ‖f i‖) $ λ g, (norm_comp_continuous_linear_le _ _).trans_eq (mul_comm _ _)

@[simp] lemma comp_continuous_linear_mapL_apply
  (g : ContinuousAlternatingMap 𝕜 E₁ G) (f : ι → E →L[𝕜] E₁ i) :
  comp_continuous_linear_mapL f g = g.comp_continuous_linear_map f :=
rfl

lemma norm_comp_continuous_linear_mapL_le (f : ι → E →L[𝕜] E₁ i) :
    ‖@comp_continuous_linear_mapL 𝕜 ι E E₁ G _ _ _ _ _ _ _ _ f‖ ≤ (∏ i, ‖f i‖) :=
linear_map.mk_continuous_norm_le _ (prod_nonneg $ λ i _, norm_nonneg _) _

variable (G)

/-- `ContinuousAlternatingMap.comp_continuous_linear_map` as a bundled continuous linear equiv,
given `f : ι → E ≃L[𝕜] E₁ i`. -/
def comp_continuous_linear_map_equivL (f : ι → E ≃L[𝕜] E₁ i) :
    ContinuousAlternatingMap 𝕜 E₁ G ≃L[𝕜] E [Λ^ι]→L[𝕜] G :=
{ inv_fun := comp_continuous_linear_mapL (λ i, ((f i).symm : E₁ i →L[𝕜] E i)),
  continuous_to_fun := (comp_continuous_linear_mapL (λ i, (f i : E i →L[𝕜] E₁ i))).continuous,
  continuous_inv_fun :=
    (comp_continuous_linear_mapL (λ i, ((f i).symm : E₁ i →L[𝕜] E i))).continuous,
  left_inv := begin
    assume g,
    ext1 m,
    simp only [continuous_linear_map.to_linear_map_eq_coe, linear_map.to_fun_eq_coe,
      continuous_linear_map.coe_coe, comp_continuous_linear_mapL_apply,
      comp_continuous_linear_map_apply, continuous_linear_equiv.coe_coe,
      continuous_linear_equiv.apply_symm_apply],
  end,
  right_inv := begin
    assume g,
    ext1 m,
    simp only [continuous_linear_map.to_linear_map_eq_coe, comp_continuous_linear_mapL_apply,
      linear_map.to_fun_eq_coe, continuous_linear_map.coe_coe, comp_continuous_linear_map_apply,
      continuous_linear_equiv.coe_coe, continuous_linear_equiv.symm_apply_apply],
  end,
  .. comp_continuous_linear_mapL (λ i, (f i : E i →L[𝕜] E₁ i)) }

@[simp] lemma comp_continuous_linear_map_equivL_symm (f : ι → E ≃L[𝕜] E₁ i) :
  (comp_continuous_linear_map_equivL G f).symm =
    comp_continuous_linear_map_equivL G (λ (i : ι), (f i).symm) :=
rfl

variable {G}

@[simp] lemma comp_continuous_linear_map_equivL_apply
  (g : ContinuousAlternatingMap 𝕜 E₁ G) (f : ι → E ≃L[𝕜] E₁ i) :
  comp_continuous_linear_map_equivL G f g =
    g.comp_continuous_linear_map (λ i, (f i : E i →L[𝕜] E₁ i)) := rfl

end ContinuousAlternatingMap

section smul

variable {R : Type*} [semiring R] [module R G] [smul_comm_class 𝕜 R G]
  [has_continuous_const_smul R G]

instance : has_continuous_const_smul R (E [Λ^ι]→L[𝕜] G) :=
⟨λ c, (continuous_linear_map.comp_ContinuousAlternatingMapL 𝕜 _ G G
  (c • continuous_linear_map.id 𝕜 G)).2⟩

end smul

section currying
/-!
### Currying

We associate to a continuous multilinear map in `n+1` variables (i.e., based on `Fin n.succ`) two
curried functions, named `f.curry_left` (which is a continuous linear map on `E 0` taking values
in continuous multilinear maps in `n` variables) and `f.curry_right` (which is a continuous
multilinear map in `n` variables taking values in continuous linear maps on `E (last n)`).
The inverse operations are called `uncurry_left` and `uncurry_right`.

We also register continuous linear equiv versions of these correspondences, in
`continuous_alternating_curry_left_equiv` and `continuous_alternating_curry_right_equiv`.
-/
open Fin function

lemma continuous_linear_map.norm_map_tail_le
    (f : Ei 0 →L[𝕜] (ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.succ) G)) (m : ∀i, Ei i) :
  ‖f (m 0) (tail m)‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
calc
  ‖f (m 0) (tail m)‖ ≤ ‖f (m 0)‖ * ∏ i, ‖(tail m) i‖ : (f (m 0)).le_op_norm _
  ... ≤ (‖f‖ * ‖m 0‖) * ∏ i, ‖(tail m) i‖ :
    mul_le_mul_of_nonneg_right (f.le_op_norm _) (prod_nonneg (λi hi, norm_nonneg _))
  ... = ‖f‖ * (‖m 0‖ * ∏ i, ‖(tail m) i‖) : by ring
  ... = ‖f‖ * ∏ i, ‖m i‖ : by { rw prod_univ_succ, refl }

lemma ContinuousAlternatingMap.norm_map_init_le
    (f : ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G))
  (m : ∀i, Ei i) :
  ‖f (init m) (m (last n))‖ ≤ ‖f‖ * ∏ i, ‖m i‖ :=
calc
  ‖f (init m) (m (last n))‖ ≤ ‖f (init m)‖ * ‖m (last n)‖ : (f (init m)).le_op_norm _
  ... ≤ (‖f‖ * (∏ i, ‖(init m) i‖)) * ‖m (last n)‖ :
    mul_le_mul_of_nonneg_right (f.le_op_norm _) (norm_nonneg _)
  ... = ‖f‖ * ((∏ i, ‖(init m) i‖) * ‖m (last n)‖) : mul_assoc _ _ _
  ... = ‖f‖ * ∏ i, ‖m i‖ : by { rw prod_univ_cast_succ, refl }

lemma ContinuousAlternatingMap.norm_map_cons_le
    (f : ContinuousAlternatingMap 𝕜 Ei G) (x : Ei 0) (m : ∀(i : Fin n), Ei i.succ) :
  ‖f (cons x m)‖ ≤ ‖f‖ * ‖x‖ * ∏ i, ‖m i‖ :=
calc
  ‖f (cons x m)‖ ≤ ‖f‖ * ∏ i, ‖cons x m i‖ : f.le_op_norm _
  ... = (‖f‖ * ‖x‖) * ∏ i, ‖m i‖ : by { rw prod_univ_succ, simp [mul_assoc] }

lemma ContinuousAlternatingMap.norm_map_snoc_le
    (f : ContinuousAlternatingMap 𝕜 Ei G) (m : ∀(i : Fin n), Ei i.cast_succ) (x : Ei (last n)) :
  ‖f (snoc m x)‖ ≤ ‖f‖ * (∏ i, ‖m i‖) * ‖x‖ :=
calc
  ‖f (snoc m x)‖ ≤ ‖f‖ * ∏ i, ‖snoc m x i‖ : f.le_op_norm _
  ... = ‖f‖ * (∏ i, ‖m i‖) * ‖x‖ : by { rw prod_univ_cast_succ, simp [mul_assoc] }

/-! #### Left currying -/

/-- Given a continuous linear map `f` from `E 0` to continuous multilinear maps on `n` variables,
construct the corresponding continuous multilinear map on `n+1` variables obtained by concatenating
the variables, given by `m ↦ f (m 0) (tail m)`-/
def continuous_linear_map.uncurry_left
    (f : Ei 0 →L[𝕜] (ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.succ) G)) :
  ContinuousAlternatingMap 𝕜 Ei G :=
(@linear_map.uncurry_left 𝕜 n Ei G _ _ _ _ _
  (ContinuousAlternatingMap.to_alternating_map_linear.comp f.to_linear_map)).mk_continuous
    (‖f‖) (λm, continuous_linear_map.norm_map_tail_le f m)

@[simp] lemma continuous_linear_map.uncurry_left_apply
  (f : Ei 0 →L[𝕜] (ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.succ) G)) (m : ∀i, Ei i) :
  f.uncurry_left m = f (m 0) (tail m) := rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous multilinear maps in `n` variables, given by
`x ↦ (m ↦ f (cons x m))`. -/
def ContinuousAlternatingMap.curry_left
    (f : ContinuousAlternatingMap 𝕜 Ei G) :
  Ei 0 →L[𝕜] (ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.succ) G) :=
linear_map.mk_continuous
{ -- define a linear map into `n` continuous multilinear maps from an `n+1` continuous multilinear
  -- map
  to_fun    := λx, (f.to_alternating_map.curry_left x).mk_continuous
    (‖f‖ * ‖x‖) (f.norm_map_cons_le x),
  map_add'  := λx y, by { ext m, exact f.cons_add m x y },
  map_smul' := λc x, by { ext m, exact f.cons_smul m c x } }
  -- then register its continuity thanks to its boundedness properties.
(‖f‖) (λx, multilinear_map.mk_continuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _)

@[simp] lemma ContinuousAlternatingMap.curry_left_apply
  (f : ContinuousAlternatingMap 𝕜 Ei G) (x : Ei 0) (m : ∀(i : Fin n), Ei i.succ) :
  f.curry_left x m = f (cons x m) := rfl

@[simp] lemma continuous_linear_map.curry_uncurry_left
  (f : Ei 0 →L[𝕜] (ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.succ) G)) :
  f.uncurry_left.curry_left = f :=
begin
  ext m x,
  simp only [tail_cons, continuous_linear_map.uncurry_left_apply,
             ContinuousAlternatingMap.curry_left_apply],
  rw cons_zero
end

@[simp] lemma ContinuousAlternatingMap.uncurry_curry_left
  (f : ContinuousAlternatingMap 𝕜 Ei G) : f.curry_left.uncurry_left = f :=
ContinuousAlternatingMap.to_alternating_map_injective $ f.to_alternating_map.uncurry_curry_left

variables (𝕜 Ei G)

/-- The space of continuous multilinear maps on `∀(i : Fin (n+1)), E i` is canonically isomorphic to
the space of continuous linear maps from `E 0` to the space of continuous multilinear maps on
`∀(i : Fin n), E i.succ `, by separating the first variable. We register this isomorphism in
`continuous_alternating_curry_left_equiv 𝕜 E E₂`. The algebraic version (without topology) is given
in `multilinear_curry_left_equiv 𝕜 E E₂`.

The direct and inverse maps are given by `f.uncurry_left` and `f.curry_left`. Use these
unless you need the full framework of linear isometric equivs. -/
def continuous_alternating_curry_left_equiv :
    (Ei 0 →L[𝕜] (ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.succ) G)) ≃ₗᵢ[𝕜]
  (ContinuousAlternatingMap 𝕜 Ei G) :=
linear_isometry_equiv.of_bounds
  { to_fun    := continuous_linear_map.uncurry_left,
    map_add'  := λf₁ f₂, by { ext m, refl },
    map_smul' := λc f, by { ext m, refl },
    inv_fun   := ContinuousAlternatingMap.curry_left,
    left_inv  := continuous_linear_map.curry_uncurry_left,
    right_inv := ContinuousAlternatingMap.uncurry_curry_left }
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)
  (λ f, linear_map.mk_continuous_norm_le _ (norm_nonneg f) _)

variables {𝕜 Ei G}

@[simp] lemma continuous_alternating_curry_left_equiv_apply
  (f : Ei 0 →L[𝕜] (ContinuousAlternatingMap 𝕜 (λ i : Fin n, Ei i.succ) G)) (v : ∀ i, Ei i) :
  continuous_alternating_curry_left_equiv 𝕜 Ei G f v = f (v 0) (tail v) := rfl

@[simp] lemma continuous_alternating_curry_left_equiv_symm_apply
  (f : ContinuousAlternatingMap 𝕜 Ei G) (x : Ei 0) (v : ∀ i : Fin n, Ei i.succ) :
  (continuous_alternating_curry_left_equiv 𝕜 Ei G).symm f x v = f (cons x v) := rfl

@[simp] lemma ContinuousAlternatingMap.curry_left_norm
  (f : ContinuousAlternatingMap 𝕜 Ei G) : ‖f.curry_left‖ = ‖f‖ :=
(continuous_alternating_curry_left_equiv 𝕜 Ei G).symm.norm_map f

@[simp] lemma continuous_linear_map.uncurry_left_norm
  (f : Ei 0 →L[𝕜] (ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.succ) G)) :
  ‖f.uncurry_left‖ = ‖f‖ :=
(continuous_alternating_curry_left_equiv 𝕜 Ei G).norm_map f

/-! #### Right currying -/

/-- Given a continuous linear map `f` from continuous multilinear maps on `n` variables to
continuous linear maps on `E 0`, construct the corresponding continuous multilinear map on `n+1`
variables obtained by concatenating the variables, given by `m ↦ f (init m) (m (last n))`. -/
def ContinuousAlternatingMap.uncurry_right
    (f : ContinuousAlternatingMap 𝕜 (λ i : Fin n, Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) :
  ContinuousAlternatingMap 𝕜 Ei G :=
let f' : multilinear_map 𝕜 (λ(i : Fin n), Ei i.cast_succ) (Ei (last n) →ₗ[𝕜] G) :=
{ to_fun    := λ m, (f m).to_linear_map,
  map_add'  := λ _ m i x y, by simp,
  map_smul' := λ _ m i c x, by simp } in
(@multilinear_map.uncurry_right 𝕜 n Ei G _ _ _ _ _ f').mk_continuous
  (‖f‖) (λm, f.norm_map_init_le m)

@[simp] lemma ContinuousAlternatingMap.uncurry_right_apply
  (f : ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G))
  (m : ∀i, Ei i) :
  f.uncurry_right m = f (init m) (m (last n)) := rfl

/-- Given a continuous multilinear map `f` in `n+1` variables, split the last variable to obtain
a continuous multilinear map in `n` variables into continuous linear maps, given by
`m ↦ (x ↦ f (snoc m x))`. -/
def ContinuousAlternatingMap.curry_right
    (f : ContinuousAlternatingMap 𝕜 Ei G) :
  ContinuousAlternatingMap 𝕜 (λ i : Fin n, Ei i.cast_succ) (Ei (last n) →L[𝕜] G) :=
let f' : multilinear_map 𝕜 (λ(i : Fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G) :=
{ to_fun    := λm, (f.to_alternating_map.curry_right m).mk_continuous
    (‖f‖ * ∏ i, ‖m i‖) $ λx, f.norm_map_snoc_le m x,
  map_add'  := λ _ m i x y, by { simp, refl },
  map_smul' := λ _ m i c x, by { simp, refl } } in
f'.mk_continuous (‖f‖) (λm, linear_map.mk_continuous_norm_le _
  (mul_nonneg (norm_nonneg _) (prod_nonneg (λj hj, norm_nonneg _))) _)

@[simp] lemma ContinuousAlternatingMap.curry_right_apply
  (f : ContinuousAlternatingMap 𝕜 Ei G) (m : ∀ i : Fin n, Ei i.cast_succ) (x : Ei (last n)) :
  f.curry_right m x = f (snoc m x) := rfl

@[simp] lemma ContinuousAlternatingMap.curry_uncurry_right
  (f : ContinuousAlternatingMap 𝕜 (λ i : Fin n, Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) :
  f.uncurry_right.curry_right = f :=
begin
  ext m x,
  simp only [snoc_last, ContinuousAlternatingMap.curry_right_apply,
             ContinuousAlternatingMap.uncurry_right_apply],
  rw init_snoc
end

@[simp] lemma ContinuousAlternatingMap.uncurry_curry_right
  (f : ContinuousAlternatingMap 𝕜 Ei G) : f.curry_right.uncurry_right = f :=
by { ext m, simp }

variables (𝕜 Ei G)

/--
The space of continuous multilinear maps on `∀(i : Fin (n+1)), Ei i` is canonically isomorphic to
the space of continuous multilinear maps on `∀(i : Fin n), Ei i.cast_succ` with values in the space
of continuous linear maps on `Ei (last n)`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuous_alternating_curry_right_equiv 𝕜 Ei G`.
The algebraic version (without topology) is given in `multilinear_curry_right_equiv 𝕜 Ei G`.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear isometric equivs.
-/
def continuous_alternating_curry_right_equiv :
    (ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) ≃ₗᵢ[𝕜]
  (ContinuousAlternatingMap 𝕜 Ei G) :=
linear_isometry_equiv.of_bounds
  { to_fun    := ContinuousAlternatingMap.uncurry_right,
    map_add'  := λf₁ f₂, by { ext m, refl },
    map_smul' := λc f, by { ext m, refl },
    inv_fun   := ContinuousAlternatingMap.curry_right,
    left_inv  := ContinuousAlternatingMap.curry_uncurry_right,
    right_inv := ContinuousAlternatingMap.uncurry_curry_right }
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)

variables (n G')

/-- The space of continuous multilinear maps on `∀(i : Fin (n+1)), G` is canonically isomorphic to
the space of continuous multilinear maps on `∀(i : Fin n), G` with values in the space
of continuous linear maps on `G`, by separating the last variable. We register this
isomorphism as a continuous linear equiv in `continuous_alternating_curry_right_equiv' 𝕜 n G G'`.
For a version allowing dependent types, see `continuous_alternating_curry_right_equiv`. When there
are no dependent types, use the primed version as it helps Lean a lot for unification.

The direct and inverse maps are given by `f.uncurry_right` and `f.curry_right`. Use these
unless you need the full framework of linear isometric equivs. -/
def continuous_alternating_curry_right_equiv' :
    (G [×n]→L[𝕜] (G →L[𝕜] G')) ≃ₗᵢ[𝕜] (G [×n.succ]→L[𝕜] G') :=
continuous_alternating_curry_right_equiv 𝕜 (λ (i : Fin n.succ), G) G'

variables {n 𝕜 G Ei G'}

@[simp] lemma continuous_alternating_curry_right_equiv_apply
  (f : (ContinuousAlternatingMap 𝕜 (λ(i : Fin n), Ei i.cast_succ) (Ei (last n) →L[𝕜] G)))
  (v : ∀ i, Ei i) :
  (continuous_alternating_curry_right_equiv 𝕜 Ei G) f v = f (init v) (v (last n)) := rfl

@[simp] lemma continuous_alternating_curry_right_equiv_symm_apply
  (f : ContinuousAlternatingMap 𝕜 Ei G)
  (v : ∀ (i : Fin n), Ei i.cast_succ) (x : Ei (last n)) :
  (continuous_alternating_curry_right_equiv 𝕜 Ei G).symm f v x = f (snoc v x) := rfl

@[simp] lemma continuous_alternating_curry_right_equiv_apply'
  (f : G [×n]→L[𝕜] (G →L[𝕜] G')) (v : Fin (n + 1) → G) :
  continuous_alternating_curry_right_equiv' 𝕜 n G G' f v = f (init v) (v (last n)) := rfl

@[simp] lemma continuous_alternating_curry_right_equiv_symm_apply'
  (f : G [×n.succ]→L[𝕜] G') (v : Fin n → G) (x : G) :
  (continuous_alternating_curry_right_equiv' 𝕜 n G G').symm f v x = f (snoc v x) := rfl

@[simp] lemma ContinuousAlternatingMap.curry_right_norm
  (f : ContinuousAlternatingMap 𝕜 Ei G) : ‖f.curry_right‖ = ‖f‖ :=
(continuous_alternating_curry_right_equiv 𝕜 Ei G).symm.norm_map f

@[simp] lemma ContinuousAlternatingMap.uncurry_right_norm
  (f : ContinuousAlternatingMap 𝕜 (λ i : Fin n, Ei i.cast_succ) (Ei (last n) →L[𝕜] G)) :
  ‖f.uncurry_right‖ = ‖f‖ :=
(continuous_alternating_curry_right_equiv 𝕜 Ei G).norm_map f

/-!
#### Currying with `0` variables

The space of multilinear maps with `0` variables is trivial: such a multilinear map is just an
arbitrary constant (note that multilinear maps in `0` variables need not map `0` to `0`!).
Therefore, the space of continuous multilinear maps on `(Fin 0) → G` with values in `E₂` is
isomorphic (and even isometric) to `E₂`. As this is the zeroth step in the construction of iterated
derivatives, we register this isomorphism. -/

section

variables {𝕜 G G'}

/-- Associating to a continuous multilinear map in `0` variables the unique value it takes. -/
def ContinuousAlternatingMap.uncurry0
    (f : ContinuousAlternatingMap 𝕜 (λ (i : Fin 0), G) G') : G' := f 0

variables (𝕜 G)
/-- Associating to an element `x` of a vector space `E₂` the continuous multilinear map in `0`
variables taking the (unique) value `x` -/
def ContinuousAlternatingMap.curry0 (x : G') : G [×0]→L[𝕜] G' :=
ContinuousAlternatingMap.const_of_is_empty 𝕜 _ x

variable {G}
@[simp] lemma ContinuousAlternatingMap.curry0_apply (x : G') (m : (Fin 0) → G) :
  ContinuousAlternatingMap.curry0 𝕜 G x m = x := rfl

variable {𝕜}
@[simp] lemma ContinuousAlternatingMap.uncurry0_apply (f : G [×0]→L[𝕜] G') :
  f.uncurry0 = f 0 := rfl

@[simp] lemma ContinuousAlternatingMap.apply_zero_curry0 (f : G [×0]→L[𝕜] G') {x : Fin 0 → G} :
  ContinuousAlternatingMap.curry0 𝕜 G (f x) = f :=
by { ext m, simp [(subsingleton.elim _ _ : x = m)] }

lemma ContinuousAlternatingMap.uncurry0_curry0 (f : G [×0]→L[𝕜] G') :
    ContinuousAlternatingMap.curry0 𝕜 G (f.uncurry0) = f :=
by simp

variables (𝕜 G)
@[simp] lemma ContinuousAlternatingMap.curry0_uncurry0 (x : G') :
  (ContinuousAlternatingMap.curry0 𝕜 G x).uncurry0 = x := rfl

@[simp] lemma ContinuousAlternatingMap.curry0_norm (x : G')  :
  ‖ContinuousAlternatingMap.curry0 𝕜 G x‖ = ‖x‖ :=
norm_const_of_is_empty _ _ _

variables {𝕜 G}
@[simp] lemma ContinuousAlternatingMap.fin0_apply_norm (f : G [×0]→L[𝕜] G') {x : Fin 0 → G} :
  ‖f x‖ = ‖f‖ :=
begin
  obtain rfl : x = 0 := subsingleton.elim _ _,
  refine le_antisymm (by simpa using f.le_op_norm 0) _,
  have : ‖ContinuousAlternatingMap.curry0 𝕜 G (f.uncurry0)‖ ≤ ‖f.uncurry0‖ :=
    ContinuousAlternatingMap.op_norm_le_bound _ (norm_nonneg _) (λm,
      by simp [-ContinuousAlternatingMap.apply_zero_curry0]),
  simpa
end

lemma ContinuousAlternatingMap.uncurry0_norm (f : G [×0]→L[𝕜] G') : ‖f.uncurry0‖ = ‖f‖ :=
by simp

variables (𝕜 G G')
/-- The continuous linear isomorphism between elements of a normed space, and continuous multilinear
maps in `0` variables with values in this normed space.

The direct and inverse maps are `uncurry0` and `curry0`. Use these unless you need the full
framework of linear isometric equivs. -/
def continuous_alternating_curry_fin0 : (G [×0]→L[𝕜] G') ≃ₗᵢ[𝕜] G' :=
{ to_fun    := λf, ContinuousAlternatingMap.uncurry0 f,
  inv_fun   := λf, ContinuousAlternatingMap.curry0 𝕜 G f,
  map_add'  := λf g, rfl,
  map_smul' := λc f, rfl,
  left_inv  := ContinuousAlternatingMap.uncurry0_curry0,
  right_inv := ContinuousAlternatingMap.curry0_uncurry0 𝕜 G,
  norm_map' := ContinuousAlternatingMap.uncurry0_norm }

variables {𝕜 G G'}

@[simp] lemma continuous_alternating_curry_fin0_apply (f : G [×0]→L[𝕜] G') :
  continuous_alternating_curry_fin0 𝕜 G G' f = f 0 := rfl

@[simp] lemma continuous_alternating_curry_fin0_symm_apply (x : G') (v : (Fin 0) → G) :
  (continuous_alternating_curry_fin0 𝕜 G G').symm x v = x := rfl

end

/-! #### With 1 variable -/

variables (𝕜 G G')

/-- Continuous multilinear maps from `G^1` to `G'` are isomorphic with continuous linear maps from
`G` to `G'`. -/
def continuous_alternating_curry_fin1 : (G [×1]→L[𝕜] G') ≃ₗᵢ[𝕜] (G →L[𝕜] G') :=
(continuous_alternating_curry_right_equiv 𝕜 (λ (i : Fin 1), G) G').symm.trans
(continuous_alternating_curry_fin0 𝕜 G (G →L[𝕜] G'))

variables {𝕜 G G'}

@[simp] lemma continuous_alternating_curry_fin1_apply (f : G [×1]→L[𝕜] G') (x : G) :
  continuous_alternating_curry_fin1 𝕜 G G' f x = f (fin.snoc 0 x) := rfl

@[simp] lemma continuous_alternating_curry_fin1_symm_apply
  (f : G →L[𝕜] G') (v : (Fin 1) → G) :
  (continuous_alternating_curry_fin1 𝕜 G G').symm f v = f (v 0) := rfl

namespace ContinuousAlternatingMap

variables (𝕜 G G')

/-- An equivalence of the index set defines a linear isometric equivalence between the spaces
of multilinear maps. -/
def dom_dom_congr (σ : ι ≃ ι') :
    ContinuousAlternatingMap 𝕜 (λ _ : ι, G) G' ≃ₗᵢ[𝕜]
    ContinuousAlternatingMap 𝕜 (λ _ : ι', G) G' :=
linear_isometry_equiv.of_bounds
  { to_fun := λ f, (multilinear_map.dom_dom_congr σ f.to_alternating_map).mk_continuous ‖f‖ $
      λ m, (f.le_op_norm (λ i, m (σ i))).trans_eq $ by rw [← σ.prod_comp],
    inv_fun := λ f, (multilinear_map.dom_dom_congr σ.symm f.to_alternating_map).mk_continuous ‖f‖ $
      λ m, (f.le_op_norm (λ i, m (σ.symm i))).trans_eq $ by rw [← σ.symm.prod_comp],
    left_inv := λ f, ext $ λ m, congr_arg f $ by simp only [σ.symm_apply_apply],
    right_inv := λ f, ext $ λ m, congr_arg f $ by simp only [σ.apply_symm_apply],
    map_add' := λ f g, rfl,
    map_smul' := λ c f, rfl }
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)

variables {𝕜 G G'}

section

/-- A continuous multilinear map with variables indexed by `ι ⊕ ι'` defines a continuous multilinear
map with variables indexed by `ι` taking values in the space of continuous multilinear maps with
variables indexed by `ι'`. -/
def curry_sum (f : ContinuousAlternatingMap 𝕜 (λ x : ι ⊕ ι', G) G') :
    ContinuousAlternatingMap 𝕜 (λ x : ι, G) (ContinuousAlternatingMap 𝕜 (λ x : ι', G) G') :=
multilinear_map.mk_continuous_alternating (multilinear_map.curry_sum f.to_alternating_map) (‖f‖) $
  λ m m', by simpa [fintype.prod_sum_type, mul_assoc] using f.le_op_norm (sum.elim m m')

@[simp] lemma curry_sum_apply (f : ContinuousAlternatingMap 𝕜 (λ x : ι ⊕ ι', G) G')
  (m : ι → G) (m' : ι' → G) :
  f.curry_sum m m' = f (sum.elim m m') :=
rfl

/-- A continuous multilinear map with variables indexed by `ι` taking values in the space of
continuous multilinear maps with variables indexed by `ι'` defines a continuous multilinear map with
variables indexed by `ι ⊕ ι'`. -/
def uncurry_sum
    (f : ContinuousAlternatingMap 𝕜 (λ x : ι, G) (ContinuousAlternatingMap 𝕜 (λ x : ι', G) G')) :
  ContinuousAlternatingMap 𝕜 (λ x : ι ⊕ ι', G) G' :=
multilinear_map.mk_continuous
  (to_alternating_map_linear.comp_alternating_map f.to_alternating_map).uncurry_sum (‖f‖) $ λ m,
  by simpa [fintype.prod_sum_type, mul_assoc]
    using (f (m ∘ sum.inl)).le_of_op_norm_le (m ∘ sum.inr) (f.le_op_norm _)

@[simp] lemma uncurry_sum_apply
  (f : ContinuousAlternatingMap 𝕜 (λ x : ι, G) (ContinuousAlternatingMap 𝕜 (λ x : ι', G) G'))
  (m : ι ⊕ ι' → G) :
  f.uncurry_sum m = f (m ∘ sum.inl) (m ∘ sum.inr) :=
rfl

variables (𝕜 ι ι' G G')

/-- Linear isometric equivalence between the space of continuous multilinear maps with variables
indexed by `ι ⊕ ι'` and the space of continuous multilinear maps with variables indexed by `ι`
taking values in the space of continuous multilinear maps with variables indexed by `ι'`.

The forward and inverse functions are `ContinuousAlternatingMap.curry_sum`
and `ContinuousAlternatingMap.uncurry_sum`. Use this definition only if you need
some properties of `linear_isometry_equiv`. -/
def curry_sum_equiv : ContinuousAlternatingMap 𝕜 (λ x : ι ⊕ ι', G) G' ≃ₗᵢ[𝕜]
    ContinuousAlternatingMap 𝕜 (λ x : ι, G) (ContinuousAlternatingMap 𝕜 (λ x : ι', G) G') :=
linear_isometry_equiv.of_bounds
  { to_fun := curry_sum,
    inv_fun := uncurry_sum,
    map_add' := λ f g, by { ext, refl },
    map_smul' := λ c f, by { ext, refl },
    left_inv := λ f, by { ext m, exact congr_arg f (sum.elim_comp_inl_inr m) },
    right_inv := λ f, by { ext m₁ m₂, change f _ _ = f _ _,
      rw [sum.elim_comp_inl, sum.elim_comp_inr] } }
  (λ f, multilinear_map.mk_continuous_alternating_norm_le _ (norm_nonneg f) _)
  (λ f, multilinear_map.mk_continuous_norm_le _ (norm_nonneg f) _)

end

section

variables (𝕜 G G') {k l : ℕ} {s : finset (Fin n)}

/-- If `s : finset (Fin n)` is a finite set of cardinality `k` and its complement has cardinality
`l`, then the space of continuous multilinear maps `G [×n]→L[𝕜] G'` of `n` variables is isomorphic
to the space of continuous multilinear maps `G [×k]→L[𝕜] G [×l]→L[𝕜] G'` of `k` variables taking
values in the space of continuous multilinear maps of `l` variables. -/
def curry_fin_finset {k l n : ℕ} {s : finset (Fin n)}
    (hk : s.card = k) (hl : sᶜ.card = l) :
  (G [×n]→L[𝕜] G') ≃ₗᵢ[𝕜] (G [×k]→L[𝕜] G [×l]→L[𝕜] G') :=
(dom_dom_congr 𝕜 G G' (fin_sum_equiv_of_finset hk hl).symm).trans
  (curry_sum_equiv 𝕜 (Fin k) (Fin l) G G')

variables {𝕜 G G'}

@[simp] lemma curry_fin_finset_apply (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×n]→L[𝕜] G') (mk : Fin k → G) (ml : Fin l → G) :
  curry_fin_finset 𝕜 G G' hk hl f mk ml =
    f (λ i, sum.elim mk ml ((fin_sum_equiv_of_finset hk hl).symm i)) :=
rfl

@[simp] lemma curry_fin_finset_symm_apply (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×k]→L[𝕜] G [×l]→L[𝕜] G') (m : Fin n → G) :
  (curry_fin_finset 𝕜 G G' hk hl).symm f m =
    f (λ i, m $ fin_sum_equiv_of_finset hk hl (sum.inl i))
      (λ i, m $ fin_sum_equiv_of_finset hk hl (sum.inr i)) :=
rfl

@[simp] lemma curry_fin_finset_symm_apply_piecewise_const (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×k]→L[𝕜] G [×l]→L[𝕜] G') (x y : G) :
  (curry_fin_finset 𝕜 G G' hk hl).symm f (s.piecewise (λ _, x) (λ _, y)) = f (λ _, x) (λ _, y) :=
multilinear_map.curry_fin_finset_symm_apply_piecewise_const hk hl _ x y

@[simp] lemma curry_fin_finset_symm_apply_const (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×k]→L[𝕜] G [×l]→L[𝕜] G') (x : G) :
  (curry_fin_finset 𝕜 G G' hk hl).symm f (λ _, x) = f (λ _, x) (λ _, x) :=
rfl

@[simp] lemma curry_fin_finset_apply_const (hk : s.card = k) (hl : sᶜ.card = l)
  (f : G [×n]→L[𝕜] G') (x y : G) :
  curry_fin_finset 𝕜 G G' hk hl f (λ _, x) (λ _, y) = f (s.piecewise (λ _, x) (λ _, y)) :=
begin
  refine (curry_fin_finset_symm_apply_piecewise_const hk hl _ _ _).symm.trans _, -- `rw` fails
  rw linear_isometry_equiv.symm_apply_apply
end

end

end ContinuousAlternatingMap

end currying
-/
