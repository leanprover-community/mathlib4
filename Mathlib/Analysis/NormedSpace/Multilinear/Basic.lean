/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Sophie Morel, Yury Kudryashov
-/
import Mathlib.Analysis.NormedSpace.OperatorNorm.NormedSpace
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Topology.Algebra.Module.Multilinear.Topology

/-!
# Operator norm on the space of continuous multilinear maps

When `f` is a continuous multilinear map in finitely many variables, we define its norm `‖f‖` as the
smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`.

We show that it is indeed a norm, and prove its basic properties.

## Main results

Let `f` be a multilinear map in finitely many variables.
* `exists_bound_of_continuous` asserts that, if `f` is continuous, then there exists `C > 0`
  with `‖f m‖ ≤ C * ∏ i, ‖m i‖` for all `m`.
* `continuous_of_bound`, conversely, asserts that this bound implies continuity.
* `mkContinuous` constructs the associated continuous multilinear map.

Let `f` be a continuous multilinear map in finitely many variables.
* `‖f‖` is its norm, i.e., the smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for
  all `m`.
* `le_opNorm f m` asserts the fundamental inequality `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖`.
* `norm_image_sub_le f m₁ m₂` gives a control of the difference `f m₁ - f m₂` in terms of
  `‖f‖` and `‖m₁ - m₂‖`.

## Implementation notes

We mostly follow the API (and the proofs) of `OperatorNorm.lean`, with the additional complexity
that we should deal with multilinear maps in several variables. The currying/uncurrying
constructions are based on those in `Multilinear.lean`.

From the mathematical point of view, all the results follow from the results on operator norm in
one variable, by applying them to one variable after the other through currying. However, this
is only well defined when there is an order on the variables (for instance on `Fin n`) although
the final result is independent of the order. While everything could be done following this
approach, it turns out that direct proofs are easier and more efficient.
-/

suppress_compilation

noncomputable section

open scoped NNReal Topology Uniformity
open Finset Metric Function Filter

/-
Porting note: These lines are not required in Mathlib4.
```lean
attribute [local instance 1001]
  AddCommGroup.toAddCommMonoid NormedAddCommGroup.toAddCommGroup NormedSpace.toModule'
```
-/

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

universe u v v' wE wE₁ wE' wG wG'

/-- Applying a multilinear map to a vector is continuous in both coordinates. -/
theorem ContinuousMultilinearMap.continuous_eval {𝕜 ι : Type*} {E : ι → Type*} {F : Type*}
    [NormedField 𝕜] [Finite ι] [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
    [TopologicalSpace F] [AddCommGroup F] [TopologicalAddGroup F] [Module 𝕜 F] :
    Continuous fun p : ContinuousMultilinearMap 𝕜 E F × ∀ i, E i => p.1 p.2 := by
  cases nonempty_fintype ι
  let _ := TopologicalAddGroup.toUniformSpace F
  have := comm_topologicalAddGroup_is_uniform (G := F)
  refine (UniformOnFun.continuousOn_eval₂ fun m ↦ ?_).comp_continuous
    (embedding_toUniformOnFun.continuous.prod_map continuous_id) fun (f, x) ↦ f.cont.continuousAt
  exact ⟨ball m 1, NormedSpace.isVonNBounded_of_isBounded _ isBounded_ball,
    ball_mem_nhds _ one_pos⟩

section Seminorm

variable {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {E : ι → Type wE} {E₁ : ι → Type wE₁}
  {E' : ι' → Type wE'} {G : Type wG} {G' : Type wG'}
  [Fintype ι'] [NontriviallyNormedField 𝕜] [∀ i, SeminormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [∀ i, SeminormedAddCommGroup (E₁ i)] [∀ i, NormedSpace 𝕜 (E₁ i)]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-!
### Continuity properties of multilinear maps

We relate continuity of multilinear maps to the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, in
both directions. Along the way, we prove useful bounds on the difference `‖f m₁ - f m₂‖`.
-/

namespace MultilinearMap

variable (f : MultilinearMap 𝕜 E G)

/-- If `f` is a continuous multilinear map in finitely many variables on `E` and `m` is an element
of `∀ i, E i` such that one of the `m i` has norm `0`, then `f m` has norm `0`.

Note that we cannot drop the continuity assumption because `f (m : Unit → E) = f (m ())`,
where the domain has zero norm and the codomain has a nonzero norm
does not satisfy this condition. -/
lemma norm_map_coord_zero (hf : Continuous f) {m : ∀ i, E i} {i : ι} (hi : ‖m i‖ = 0) :
    ‖f m‖ = 0 := by
  classical
  rw [← inseparable_zero_iff_norm] at hi ⊢
  have : Inseparable (update m i 0) m := inseparable_pi.2 <|
    (forall_update_iff m fun i a ↦ Inseparable a (m i)).2 ⟨hi.symm, fun _ _ ↦ rfl⟩
  simpa only [map_update_zero] using this.symm.map hf

variable [Fintype ι]

theorem bound_of_shell_of_norm_map_coord_zero (hf₀ : ∀ {m i}, ‖m i‖ = 0 → ‖f m‖ = 0)
    {ε : ι → ℝ} {C : ℝ} (hε : ∀ i, 0 < ε i) {c : ι → 𝕜} (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ∀ i, E i, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ∀ i, E i) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ := by
  rcases em (∃ i, ‖m i‖ = 0) with (⟨i, hi⟩ | hm)
  · rw [hf₀ hi, prod_eq_zero (mem_univ i) hi, mul_zero]
  push_neg at hm
  choose δ hδ0 hδm_lt hle_δm _ using fun i => rescale_to_shell_semi_normed (hc i) (hε i) (hm i)
  have hδ0 : 0 < ∏ i, ‖δ i‖ := prod_pos fun i _ => norm_pos_iff.2 (hδ0 i)
  simpa [map_smul_univ, norm_smul, prod_mul_distrib, mul_left_comm C, mul_le_mul_left hδ0] using
    hf (fun i => δ i • m i) hle_δm hδm_lt

/-- If a continuous multilinear map in finitely many variables on normed spaces satisfies
the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` for some positive
numbers `ε i` and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequality for all `m`. -/
theorem bound_of_shell_of_continuous (hfc : Continuous f)
    {ε : ι → ℝ} {C : ℝ} (hε : ∀ i, 0 < ε i) {c : ι → 𝕜} (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ∀ i, E i, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ∀ i, E i) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  bound_of_shell_of_norm_map_coord_zero f (norm_map_coord_zero f hfc) hε hc hf m

/-- If a multilinear map in finitely many variables on normed spaces is continuous, then it
satisfies the inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, for some `C` which can be chosen to be
positive. -/
theorem exists_bound_of_continuous (hf : Continuous f) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖ := by
  cases isEmpty_or_nonempty ι
  · refine ⟨‖f 0‖ + 1, add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one, fun m => ?_⟩
    obtain rfl : m = 0 := funext (IsEmpty.elim ‹_›)
    simp [univ_eq_empty, zero_le_one]
  obtain ⟨ε : ℝ, ε0 : 0 < ε, hε : ∀ m : ∀ i, E i, ‖m - 0‖ < ε → ‖f m - f 0‖ < 1⟩ :=
    NormedAddCommGroup.tendsto_nhds_nhds.1 (hf.tendsto 0) 1 zero_lt_one
  simp only [sub_zero, f.map_zero] at hε
  rcases NormedField.exists_one_lt_norm 𝕜 with ⟨c, hc⟩
  have : 0 < (‖c‖ / ε) ^ Fintype.card ι := pow_pos (div_pos (zero_lt_one.trans hc) ε0) _
  refine ⟨_, this, ?_⟩
  refine f.bound_of_shell_of_continuous hf (fun _ => ε0) (fun _ => hc) fun m hcm hm => ?_
  refine (hε m ((pi_norm_lt_iff ε0).2 hm)).le.trans ?_
  rw [← div_le_iff₀' this, one_div, ← inv_pow, inv_div, Fintype.card, ← prod_const]
  exact prod_le_prod (fun _ _ => div_nonneg ε0.le (norm_nonneg _)) fun i _ => hcm i

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a precise but hard to use version. See
`norm_image_sub_le_of_bound` for a less precise but more usable version. The bound reads
`‖f m - f m'‖ ≤
  C * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
theorem norm_image_sub_le_of_bound' [DecidableEq ι] {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) (m₁ m₂ : ∀ i, E i) :
    ‖f m₁ - f m₂‖ ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
  have A :
    ∀ s : Finset ι,
      ‖f m₁ - f (s.piecewise m₂ m₁)‖ ≤
        C * ∑ i ∈ s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
    intro s
    induction' s using Finset.induction with i s his Hrec
    · simp
    have I :
      ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ ≤
        C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
      have A : (insert i s).piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₂ i) :=
        s.piecewise_insert _ _ _
      have B : s.piecewise m₂ m₁ = Function.update (s.piecewise m₂ m₁) i (m₁ i) := by
        simp [eq_update_iff, his]
      rw [B, A, ← f.map_sub]
      apply le_trans (H _)
      gcongr with j
      by_cases h : j = i
      · rw [h]
        simp
      · by_cases h' : j ∈ s <;> simp [h', h, le_refl]
    calc
      ‖f m₁ - f ((insert i s).piecewise m₂ m₁)‖ ≤
          ‖f m₁ - f (s.piecewise m₂ m₁)‖ +
            ‖f (s.piecewise m₂ m₁) - f ((insert i s).piecewise m₂ m₁)‖ := by
        rw [← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm]
        exact dist_triangle _ _ _
      _ ≤ (C * ∑ i ∈ s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) +
            C * ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
        (add_le_add Hrec I)
      _ = C * ∑ i ∈ insert i s, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ := by
        simp [his, add_comm, left_distrib]
  convert A univ
  simp

/-- If `f` satisfies a boundedness property around `0`, one can deduce a bound on `f m₁ - f m₂`
using the multilinearity. Here, we give a usable but not very precise version. See
`norm_image_sub_le_of_bound'` for a more precise but less usable version. The bound is
`‖f m - f m'‖ ≤ C * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
theorem norm_image_sub_le_of_bound {C : ℝ} (hC : 0 ≤ C) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m₁ m₂ : ∀ i, E i) :
    ‖f m₁ - f m₂‖ ≤ C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
  classical
  have A :
    ∀ i : ι,
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) ≤
        ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
    intro i
    calc
      ∏ j, (if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖) ≤
          ∏ j : ι, Function.update (fun _ => max ‖m₁‖ ‖m₂‖) i ‖m₁ - m₂‖ j := by
        apply Finset.prod_le_prod
        · intro j _
          by_cases h : j = i <;> simp [h, norm_nonneg]
        · intro j _
          by_cases h : j = i
          · rw [h]
            simp only [ite_true, Function.update_same]
            exact norm_le_pi_norm (m₁ - m₂) i
          · simp [h, -le_max_iff, -max_le_iff, max_le_max, norm_le_pi_norm (_ : ∀ i, E i)]
      _ = ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by
        rw [prod_update_of_mem (Finset.mem_univ _)]
        simp [card_univ_diff]
  calc
    ‖f m₁ - f m₂‖ ≤ C * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
      f.norm_image_sub_le_of_bound' hC H m₁ m₂
    _ ≤ C * ∑ _i, ‖m₁ - m₂‖ * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) := by gcongr; apply A
    _ = C * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      ring

/-- If a multilinear map satisfies an inequality `‖f m‖ ≤ C * ∏ i, ‖m i‖`, then it is
continuous. -/
theorem continuous_of_bound (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : Continuous f := by
  let D := max C 1
  have D_pos : 0 ≤ D := le_trans zero_le_one (le_max_right _ _)
  replace H (m) : ‖f m‖ ≤ D * ∏ i, ‖m i‖ :=
    (H m).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) <| by positivity)
  refine continuous_iff_continuousAt.2 fun m => ?_
  refine
    continuousAt_of_locally_lipschitz zero_lt_one
      (D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1)) fun m' h' => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have : max ‖m'‖ ‖m‖ ≤ ‖m‖ + 1 := by
    simp [zero_le_one, norm_le_of_mem_closedBall (le_of_lt h')]
  calc
    ‖f m' - f m‖ ≤ D * Fintype.card ι * max ‖m'‖ ‖m‖ ^ (Fintype.card ι - 1) * ‖m' - m‖ :=
      f.norm_image_sub_le_of_bound D_pos H m' m
    _ ≤ D * Fintype.card ι * (‖m‖ + 1) ^ (Fintype.card ι - 1) * ‖m' - m‖ := by gcongr

/-- Constructing a continuous multilinear map from a multilinear map satisfying a boundedness
condition. -/
def mkContinuous (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ContinuousMultilinearMap 𝕜 E G :=
  { f with cont := f.continuous_of_bound C H }

@[simp]
theorem coe_mkContinuous (C : ℝ) (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ⇑(f.mkContinuous C H) = f :=
  rfl

/-- Given a multilinear map in `n` variables, if one restricts it to `k` variables putting `z` on
the other coordinates, then the resulting restricted function satisfies an inequality
`‖f.restr v‖ ≤ C * ‖z‖^(n-k) * Π ‖v i‖` if the original function satisfies `‖f v‖ ≤ C * Π ‖v i‖`. -/
theorem restr_norm_le {k n : ℕ} (f : (MultilinearMap 𝕜 (fun _ : Fin n => G) G' : _))
    (s : Finset (Fin n)) (hk : s.card = k) (z : G) {C : ℝ} (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (v : Fin k → G) : ‖f.restr s hk z v‖ ≤ C * ‖z‖ ^ (n - k) * ∏ i, ‖v i‖ := by
  rw [mul_right_comm, mul_assoc]
  convert H _ using 2
  simp only [apply_dite norm, Fintype.prod_dite, prod_const ‖z‖, Finset.card_univ,
    Fintype.card_of_subtype sᶜ fun _ => mem_compl, card_compl, Fintype.card_fin, hk, mk_coe, ←
    (s.orderIsoOfFin hk).symm.bijective.prod_comp fun x => ‖v x‖]
  convert rfl

end MultilinearMap

/-!
### Continuous multilinear maps

We define the norm `‖f‖` of a continuous multilinear map `f` in finitely many variables as the
smallest number such that `‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖` for all `m`. We show that this
defines a normed space structure on `ContinuousMultilinearMap 𝕜 E G`.
-/


namespace ContinuousMultilinearMap

variable [Fintype ι] (c : 𝕜) (f g : ContinuousMultilinearMap 𝕜 E G) (m : ∀ i, E i)

theorem bound : ∃ C : ℝ, 0 < C ∧ ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  f.toMultilinearMap.exists_bound_of_continuous f.2

open Real

/-- The operator norm of a continuous multilinear map is the inf of all its bounds. -/
def opNorm :=
  sInf { c | 0 ≤ (c : ℝ) ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ }

instance hasOpNorm : Norm (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨opNorm⟩

/-- An alias of `ContinuousMultilinearMap.hasOpNorm` with non-dependent types to help typeclass
search. -/
instance hasOpNorm' : Norm (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :=
  ContinuousMultilinearMap.hasOpNorm

theorem norm_def : ‖f‖ = sInf { c | 0 ≤ (c : ℝ) ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ } :=
  rfl

-- So that invocations of `le_csInf` make sense: we show that the set of
-- bounds is nonempty and bounded below.
theorem bounds_nonempty {f : ContinuousMultilinearMap 𝕜 E G} :
    ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ } :=
  let ⟨M, hMp, hMb⟩ := f.bound
  ⟨M, le_of_lt hMp, hMb⟩

theorem bounds_bddBelow {f : ContinuousMultilinearMap 𝕜 E G} :
    BddBelow { c | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖ } :=
  ⟨0, fun _ ⟨hn, _⟩ => hn⟩

theorem isLeast_opNorm : IsLeast {c : ℝ | 0 ≤ c ∧ ∀ m, ‖f m‖ ≤ c * ∏ i, ‖m i‖} ‖f‖ := by
  refine IsClosed.isLeast_csInf ?_ bounds_nonempty bounds_bddBelow
  simp only [Set.setOf_and, Set.setOf_forall]
  exact isClosed_Ici.inter (isClosed_iInter fun m ↦
    isClosed_le continuous_const (continuous_id.mul continuous_const))

@[deprecated (since := "2024-02-02")] alias isLeast_op_norm := isLeast_opNorm

theorem opNorm_nonneg : 0 ≤ ‖f‖ :=
  Real.sInf_nonneg _ fun _ ⟨hx, _⟩ => hx

@[deprecated (since := "2024-02-02")] alias op_norm_nonneg := opNorm_nonneg

/-- The fundamental property of the operator norm of a continuous multilinear map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`. -/
theorem le_opNorm : ‖f m‖ ≤ ‖f‖ * ∏ i, ‖m i‖ := f.isLeast_opNorm.1.2 m

@[deprecated (since := "2024-02-02")] alias le_op_norm := le_opNorm

variable {f m}

theorem le_mul_prod_of_le_opNorm_of_le {C : ℝ} {b : ι → ℝ} (hC : ‖f‖ ≤ C) (hm : ∀ i, ‖m i‖ ≤ b i) :
    ‖f m‖ ≤ C * ∏ i, b i :=
  (f.le_opNorm m).trans <| mul_le_mul hC (prod_le_prod (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ hm _)
    (by positivity) ((opNorm_nonneg _).trans hC)

@[deprecated (since := "2024-02-02")]
alias le_mul_prod_of_le_op_norm_of_le := le_mul_prod_of_le_opNorm_of_le

variable (f)

theorem le_opNorm_mul_prod_of_le {b : ι → ℝ} (hm : ∀ i, ‖m i‖ ≤ b i) : ‖f m‖ ≤ ‖f‖ * ∏ i, b i :=
  le_mul_prod_of_le_opNorm_of_le le_rfl hm

@[deprecated (since := "2024-02-02")] alias le_op_norm_mul_prod_of_le := le_opNorm_mul_prod_of_le

theorem le_opNorm_mul_pow_card_of_le {b : ℝ} (hm : ‖m‖ ≤ b) :
    ‖f m‖ ≤ ‖f‖ * b ^ Fintype.card ι := by
  simpa only [prod_const] using f.le_opNorm_mul_prod_of_le fun i => (norm_le_pi_norm m i).trans hm

@[deprecated (since := "2024-02-02")]
alias le_op_norm_mul_pow_card_of_le := le_opNorm_mul_pow_card_of_le

theorem le_opNorm_mul_pow_of_le {n : ℕ} {Ei : Fin n → Type*} [∀ i, SeminormedAddCommGroup (Ei i)]
    [∀ i, NormedSpace 𝕜 (Ei i)] (f : ContinuousMultilinearMap 𝕜 Ei G) {m : ∀ i, Ei i} {b : ℝ}
    (hm : ‖m‖ ≤ b) : ‖f m‖ ≤ ‖f‖ * b ^ n := by
  simpa only [Fintype.card_fin] using f.le_opNorm_mul_pow_card_of_le hm

@[deprecated (since := "2024-02-02")] alias le_op_norm_mul_pow_of_le := le_opNorm_mul_pow_of_le

variable {f} (m)

theorem le_of_opNorm_le {C : ℝ} (h : ‖f‖ ≤ C) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  le_mul_prod_of_le_opNorm_of_le h fun _ ↦ le_rfl

@[deprecated (since := "2024-02-02")] alias le_of_op_norm_le := le_of_opNorm_le

variable (f)

theorem ratio_le_opNorm : (‖f m‖ / ∏ i, ‖m i‖) ≤ ‖f‖ :=
  div_le_of_nonneg_of_le_mul (by positivity) (opNorm_nonneg _) (f.le_opNorm m)

@[deprecated (since := "2024-02-02")] alias ratio_le_op_norm := ratio_le_opNorm

/-- The image of the unit ball under a continuous multilinear map is bounded. -/
theorem unit_le_opNorm (h : ‖m‖ ≤ 1) : ‖f m‖ ≤ ‖f‖ :=
  (le_opNorm_mul_pow_card_of_le f h).trans <| by simp

@[deprecated (since := "2024-02-02")] alias unit_le_op_norm := unit_le_opNorm

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
theorem opNorm_le_bound {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ m, ‖f m‖ ≤ M * ∏ i, ‖m i‖) : ‖f‖ ≤ M :=
  csInf_le bounds_bddBelow ⟨hMp, hM⟩

@[deprecated (since := "2024-02-02")] alias op_norm_le_bound := opNorm_le_bound

theorem opNorm_le_iff {C : ℝ} (hC : 0 ≤ C) : ‖f‖ ≤ C ↔ ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  ⟨fun h _ ↦ le_of_opNorm_le _ h, opNorm_le_bound _ hC⟩

@[deprecated (since := "2024-02-02")] alias op_norm_le_iff := opNorm_le_iff

/-- The operator norm satisfies the triangle inequality. -/
theorem opNorm_add_le : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  opNorm_le_bound _ (add_nonneg (opNorm_nonneg _) (opNorm_nonneg _)) fun x => by
    rw [add_mul]
    exact norm_add_le_of_le (le_opNorm _ _) (le_opNorm _ _)

@[deprecated (since := "2024-02-02")] alias op_norm_add_le := opNorm_add_le

theorem opNorm_zero : ‖(0 : ContinuousMultilinearMap 𝕜 E G)‖ = 0 :=
  (opNorm_nonneg _).antisymm' <| opNorm_le_bound 0 le_rfl fun m => by simp

@[deprecated (since := "2024-02-02")] alias op_norm_zero := opNorm_zero

section

variable {𝕜' : Type*} [NormedField 𝕜'] [NormedSpace 𝕜' G] [SMulCommClass 𝕜 𝕜' G]

theorem opNorm_smul_le (c : 𝕜') : ‖c • f‖ ≤ ‖c‖ * ‖f‖ :=
  (c • f).opNorm_le_bound (mul_nonneg (norm_nonneg _) (opNorm_nonneg _)) fun m ↦ by
    rw [smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)

@[deprecated (since := "2024-02-02")] alias op_norm_smul_le := opNorm_smul_le

theorem opNorm_neg : ‖-f‖ = ‖f‖ := by
  rw [norm_def]
  apply congr_arg
  ext
  simp

@[deprecated (since := "2024-02-02")] alias op_norm_neg := opNorm_neg

variable (𝕜 E G) in
/-- Operator seminorm on the space of continuous multilinear maps, as `Seminorm`.

We use this seminorm
to define a `SeminormedAddCommGroup` structure on `ContinuousMultilinearMap 𝕜 E G`,
but we have to override the projection `UniformSpace`
so that it is definitionally equal to the one coming from the topologies on `E` and `G`. -/
protected def seminorm : Seminorm 𝕜 (ContinuousMultilinearMap 𝕜 E G) :=
  .ofSMulLE norm opNorm_zero opNorm_add_le fun c f ↦ opNorm_smul_le f c

private lemma uniformity_eq_seminorm :
    𝓤 (ContinuousMultilinearMap 𝕜 E G) = ⨅ r > 0, 𝓟 {f | ‖f.1 - f.2‖ < r} := by
  refine (ContinuousMultilinearMap.seminorm 𝕜 E G).uniformity_eq_of_hasBasis
    (ContinuousMultilinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall)
    ?_ fun (s, r) ⟨hs, hr⟩ ↦ ?_
  · rcases NormedField.exists_lt_norm 𝕜 1 with ⟨c, hc⟩
    have hc₀ : 0 < ‖c‖ := one_pos.trans hc
    simp only [hasBasis_nhds_zero.mem_iff, Prod.exists]
    use 1, closedBall 0 ‖c‖, closedBall 0 1
    suffices ∀ f : ContinuousMultilinearMap 𝕜 E G, (∀ x, ‖x‖ ≤ ‖c‖ → ‖f x‖ ≤ 1) → ‖f‖ ≤ 1 by
      simpa [NormedSpace.isVonNBounded_closedBall, closedBall_mem_nhds, Set.subset_def, Set.MapsTo]
    intro f hf
    refine opNorm_le_bound _ (by positivity) <|
      f.1.bound_of_shell_of_continuous f.2 (fun _ ↦ hc₀) (fun _ ↦ hc) fun x hcx hx ↦ ?_
    calc
      ‖f x‖ ≤ 1 := hf _ <| (pi_norm_le_iff_of_nonneg (norm_nonneg c)).2 fun i ↦ (hx i).le
      _ = ∏ i : ι, 1 := by simp
      _ ≤ ∏ i, ‖x i‖ := Finset.prod_le_prod (fun _ _ ↦ zero_le_one) fun i _ ↦ by
        simpa only [div_self hc₀.ne'] using hcx i
      _ = 1 * ∏ i, ‖x i‖ := (one_mul _).symm
  · rcases (NormedSpace.isVonNBounded_iff' _).1 hs with ⟨ε, hε⟩
    rcases exists_pos_mul_lt hr (ε ^ Fintype.card ι) with ⟨δ, hδ₀, hδ⟩
    refine ⟨δ, hδ₀, fun f hf x hx ↦ ?_⟩
    simp only [Seminorm.mem_ball_zero, mem_closedBall_zero_iff] at hf ⊢
    replace hf : ‖f‖ ≤ δ := hf.le
    replace hx : ‖x‖ ≤ ε := hε x hx
    calc
      ‖f x‖ ≤ ‖f‖ * ε ^ Fintype.card ι := le_opNorm_mul_pow_card_of_le f hx
      _ ≤ δ * ε ^ Fintype.card ι := by have := (norm_nonneg x).trans hx; gcongr
      _ ≤ r := (mul_comm _ _).trans_le hδ.le

instance instPseudoMetricSpace : PseudoMetricSpace (ContinuousMultilinearMap 𝕜 E G) :=
  .replaceUniformity
    (ContinuousMultilinearMap.seminorm 𝕜 E G).toSeminormedAddCommGroup.toPseudoMetricSpace
    uniformity_eq_seminorm

/-- Continuous multilinear maps themselves form a seminormed space with respect to
    the operator norm. -/
instance seminormedAddCommGroup :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G) := ⟨fun _ _ ↦ rfl⟩

/-- An alias of `ContinuousMultilinearMap.seminormedAddCommGroup` with non-dependent types to help
typeclass search. -/
instance seminormedAddCommGroup' :
    SeminormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : ι => G) G') :=
  ContinuousMultilinearMap.seminormedAddCommGroup

instance normedSpace : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 E G) :=
  ⟨fun c f => f.opNorm_smul_le c⟩

/-- An alias of `ContinuousMultilinearMap.normedSpace` with non-dependent types to help typeclass
search. -/
instance normedSpace' : NormedSpace 𝕜' (ContinuousMultilinearMap 𝕜 (fun _ : ι => G') G) :=
  ContinuousMultilinearMap.normedSpace

/-- The fundamental property of the operator norm of a continuous multilinear map:
`‖f m‖` is bounded by `‖f‖` times the product of the `‖m i‖`, `nnnorm` version. -/
theorem le_opNNNorm : ‖f m‖₊ ≤ ‖f‖₊ * ∏ i, ‖m i‖₊ :=
  NNReal.coe_le_coe.1 <| by
    push_cast
    exact f.le_opNorm m

@[deprecated (since := "2024-02-02")] alias le_op_nnnorm := le_opNNNorm

theorem le_of_opNNNorm_le {C : ℝ≥0} (h : ‖f‖₊ ≤ C) : ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ :=
  (f.le_opNNNorm m).trans <| mul_le_mul' h le_rfl

@[deprecated (since := "2024-02-02")] alias le_of_op_nnnorm_le := le_of_opNNNorm_le

theorem opNNNorm_le_iff {C : ℝ≥0} : ‖f‖₊ ≤ C ↔ ∀ m, ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊ := by
  simp only [← NNReal.coe_le_coe]; simp [opNorm_le_iff _ C.coe_nonneg, NNReal.coe_prod]

@[deprecated (since := "2024-02-02")] alias op_nnnorm_le_iff := opNNNorm_le_iff

theorem isLeast_opNNNorm : IsLeast {C : ℝ≥0 | ∀ m, ‖f m‖₊ ≤ C * ∏ i, ‖m i‖₊} ‖f‖₊ := by
  simpa only [← opNNNorm_le_iff] using isLeast_Ici

@[deprecated (since := "2024-02-02")] alias isLeast_op_nnnorm := isLeast_opNNNorm

theorem opNNNorm_prod (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') :
    ‖f.prod g‖₊ = max ‖f‖₊ ‖g‖₊ :=
  eq_of_forall_ge_iff fun _ ↦ by
    simp only [opNNNorm_le_iff, prod_apply, Prod.nnnorm_def', max_le_iff, forall_and]

@[deprecated (since := "2024-02-02")] alias op_nnnorm_prod := opNNNorm_prod

theorem opNorm_prod (f : ContinuousMultilinearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') :
    ‖f.prod g‖ = max ‖f‖ ‖g‖ :=
  congr_arg NNReal.toReal (opNNNorm_prod f g)

@[deprecated (since := "2024-02-02")] alias op_norm_prod := opNorm_prod

theorem opNNNorm_pi
    [∀ i', SeminormedAddCommGroup (E' i')] [∀ i', NormedSpace 𝕜 (E' i')]
    (f : ∀ i', ContinuousMultilinearMap 𝕜 E (E' i')) : ‖pi f‖₊ = ‖f‖₊ :=
  eq_of_forall_ge_iff fun _ ↦ by simpa [opNNNorm_le_iff, pi_nnnorm_le_iff] using forall_swap

theorem opNorm_pi {ι' : Type v'} [Fintype ι'] {E' : ι' → Type wE'}
    [∀ i', SeminormedAddCommGroup (E' i')] [∀ i', NormedSpace 𝕜 (E' i')]
    (f : ∀ i', ContinuousMultilinearMap 𝕜 E (E' i')) :
    ‖pi f‖ = ‖f‖ :=
  congr_arg NNReal.toReal (opNNNorm_pi f)

@[deprecated (since := "2024-02-02")] alias op_norm_pi := opNorm_pi

section

@[simp]
theorem norm_ofSubsingleton [Subsingleton ι] (i : ι) (f : G →L[𝕜] G') :
    ‖ofSubsingleton 𝕜 G G' i f‖ = ‖f‖ := by
  letI : Unique ι := uniqueOfSubsingleton i
  simp [norm_def, ContinuousLinearMap.norm_def, (Equiv.funUnique _ _).symm.surjective.forall]

@[simp]
theorem nnnorm_ofSubsingleton [Subsingleton ι] (i : ι) (f : G →L[𝕜] G') :
    ‖ofSubsingleton 𝕜 G G' i f‖₊ = ‖f‖₊ :=
  NNReal.eq <| norm_ofSubsingleton i f

variable (𝕜 G)

/-- Linear isometry between continuous linear maps from `G` to `G'`
and continuous `1`-multilinear maps from `G` to `G'`. -/
@[simps apply symm_apply]
def ofSubsingletonₗᵢ [Subsingleton ι] (i : ι) :
    (G →L[𝕜] G') ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ G) G' :=
  { ofSubsingleton 𝕜 G G' i with
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    norm_map' := norm_ofSubsingleton i }

theorem norm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ ≤ 1 := by
  rw [norm_ofSubsingleton]
  apply ContinuousLinearMap.norm_id_le

theorem nnnorm_ofSubsingleton_id_le [Subsingleton ι] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖₊ ≤ 1 :=
  norm_ofSubsingleton_id_le _ _ _

variable {G} (E)

@[simp]
theorem norm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖ = ‖x‖ := by
  apply le_antisymm
  · refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    rw [Fintype.prod_empty, mul_one, constOfIsEmpty_apply]
  · simpa using (constOfIsEmpty 𝕜 E x).le_opNorm 0

@[simp]
theorem nnnorm_constOfIsEmpty [IsEmpty ι] (x : G) : ‖constOfIsEmpty 𝕜 E x‖₊ = ‖x‖₊ :=
  NNReal.eq <| norm_constOfIsEmpty _ _ _

end

section

variable (𝕜 E E' G G')

/-- `ContinuousMultilinearMap.prod` as a `LinearIsometryEquiv`. -/
def prodL :
    ContinuousMultilinearMap 𝕜 E G × ContinuousMultilinearMap 𝕜 E G' ≃ₗᵢ[𝕜]
      ContinuousMultilinearMap 𝕜 E (G × G') where
  toFun f := f.1.prod f.2
  invFun f :=
    ((ContinuousLinearMap.fst 𝕜 G G').compContinuousMultilinearMap f,
      (ContinuousLinearMap.snd 𝕜 G G').compContinuousMultilinearMap f)
  map_add' f g := rfl
  map_smul' c f := rfl
  left_inv f := by ext <;> rfl
  right_inv f := by ext <;> rfl
  norm_map' f := opNorm_prod f.1 f.2

/-- `ContinuousMultilinearMap.pi` as a `LinearIsometryEquiv`. -/
def piₗᵢ {ι' : Type v'} [Fintype ι'] {E' : ι' → Type wE'} [∀ i', NormedAddCommGroup (E' i')]
    [∀ i', NormedSpace 𝕜 (E' i')] :
    @LinearIsometryEquiv 𝕜 𝕜 _ _ (RingHom.id 𝕜) _ _ _ (∀ i', ContinuousMultilinearMap 𝕜 E (E' i'))
      (ContinuousMultilinearMap 𝕜 E (∀ i, E' i)) _ _ (@Pi.module ι' _ 𝕜 _ _ fun _ => inferInstance)
      _ where
  toLinearEquiv := piLinearEquiv
  norm_map' := opNorm_pi

end

end

section RestrictScalars

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜' 𝕜]
variable [NormedSpace 𝕜' G] [IsScalarTower 𝕜' 𝕜 G]
variable [∀ i, NormedSpace 𝕜' (E i)] [∀ i, IsScalarTower 𝕜' 𝕜 (E i)]

@[simp]
theorem norm_restrictScalars : ‖f.restrictScalars 𝕜'‖ = ‖f‖ := rfl

variable (𝕜')

/-- `ContinuousMultilinearMap.restrictScalars` as a `LinearIsometry`. -/
def restrictScalarsₗᵢ : ContinuousMultilinearMap 𝕜 E G →ₗᵢ[𝕜'] ContinuousMultilinearMap 𝕜' E G where
  toFun := restrictScalars 𝕜'
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

end RestrictScalars

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, precise version.
For a less precise but more usable version, see `norm_image_sub_le`. The bound reads
`‖f m - f m'‖ ≤
  ‖f‖ * ‖m 1 - m' 1‖ * max ‖m 2‖ ‖m' 2‖ * max ‖m 3‖ ‖m' 3‖ * ... * max ‖m n‖ ‖m' n‖ + ...`,
where the other terms in the sum are the same products where `1` is replaced by any `i`. -/
theorem norm_image_sub_le' [DecidableEq ι] (m₁ m₂ : ∀ i, E i) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * ∑ i, ∏ j, if j = i then ‖m₁ i - m₂ i‖ else max ‖m₁ j‖ ‖m₂ j‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound' (norm_nonneg _) f.le_opNorm _ _

/-- The difference `f m₁ - f m₂` is controlled in terms of `‖f‖` and `‖m₁ - m₂‖`, less precise
version. For a more precise but less usable version, see `norm_image_sub_le'`.
The bound is `‖f m - f m'‖ ≤ ‖f‖ * card ι * ‖m - m'‖ * (max ‖m‖ ‖m'‖) ^ (card ι - 1)`. -/
theorem norm_image_sub_le (m₁ m₂ : ∀ i, E i) :
    ‖f m₁ - f m₂‖ ≤ ‖f‖ * Fintype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fintype.card ι - 1) * ‖m₁ - m₂‖ :=
  f.toMultilinearMap.norm_image_sub_le_of_bound (norm_nonneg _) f.le_opNorm _ _

end ContinuousMultilinearMap

variable [Fintype ι]

/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem MultilinearMap.mkContinuous_norm_le (f : MultilinearMap 𝕜 E G) {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ C :=
  ContinuousMultilinearMap.opNorm_le_bound _ hC fun m => H m

/-- If a continuous multilinear map is constructed from a multilinear map via the constructor
`mkContinuous`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
theorem MultilinearMap.mkContinuous_norm_le' (f : MultilinearMap 𝕜 E G) {C : ℝ}
    (H : ∀ m, ‖f m‖ ≤ C * ∏ i, ‖m i‖) : ‖f.mkContinuous C H‖ ≤ max C 0 :=
  ContinuousMultilinearMap.opNorm_le_bound _ (le_max_right _ _) fun m ↦ (H m).trans <|
    mul_le_mul_of_nonneg_right (le_max_left _ _) <| by positivity

namespace ContinuousMultilinearMap

/-- Given a continuous multilinear map `f` on `n` variables (parameterized by `Fin n`) and a subset
`s` of `k` of these variables, one gets a new continuous multilinear map on `Fin k` by varying
these variables, and fixing the other ones equal to a given value `z`. It is denoted by
`f.restr s hk z`, where `hk` is a proof that the cardinality of `s` is `k`. The implicit
identification between `Fin k` and `s` that we use is the canonical (increasing) bijection. -/
def restr {k n : ℕ} (f : (G[×n]→L[𝕜] G' : _)) (s : Finset (Fin n)) (hk : s.card = k) (z : G) :
    G[×k]→L[𝕜] G' :=
  (f.toMultilinearMap.restr s hk z).mkContinuous (‖f‖ * ‖z‖ ^ (n - k)) fun _ =>
    MultilinearMap.restr_norm_le _ _ _ _ f.le_opNorm _

theorem norm_restr {k n : ℕ} (f : G[×n]→L[𝕜] G') (s : Finset (Fin n)) (hk : s.card = k) (z : G) :
    ‖f.restr s hk z‖ ≤ ‖f‖ * ‖z‖ ^ (n - k) := by
  apply MultilinearMap.mkContinuous_norm_le
  exact mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)

section

variable {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]

@[simp]
theorem norm_mkPiAlgebra_le [Nonempty ι] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebra_apply, one_mul]
  exact norm_prod_le' _ univ_nonempty _

theorem norm_mkPiAlgebra_of_empty [IsEmpty ι] :
    ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = ‖(1 : A)‖ := by
  apply le_antisymm
  · apply opNorm_le_bound <;> simp
  · -- Porting note: have to annotate types to get mvars to unify
    convert ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => (1 : A)
    simp [eq_empty_of_isEmpty (univ : Finset ι)]

@[simp]
theorem norm_mkPiAlgebra [NormOneClass A] : ‖ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A‖ = 1 := by
  cases isEmpty_or_nonempty ι
  · simp [norm_mkPiAlgebra_of_empty]
  · refine le_antisymm norm_mkPiAlgebra_le ?_
    convert ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι A) fun _ => 1
    simp

end

section

variable {n : ℕ} {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]

theorem norm_mkPiAlgebraFin_succ_le : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n.succ A‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun m => ?_
  simp only [ContinuousMultilinearMap.mkPiAlgebraFin_apply, one_mul, List.ofFn_eq_map,
    Fin.prod_univ_def, Multiset.map_coe, Multiset.prod_coe]
  refine (List.norm_prod_le' ?_).trans_eq ?_
  · rw [Ne, List.map_eq_nil, List.finRange_eq_nil]
    exact Nat.succ_ne_zero _
  rw [List.map_map, Function.comp_def]

theorem norm_mkPiAlgebraFin_le_of_pos (hn : 0 < n) :
    ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ ≤ 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact norm_mkPiAlgebraFin_succ_le

theorem norm_mkPiAlgebraFin_zero : ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A‖ = ‖(1 : A)‖ := by
  refine le_antisymm ?_ ?_
  · refine opNorm_le_bound _ (norm_nonneg (1 : A)) ?_
    simp
  · convert ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 0 A) fun _ => (1 : A)
    simp

theorem norm_mkPiAlgebraFin_le :
    ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ ≤ max 1 ‖(1 : A)‖ := by
  cases n
  · exact norm_mkPiAlgebraFin_zero.le.trans (le_max_right _ _)
  · exact (norm_mkPiAlgebraFin_le_of_pos (Nat.zero_lt_succ _)).trans (le_max_left _ _)

@[simp]
theorem norm_mkPiAlgebraFin [NormOneClass A] :
    ‖ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A‖ = 1 := by
  cases n
  · rw [norm_mkPiAlgebraFin_zero]
    simp
  · refine le_antisymm norm_mkPiAlgebraFin_succ_le ?_
    refine le_of_eq_of_le ?_ <|
      ratio_le_opNorm (ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 (Nat.succ _) A) fun _ => 1
    simp

end

@[simp]
theorem nnnorm_smulRight (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
    ‖f.smulRight z‖₊ = ‖f‖₊ * ‖z‖₊ := by
  refine le_antisymm ?_ ?_
  · refine (opNNNorm_le_iff _ |>.2 fun m => (nnnorm_smul_le _ _).trans ?_)
    rw [mul_right_comm]
    gcongr
    exact le_opNNNorm _ _
  · obtain hz | hz := eq_zero_or_pos ‖z‖₊
    · simp [hz]
    rw [← le_div_iff₀ hz, opNNNorm_le_iff]
    intro m
    rw [div_mul_eq_mul_div, le_div_iff₀ hz]
    refine le_trans ?_ ((f.smulRight z).le_opNNNorm m)
    rw [smulRight_apply, nnnorm_smul]

@[simp]
theorem norm_smulRight (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
    ‖f.smulRight z‖ = ‖f‖ * ‖z‖ :=
  congr_arg NNReal.toReal (nnnorm_smulRight f z)

@[simp]
theorem norm_mkPiRing (z : G) : ‖ContinuousMultilinearMap.mkPiRing 𝕜 ι z‖ = ‖z‖ := by
  rw [ContinuousMultilinearMap.mkPiRing, norm_smulRight, norm_mkPiAlgebra, one_mul]

variable (𝕜 E G) in
/-- Continuous bilinear map realizing `(f, z) ↦ f.smulRight z`. -/
def smulRightL : ContinuousMultilinearMap 𝕜 E 𝕜 →L[𝕜] G →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  LinearMap.mkContinuous₂
    { toFun := fun f ↦
        { toFun := fun z ↦ f.smulRight z
          map_add' := fun x y ↦ by ext; simp
          map_smul' := fun c x ↦ by ext; simp [smul_smul, mul_comm] }
      map_add' := fun f g ↦ by ext; simp [add_smul]
      map_smul' := fun c f ↦ by ext; simp [smul_smul] }
    1 (fun f z ↦ by simp [norm_smulRight])

@[simp] lemma smulRightL_apply (f : ContinuousMultilinearMap 𝕜 E 𝕜) (z : G) :
  smulRightL 𝕜 E G f z = f.smulRight z := rfl

#adaptation_note
/--
Before https://github.com/leanprover/lean4/pull/4119 we had to create a local instance:
```
letI : SeminormedAddCommGroup
  (ContinuousMultilinearMap 𝕜 E 𝕜 →L[𝕜] G →L[𝕜] ContinuousMultilinearMap 𝕜 E G) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
    (F := G →L[𝕜] ContinuousMultilinearMap 𝕜 E G) (σ₁₂ := RingHom.id 𝕜)
```
-/
set_option maxSynthPendingDepth 2 in
lemma norm_smulRightL_le : ‖smulRightL 𝕜 E G‖ ≤ 1 :=
  LinearMap.mkContinuous₂_norm_le _ zero_le_one _

variable (𝕜 ι G)

/-- Continuous multilinear maps on `𝕜^n` with values in `G` are in bijection with `G`, as such a
continuous multilinear map is completely determined by its value on the constant vector made of
ones. We register this bijection as a linear isometry in
`ContinuousMultilinearMap.piFieldEquiv`. -/
protected def piFieldEquiv : G ≃ₗᵢ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => 𝕜) G where
  toFun z := ContinuousMultilinearMap.mkPiRing 𝕜 ι z
  invFun f := f fun i => 1
  map_add' z z' := by
    ext m
    simp [smul_add]
  map_smul' c z := by
    ext m
    simp [smul_smul, mul_comm]
  left_inv z := by simp
  right_inv f := f.mkPiRing_apply_one_eq_self
  norm_map' := norm_mkPiRing

end ContinuousMultilinearMap

namespace ContinuousLinearMap

theorem norm_compContinuousMultilinearMap_le (g : G →L[𝕜] G') (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖g.compContinuousMultilinearMap f‖ ≤ ‖g‖ * ‖f‖ :=
  ContinuousMultilinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun m =>
    calc
      ‖g (f m)‖ ≤ ‖g‖ * (‖f‖ * ∏ i, ‖m i‖) := g.le_opNorm_of_le <| f.le_opNorm _
      _ = _ := (mul_assoc _ _ _).symm

variable (𝕜 E G G')


/-- `ContinuousLinearMap.compContinuousMultilinearMap` as a bundled continuous bilinear map. -/
def compContinuousMultilinearMapL :
    (G →L[𝕜] G') →L[𝕜] ContinuousMultilinearMap 𝕜 E G →L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜 compContinuousMultilinearMap (fun f₁ f₂ g => rfl) (fun c f g => rfl)
      (fun f g₁ g₂ => by ext1; apply f.map_add)
      (fun c f g => by ext1; simp))
    1
    fun f g => by rw [one_mul]; exact f.norm_compContinuousMultilinearMap_le g

variable {𝕜 G G'}

/-- `ContinuousLinearMap.compContinuousMultilinearMap` as a bundled
continuous linear equiv. -/
nonrec
def _root_.ContinuousLinearEquiv.compContinuousMultilinearMapL (g : G ≃L[𝕜] G') :
    ContinuousMultilinearMap 𝕜 E G ≃L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  { compContinuousMultilinearMapL 𝕜 E G G' g.toContinuousLinearMap with
    invFun := compContinuousMultilinearMapL 𝕜 E G' G g.symm.toContinuousLinearMap
    left_inv := by
      intro f
      ext1 m
      simp [compContinuousMultilinearMapL]
    right_inv := by
      intro f
      ext1 m
      simp [compContinuousMultilinearMapL]
    continuous_toFun := (compContinuousMultilinearMapL 𝕜 E G G' g.toContinuousLinearMap).continuous
    continuous_invFun :=
      (compContinuousMultilinearMapL 𝕜 E G' G g.symm.toContinuousLinearMap).continuous }

@[simp]
theorem _root_.ContinuousLinearEquiv.compContinuousMultilinearMapL_symm (g : G ≃L[𝕜] G') :
    (g.compContinuousMultilinearMapL E).symm = g.symm.compContinuousMultilinearMapL E :=
  rfl

variable {E}

@[simp]
theorem _root_.ContinuousLinearEquiv.compContinuousMultilinearMapL_apply (g : G ≃L[𝕜] G')
    (f : ContinuousMultilinearMap 𝕜 E G) :
    g.compContinuousMultilinearMapL E f = (g : G →L[𝕜] G').compContinuousMultilinearMap f :=
  rfl

/-- Flip arguments in `f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G'` to get
`ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G')` -/
@[simps! apply_apply]
def flipMultilinear (f : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G') :
    ContinuousMultilinearMap 𝕜 E (G →L[𝕜] G') :=
  MultilinearMap.mkContinuous
    { toFun := fun m =>
        LinearMap.mkContinuous
          { toFun := fun x => f x m
            map_add' := fun x y => by simp only [map_add, ContinuousMultilinearMap.add_apply]
            map_smul' := fun c x => by
              simp only [ContinuousMultilinearMap.smul_apply, map_smul, RingHom.id_apply] }
          (‖f‖ * ∏ i, ‖m i‖) fun x => by
          rw [mul_right_comm]
          exact (f x).le_of_opNorm_le _ (f.le_opNorm x)
      map_add' := fun m i x y => by
        ext1
        simp only [add_apply, ContinuousMultilinearMap.map_add, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, AddHom.coe_mk]
      map_smul' := fun m i c x => by
        ext1
        simp only [coe_smul', ContinuousMultilinearMap.map_smul, LinearMap.coe_mk,
          LinearMap.mkContinuous_apply, Pi.smul_apply, AddHom.coe_mk] }
    ‖f‖ fun m => by
      dsimp only [MultilinearMap.coe_mk]
      exact LinearMap.mkContinuous_norm_le _ (by positivity) _

end ContinuousLinearMap

theorem LinearIsometry.norm_compContinuousMultilinearMap (g : G →ₗᵢ[𝕜] G')
    (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖g.toContinuousLinearMap.compContinuousMultilinearMap f‖ = ‖f‖ := by
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
    ContinuousMultilinearMap.norm_def, Function.comp_apply]

open ContinuousMultilinearMap

namespace MultilinearMap

/-- Given a map `f : G →ₗ[𝕜] MultilinearMap 𝕜 E G'` and an estimate
`H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖`, construct a continuous linear
map from `G` to `ContinuousMultilinearMap 𝕜 E G'`.

In order to lift, e.g., a map `f : (MultilinearMap 𝕜 E G) →ₗ[𝕜] MultilinearMap 𝕜 E' G'`
to a map `(ContinuousMultilinearMap 𝕜 E G) →L[𝕜] ContinuousMultilinearMap 𝕜 E' G'`,
one can apply this construction to `f.comp ContinuousMultilinearMap.toMultilinearMapLinear`
which is a linear map from `ContinuousMultilinearMap 𝕜 E G` to `MultilinearMap 𝕜 E' G'`. -/
def mkContinuousLinear (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : G →L[𝕜] ContinuousMultilinearMap 𝕜 E G' :=
  LinearMap.mkContinuous
    { toFun := fun x => (f x).mkContinuous (C * ‖x‖) <| H x
      map_add' := fun x y => by
        ext1
        simp only [_root_.map_add]
        rfl
      map_smul' := fun c x => by
        ext1
        simp only [_root_.map_smul]
        rfl }
    (max C 0) fun x => by
      rw [LinearMap.coe_mk, AddHom.coe_mk] -- Porting note: added
      exact ((f x).mkContinuous_norm_le' _).trans_eq <| by
        rw [max_mul_of_nonneg _ _ (norm_nonneg x), zero_mul]

theorem mkContinuousLinear_norm_le' (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') (C : ℝ)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ max C 0 := by
  dsimp only [mkContinuousLinear]
  exact LinearMap.mkContinuous_norm_le _ (le_max_right _ _) _

theorem mkContinuousLinear_norm_le (f : G →ₗ[𝕜] MultilinearMap 𝕜 E G') {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ x m, ‖f x m‖ ≤ C * ‖x‖ * ∏ i, ‖m i‖) : ‖mkContinuousLinear f C H‖ ≤ C :=
  (mkContinuousLinear_norm_le' f C H).trans_eq (max_eq_left hC)

variable [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]

/-- Given a map `f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)` and an estimate
`H : ∀ m m', ‖f m m'‖ ≤ C * ∏ i, ‖m i‖ * ∏ i, ‖m' i‖`, upgrade all `MultilinearMap`s in the type to
`ContinuousMultilinearMap`s. -/
def mkContinuousMultilinear (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : ℝ)
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ContinuousMultilinearMap 𝕜 E (ContinuousMultilinearMap 𝕜 E' G) :=
  mkContinuous
    { toFun := fun m => mkContinuous (f m) (C * ∏ i, ‖m i‖) <| H m
      map_add' := fun m i x y => by
        ext1
        simp
      map_smul' := fun m i c x => by
        ext1
        simp }
    (max C 0) fun m => by
      simp only [coe_mk]
      refine ((f m).mkContinuous_norm_le' _).trans_eq ?_
      rw [max_mul_of_nonneg, zero_mul]
      positivity

@[simp]
theorem mkContinuousMultilinear_apply (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : ℝ}
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) (m : ∀ i, E i) :
    ⇑(mkContinuousMultilinear f C H m) = f m :=
  rfl

theorem mkContinuousMultilinear_norm_le' (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) (C : ℝ)
    (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousMultilinear f C H‖ ≤ max C 0 := by
  dsimp only [mkContinuousMultilinear]
  exact mkContinuous_norm_le _ (le_max_right _ _) _

theorem mkContinuousMultilinear_norm_le (f : MultilinearMap 𝕜 E (MultilinearMap 𝕜 E' G)) {C : ℝ}
    (hC : 0 ≤ C) (H : ∀ m₁ m₂, ‖f m₁ m₂‖ ≤ (C * ∏ i, ‖m₁ i‖) * ∏ i, ‖m₂ i‖) :
    ‖mkContinuousMultilinear f C H‖ ≤ C :=
  (mkContinuousMultilinear_norm_le' f C H).trans_eq (max_eq_left hC)

end MultilinearMap

namespace ContinuousMultilinearMap


theorem norm_compContinuousLinearMap_le (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i →L[𝕜] E₁ i) : ‖g.compContinuousLinearMap f‖ ≤ ‖g‖ * ∏ i, ‖f i‖ :=
  opNorm_le_bound _ (by positivity) fun m =>
    calc
      ‖g fun i => f i (m i)‖ ≤ ‖g‖ * ∏ i, ‖f i (m i)‖ := g.le_opNorm _
      _ ≤ ‖g‖ * ∏ i, ‖f i‖ * ‖m i‖ :=
        (mul_le_mul_of_nonneg_left
          (prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => (f i).le_opNorm (m i))
          (norm_nonneg g))
      _ = (‖g‖ * ∏ i, ‖f i‖) * ∏ i, ‖m i‖ := by rw [prod_mul_distrib, mul_assoc]

theorem norm_compContinuous_linearIsometry_le (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i →ₗᵢ[𝕜] E₁ i) :
    ‖g.compContinuousLinearMap fun i => (f i).toContinuousLinearMap‖ ≤ ‖g‖ := by
  refine opNorm_le_bound _ (norm_nonneg _) fun m => ?_
  apply (g.le_opNorm _).trans _
  simp only [ContinuousLinearMap.coe_coe, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map, le_rfl]

theorem norm_compContinuous_linearIsometryEquiv (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i ≃ₗᵢ[𝕜] E₁ i) :
    ‖g.compContinuousLinearMap fun i => (f i : E i →L[𝕜] E₁ i)‖ = ‖g‖ := by
  apply le_antisymm (g.norm_compContinuous_linearIsometry_le fun i => (f i).toLinearIsometry)
  have : g = (g.compContinuousLinearMap fun i => (f i : E i →L[𝕜] E₁ i)).compContinuousLinearMap
      fun i => ((f i).symm : E₁ i →L[𝕜] E i) := by
    ext1 m
    simp only [compContinuousLinearMap_apply, LinearIsometryEquiv.coe_coe'',
      LinearIsometryEquiv.apply_symm_apply]
  conv_lhs => rw [this]
  apply (g.compContinuousLinearMap fun i =>
    (f i : E i →L[𝕜] E₁ i)).norm_compContinuous_linearIsometry_le
      fun i => (f i).symm.toLinearIsometry

/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear map.
This implementation fixes `f : Π i, E i →L[𝕜] E₁ i`.

Actually, the map is multilinear in `f`,
see `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.

For a version fixing `g` and varying `f`, see `compContinuousLinearMapLRight`. -/
def compContinuousLinearMapL (f : ∀ i, E i →L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ G →L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  LinearMap.mkContinuous
    { toFun := fun g => g.compContinuousLinearMap f
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (∏ i, ‖f i‖)
    fun _ => (norm_compContinuousLinearMap_le _ _).trans_eq (mul_comm _ _)

@[simp]
theorem compContinuousLinearMapL_apply (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i →L[𝕜] E₁ i) : compContinuousLinearMapL f g = g.compContinuousLinearMap f :=
  rfl

variable (G) in
theorem norm_compContinuousLinearMapL_le (f : ∀ i, E i →L[𝕜] E₁ i) :
    ‖compContinuousLinearMapL (G := G) f‖ ≤ ∏ i, ‖f i‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear map.
This implementation fixes `g : ContinuousMultilinearMap 𝕜 E₁ G`.

Actually, the map is linear in `g`,
see `ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear`.

For a version fixing `f` and varying `g`, see `compContinuousLinearMapL`. -/
def compContinuousLinearMapLRight (g : ContinuousMultilinearMap 𝕜 E₁ G) :
    ContinuousMultilinearMap 𝕜 (fun i ↦ E i →L[𝕜] E₁ i) (ContinuousMultilinearMap 𝕜 E G) :=
  MultilinearMap.mkContinuous
    { toFun := fun f => g.compContinuousLinearMap f
      map_add' := by
        intro h f i f₁ f₂
        ext x
        simp only [compContinuousLinearMap_apply, add_apply]
        convert g.map_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _
      map_smul' := by
        intro h f i a f₀
        ext x
        simp only [compContinuousLinearMap_apply, smul_apply]
        convert g.map_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) <;>
          exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _ }
    (‖g‖) (fun f ↦ by simp [norm_compContinuousLinearMap_le])

@[simp]
theorem compContinuousLinearMapLRight_apply (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i →L[𝕜] E₁ i) : compContinuousLinearMapLRight g f = g.compContinuousLinearMap f :=
  rfl

variable (E) in
theorem norm_compContinuousLinearMapLRight_le (g : ContinuousMultilinearMap 𝕜 E₁ G) :
    ‖compContinuousLinearMapLRight (E := E) g‖ ≤ ‖g‖ :=
  MultilinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

variable (𝕜 E E₁ G)

open Function in
/-- If `f` is a collection of continuous linear maps, then the construction
`ContinuousMultilinearMap.compContinuousLinearMap`
sending a continuous multilinear map `g` to `g (f₁ ·, ..., fₙ ·)`
is continuous-linear in `g` and multilinear in `f₁, ..., fₙ`. -/
noncomputable def compContinuousLinearMapMultilinear :
    MultilinearMap 𝕜 (fun i ↦ E i →L[𝕜] E₁ i)
      ((ContinuousMultilinearMap 𝕜 E₁ G) →L[𝕜] ContinuousMultilinearMap 𝕜 E G) where
  toFun := compContinuousLinearMapL
  map_add' f i f₁ f₂ := by
    ext g x
    change (g fun j ↦ update f i (f₁ + f₂) j <| x j) =
        (g fun j ↦ update f i f₁ j <| x j) + g fun j ↦ update f i f₂ j (x j)
    convert g.map_add (fun j ↦ f j (x j)) i (f₁ (x i)) (f₂ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _
  map_smul' f i a f₀ := by
    ext g x
    change (g fun j ↦ update f i (a • f₀) j <| x j) = a • g fun j ↦ update f i f₀ j (x j)
    convert g.map_smul (fun j ↦ f j (x j)) i a (f₀ (x i)) <;>
      exact apply_update (fun (i : ι) (f : E i →L[𝕜] E₁ i) ↦ f (x i)) f i _ _

/-- If `f` is a collection of continuous linear maps, then the construction
`ContinuousMultilinearMap.compContinuousLinearMap`
sending a continuous multilinear map `g` to `g (f₁ ·, ..., fₙ ·)` is continuous-linear in `g` and
continuous-multilinear in `f₁, ..., fₙ`. -/
noncomputable def compContinuousLinearMapContinuousMultilinear :
    ContinuousMultilinearMap 𝕜 (fun i ↦ E i →L[𝕜] E₁ i)
      ((ContinuousMultilinearMap 𝕜 E₁ G) →L[𝕜] ContinuousMultilinearMap 𝕜 E G) :=
  @MultilinearMap.mkContinuous 𝕜 ι (fun i ↦ E i →L[𝕜] E₁ i)
    ((ContinuousMultilinearMap 𝕜 E₁ G) →L[𝕜] ContinuousMultilinearMap 𝕜 E G) _
    (fun _ ↦ ContinuousLinearMap.toSeminormedAddCommGroup)
    (fun _ ↦ ContinuousLinearMap.toNormedSpace) _ _
    (compContinuousLinearMapMultilinear 𝕜 E E₁ G) _ 1
    fun f ↦ by simpa using norm_compContinuousLinearMapL_le G f

variable {𝕜 E E₁}

/-- `ContinuousMultilinearMap.compContinuousLinearMap` as a bundled continuous linear equiv,
given `f : Π i, E i ≃L[𝕜] E₁ i`. -/
def compContinuousLinearMapEquivL (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    ContinuousMultilinearMap 𝕜 E₁ G ≃L[𝕜] ContinuousMultilinearMap 𝕜 E G :=
  { compContinuousLinearMapL fun i => (f i : E i →L[𝕜] E₁ i) with
    invFun := compContinuousLinearMapL fun i => ((f i).symm : E₁ i →L[𝕜] E i)
    continuous_toFun := (compContinuousLinearMapL fun i => (f i : E i →L[𝕜] E₁ i)).continuous
    continuous_invFun :=
      (compContinuousLinearMapL fun i => ((f i).symm : E₁ i →L[𝕜] E i)).continuous
    left_inv := by
      intro g
      ext1 m
      simp only [LinearMap.toFun_eq_coe, ContinuousLinearMap.coe_coe,
        compContinuousLinearMapL_apply, compContinuousLinearMap_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    right_inv := by
      intro g
      ext1 m
      simp only [compContinuousLinearMapL_apply, LinearMap.toFun_eq_coe,
        ContinuousLinearMap.coe_coe, compContinuousLinearMap_apply,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] }

@[simp]
theorem compContinuousLinearMapEquivL_symm (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    (compContinuousLinearMapEquivL G f).symm =
      compContinuousLinearMapEquivL G fun i : ι => (f i).symm :=
  rfl

variable {G}

@[simp]
theorem compContinuousLinearMapEquivL_apply (g : ContinuousMultilinearMap 𝕜 E₁ G)
    (f : ∀ i, E i ≃L[𝕜] E₁ i) :
    compContinuousLinearMapEquivL G f g =
      g.compContinuousLinearMap fun i => (f i : E i →L[𝕜] E₁ i) :=
  rfl

/-- One of the components of the iterated derivative of a continuous multilinear map. Given a
bijection `e` between a type `α` (typically `Fin k`) and a subset `s` of `ι`, this component is a
continuous multilinear map of `k` vectors `v₁, ..., vₖ`, mapping them
to `f (x₁, (v_{e.symm 2})₂, x₃, ...)`, where at indices `i` in `s` one uses the `i`-th coordinate of
the vector `v_{e.symm i}` and otherwise one uses the `i`-th coordinate of a reference vector `x`.
This is continuous multilinear in the components of `x` outside of `s`, and in the `v_j`. -/
noncomputable def iteratedFDerivComponent {α : Type*} [Fintype α]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· ∈ s)] :
    ContinuousMultilinearMap 𝕜 (fun (i : {a : ι // a ∉ s}) ↦ E₁ i)
      (ContinuousMultilinearMap 𝕜 (fun (_ : α) ↦ (∀ i, E₁ i)) G) :=
  (f.toMultilinearMap.iteratedFDerivComponent e).mkContinuousMultilinear ‖f‖ <| by
    intro x m
    simp only [MultilinearMap.iteratedFDerivComponent, MultilinearMap.domDomRestrictₗ,
      MultilinearMap.coe_mk, MultilinearMap.domDomRestrict_apply, coe_coe]
    apply (f.le_opNorm _).trans _
    classical
    rw [← prod_compl_mul_prod s.toFinset, mul_assoc]
    gcongr
    · apply le_of_eq
      have : ∀ x, x ∈ s.toFinsetᶜ ↔ (fun x ↦ x ∉ s) x := by simp
      rw [prod_subtype _ this]
      congr with i
      simp [i.2]
    · rw [prod_subtype _ (fun _ ↦ s.mem_toFinset), ← Equiv.prod_comp e.symm]
      apply Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) (fun i _ ↦ ?_)
      simpa only [i.2, ↓reduceDIte, Subtype.coe_eta] using norm_le_pi_norm (m (e.symm i)) ↑i

@[simp] lemma iteratedFDerivComponent_apply {α : Type*} [Fintype α]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· ∈ s)]
    (v : ∀ i : {a : ι // a ∉ s}, E₁ i) (w : α → (∀ i, E₁ i)) :
    f.iteratedFDerivComponent e v w =
      f (fun j ↦ if h : j ∈ s then w (e.symm ⟨j, h⟩) j else v ⟨j, h⟩) := by
  simp [iteratedFDerivComponent, MultilinearMap.iteratedFDerivComponent,
    MultilinearMap.domDomRestrictₗ]

lemma norm_iteratedFDerivComponent_le {α : Type*} [Fintype α]
    (f : ContinuousMultilinearMap 𝕜 E₁ G) {s : Set ι} (e : α ≃ s) [DecidablePred (· ∈ s)]
    (x : (i : ι) → E₁ i) :
    ‖f.iteratedFDerivComponent e (x ·)‖ ≤ ‖f‖ * ‖x‖ ^ (Fintype.card ι - Fintype.card α) := calc
  ‖f.iteratedFDerivComponent e (fun i ↦ x i)‖
    ≤ ‖f.iteratedFDerivComponent e‖ * ∏ i : {a : ι // a ∉ s}, ‖x i‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
  _ ≤ ‖f‖ * ∏ _i : {a : ι // a ∉ s}, ‖x‖ := by
      gcongr
      · exact MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg _) _
      · exact norm_le_pi_norm _ _
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card {a : ι // a ∉ s}) := by rw [prod_const, card_univ]
  _ = ‖f‖ * ‖x‖ ^ (Fintype.card ι - Fintype.card α) := by simp [Fintype.card_congr e]

open Classical in
/-- The `k`-th iterated derivative of a continuous multilinear map `f` at the point `x`. It is a
continuous multilinear map of `k` vectors `v₁, ..., vₖ` (with the same type as `x`), mapping them
to `∑ f (x₁, (v_{i₁})₂, x₃, ...)`, where at each index `j` one uses either `xⱼ` or one
of the `(vᵢ)ⱼ`, and each `vᵢ` has to be used exactly once.
The sum is parameterized by the embeddings of `Fin k` in the index type `ι` (or, equivalently,
by the subsets `s` of `ι` of cardinality `k` and then the bijections between `Fin k` and `s`).

The fact that this is indeed the iterated Fréchet derivative is proved in
`ContinuousMultilinearMap.iteratedFDeriv_eq`.
-/
protected def iteratedFDeriv (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : ℕ) (x : (i : ι) → E₁ i) :
    ContinuousMultilinearMap 𝕜 (fun (_ : Fin k) ↦ (∀ i, E₁ i)) G :=
  ∑ e : Fin k ↪ ι, iteratedFDerivComponent f e.toEquivRange (Pi.compRightL 𝕜 _ Subtype.val x)

/-- Controlling the norm of `f.iteratedFDeriv` when `f` is continuous multilinear. For the same
bound on the iterated derivative of `f` in the calculus sense,
see `ContinuousMultilinearMap.norm_iteratedFDeriv_le`. -/
lemma norm_iteratedFDeriv_le' (f : ContinuousMultilinearMap 𝕜 E₁ G) (k : ℕ) (x : (i : ι) → E₁ i) :
    ‖f.iteratedFDeriv k x‖
      ≤ Nat.descFactorial (Fintype.card ι) k * ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
  classical
  calc ‖f.iteratedFDeriv k x‖
  _ ≤ ∑ e : Fin k ↪ ι, ‖iteratedFDerivComponent f e.toEquivRange (fun i ↦ x i)‖ := norm_sum_le _ _
  _ ≤ ∑ _ : Fin k ↪ ι, ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    gcongr with e _
    simpa using norm_iteratedFDerivComponent_le f e.toEquivRange x
  _ = Nat.descFactorial (Fintype.card ι) k * ‖f‖ * ‖x‖ ^ (Fintype.card ι - k) := by
    simp [card_univ, mul_assoc]

end ContinuousMultilinearMap

end Seminorm

section Norm

namespace ContinuousMultilinearMap

/-! Results that are only true if the target space is a `NormedAddCommGroup` (and not just a
`SeminormedAddCommGroup`). -/

variable {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [NontriviallyNormedField 𝕜] [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable (f : ContinuousMultilinearMap 𝕜 E G)

/-- A continuous linear map is zero iff its norm vanishes. -/
theorem opNorm_zero_iff : ‖f‖ = 0 ↔ f = 0 := by
  simp [← (opNorm_nonneg f).le_iff_eq, opNorm_le_iff f le_rfl, ContinuousMultilinearMap.ext_iff]

@[deprecated (since := "2024-02-02")] alias op_norm_zero_iff := opNorm_zero_iff

/-- Continuous multilinear maps themselves form a normed group with respect to
    the operator norm. -/
instance normedAddCommGroup : NormedAddCommGroup (ContinuousMultilinearMap 𝕜 E G) :=
  NormedAddCommGroup.ofSeparation (fun f ↦ (opNorm_zero_iff f).mp)

/-- An alias of `ContinuousMultilinearMap.normedAddCommGroup` with non-dependent types to help
typeclass search. -/
instance normedAddCommGroup' :
    NormedAddCommGroup (ContinuousMultilinearMap 𝕜 (fun _ : ι => G') G) :=
  ContinuousMultilinearMap.normedAddCommGroup

variable (𝕜 G)

theorem norm_ofSubsingleton_id [Subsingleton ι] [Nontrivial G] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖ = 1 := by simp

theorem nnnorm_ofSubsingleton_id [Subsingleton ι] [Nontrivial G] (i : ι) :
    ‖ofSubsingleton 𝕜 G G i (.id _ _)‖₊ = 1 :=
  NNReal.eq <| norm_ofSubsingleton_id _ _ _

end ContinuousMultilinearMap

end Norm

section Norm

/-! Results that are only true if the source is a `NormedAddCommGroup` (and not just a
`SeminormedAddCommGroup`). -/

variable {𝕜 : Type u} {ι : Type v} {E : ι → Type wE} {G : Type wG} [Fintype ι]
  [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace MultilinearMap

variable (f : MultilinearMap 𝕜 E G)

/-- If a multilinear map in finitely many variables on normed spaces satisfies the inequality
`‖f m‖ ≤ C * ∏ i, ‖m i‖` on a shell `ε i / ‖c i‖ < ‖m i‖ < ε i` for some positive numbers `ε i`
and elements `c i : 𝕜`, `1 < ‖c i‖`, then it satisfies this inequality for all `m`. -/
theorem bound_of_shell {ε : ι → ℝ} {C : ℝ} (hε : ∀ i, 0 < ε i) {c : ι → 𝕜} (hc : ∀ i, 1 < ‖c i‖)
    (hf : ∀ m : ∀ i, E i, (∀ i, ε i / ‖c i‖ ≤ ‖m i‖) → (∀ i, ‖m i‖ < ε i) → ‖f m‖ ≤ C * ∏ i, ‖m i‖)
    (m : ∀ i, E i) : ‖f m‖ ≤ C * ∏ i, ‖m i‖ :=
  bound_of_shell_of_norm_map_coord_zero f
    (fun h ↦ by rw [map_coord_zero f _ (norm_eq_zero.1 h), norm_zero]) hε hc hf m

end MultilinearMap

end Norm
