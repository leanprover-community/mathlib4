/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Riccardo Brasca

! This file was ported from Lean 3 source module analysis.normed.group.quotient
! leanprover-community/mathlib commit 2196ab363eb097c008d4497125e0dde23fb36db2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.RingTheory.Ideal.QuotientOperations

/-!
# Quotients of seminormed groups

For any `seminormed_add_comm_group M` and any `S : add_subgroup M`, we provide a
`seminormed_add_comm_group`, the group quotient `M ⧸ S`.
If `S` is closed, we provide `normed_add_comm_group (M ⧸ S)` (regardless of whether `M` itself is
separated). The two main properties of these structures are the underlying topology is the quotient
topology and the projection is a normed group homomorphism which is norm non-increasing
(better, it has operator norm exactly one unless `S` is dense in `M`). The corresponding
universal property is that every normed group hom defined on `M` which vanishes on `S` descends
to a normed group hom defined on `M ⧸ S`.

This file also introduces a predicate `is_quotient` characterizing normed group homs that
are isomorphic to the canonical projection onto a normed group quotient.

In addition, this file also provides normed structures for quotients of modules by submodules, and
of (commutative) rings by ideals. The `seminormed_add_comm_group` and `normed_add_comm_group`
instances described above are transferred directly, but we also define instances of `normed_space`,
`semi_normed_comm_ring`, `normed_comm_ring` and `normed_algebra` under appropriate type class
assumptions on the original space. Moreover, while `quotient_add_group.complete_space` works
out-of-the-box for quotients of `normed_add_comm_group`s by `add_subgroup`s, we need to transfer
this instance in `submodule.quotient.complete_space` so that it applies to these other quotients.

## Main definitions


We use `M` and `N` to denote seminormed groups and `S : add_subgroup M`.
All the following definitions are in the `add_subgroup` namespace. Hence we can access
`add_subgroup.normed_mk S` as `S.normed_mk`.

* `seminormed_add_comm_group_quotient` : The seminormed group structure on the quotient by
    an additive subgroup. This is an instance so there is no need to explictly use it.

* `normed_add_comm_group_quotient` : The normed group structure on the quotient by
    a closed additive subgroup. This is an instance so there is no need to explictly use it.

* `normed_mk S` : the normed group hom from `M` to `M ⧸ S`.

* `lift S f hf`: implements the universal property of `M ⧸ S`. Here
    `(f : normed_add_group_hom M N)`, `(hf : ∀ s ∈ S, f s = 0)` and
    `lift S f hf : normed_add_group_hom (M ⧸ S) N`.

* `is_quotient`: given `f : normed_add_group_hom M N`, `is_quotient f` means `N` is isomorphic
    to a quotient of `M` by a subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

* `norm_normed_mk` : the operator norm of the projection is `1` if the subspace is not dense.

* `is_quotient.norm_lift`: Provided `f : normed_hom M N` satisfies `is_quotient f`, for every
     `n : N` and positive `ε`, there exists `m` such that `f m = n ∧ ‖m‖ < ‖n‖ + ε`.


## Implementation details

For any `seminormed_add_comm_group M` and any `S : add_subgroup M` we define a norm on `M ⧸ S` by
`‖x‖ = Inf (norm '' {m | mk' S m = x})`. This formula is really an implementation detail, it
shouldn't be needed outside of this file setting up the theory.

Since `M ⧸ S` is automatically a topological space (as any quotient of a topological space),
one needs to be careful while defining the `seminormed_add_comm_group` instance to avoid having two
different topologies on this quotient. This is not purely a technological issue.
Mathematically there is something to prove. The main point is proved in the auxiliary lemma
`quotient_nhd_basis` that has no use beyond this verification and states that zero in the quotient
admits as basis of neighborhoods in the quotient topology the sets `{x | ‖x‖ < ε}` for positive `ε`.

Once this mathematical point it settled, we have two topologies that are propositionaly equal. This
is not good enough for the type class system. As usual we ensure *definitional* equality
using forgetful inheritance, see Note [forgetful inheritance]. A (semi)-normed group structure
includes a uniform space structure which includes a topological space structure, together
with propositional fields asserting compatibility conditions.
The usual way to define a `seminormed_add_comm_group` is to let Lean build a uniform space structure
using the provided norm, and then trivially build a proof that the norm and uniform structure are
compatible. Here the uniform structure is provided using `topological_add_group.to_uniform_space`
which uses the topological structure and the group structure to build the uniform structure. This
uniform structure induces the correct topological structure by construction, but the fact that it
is compatible with the norm is not obvious; this is where the mathematical content explained in
the previous paragraph kicks in.

-/


noncomputable section

open quotientAddGroup Metric Set

open Topology NNReal

variable {M N : Type _} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

/-- The definition of the norm on the quotient by an additive subgroup. -/
noncomputable instance normOnQuotient (S : AddSubgroup M) : Norm (M ⧸ S)
    where norm x := infₛ (norm '' { m | mk' S m = x })
#align norm_on_quotient normOnQuotient

theorem AddSubgroup.quotient_norm_eq {S : AddSubgroup M} (x : M ⧸ S) :
    ‖x‖ = infₛ (norm '' { m : M | (m : M ⧸ S) = x }) :=
  rfl
#align add_subgroup.quotient_norm_eq AddSubgroup.quotient_norm_eq

theorem image_norm_nonempty {S : AddSubgroup M} :
    ∀ x : M ⧸ S, (norm '' { m | mk' S m = x }).Nonempty :=
  by
  rintro ⟨m⟩
  rw [Set.nonempty_image_iff]
  use m
  change mk' S m = _
  rfl
#align image_norm_nonempty image_norm_nonempty

theorem bddBelow_image_norm (s : Set M) : BddBelow (norm '' s) :=
  by
  use 0
  rintro _ ⟨x, hx, rfl⟩
  apply norm_nonneg
#align bdd_below_image_norm bddBelow_image_norm

/-- The norm on the quotient satisfies `‖-x‖ = ‖x‖`. -/
theorem quotient_norm_neg {S : AddSubgroup M} (x : M ⧸ S) : ‖-x‖ = ‖x‖ :=
  by
  suffices norm '' { m | mk' S m = x } = norm '' { m | mk' S m = -x } by simp only [this, norm]
  ext r
  constructor
  · rintro ⟨m, rfl : mk' S m = x, rfl⟩
    rw [← norm_neg]
    exact ⟨-m, by simp only [(mk' S).map_neg, Set.mem_setOf_eq], rfl⟩
  · rintro ⟨m, hm : mk' S m = -x, rfl⟩
    exact ⟨-m, by simpa using neg_eq_iff_eq_neg.mpr ((mk'_apply _ _).symm.trans hm)⟩
#align quotient_norm_neg quotient_norm_neg

theorem quotient_norm_sub_rev {S : AddSubgroup M} (x y : M ⧸ S) : ‖x - y‖ = ‖y - x‖ := by
  rw [show x - y = -(y - x) by abel, quotient_norm_neg]
#align quotient_norm_sub_rev quotient_norm_sub_rev

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
theorem quotient_norm_mk_le (S : AddSubgroup M) (m : M) : ‖mk' S m‖ ≤ ‖m‖ :=
  by
  apply cinfₛ_le
  use 0
  · rintro _ ⟨n, h, rfl⟩
    apply norm_nonneg
  · apply Set.mem_image_of_mem
    rw [Set.mem_setOf_eq]
#align quotient_norm_mk_le quotient_norm_mk_le

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
theorem quotient_norm_mk_le' (S : AddSubgroup M) (m : M) : ‖(m : M ⧸ S)‖ ≤ ‖m‖ :=
  quotient_norm_mk_le S m
#align quotient_norm_mk_le' quotient_norm_mk_le'

/-- The norm of the image under the natural morphism to the quotient. -/
theorem quotient_norm_mk_eq (S : AddSubgroup M) (m : M) :
    ‖mk' S m‖ = infₛ ((fun x => ‖m + x‖) '' S) :=
  by
  change Inf _ = _
  congr 1
  ext r
  simp_rw [coe_mk', eq_iff_sub_mem]
  constructor
  · rintro ⟨y, h, rfl⟩
    use y - m, h
    simp
  · rintro ⟨y, h, rfl⟩
    use m + y
    simpa using h
#align quotient_norm_mk_eq quotient_norm_mk_eq

/-- The quotient norm is nonnegative. -/
theorem quotient_norm_nonneg (S : AddSubgroup M) : ∀ x : M ⧸ S, 0 ≤ ‖x‖ :=
  by
  rintro ⟨m⟩
  change 0 ≤ ‖mk' S m‖
  apply le_cinfₛ (image_norm_nonempty _)
  rintro _ ⟨n, h, rfl⟩
  apply norm_nonneg
#align quotient_norm_nonneg quotient_norm_nonneg

/-- The quotient norm is nonnegative. -/
theorem norm_mk_nonneg (S : AddSubgroup M) (m : M) : 0 ≤ ‖mk' S m‖ :=
  quotient_norm_nonneg S _
#align norm_mk_nonneg norm_mk_nonneg

/-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m` belongs
to the closure of `S`. -/
theorem quotient_norm_eq_zero_iff (S : AddSubgroup M) (m : M) :
    ‖mk' S m‖ = 0 ↔ m ∈ closure (S : Set M) :=
  by
  have : 0 ≤ ‖mk' S m‖ := norm_mk_nonneg S m
  rw [← this.le_iff_eq, quotient_norm_mk_eq, Real.infₛ_le_iff]
  simp_rw [zero_add]
  · calc
      (∀ ε > (0 : ℝ), ∃ r ∈ (fun x => ‖m + x‖) '' (S : Set M), r < ε) ↔
          ∀ ε > 0, ∃ x ∈ S, ‖m + x‖ < ε :=
        by simp [Set.bex_image_iff]
      _ ↔ ∀ ε > 0, ∃ x ∈ S, ‖m + -x‖ < ε := _
      _ ↔ ∀ ε > 0, ∃ x ∈ S, x ∈ Metric.ball m ε := by
        simp [dist_eq_norm, ← sub_eq_add_neg, norm_sub_rev]
      _ ↔ m ∈ closure ↑S := by simp [Metric.mem_closure_iff, dist_comm]
      
    refine' forall₂_congr fun ε ε_pos => _
    rw [← S.exists_neg_mem_iff_exists_mem]
    simp
  · use 0
    rintro _ ⟨x, x_in, rfl⟩
    apply norm_nonneg
  rw [Set.nonempty_image_iff]
  use 0, S.zero_mem
#align quotient_norm_eq_zero_iff quotient_norm_eq_zero_iff

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `‖m‖ < ‖x‖ + ε`. -/
theorem norm_mk_lt {S : AddSubgroup M} (x : M ⧸ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : M, mk' S m = x ∧ ‖m‖ < ‖x‖ + ε :=
  by
  obtain ⟨_, ⟨m : M, H : mk' S m = x, rfl⟩, hnorm : ‖m‖ < ‖x‖ + ε⟩ :=
    Real.lt_infₛ_add_pos (image_norm_nonempty x) hε
  subst H
  exact ⟨m, rfl, hnorm⟩
#align norm_mk_lt norm_mk_lt

/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `‖m + s‖ < ‖mk' S m‖ + ε`. -/
theorem norm_mk_lt' (S : AddSubgroup M) (m : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, ‖m + s‖ < ‖mk' S m‖ + ε :=
  by
  obtain ⟨n : M, hn : mk' S n = mk' S m, hn' : ‖n‖ < ‖mk' S m‖ + ε⟩ :=
    norm_mk_lt (QuotientAddGroup.mk' S m) hε
  erw [eq_comm, QuotientAddGroup.eq] at hn
  use -m + n, hn
  rwa [add_neg_cancel_left]
#align norm_mk_lt' norm_mk_lt'

/-- The quotient norm satisfies the triangle inequality. -/
theorem quotient_norm_add_le (S : AddSubgroup M) (x y : M ⧸ S) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  by
  refine' le_of_forall_pos_le_add fun ε hε => _
  replace hε := half_pos hε
  obtain ⟨m, rfl, hm : ‖m‖ < ‖mk' S m‖ + ε / 2⟩ := norm_mk_lt x hε
  obtain ⟨n, rfl, hn : ‖n‖ < ‖mk' S n‖ + ε / 2⟩ := norm_mk_lt y hε
  calc
    ‖mk' S m + mk' S n‖ = ‖mk' S (m + n)‖ := by rw [(mk' S).map_add]
    _ ≤ ‖m + n‖ := (quotient_norm_mk_le S (m + n))
    _ ≤ ‖m‖ + ‖n‖ := (norm_add_le _ _)
    _ ≤ ‖mk' S m‖ + ‖mk' S n‖ + ε := by linarith
    
#align quotient_norm_add_le quotient_norm_add_le

/-- The quotient norm of `0` is `0`. -/
theorem norm_mk_zero (S : AddSubgroup M) : ‖(0 : M ⧸ S)‖ = 0 :=
  by
  erw [quotient_norm_eq_zero_iff]
  exact subset_closure S.zero_mem
#align norm_mk_zero norm_mk_zero

/-- If `(m : M)` has norm equal to `0` in `M ⧸ S` for a closed subgroup `S` of `M`, then
`m ∈ S`. -/
theorem norm_zero_eq_zero (S : AddSubgroup M) (hS : IsClosed (S : Set M)) (m : M)
    (h : ‖mk' S m‖ = 0) : m ∈ S := by rwa [quotient_norm_eq_zero_iff, hS.closure_eq] at h
#align norm_zero_eq_zero norm_zero_eq_zero

theorem quotient_nhd_basis (S : AddSubgroup M) :
    (𝓝 (0 : M ⧸ S)).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { x | ‖x‖ < ε } :=
  ⟨by
    intro U
    constructor
    · intro U_in
      rw [← (mk' S).map_zero] at U_in
      have := preimage_nhds_coinduced U_in
      rcases metric.mem_nhds_iff.mp this with ⟨ε, ε_pos, H⟩
      use ε / 2, half_pos ε_pos
      intro x x_in
      dsimp at x_in
      rcases norm_mk_lt x (half_pos ε_pos) with ⟨y, rfl, ry⟩
      apply H
      rw [ball_zero_eq]
      dsimp
      linarith
    · rintro ⟨ε, ε_pos, h⟩
      have : mk' S '' ball (0 : M) ε ⊆ { x | ‖x‖ < ε } :=
        by
        rintro _ ⟨x, x_in, rfl⟩
        rw [mem_ball_zero_iff] at x_in
        exact lt_of_le_of_lt (quotient_norm_mk_le S x) x_in
      apply Filter.mem_of_superset _ (Set.Subset.trans this h)
      clear h U this
      apply IsOpen.mem_nhds
      · change IsOpen (mk' S ⁻¹' _)
        erw [QuotientAddGroup.preimage_image_mk]
        apply isOpen_unionᵢ
        rintro ⟨s, s_in⟩
        exact (continuous_add_right s).isOpen_preimage _ is_open_ball
      · exact ⟨(0 : M), mem_ball_self ε_pos, (mk' S).map_zero⟩⟩
#align quotient_nhd_basis quotient_nhd_basis

/-- The seminormed group structure on the quotient by an additive subgroup. -/
noncomputable instance AddSubgroup.seminormedAddCommGroupQuotient (S : AddSubgroup M) :
    SeminormedAddCommGroup (M ⧸ S) where
  dist x y := ‖x - y‖
  dist_self x := by simp only [norm_mk_zero, sub_self]
  dist_comm := quotient_norm_sub_rev
  dist_triangle x y z := by
    unfold dist
    have : x - z = x - y + (y - z) := by abel
    rw [this]
    exact quotient_norm_add_le S (x - y) (y - z)
  dist_eq x y := rfl
  toUniformSpace := TopologicalAddGroup.toUniformSpace (M ⧸ S)
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_zero']
    have := (quotient_nhd_basis S).comap fun p : (M ⧸ S) × M ⧸ S => p.2 - p.1
    apply this.eq_of_same_basis
    have :
      ∀ ε : ℝ,
        (fun p : (M ⧸ S) × M ⧸ S => p.snd - p.fst) ⁻¹' { x | ‖x‖ < ε } =
          { p : (M ⧸ S) × M ⧸ S | ‖p.fst - p.snd‖ < ε } :=
      by
      intro ε
      ext x
      dsimp
      rw [quotient_norm_sub_rev]
    rw [funext this]
    refine' Filter.hasBasis_binfᵢ_principal _ Set.nonempty_Ioi
    rintro ε (ε_pos : 0 < ε) η (η_pos : 0 < η)
    refine' ⟨min ε η, lt_min ε_pos η_pos, _, _⟩
    · suffices ∀ a b : M ⧸ S, ‖a - b‖ < ε → ‖a - b‖ < η → ‖a - b‖ < ε by simpa
      exact fun a b h h' => h
    · simp
#align add_subgroup.seminormed_add_comm_group_quotient AddSubgroup.seminormedAddCommGroupQuotient

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example (S : AddSubgroup M) :
    (Quotient.topologicalSpace : TopologicalSpace <| M ⧸ S) =
      S.seminormedAddCommGroupQuotient.toUniformSpace.toTopologicalSpace :=
  rfl

/-- The quotient in the category of normed groups. -/
noncomputable instance AddSubgroup.normedAddCommGroupQuotient (S : AddSubgroup M)
    [IsClosed (S : Set M)] : NormedAddCommGroup (M ⧸ S) :=
  { AddSubgroup.seminormedAddCommGroupQuotient S with
    eq_of_dist_eq_zero := by
      rintro ⟨m⟩ ⟨m'⟩ (h : ‖mk' S m - mk' S m'‖ = 0)
      erw [← (mk' S).map_sub, quotient_norm_eq_zero_iff, ‹IsClosed _›.closure_eq, ←
        QuotientAddGroup.eq_iff_sub_mem] at h
      exact h }
#align add_subgroup.normed_add_comm_group_quotient AddSubgroup.normedAddCommGroupQuotient

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example (S : AddSubgroup M) [IsClosed (S : Set M)] :
    S.seminormedAddCommGroupQuotient = NormedAddCommGroup.toSeminormedAddCommGroup :=
  rfl

namespace AddSubgroup

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by a subgroup. -/
noncomputable def normedMk (S : AddSubgroup M) : NormedAddGroupHom M (M ⧸ S) :=
  { QuotientAddGroup.mk' S with
    bound' := ⟨1, fun m => by simpa [one_mul] using quotient_norm_mk_le _ m⟩ }
#align add_subgroup.normed_mk AddSubgroup.normedMk

/-- `S.normed_mk` agrees with `quotient_add_group.mk' S`. -/
@[simp]
theorem normedMk.apply (S : AddSubgroup M) (m : M) : normedMk S m = QuotientAddGroup.mk' S m :=
  rfl
#align add_subgroup.normed_mk.apply AddSubgroup.normedMk.apply

/-- `S.normed_mk` is surjective. -/
theorem surjective_normedMk (S : AddSubgroup M) : Function.Surjective (normedMk S) :=
  surjective_quot_mk _
#align add_subgroup.surjective_normed_mk AddSubgroup.surjective_normedMk

/-- The kernel of `S.normed_mk` is `S`. -/
theorem ker_normedMk (S : AddSubgroup M) : S.normedMk.ker = S :=
  QuotientAddGroup.ker_mk' _
#align add_subgroup.ker_normed_mk AddSubgroup.ker_normedMk

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normedMk_le (S : AddSubgroup M) : ‖S.normedMk‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp [quotient_norm_mk_le']
#align add_subgroup.norm_normed_mk_le AddSubgroup.norm_normedMk_le

/-- The operator norm of the projection is `1` if the subspace is not dense. -/
theorem norm_normedMk (S : AddSubgroup M) (h : (S.topologicalClosure : Set M) ≠ univ) :
    ‖S.normedMk‖ = 1 := by
  obtain ⟨x, hx⟩ := Set.nonempty_compl.2 h
  let y := S.normed_mk x
  have hy : ‖y‖ ≠ 0 := by
    intro h0
    exact Set.not_mem_of_mem_compl hx ((quotient_norm_eq_zero_iff S x).1 h0)
  refine' le_antisymm (norm_normed_mk_le S) (le_of_forall_pos_le_add fun ε hε => _)
  suffices 1 ≤ ‖S.normed_mk‖ + min ε ((1 : ℝ) / 2) by
    exact le_add_of_le_add_left this (min_le_left ε ((1 : ℝ) / 2))
  have hδ := sub_pos.mpr (lt_of_le_of_lt (min_le_right ε ((1 : ℝ) / 2)) one_half_lt_one)
  have hδpos : 0 < min ε ((1 : ℝ) / 2) := lt_min hε one_half_pos
  have hδnorm := mul_pos (div_pos hδpos hδ) (lt_of_le_of_ne (norm_nonneg y) hy.symm)
  obtain ⟨m, hm, hlt⟩ := norm_mk_lt y hδnorm
  have hrw :
    ‖y‖ + min ε (1 / 2) / (1 - min ε (1 / 2)) * ‖y‖ =
      ‖y‖ * (1 + min ε (1 / 2) / (1 - min ε (1 / 2))) :=
    by ring
  rw [hrw] at hlt
  have hm0 : ‖m‖ ≠ 0 := by
    intro h0
    have hnorm := quotient_norm_mk_le S m
    rw [h0, hm] at hnorm
    replace hnorm := le_antisymm hnorm (norm_nonneg _)
    simpa [hnorm] using hy
  replace hlt := (div_lt_div_right (lt_of_le_of_ne (norm_nonneg m) hm0.symm)).2 hlt
  simp only [hm0, div_self, Ne.def, not_false_iff] at hlt
  have hrw₁ :
    ‖y‖ * (1 + min ε (1 / 2) / (1 - min ε (1 / 2))) / ‖m‖ =
      ‖y‖ / ‖m‖ * (1 + min ε (1 / 2) / (1 - min ε (1 / 2))) :=
    by ring
  rw [hrw₁] at hlt
  replace hlt := (inv_pos_lt_iff_one_lt_mul (lt_trans (div_pos hδpos hδ) (lt_one_add _))).2 hlt
  suffices ‖S.normed_mk‖ ≥ 1 - min ε (1 / 2) by exact sub_le_iff_le_add.mp this
  calc
    ‖S.normed_mk‖ ≥ ‖S.normed_mk m‖ / ‖m‖ := ratio_le_op_norm S.normed_mk m
    _ = ‖y‖ / ‖m‖ := by rw [normed_mk.apply, hm]
    _ ≥ (1 + min ε (1 / 2) / (1 - min ε (1 / 2)))⁻¹ := (le_of_lt hlt)
    _ = 1 - min ε (1 / 2) := by field_simp [(ne_of_lt hδ).symm]
    
#align add_subgroup.norm_normed_mk AddSubgroup.norm_normedMk

/-- The operator norm of the projection is `0` if the subspace is dense. -/
theorem norm_trivial_quotient_mk (S : AddSubgroup M)
    (h : (S.topologicalClosure : Set M) = Set.univ) : ‖S.normedMk‖ = 0 :=
  by
  refine' le_antisymm (op_norm_le_bound _ le_rfl fun x => _) (norm_nonneg _)
  have hker : x ∈ S.normed_mk.ker.topologicalClosure :=
    by
    rw [S.ker_normed_mk]
    exact Set.mem_of_eq_of_mem h trivial
  rw [ker_normed_mk] at hker
  simp only [(quotient_norm_eq_zero_iff S x).mpr hker, normed_mk.apply, MulZeroClass.zero_mul]
#align add_subgroup.norm_trivial_quotient_mk AddSubgroup.norm_trivial_quotient_mk

end AddSubgroup

namespace NormedAddGroupHom

/-- `is_quotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of `M`
by the kernel of `f`. -/
structure IsQuotient (f : NormedAddGroupHom M N) : Prop where
  Surjective : Function.Surjective f
  norm : ∀ x, ‖f x‖ = infₛ ((fun m => ‖x + m‖) '' f.ker)
#align normed_add_group_hom.is_quotient NormedAddGroupHom.IsQuotient

/-- Given  `f : normed_add_group_hom M N` such that `f s = 0` for all `s ∈ S`, where,
`S : add_subgroup M` is closed, the induced morphism `normed_add_group_hom (M ⧸ S) N`. -/
noncomputable def lift {N : Type _} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) : NormedAddGroupHom (M ⧸ S) N :=
  { QuotientAddGroup.lift S f.toAddMonoidHom hf with
    bound' := by
      obtain ⟨c : ℝ, hcpos : (0 : ℝ) < c, hc : ∀ x, ‖f x‖ ≤ c * ‖x‖⟩ := f.bound
      refine' ⟨c, fun mbar => le_of_forall_pos_le_add fun ε hε => _⟩
      obtain ⟨m : M, rfl : mk' S m = mbar, hmnorm : ‖m‖ < ‖mk' S m‖ + ε / c⟩ :=
        norm_mk_lt mbar (div_pos hε hcpos)
      calc
        ‖f m‖ ≤ c * ‖m‖ := hc m
        _ ≤ c * (‖mk' S m‖ + ε / c) := ((mul_lt_mul_left hcpos).mpr hmnorm).le
        _ = c * ‖mk' S m‖ + ε := by rw [mul_add, mul_div_cancel' _ hcpos.ne.symm]
         }
#align normed_add_group_hom.lift NormedAddGroupHom.lift

theorem lift_mk {N : Type _} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (m : M) :
    lift S f hf (S.normedMk m) = f m :=
  rfl
#align normed_add_group_hom.lift_mk NormedAddGroupHom.lift_mk

theorem lift_unique {N : Type _} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (g : NormedAddGroupHom (M ⧸ S) N) :
    g.comp S.normedMk = f → g = lift S f hf :=
  by
  intro h
  ext
  rcases AddSubgroup.surjective_normedMk _ x with ⟨x, rfl⟩
  change g.comp S.normed_mk x = _
  simpa only [h]
#align normed_add_group_hom.lift_unique NormedAddGroupHom.lift_unique

/-- `S.normed_mk` satisfies `is_quotient`. -/
theorem isQuotientQuotient (S : AddSubgroup M) : IsQuotient S.normedMk :=
  ⟨S.surjective_normedMk, fun m => by simpa [S.ker_normed_mk] using quotient_norm_mk_eq _ m⟩
#align normed_add_group_hom.is_quotient_quotient NormedAddGroupHom.isQuotientQuotient

theorem IsQuotient.norm_lift {f : NormedAddGroupHom M N} (hquot : IsQuotient f) {ε : ℝ} (hε : 0 < ε)
    (n : N) : ∃ m : M, f m = n ∧ ‖m‖ < ‖n‖ + ε :=
  by
  obtain ⟨m, rfl⟩ := hquot.surjective n
  have nonemp : ((fun m' => ‖m + m'‖) '' f.ker).Nonempty :=
    by
    rw [Set.nonempty_image_iff]
    exact ⟨0, f.ker.zero_mem⟩
  rcases Real.lt_infₛ_add_pos nonemp hε with
    ⟨_, ⟨⟨x, hx, rfl⟩, H : ‖m + x‖ < Inf ((fun m' : M => ‖m + m'‖) '' f.ker) + ε⟩⟩
  exact
    ⟨m + x, by rw [map_add, (NormedAddGroupHom.mem_ker f x).mp hx, add_zero], by rwa [hquot.norm]⟩
#align normed_add_group_hom.is_quotient.norm_lift NormedAddGroupHom.IsQuotient.norm_lift

theorem IsQuotient.norm_le {f : NormedAddGroupHom M N} (hquot : IsQuotient f) (m : M) :
    ‖f m‖ ≤ ‖m‖ := by
  rw [hquot.norm]
  apply cinfₛ_le
  · use 0
    rintro _ ⟨m', hm', rfl⟩
    apply norm_nonneg
  · exact ⟨0, f.ker.zero_mem, by simp⟩
#align normed_add_group_hom.is_quotient.norm_le NormedAddGroupHom.IsQuotient.norm_le

theorem lift_norm_le {N : Type _} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) :
    ‖lift S f hf‖ ≤ c := by
  apply op_norm_le_bound _ c.coe_nonneg
  intro x
  by_cases hc : c = 0
  · simp only [hc, NNReal.coe_zero, MulZeroClass.zero_mul] at fb⊢
    obtain ⟨x, rfl⟩ := surjective_quot_mk _ x
    show ‖f x‖ ≤ 0
    calc
      ‖f x‖ ≤ 0 * ‖x‖ := f.le_of_op_norm_le fb x
      _ = 0 := MulZeroClass.zero_mul _
      
  · replace hc : 0 < c := pos_iff_ne_zero.mpr hc
    apply le_of_forall_pos_le_add
    intro ε hε
    have aux : 0 < ε / c := div_pos hε hc
    obtain ⟨x, rfl, Hx⟩ : ∃ x', S.normed_mk x' = x ∧ ‖x'‖ < ‖x‖ + ε / c :=
      (is_quotient_quotient _).norm_lift aux _
    rw [lift_mk]
    calc
      ‖f x‖ ≤ c * ‖x‖ := f.le_of_op_norm_le fb x
      _ ≤ c * (‖S.normed_mk x‖ + ε / c) := ((mul_le_mul_left _).mpr Hx.le)
      _ = c * _ + ε := _
      
    · exact_mod_cast hc
    · rw [mul_add, mul_div_cancel']
      exact_mod_cast hc.ne'
#align normed_add_group_hom.lift_norm_le NormedAddGroupHom.lift_norm_le

theorem lift_normNoninc {N : Type _} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (fb : f.NormNoninc) :
    (lift S f hf).NormNoninc := fun x =>
  by
  have fb' : ‖f‖ ≤ (1 : ℝ≥0) := norm_noninc.norm_noninc_iff_norm_le_one.mp fb
  simpa using le_of_op_norm_le _ (f.lift_norm_le _ _ fb') _
#align normed_add_group_hom.lift_norm_noninc NormedAddGroupHom.lift_normNoninc

end NormedAddGroupHom

/-!
### Submodules and ideals

In what follows, the norm structures created above for quotients of (semi)`normed_add_comm_group`s
by `add_subgroup`s are transferred via definitional equality to quotients of modules by submodules,
and of rings by ideals, thereby preserving the definitional equality for the topological group and
uniform structures worked for above. Completeness is also transferred via this definitional
equality.

In addition, instances are constructed for `normed_space`, `semi_normed_comm_ring`,
`normed_comm_ring` and `normed_algebra` under the appropriate hypotheses. Currently, we do not
have quotients of rings by two-sided ideals, hence the commutativity hypotheses are required.
 -/


section Submodule

variable {R : Type _} [Ring R] [Module R M] (S : Submodule R M)

instance Submodule.Quotient.seminormedAddCommGroup : SeminormedAddCommGroup (M ⧸ S) :=
  AddSubgroup.seminormedAddCommGroupQuotient S.toAddSubgroup
#align submodule.quotient.seminormed_add_comm_group Submodule.Quotient.seminormedAddCommGroup

instance Submodule.Quotient.normedAddCommGroup [hS : IsClosed (S : Set M)] :
    NormedAddCommGroup (M ⧸ S) :=
  @AddSubgroup.normedAddCommGroupQuotient _ _ S.toAddSubgroup hS
#align submodule.quotient.normed_add_comm_group Submodule.Quotient.normedAddCommGroup

instance Submodule.Quotient.completeSpace [CompleteSpace M] : CompleteSpace (M ⧸ S) :=
  QuotientAddGroup.completeSpace M S.toAddSubgroup
#align submodule.quotient.complete_space Submodule.Quotient.completeSpace

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `submodule.quotient.mk m = x`
and `‖m‖ < ‖x‖ + ε`. -/
theorem Submodule.Quotient.norm_mk_lt {S : Submodule R M} (x : M ⧸ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : M, Submodule.Quotient.mk m = x ∧ ‖m‖ < ‖x‖ + ε :=
  norm_mk_lt x hε
#align submodule.quotient.norm_mk_lt Submodule.Quotient.norm_mk_lt

theorem Submodule.Quotient.norm_mk_le (m : M) : ‖(Submodule.Quotient.mk m : M ⧸ S)‖ ≤ ‖m‖ :=
  quotient_norm_mk_le S.toAddSubgroup m
#align submodule.quotient.norm_mk_le Submodule.Quotient.norm_mk_le

instance Submodule.Quotient.normedSpace (𝕜 : Type _) [NormedField 𝕜] [NormedSpace 𝕜 M] [SMul 𝕜 R]
    [IsScalarTower 𝕜 R M] : NormedSpace 𝕜 (M ⧸ S) :=
  { Submodule.Quotient.module' S with
    norm_smul_le := fun k x =>
      le_of_forall_pos_le_add fun ε hε =>
        by
        have :=
          (nhds_basis_ball.tendsto_iff nhds_basis_ball).mp
            ((@Real.uniformContinuous_const_mul ‖k‖).Continuous.Tendsto ‖x‖) ε hε
        simp only [mem_ball, exists_prop, dist, abs_sub_lt_iff] at this
        rcases this with ⟨δ, hδ, h⟩
        obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hδ
        specialize h ‖a‖ ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le S a]⟩
        calc
          _ ≤ ‖k‖ * ‖a‖ := (quotient_norm_mk_le S.to_add_subgroup (k • a)).trans_eq (norm_smul k a)
          _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le
           }
#align submodule.quotient.normed_space Submodule.Quotient.normedSpace

end Submodule

section Ideal

variable {R : Type _} [SeminormedCommRing R] (I : Ideal R)

theorem Ideal.Quotient.norm_mk_lt {I : Ideal R} (x : R ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : R, Ideal.Quotient.mk I r = x ∧ ‖r‖ < ‖x‖ + ε :=
  norm_mk_lt x hε
#align ideal.quotient.norm_mk_lt Ideal.Quotient.norm_mk_lt

theorem Ideal.Quotient.norm_mk_le (r : R) : ‖Ideal.Quotient.mk I r‖ ≤ ‖r‖ :=
  quotient_norm_mk_le I.toAddSubgroup r
#align ideal.quotient.norm_mk_le Ideal.Quotient.norm_mk_le

instance Ideal.Quotient.semiNormedCommRing : SeminormedCommRing (R ⧸ I) :=
  {
    Submodule.Quotient.seminormedAddCommGroup
      I with
    mul_comm := mul_comm
    norm_mul := fun x y =>
      le_of_forall_pos_le_add fun ε hε =>
        by
        have :=
          ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iffₓ nhds_basis_ball).mp
            (real.continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
        simp only [Set.mem_prod, mem_ball, and_imp, Prod.forall, exists_prop, Prod.exists] at this
        rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
        obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := Ideal.Quotient.norm_mk_lt x h₁,
          Ideal.Quotient.norm_mk_lt y h₂
        simp only [dist, abs_sub_lt_iff] at h
        specialize
          h ‖a‖ ‖b‖ ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I a]⟩
            ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I b]⟩
        calc
          _ ≤ ‖a‖ * ‖b‖ := (Ideal.Quotient.norm_mk_le I (a * b)).trans (norm_mul_le a b)
          _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le
           }
#align ideal.quotient.semi_normed_comm_ring Ideal.Quotient.semiNormedCommRing

instance Ideal.Quotient.normedCommRing [IsClosed (I : Set R)] : NormedCommRing (R ⧸ I) :=
  { Ideal.Quotient.semiNormedCommRing I, Submodule.Quotient.normedAddCommGroup I with }
#align ideal.quotient.normed_comm_ring Ideal.Quotient.normedCommRing

variable (𝕜 : Type _) [NormedField 𝕜]

instance Ideal.Quotient.normedAlgebra [NormedAlgebra 𝕜 R] : NormedAlgebra 𝕜 (R ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }
#align ideal.quotient.normed_algebra Ideal.Quotient.normedAlgebra

end Ideal

