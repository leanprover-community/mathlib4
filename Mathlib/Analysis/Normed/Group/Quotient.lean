/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Riccardo Brasca
-/
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.Data.Real.Sqrt
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.Topology.MetricSpace.HausdorffDistance

#align_import analysis.normed.group.quotient from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# Quotients of seminormed groups

For any `SeminormedAddCommGroup M` and any `S : AddSubgroup M`, we provide a
`SeminormedAddCommGroup`, the group quotient `M ⧸ S`.
If `S` is closed, we provide `NormedAddCommGroup (M ⧸ S)` (regardless of whether `M` itself is
separated). The two main properties of these structures are the underlying topology is the quotient
topology and the projection is a normed group homomorphism which is norm non-increasing
(better, it has operator norm exactly one unless `S` is dense in `M`). The corresponding
universal property is that every normed group hom defined on `M` which vanishes on `S` descends
to a normed group hom defined on `M ⧸ S`.

This file also introduces a predicate `IsQuotient` characterizing normed group homs that
are isomorphic to the canonical projection onto a normed group quotient.

In addition, this file also provides normed structures for quotients of modules by submodules, and
of (commutative) rings by ideals. The `SeminormedAddCommGroup` and `NormedAddCommGroup`
instances described above are transferred directly, but we also define instances of `NormedSpace`,
`SeminormedCommRing`, `NormedCommRing` and `NormedAlgebra` under appropriate type class
assumptions on the original space. Moreover, while `QuotientAddGroup.completeSpace` works
out-of-the-box for quotients of `NormedAddCommGroup`s by `AddSubgroup`s, we need to transfer
this instance in `Submodule.Quotient.completeSpace` so that it applies to these other quotients.

## Main definitions


We use `M` and `N` to denote seminormed groups and `S : AddSubgroup M`.
All the following definitions are in the `AddSubgroup` namespace. Hence we can access
`AddSubgroup.normedMk S` as `S.normedMk`.

* `seminormedAddCommGroupQuotient` : The seminormed group structure on the quotient by
    an additive subgroup. This is an instance so there is no need to explicitly use it.

* `normedAddCommGroupQuotient` : The normed group structure on the quotient by
    a closed additive subgroup. This is an instance so there is no need to explicitly use it.

* `normedMk S` : the normed group hom from `M` to `M ⧸ S`.

* `lift S f hf`: implements the universal property of `M ⧸ S`. Here
    `(f : NormedAddGroupHom M N)`, `(hf : ∀ s ∈ S, f s = 0)` and
    `lift S f hf : NormedAddGroupHom (M ⧸ S) N`.

* `IsQuotient`: given `f : NormedAddGroupHom M N`, `IsQuotient f` means `N` is isomorphic
    to a quotient of `M` by a subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

* `norm_normedMk` : the operator norm of the projection is `1` if the subspace is not dense.

* `IsQuotient.norm_lift`: Provided `f : normed_hom M N` satisfies `IsQuotient f`, for every
     `n : N` and positive `ε`, there exists `m` such that `f m = n ∧ ‖m‖ < ‖n‖ + ε`.


## Implementation details

For any `SeminormedAddCommGroup M` and any `S : AddSubgroup M` we define a norm on `M ⧸ S` by
`‖x‖ = sInf (norm '' {m | mk' S m = x})`. This formula is really an implementation detail, it
shouldn't be needed outside of this file setting up the theory.

Since `M ⧸ S` is automatically a topological space (as any quotient of a topological space),
one needs to be careful while defining the `SeminormedAddCommGroup` instance to avoid having two
different topologies on this quotient. This is not purely a technological issue.
Mathematically there is something to prove. The main point is proved in the auxiliary lemma
`quotient_nhd_basis` that has no use beyond this verification and states that zero in the quotient
admits as basis of neighborhoods in the quotient topology the sets `{x | ‖x‖ < ε}` for positive `ε`.

Once this mathematical point is settled, we have two topologies that are propositionally equal. This
is not good enough for the type class system. As usual we ensure *definitional* equality
using forgetful inheritance, see Note [forgetful inheritance]. A (semi)-normed group structure
includes a uniform space structure which includes a topological space structure, together
with propositional fields asserting compatibility conditions.
The usual way to define a `SeminormedAddCommGroup` is to let Lean build a uniform space structure
using the provided norm, and then trivially build a proof that the norm and uniform structure are
compatible. Here the uniform structure is provided using `TopologicalAddGroup.toUniformSpace`
which uses the topological structure and the group structure to build the uniform structure. This
uniform structure induces the correct topological structure by construction, but the fact that it
is compatible with the norm is not obvious; this is where the mathematical content explained in
the previous paragraph kicks in.

-/


noncomputable section

open QuotientAddGroup Metric Set Topology NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

/-- The definition of the norm on the quotient by an additive subgroup. -/
noncomputable instance normOnQuotient (S : AddSubgroup M) : Norm (M ⧸ S) where
  norm x := sInf (norm '' { m | mk' S m = x })
#align norm_on_quotient normOnQuotient

theorem AddSubgroup.quotient_norm_eq {S : AddSubgroup M} (x : M ⧸ S) :
    ‖x‖ = sInf (norm '' { m : M | (m : M ⧸ S) = x }) :=
  rfl
#align add_subgroup.quotient_norm_eq AddSubgroup.quotient_norm_eq

theorem QuotientAddGroup.norm_eq_infDist {S : AddSubgroup M} (x : M ⧸ S) :
    ‖x‖ = infDist 0 { m : M | (m : M ⧸ S) = x } := by
  simp only [AddSubgroup.quotient_norm_eq, infDist_eq_iInf, sInf_image', dist_zero_left]

/-- An alternative definition of the norm on the quotient group: the norm of `((x : M) : M ⧸ S)` is
equal to the distance from `x` to `S`. -/
theorem QuotientAddGroup.norm_mk {S : AddSubgroup M} (x : M) :
    ‖(x : M ⧸ S)‖ = infDist x S := by
  rw [norm_eq_infDist, ← infDist_image (IsometryEquiv.subLeft x).isometry,
    IsometryEquiv.subLeft_apply, sub_zero, ← IsometryEquiv.preimage_symm]
  congr 1 with y
  simp only [mem_preimage, IsometryEquiv.subLeft_symm_apply, mem_setOf_eq, QuotientAddGroup.eq,
    neg_add, neg_neg, neg_add_cancel_right, SetLike.mem_coe]

theorem image_norm_nonempty {S : AddSubgroup M} (x : M ⧸ S) :
    (norm '' { m | mk' S m = x }).Nonempty :=
  .image _ <| Quot.exists_rep x
#align image_norm_nonempty image_norm_nonempty

theorem bddBelow_image_norm (s : Set M) : BddBelow (norm '' s) :=
  ⟨0, forall_mem_image.2 fun _ _ ↦ norm_nonneg _⟩
#align bdd_below_image_norm bddBelow_image_norm

theorem isGLB_quotient_norm {S : AddSubgroup M} (x : M ⧸ S) :
    IsGLB (norm '' { m | mk' S m = x }) (‖x‖) :=
  isGLB_csInf (image_norm_nonempty x) (bddBelow_image_norm _)

/-- The norm on the quotient satisfies `‖-x‖ = ‖x‖`. -/
theorem quotient_norm_neg {S : AddSubgroup M} (x : M ⧸ S) : ‖-x‖ = ‖x‖ := by
  simp only [AddSubgroup.quotient_norm_eq]
  congr 1 with r
  constructor <;> { rintro ⟨m, hm, rfl⟩; use -m; simpa [neg_eq_iff_eq_neg] using hm }
#align quotient_norm_neg quotient_norm_neg

theorem quotient_norm_sub_rev {S : AddSubgroup M} (x y : M ⧸ S) : ‖x - y‖ = ‖y - x‖ := by
  rw [← neg_sub, quotient_norm_neg]
#align quotient_norm_sub_rev quotient_norm_sub_rev

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
theorem quotient_norm_mk_le (S : AddSubgroup M) (m : M) : ‖mk' S m‖ ≤ ‖m‖ :=
  csInf_le (bddBelow_image_norm _) <| Set.mem_image_of_mem _ rfl
#align quotient_norm_mk_le quotient_norm_mk_le

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
theorem quotient_norm_mk_le' (S : AddSubgroup M) (m : M) : ‖(m : M ⧸ S)‖ ≤ ‖m‖ :=
  quotient_norm_mk_le S m
#align quotient_norm_mk_le' quotient_norm_mk_le'

/-- The norm of the image under the natural morphism to the quotient. -/
theorem quotient_norm_mk_eq (S : AddSubgroup M) (m : M) :
    ‖mk' S m‖ = sInf ((‖m + ·‖) '' S) := by
  rw [mk'_apply, norm_mk, sInf_image', ← infDist_image isometry_neg, image_neg,
    neg_coe_set (H := S), infDist_eq_iInf]
  simp only [dist_eq_norm', sub_neg_eq_add, add_comm]
#align quotient_norm_mk_eq quotient_norm_mk_eq

/-- The quotient norm is nonnegative. -/
theorem quotient_norm_nonneg (S : AddSubgroup M) (x : M ⧸ S) : 0 ≤ ‖x‖ :=
  Real.sInf_nonneg _ <| forall_mem_image.2 fun _ _ ↦ norm_nonneg _
#align quotient_norm_nonneg quotient_norm_nonneg

/-- The quotient norm is nonnegative. -/
theorem norm_mk_nonneg (S : AddSubgroup M) (m : M) : 0 ≤ ‖mk' S m‖ :=
  quotient_norm_nonneg S _
#align norm_mk_nonneg norm_mk_nonneg

/-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m` belongs
to the closure of `S`. -/
theorem quotient_norm_eq_zero_iff (S : AddSubgroup M) (m : M) :
    ‖mk' S m‖ = 0 ↔ m ∈ closure (S : Set M) := by
  rw [mk'_apply, norm_mk, ← mem_closure_iff_infDist_zero]
  exact ⟨0, S.zero_mem⟩
#align quotient_norm_eq_zero_iff quotient_norm_eq_zero_iff

theorem QuotientAddGroup.norm_lt_iff {S : AddSubgroup M} {x : M ⧸ S} {r : ℝ} :
    ‖x‖ < r ↔ ∃ m : M, ↑m = x ∧ ‖m‖ < r := by
  rw [isGLB_lt_iff (isGLB_quotient_norm _), exists_mem_image]
  rfl

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `‖m‖ < ‖x‖ + ε`. -/
theorem norm_mk_lt {S : AddSubgroup M} (x : M ⧸ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : M, mk' S m = x ∧ ‖m‖ < ‖x‖ + ε :=
  norm_lt_iff.1 <| lt_add_of_pos_right _ hε
#align norm_mk_lt norm_mk_lt

/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `‖m + s‖ < ‖mk' S m‖ + ε`. -/
theorem norm_mk_lt' (S : AddSubgroup M) (m : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, ‖m + s‖ < ‖mk' S m‖ + ε := by
  obtain ⟨n : M, hn : mk' S n = mk' S m, hn' : ‖n‖ < ‖mk' S m‖ + ε⟩ :=
    norm_mk_lt (QuotientAddGroup.mk' S m) hε
  erw [eq_comm, QuotientAddGroup.eq] at hn
  use -m + n, hn
  rwa [add_neg_cancel_left]
#align norm_mk_lt' norm_mk_lt'

/-- The quotient norm satisfies the triangle inequality. -/
theorem quotient_norm_add_le (S : AddSubgroup M) (x y : M ⧸ S) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  rcases And.intro (mk_surjective x) (mk_surjective y) with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  simp only [← mk'_apply, ← map_add, quotient_norm_mk_eq, sInf_image']
  refine le_ciInf_add_ciInf fun a b ↦ ?_
  refine ciInf_le_of_le ⟨0, forall_mem_range.2 fun _ ↦ norm_nonneg _⟩ (a + b) ?_
  exact (congr_arg norm (add_add_add_comm _ _ _ _)).trans_le (norm_add_le _ _)
#align quotient_norm_add_le quotient_norm_add_le

/-- The quotient norm of `0` is `0`. -/
theorem norm_mk_zero (S : AddSubgroup M) : ‖(0 : M ⧸ S)‖ = 0 := by
  erw [quotient_norm_eq_zero_iff]
  exact subset_closure S.zero_mem
#align norm_mk_zero norm_mk_zero

/-- If `(m : M)` has norm equal to `0` in `M ⧸ S` for a closed subgroup `S` of `M`, then
`m ∈ S`. -/
theorem norm_mk_eq_zero (S : AddSubgroup M) (hS : IsClosed (S : Set M)) (m : M)
    (h : ‖mk' S m‖ = 0) : m ∈ S := by rwa [quotient_norm_eq_zero_iff, hS.closure_eq] at h
#align norm_zero_eq_zero norm_mk_eq_zero

theorem quotient_nhd_basis (S : AddSubgroup M) :
    (𝓝 (0 : M ⧸ S)).HasBasis (fun ε ↦ 0 < ε) fun ε ↦ { x | ‖x‖ < ε } := by
  have : ∀ ε : ℝ, mk '' ball (0 : M) ε = { x : M ⧸ S | ‖x‖ < ε } := by
    refine fun ε ↦ Set.ext <| forall_mk.2 fun x ↦ ?_
    rw [ball_zero_eq, mem_setOf_eq, norm_lt_iff, mem_image]
    exact exists_congr fun _ ↦ and_comm
  rw [← mk_zero, nhds_eq, ← funext this]
  exact .map _ Metric.nhds_basis_ball
#align quotient_nhd_basis quotient_nhd_basis

/-- The seminormed group structure on the quotient by an additive subgroup. -/
noncomputable instance AddSubgroup.seminormedAddCommGroupQuotient (S : AddSubgroup M) :
    SeminormedAddCommGroup (M ⧸ S) where
  dist x y := ‖x - y‖
  dist_self x := by simp only [norm_mk_zero, sub_self]
  dist_comm := quotient_norm_sub_rev
  dist_triangle x y z := by
    refine le_trans ?_ (quotient_norm_add_le _ _ _)
    exact (congr_arg norm (sub_add_sub_cancel _ _ _).symm).le
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
  toUniformSpace := TopologicalAddGroup.toUniformSpace (M ⧸ S)
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_zero', ((quotient_nhd_basis S).comap _).eq_biInf]
    simp only [dist, quotient_norm_sub_rev (Prod.fst _), preimage_setOf_eq]
#align add_subgroup.seminormed_add_comm_group_quotient AddSubgroup.seminormedAddCommGroupQuotient

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example (S : AddSubgroup M) :
    (instTopologicalSpaceQuotient : TopologicalSpace <| M ⧸ S) =
      S.seminormedAddCommGroupQuotient.toUniformSpace.toTopologicalSpace :=
  rfl

/-- The quotient in the category of normed groups. -/
noncomputable instance AddSubgroup.normedAddCommGroupQuotient (S : AddSubgroup M)
    [IsClosed (S : Set M)] : NormedAddCommGroup (M ⧸ S) :=
  { AddSubgroup.seminormedAddCommGroupQuotient S, MetricSpace.ofT0PseudoMetricSpace _ with }
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

/-- `S.normedMk` agrees with `QuotientAddGroup.mk' S`. -/
@[simp]
theorem normedMk.apply (S : AddSubgroup M) (m : M) : normedMk S m = QuotientAddGroup.mk' S m :=
  rfl
#align add_subgroup.normed_mk.apply AddSubgroup.normedMk.apply

/-- `S.normedMk` is surjective. -/
theorem surjective_normedMk (S : AddSubgroup M) : Function.Surjective (normedMk S) :=
  surjective_quot_mk _
#align add_subgroup.surjective_normed_mk AddSubgroup.surjective_normedMk

/-- The kernel of `S.normedMk` is `S`. -/
theorem ker_normedMk (S : AddSubgroup M) : S.normedMk.ker = S :=
  QuotientAddGroup.ker_mk' _
#align add_subgroup.ker_normed_mk AddSubgroup.ker_normedMk

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normedMk_le (S : AddSubgroup M) : ‖S.normedMk‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp [quotient_norm_mk_le']
#align add_subgroup.norm_normed_mk_le AddSubgroup.norm_normedMk_le

theorem _root_.QuotientAddGroup.norm_lift_apply_le {S : AddSubgroup M} (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ S, f x = 0) (x : M ⧸ S) : ‖lift S f.toAddMonoidHom hf x‖ ≤ ‖f‖ * ‖x‖ := by
  cases (norm_nonneg f).eq_or_gt with
  | inl h =>
    rcases mk_surjective x with ⟨x, rfl⟩
    simpa [h] using le_opNorm f x
  | inr h =>
    rw [← not_lt, ← _root_.lt_div_iff' h, norm_lt_iff]
    rintro ⟨x, rfl, hx⟩
    exact ((lt_div_iff' h).1 hx).not_le (le_opNorm f x)

/-- The operator norm of the projection is `1` if the subspace is not dense. -/
theorem norm_normedMk (S : AddSubgroup M) (h : (S.topologicalClosure : Set M) ≠ univ) :
    ‖S.normedMk‖ = 1 := by
  refine le_antisymm (norm_normedMk_le S) ?_
  obtain ⟨x, hx⟩ : ∃ x : M, 0 < ‖(x : M ⧸ S)‖ := by
    refine (Set.nonempty_compl.2 h).imp fun x hx ↦ ?_
    exact (norm_nonneg _).lt_of_ne' <| mt (quotient_norm_eq_zero_iff S x).1 hx
  refine (le_mul_iff_one_le_left hx).1 ?_
  exact norm_lift_apply_le S.normedMk (fun x ↦ (eq_zero_iff x).2) x
#align add_subgroup.norm_normed_mk AddSubgroup.norm_normedMk

/-- The operator norm of the projection is `0` if the subspace is dense. -/
theorem norm_trivial_quotient_mk (S : AddSubgroup M)
    (h : (S.topologicalClosure : Set M) = Set.univ) : ‖S.normedMk‖ = 0 := by
  refine' le_antisymm (opNorm_le_bound _ le_rfl fun x => _) (norm_nonneg _)
  have hker : x ∈ S.normedMk.ker.topologicalClosure := by
    rw [S.ker_normedMk, ← SetLike.mem_coe, h]
    trivial
  rw [ker_normedMk] at hker
  simp only [(quotient_norm_eq_zero_iff S x).mpr hker, normedMk.apply, zero_mul, le_rfl]
#align add_subgroup.norm_trivial_quotient_mk AddSubgroup.norm_trivial_quotient_mk

end AddSubgroup

namespace NormedAddGroupHom

/-- `IsQuotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of `M`
by the kernel of `f`. -/
structure IsQuotient (f : NormedAddGroupHom M N) : Prop where
  protected surjective : Function.Surjective f
  protected norm : ∀ x, ‖f x‖ = sInf ((fun m => ‖x + m‖) '' f.ker)
#align normed_add_group_hom.is_quotient NormedAddGroupHom.IsQuotient

/-- Given `f : NormedAddGroupHom M N` such that `f s = 0` for all `s ∈ S`, where,
`S : AddSubgroup M` is closed, the induced morphism `NormedAddGroupHom (M ⧸ S) N`. -/
noncomputable def lift {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) : NormedAddGroupHom (M ⧸ S) N :=
  { QuotientAddGroup.lift S f.toAddMonoidHom hf with
    bound' := ⟨‖f‖, norm_lift_apply_le f hf⟩ }
#align normed_add_group_hom.lift NormedAddGroupHom.lift

theorem lift_mk {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (m : M) :
    lift S f hf (S.normedMk m) = f m :=
  rfl
#align normed_add_group_hom.lift_mk NormedAddGroupHom.lift_mk

theorem lift_unique {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (g : NormedAddGroupHom (M ⧸ S) N)
    (h : g.comp S.normedMk = f) : g = lift S f hf := by
  ext x
  rcases AddSubgroup.surjective_normedMk _ x with ⟨x, rfl⟩
  change g.comp S.normedMk x = _
  simp only [h]
  rfl
#align normed_add_group_hom.lift_unique NormedAddGroupHom.lift_unique

/-- `S.normedMk` satisfies `IsQuotient`. -/
theorem isQuotientQuotient (S : AddSubgroup M) : IsQuotient S.normedMk :=
  ⟨S.surjective_normedMk, fun m => by simpa [S.ker_normedMk] using quotient_norm_mk_eq _ m⟩
#align normed_add_group_hom.is_quotient_quotient NormedAddGroupHom.isQuotientQuotient

theorem IsQuotient.norm_lift {f : NormedAddGroupHom M N} (hquot : IsQuotient f) {ε : ℝ} (hε : 0 < ε)
    (n : N) : ∃ m : M, f m = n ∧ ‖m‖ < ‖n‖ + ε := by
  obtain ⟨m, rfl⟩ := hquot.surjective n
  have nonemp : ((fun m' => ‖m + m'‖) '' f.ker).Nonempty := by
    rw [Set.image_nonempty]
    exact ⟨0, f.ker.zero_mem⟩
  rcases Real.lt_sInf_add_pos nonemp hε
    with ⟨_, ⟨⟨x, hx, rfl⟩, H : ‖m + x‖ < sInf ((fun m' : M => ‖m + m'‖) '' f.ker) + ε⟩⟩
  exact ⟨m + x, by rw [map_add, (NormedAddGroupHom.mem_ker f x).mp hx, add_zero], by
    rwa [hquot.norm]⟩
#align normed_add_group_hom.is_quotient.norm_lift NormedAddGroupHom.IsQuotient.norm_lift

theorem IsQuotient.norm_le {f : NormedAddGroupHom M N} (hquot : IsQuotient f) (m : M) :
    ‖f m‖ ≤ ‖m‖ := by
  rw [hquot.norm]
  apply csInf_le
  · use 0
    rintro _ ⟨m', -, rfl⟩
    apply norm_nonneg
  · exact ⟨0, f.ker.zero_mem, by simp⟩
#align normed_add_group_hom.is_quotient.norm_le NormedAddGroupHom.IsQuotient.norm_le

-- Porting note (#10756): new lemma
theorem norm_lift_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) :
    ‖lift S f hf‖ ≤ ‖f‖ :=
  opNorm_le_bound _ (norm_nonneg f) (norm_lift_apply_le f hf)

-- Porting note (#11215): TODO: deprecate?
theorem lift_norm_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) :
    ‖lift S f hf‖ ≤ c :=
  (norm_lift_le S f hf).trans fb
#align normed_add_group_hom.lift_norm_le NormedAddGroupHom.lift_norm_le

theorem lift_normNoninc {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (fb : f.NormNoninc) :
    (lift S f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ (1 : ℝ≥0) := NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using le_of_opNorm_le _ (f.lift_norm_le _ _ fb') _
#align normed_add_group_hom.lift_norm_noninc NormedAddGroupHom.lift_normNoninc

end NormedAddGroupHom

/-!
### Submodules and ideals

In what follows, the norm structures created above for quotients of (semi)`NormedAddCommGroup`s
by `AddSubgroup`s are transferred via definitional equality to quotients of modules by submodules,
and of rings by ideals, thereby preserving the definitional equality for the topological group and
uniform structures worked for above. Completeness is also transferred via this definitional
equality.

In addition, instances are constructed for `NormedSpace`, `SeminormedCommRing`,
`NormedCommRing` and `NormedAlgebra` under the appropriate hypotheses. Currently, we do not
have quotients of rings by two-sided ideals, hence the commutativity hypotheses are required.
-/

section Submodule

variable {R : Type*} [Ring R] [Module R M] (S : Submodule R M)

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

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `Submodule.Quotient.mk m = x`
and `‖m‖ < ‖x‖ + ε`. -/
nonrec theorem Submodule.Quotient.norm_mk_lt {S : Submodule R M} (x : M ⧸ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : M, Submodule.Quotient.mk m = x ∧ ‖m‖ < ‖x‖ + ε :=
  norm_mk_lt x hε
#align submodule.quotient.norm_mk_lt Submodule.Quotient.norm_mk_lt

theorem Submodule.Quotient.norm_mk_le (m : M) : ‖(Submodule.Quotient.mk m : M ⧸ S)‖ ≤ ‖m‖ :=
  quotient_norm_mk_le S.toAddSubgroup m
#align submodule.quotient.norm_mk_le Submodule.Quotient.norm_mk_le

instance Submodule.Quotient.instBoundedSMul (𝕜 : Type*)
    [SeminormedCommRing 𝕜] [Module 𝕜 M] [BoundedSMul 𝕜 M] [SMul 𝕜 R] [IsScalarTower 𝕜 R M] :
    BoundedSMul 𝕜 (M ⧸ S) :=
  .of_norm_smul_le fun k x =>
    -- Porting note: this is `QuotientAddGroup.norm_lift_apply_le` for `f : M → M ⧸ S` given by
    -- `x ↦ mk (k • x)`; todo: add scalar multiplication as `NormedAddGroupHom`, use it here
    _root_.le_of_forall_pos_le_add fun ε hε => by
      have := (nhds_basis_ball.tendsto_iff nhds_basis_ball).mp
        ((@Real.uniformContinuous_const_mul ‖k‖).continuous.tendsto ‖x‖) ε hε
      simp only [mem_ball, exists_prop, dist, abs_sub_lt_iff] at this
      rcases this with ⟨δ, hδ, h⟩
      obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hδ
      specialize h ‖a‖ ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le S a]⟩
      calc
        _ ≤ ‖k‖ * ‖a‖ := (quotient_norm_mk_le S.toAddSubgroup (k • a)).trans (norm_smul_le k a)
        _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

instance Submodule.Quotient.normedSpace (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 M] [SMul 𝕜 R]
    [IsScalarTower 𝕜 R M] : NormedSpace 𝕜 (M ⧸ S) where
  norm_smul_le := norm_smul_le
#align submodule.quotient.normed_space Submodule.Quotient.normedSpace

end Submodule

section Ideal

variable {R : Type*} [SeminormedCommRing R] (I : Ideal R)

nonrec theorem Ideal.Quotient.norm_mk_lt {I : Ideal R} (x : R ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : R, Ideal.Quotient.mk I r = x ∧ ‖r‖ < ‖x‖ + ε :=
  norm_mk_lt x hε
#align ideal.quotient.norm_mk_lt Ideal.Quotient.norm_mk_lt

theorem Ideal.Quotient.norm_mk_le (r : R) : ‖Ideal.Quotient.mk I r‖ ≤ ‖r‖ :=
  quotient_norm_mk_le I.toAddSubgroup r
#align ideal.quotient.norm_mk_le Ideal.Quotient.norm_mk_le

instance Ideal.Quotient.semiNormedCommRing : SeminormedCommRing (R ⧸ I) where
  dist_eq := dist_eq_norm
  mul_comm := _root_.mul_comm
  norm_mul x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, mem_ball, and_imp, Prod.forall, exists_prop, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := Ideal.Quotient.norm_mk_lt x h₁,
      Ideal.Quotient.norm_mk_lt y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I a]⟩
      ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ := (Ideal.Quotient.norm_mk_le I (a * b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le
#align ideal.quotient.semi_normed_comm_ring Ideal.Quotient.semiNormedCommRing

instance Ideal.Quotient.normedCommRing [IsClosed (I : Set R)] : NormedCommRing (R ⧸ I) :=
  { Ideal.Quotient.semiNormedCommRing I, Submodule.Quotient.normedAddCommGroup I with }
#align ideal.quotient.normed_comm_ring Ideal.Quotient.normedCommRing

variable (𝕜 : Type*) [NormedField 𝕜]

instance Ideal.Quotient.normedAlgebra [NormedAlgebra 𝕜 R] : NormedAlgebra 𝕜 (R ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }
#align ideal.quotient.normed_algebra Ideal.Quotient.normedAlgebra

end Ideal
