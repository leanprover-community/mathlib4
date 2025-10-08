/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Riccardo Brasca
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Topology.MetricSpace.HausdorffDistance

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
`quotient_nhds_basis` that has no use beyond this verification and states that zero in the quotient
admits as basis of neighborhoods in the quotient topology the sets `{x | ‖x‖ < ε}` for positive `ε`.

Once this mathematical point is settled, we have two topologies that are propositionally equal. This
is not good enough for the type class system. As usual we ensure *definitional* equality
using forgetful inheritance, see Note [forgetful inheritance]. A (semi)-normed group structure
includes a uniform space structure which includes a topological space structure, together
with propositional fields asserting compatibility conditions.
The usual way to define a `SeminormedAddCommGroup` is to let Lean build a uniform space structure
using the provided norm, and then trivially build a proof that the norm and uniform structure are
compatible. Here the uniform structure is provided using `IsTopologicalAddGroup.toUniformSpace`
which uses the topological structure and the group structure to build the uniform structure. This
uniform structure induces the correct topological structure by construction, but the fact that it
is compatible with the norm is not obvious; this is where the mathematical content explained in
the previous paragraph kicks in.

-/


noncomputable section

open Metric Set Topology NNReal

namespace QuotientGroup
variable {M : Type*} [SeminormedCommGroup M] {S : Subgroup M} {x : M ⧸ S} {m : M} {r ε : ℝ}

@[to_additive add_norm_aux]
private lemma norm_aux (x : M ⧸ S) : {m : M | (m : M ⧸ S) = x}.Nonempty := Quot.exists_rep x

/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x * M`. -/
@[to_additive
/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x + S`. -/]
noncomputable def groupSeminorm : GroupSeminorm (M ⧸ S) where
  toFun x := infDist 1 {m : M | (m : M ⧸ S) = x}
  map_one' := infDist_zero_of_mem (by simp)
  mul_le' x y := by
    simp only [infDist_eq_iInf]
    have := (norm_aux x).to_subtype
    have := (norm_aux y).to_subtype
    refine le_ciInf_add_ciInf ?_
    rintro ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ciInf_le_of_le ⟨0, forall_mem_range.2 fun _ ↦ dist_nonneg⟩ ⟨a * b, rfl⟩ ?_
    simpa using norm_mul_le' _ _
  inv' x := eq_of_forall_le_iff fun r ↦ by
    simp only [le_infDist (norm_aux _)]
    exact (Equiv.inv _).forall_congr (by simp [← inv_eq_iff_eq_inv])

/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x * S`. -/
@[to_additive
/-- The norm of `x` on the quotient by a subgroup `S` is defined as the infimum of the norm on
`x + S`. -/]
noncomputable instance instNorm : Norm (M ⧸ S) where norm := groupSeminorm

@[to_additive]
lemma norm_eq_groupSeminorm (x : M ⧸ S) : ‖x‖ = groupSeminorm x := rfl

@[to_additive]
lemma norm_eq_infDist (x : M ⧸ S) : ‖x‖ = infDist 1 {m : M | (m : M ⧸ S) = x} := rfl

@[to_additive]
lemma le_norm_iff : r ≤ ‖x‖ ↔ ∀ m : M, ↑m = x → r ≤ ‖m‖ := by
  simp [norm_eq_infDist, le_infDist (norm_aux _)]

@[to_additive]
lemma norm_lt_iff : ‖x‖ < r ↔ ∃ m : M, ↑m = x ∧ ‖m‖ < r := by
  simp [norm_eq_infDist, infDist_lt_iff (norm_aux _)]

@[to_additive]
lemma nhds_one_hasBasis : (𝓝 (1 : M ⧸ S)).HasBasis (fun ε ↦ 0 < ε) fun ε ↦ {x | ‖x‖ < ε} := by
  have : ∀ ε : ℝ, mk '' ball (1 : M) ε = {x : M ⧸ S | ‖x‖ < ε} := by
    refine fun ε ↦ Set.ext <| forall_mk.2 fun x ↦ ?_
    rw [ball_one_eq, mem_setOf_eq, norm_lt_iff, mem_image]
    exact exists_congr fun _ ↦ and_comm
  rw [← mk_one, nhds_eq, ← funext this]
  exact .map _ Metric.nhds_basis_ball

/-- An alternative definition of the norm on the quotient group: the norm of `((x : M) : M ⧸ S)` is
equal to the distance from `x` to `S`. -/
@[to_additive
/-- An alternative definition of the norm on the quotient group: the norm of `((x : M) : M ⧸ S)` is
equal to the distance from `x` to `S`. -/]
lemma norm_mk (x : M) : ‖(x : M ⧸ S)‖ = infDist x S := by
  rw [norm_eq_infDist, ← infDist_image (IsometryEquiv.divLeft x).isometry,
    ← IsometryEquiv.preimage_symm]
  simp

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
@[to_additive
/-- The norm of the projection is smaller or equal to the norm of the original element. -/]
lemma norm_mk_le_norm : ‖(m : M ⧸ S)‖ ≤ ‖m‖ :=
  (infDist_le_dist_of_mem (by simp)).trans_eq (dist_one_left _)

/-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m` belongs
to the closure of `S`. -/
@[to_additive /-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m`
belongs to the closure of `S`. -/]
lemma norm_mk_eq_zero_iff_mem_closure : ‖(m : M ⧸ S)‖ = 0 ↔ m ∈ closure (S : Set M) := by
  rw [norm_mk, ← mem_closure_iff_infDist_zero]
  exact ⟨1, S.one_mem⟩

/-- The norm of the image of `m : M` in the quotient by a closed subgroup `S` is zero if and only if
`m ∈ S`. -/
@[to_additive /-- The norm of the image of `m : M` in the quotient by a closed subgroup `S` is zero
if and only if `m ∈ S`. -/]
lemma norm_mk_eq_zero [hS : IsClosed (S : Set M)] : ‖(m : M ⧸ S)‖ = 0 ↔ m ∈ S := by
  rw [norm_mk_eq_zero_iff_mem_closure, hS.closure_eq, SetLike.mem_coe]

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `‖m‖ < ‖x‖ + ε`. -/
@[to_additive /-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `‖m‖ < ‖x‖ + ε`. -/]
lemma exists_norm_mk_lt (x : M ⧸ S) (hε : 0 < ε) : ∃ m : M, m = x ∧ ‖m‖ < ‖x‖ + ε :=
  norm_lt_iff.1 <| lt_add_of_pos_right _ hε

/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `‖m * s‖ < ‖mk' S m‖ + ε`. -/
@[to_additive
/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `‖m + s‖ < ‖mk' S m‖ + ε`. -/]
lemma exists_norm_mul_lt (S : Subgroup M) (m : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, ‖m * s‖ < ‖mk' S m‖ + ε := by
  obtain ⟨n : M, hn, hn'⟩ := exists_norm_mk_lt (QuotientGroup.mk' S m) hε
  exact ⟨m⁻¹ * n, by simpa [eq_comm, QuotientGroup.eq] using hn, by simpa⟩

variable (S) in
/-- The seminormed group structure on the quotient by a subgroup. -/
@[to_additive /-- The seminormed group structure on the quotient by an additive subgroup. -/]
noncomputable instance instSeminormedCommGroup : SeminormedCommGroup (M ⧸ S) where
  toUniformSpace := IsTopologicalGroup.toUniformSpace (M ⧸ S)
  __ := groupSeminorm.toSeminormedCommGroup
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_one', (nhds_one_hasBasis.comap _).eq_biInf]
    simp only [dist, preimage_setOf_eq, norm_eq_groupSeminorm, map_div_rev]

variable (S) in
/-- The quotient in the category of normed groups. -/
@[to_additive /-- The quotient in the category of normed groups. -/]
noncomputable instance instNormedCommGroup [hS : IsClosed (S : Set M)] :
    NormedCommGroup (M ⧸ S) where
  __ := MetricSpace.ofT0PseudoMetricSpace _

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example :
    (instTopologicalSpaceQuotient : TopologicalSpace <| M ⧸ S) =
      (instSeminormedCommGroup S).toUniformSpace.toTopologicalSpace := rfl

example [IsClosed (S : Set M)] :
    (instSeminormedCommGroup S) = NormedCommGroup.toSeminormedCommGroup := rfl

end QuotientGroup

open QuotientAddGroup Metric Set Topology NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

/-- The norm of the image under the natural morphism to the quotient. -/
theorem quotient_norm_mk_eq (S : AddSubgroup M) (m : M) :
    ‖mk' S m‖ = sInf ((‖m + ·‖) '' S) := by
  rw [mk'_apply, norm_mk, sInf_image', ← infDist_image isometry_neg, image_neg_eq_neg,
    neg_coe_set (H := S), infDist_eq_iInf]
  simp only [dist_eq_norm', sub_neg_eq_add, add_comm]

/-- The quotient norm satisfies the triangle inequality. -/
theorem quotient_norm_add_le (S : AddSubgroup M) (x y : M ⧸ S) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

namespace AddSubgroup

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by a subgroup. -/
noncomputable def normedMk (S : AddSubgroup M) : NormedAddGroupHom M (M ⧸ S) where
  __ := QuotientAddGroup.mk' S
  bound' := ⟨1, fun m => by simpa [one_mul] using norm_mk_le_norm⟩

/-- `S.normedMk` agrees with `QuotientAddGroup.mk' S`. -/
@[simp]
theorem normedMk.apply (S : AddSubgroup M) (m : M) : normedMk S m = QuotientAddGroup.mk' S m :=
  rfl

/-- `S.normedMk` is surjective. -/
theorem surjective_normedMk (S : AddSubgroup M) : Function.Surjective (normedMk S) :=
  Quot.mk_surjective

/-- The kernel of `S.normedMk` is `S`. -/
theorem ker_normedMk (S : AddSubgroup M) : S.normedMk.ker = S :=
  QuotientAddGroup.ker_mk' _

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normedMk_le (S : AddSubgroup M) : ‖S.normedMk‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp [norm_mk_le_norm]

theorem _root_.QuotientAddGroup.norm_lift_apply_le {S : AddSubgroup M} (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ S, f x = 0) (x : M ⧸ S) : ‖lift S f.toAddMonoidHom hf x‖ ≤ ‖f‖ * ‖x‖ := by
  cases (norm_nonneg f).eq_or_lt' with
  | inl h =>
    rcases mk_surjective x with ⟨x, rfl⟩
    simpa [h] using le_opNorm f x
  | inr h =>
    rw [← not_lt, ← lt_div_iff₀' h, norm_lt_iff]
    rintro ⟨x, rfl, hx⟩
    exact ((lt_div_iff₀' h).1 hx).not_ge (le_opNorm f x)

/-- The operator norm of the projection is `1` if the subspace is not dense. -/
theorem norm_normedMk (S : AddSubgroup M) (h : (S.topologicalClosure : Set M) ≠ univ) :
    ‖S.normedMk‖ = 1 := by
  refine le_antisymm (norm_normedMk_le S) ?_
  obtain ⟨x, hx⟩ : ∃ x : M, 0 < ‖(x : M ⧸ S)‖ := by
    refine (Set.nonempty_compl.2 h).imp fun x hx ↦ ?_
    exact (norm_nonneg _).lt_of_ne' <| mt norm_mk_eq_zero_iff_mem_closure.1 hx
  refine (le_mul_iff_one_le_left hx).1 ?_
  exact norm_lift_apply_le S.normedMk (fun x ↦ (eq_zero_iff x).2) x

/-- The operator norm of the projection is `0` if the subspace is dense. -/
theorem norm_trivial_quotient_mk (S : AddSubgroup M)
    (h : (S.topologicalClosure : Set M) = Set.univ) : ‖S.normedMk‖ = 0 := by
  refine le_antisymm (opNorm_le_bound _ le_rfl fun x => ?_) (norm_nonneg _)
  have hker : x ∈ S.normedMk.ker.topologicalClosure := by
    rw [S.ker_normedMk, ← SetLike.mem_coe, h]
    trivial
  rw [ker_normedMk] at hker
  simp [norm_mk_eq_zero_iff_mem_closure.mpr hker]

end AddSubgroup

namespace NormedAddGroupHom

/-- `IsQuotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of `M`
by the kernel of `f`. -/
structure IsQuotient (f : NormedAddGroupHom M N) : Prop where
  protected surjective : Function.Surjective f
  protected norm : ∀ x, ‖f x‖ = sInf ((fun m => ‖x + m‖) '' f.ker)

/-- Given `f : NormedAddGroupHom M N` such that `f s = 0` for all `s ∈ S`, where,
`S : AddSubgroup M` is closed, the induced morphism `NormedAddGroupHom (M ⧸ S) N`. -/
noncomputable def lift {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) : NormedAddGroupHom (M ⧸ S) N :=
  { QuotientAddGroup.lift S f.toAddMonoidHom hf with
    bound' := ⟨‖f‖, norm_lift_apply_le f hf⟩ }

theorem lift_mk {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (m : M) :
    lift S f hf (S.normedMk m) = f m :=
  rfl

theorem lift_unique {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (g : NormedAddGroupHom (M ⧸ S) N)
    (h : g.comp S.normedMk = f) : g = lift S f hf := by
  ext x
  rcases AddSubgroup.surjective_normedMk _ x with ⟨x, rfl⟩
  change g.comp S.normedMk x = _
  simp only [h]
  rfl

/-- `S.normedMk` satisfies `IsQuotient`. -/
theorem isQuotientQuotient (S : AddSubgroup M) : IsQuotient S.normedMk :=
  ⟨S.surjective_normedMk, fun m => by simpa [S.ker_normedMk] using quotient_norm_mk_eq _ m⟩

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

theorem IsQuotient.norm_le {f : NormedAddGroupHom M N} (hquot : IsQuotient f) (m : M) :
    ‖f m‖ ≤ ‖m‖ := by
  rw [hquot.norm]
  apply csInf_le
  · use 0
    rintro _ ⟨m', -, rfl⟩
    apply norm_nonneg
  · exact ⟨0, f.ker.zero_mem, by simp⟩

theorem norm_lift_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) :
    ‖lift S f hf‖ ≤ ‖f‖ :=
  opNorm_le_bound _ (norm_nonneg f) (norm_lift_apply_le f hf)

-- TODO: deprecate?
theorem lift_norm_le {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) :
    ‖lift S f hf‖ ≤ c :=
  (norm_lift_le S f hf).trans fb

theorem lift_normNoninc {N : Type*} [SeminormedAddCommGroup N] (S : AddSubgroup M)
    (f : NormedAddGroupHom M N) (hf : ∀ s ∈ S, f s = 0) (fb : f.NormNoninc) :
    (lift S f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ (1 : ℝ≥0) := NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using le_of_opNorm_le _ (f.lift_norm_le _ _ fb') _

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
  QuotientAddGroup.instSeminormedAddCommGroup S.toAddSubgroup

instance Submodule.Quotient.normedAddCommGroup [hS : IsClosed (S : Set M)] :
    NormedAddCommGroup (M ⧸ S) :=
  QuotientAddGroup.instNormedAddCommGroup S.toAddSubgroup (hS := hS)

instance Submodule.Quotient.completeSpace [CompleteSpace M] : CompleteSpace (M ⧸ S) :=
  QuotientAddGroup.completeSpace M S.toAddSubgroup

/-- For any `x : M ⧸ S` and any `0 < ε`, there is `m : M` such that `Submodule.Quotient.mk m = x`
and `‖m‖ < ‖x‖ + ε`. -/
nonrec theorem Submodule.Quotient.norm_mk_lt {S : Submodule R M} (x : M ⧸ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : M, Submodule.Quotient.mk m = x ∧ ‖m‖ < ‖x‖ + ε :=
  exists_norm_mk_lt x hε

theorem Submodule.Quotient.norm_mk_le (m : M) : ‖(Submodule.Quotient.mk m : M ⧸ S)‖ ≤ ‖m‖ :=
  norm_mk_le_norm

instance Submodule.Quotient.instIsBoundedSMul (𝕜 : Type*)
    [SeminormedCommRing 𝕜] [Module 𝕜 M] [IsBoundedSMul 𝕜 M] [SMul 𝕜 R] [IsScalarTower 𝕜 R M] :
    IsBoundedSMul 𝕜 (M ⧸ S) :=
  .of_norm_smul_le fun k x =>
    -- this is `QuotientAddGroup.norm_lift_apply_le` for `f : M → M ⧸ S` given by
    -- `x ↦ mk (k • x)`; todo: add scalar multiplication as `NormedAddGroupHom`, use it here
    _root_.le_of_forall_pos_le_add fun ε hε => by
      have := (nhds_basis_ball.tendsto_iff nhds_basis_ball).mp
        ((@Real.uniformContinuous_const_mul ‖k‖).continuous.tendsto ‖x‖) ε hε
      simp only [mem_ball, dist, abs_sub_lt_iff] at this
      rcases this with ⟨δ, hδ, h⟩
      obtain ⟨a, rfl, ha⟩ := Submodule.Quotient.norm_mk_lt x hδ
      specialize h ‖a‖ ⟨by linarith, by linarith [Submodule.Quotient.norm_mk_le S a]⟩
      calc
        _ ≤ ‖k‖ * ‖a‖ := (norm_mk_le ..).trans (norm_smul_le k a)
        _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

instance Submodule.Quotient.normedSpace (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 M] [SMul 𝕜 R]
    [IsScalarTower 𝕜 R M] : NormedSpace 𝕜 (M ⧸ S) where
  norm_smul_le := norm_smul_le

end Submodule

section Ideal

variable {R : Type*} [SeminormedCommRing R] (I : Ideal R)

nonrec theorem Ideal.Quotient.norm_mk_lt {I : Ideal R} (x : R ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : R, Ideal.Quotient.mk I r = x ∧ ‖r‖ < ‖x‖ + ε :=
  exists_norm_mk_lt x hε

theorem Ideal.Quotient.norm_mk_le (r : R) : ‖Ideal.Quotient.mk I r‖ ≤ ‖r‖ := norm_mk_le_norm

instance Ideal.Quotient.semiNormedCommRing : SeminormedCommRing (R ⧸ I) where
  dist_eq := dist_eq_norm
  mul_comm := _root_.mul_comm
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, mem_ball, and_imp, Prod.forall, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := Ideal.Quotient.norm_mk_lt x h₁,
      Ideal.Quotient.norm_mk_lt y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I a]⟩
      ⟨by linarith, by linarith [Ideal.Quotient.norm_mk_le I b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ := (Ideal.Quotient.norm_mk_le I (a * b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

instance Ideal.Quotient.normedCommRing [IsClosed (I : Set R)] : NormedCommRing (R ⧸ I) :=
  { Ideal.Quotient.semiNormedCommRing I, Submodule.Quotient.normedAddCommGroup I with }

variable (𝕜 : Type*) [NormedField 𝕜]

instance Ideal.Quotient.normedAlgebra [NormedAlgebra 𝕜 R] : NormedAlgebra 𝕜 (R ⧸ I) :=
  { Submodule.Quotient.normedSpace I 𝕜, Ideal.Quotient.algebra 𝕜 with }

end Ideal
