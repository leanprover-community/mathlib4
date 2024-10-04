/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Hom
import Mathlib.Topology.Algebra.SeparationQuotient
import Mathlib.Topology.MetricSpace.HausdorffDistance

-- TODO modify doc, check if instances are really needed, golf

/-!
# Quotients of seminormed groups by the null space

For any `SeminormedAddCommGroup M`, we provide a `SeminormedAddCommGroup`, the group quotient
`SeparationQuotient M`, the quotient by the null space.
On the quotient we define the quotient norm and the projection is a normed group homomorphism which
is norm non-increasing (better, it has operator norm exactly one unless the nullSpace is equal to
in `M`). The corresponding universal property is that every normed group hom defined on `M` which
vanishes on the null space descends to a normed group hom defined on `SeparationQuotient M`.

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

* `normedMk S` : the normed group hom from `M` to `SeparationQuotient M`.

* `lift S f hf`: implements the universal property of `SeparationQuotient M`. Here
    `(f : NormedAddGroupHom M N)`, `(hf : ∀ s ∈ S, f s = 0)` and
    `lift S f hf : NormedAddGroupHom (SeparationQuotient M) N`.

* `IsQuotient`: given `f : NormedAddGroupHom M N`, `IsQuotient f` means `N` is isomorphic
    to a quotient of `M` by a subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

* `norm_normedMk` : the operator norm of the projection is `1` if the subspace is not dense.

* `IsQuotient.norm_lift`: Provided `f : normed_hom M N` satisfies `IsQuotient f`, for every
     `n : N` and positive `ε`, there exists `m` such that `f m = n ∧ ‖m‖ < ‖n‖ + ε`.


## Implementation details

For any `SeminormedAddCommGroup M` and any `S : AddSubgroup M` we define a norm on `SeparationQuotient M` by
`‖x‖ = sInf (norm '' {m | mk' S m = x})`. This formula is really an implementation detail, it
shouldn't be needed outside of this file setting up the theory.

Since `SeparationQuotient M` is automatically a topological space (as any quotient of a topological space),
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

open SeparationQuotient Metric Set Topology NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

namespace SeparationQuotient

/-- The null space with respect to the norm. -/
def nullSpace : AddSubgroup M where
  carrier := {x : M | ‖x‖ = 0}
  add_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_add_le x y).trans_eq ?_
    rw [hx, hy, add_zero]
  zero_mem' := norm_zero
  neg_mem' {x} (hx : ‖x‖ = 0) := by
    simp only [mem_setOf_eq, norm_neg]
    exact hx
--   smul_mem' c x (hx : ‖x‖ = 0) := by
--     apply le_antisymm _ (norm_nonneg _)
--     refine (norm_smul_le _ _).trans_eq ?_
--     rw [hx, mul_zero]

lemma inseparable_iff_norm_zero (x y : M) : Inseparable x y ↔ ‖x - y‖ = 0 := by
  rw [Metric.inseparable_iff, dist_eq_norm]

lemma isClosed_nullSpace : IsClosed (@nullSpace M _ : Set M) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  rw [Metric.mem_nhds_iff]
  use ‖x‖ / 2
  have : 0 < ‖x‖ := by
    apply Ne.lt_of_le _ (norm_nonneg x)
    exact fun a ↦ hx (id (Eq.symm a))
  constructor
  · exact half_pos this
  · intro y hy
    simp only [mem_ball, dist_eq_norm] at hy
    have : ‖x‖ / 2 < ‖y‖ := by
      calc ‖x‖ / 2  = ‖x‖ - ‖x‖ / 2 := by ring
      _ < ‖x‖ - ‖y - x‖ := by exact sub_lt_sub_left hy ‖x‖
      _ = ‖x‖ - ‖x - y‖ := by rw [← norm_neg (y-x), ← neg_sub y x]
      _ ≤ ‖x - (x - y)‖ := by exact norm_sub_norm_le x (x - y)
      _ = ‖y‖ := by rw [sub_sub_self x y]
    exact ne_of_gt (lt_of_le_of_lt (div_nonneg (norm_nonneg x) (zero_le_two)) this)

instance : Nonempty (@nullSpace M _) := ⟨0⟩

/-- The definition of the norm on the quotient by an additive subgroup. -/
noncomputable instance normOnSeparationQuotient : Norm (SeparationQuotient M) where
  norm x := sInf (norm '' { m | mk m = x })

theorem norm_eq (x : SeparationQuotient M) :
    ‖x‖ = sInf (norm '' { m : M | mk m = x }) := rfl

theorem norm_eq_infDist (x : SeparationQuotient M) :
    ‖x‖ = infDist 0 { m : M | mk m = x } := by
  simp only [norm_eq, infDist_eq_iInf, sInf_image', dist_zero_left]

/-- An alternative definition of the norm on the quotient group: the norm of `mk x` is
equal to the distance from `x` to `nullSpace`. -/
theorem norm_mk (x : M) : ‖mk x‖ = infDist x (@nullSpace M _) := by
  rw [norm_eq_infDist, ← infDist_image (IsometryEquiv.subLeft x).isometry,
    IsometryEquiv.subLeft_apply, sub_zero, ← IsometryEquiv.preimage_symm]
  congr 1 with y
  simp only [mk_eq_mk, preimage_setOf_eq, IsometryEquiv.subLeft_symm_apply, mem_setOf_eq,
    AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, AddSubgroup.mem_toAddSubmonoid]
  rw [inseparable_iff_norm_zero]
  simp only [add_sub_cancel_right, norm_neg]
  exact Eq.to_iff rfl

theorem image_norm_nonempty (x : SeparationQuotient M) :
    (norm '' { m | mk m = x }).Nonempty := .image _ <| Quot.exists_rep x

theorem bddBelow_image_norm (s : Set M) : BddBelow (norm '' s) :=
  ⟨0, forall_mem_image.2 fun _ _ ↦ norm_nonneg _⟩

theorem isGLB_quotient_norm (x : SeparationQuotient M) :
    IsGLB (norm '' { m | mk m = x }) (‖x‖) :=
  isGLB_csInf (image_norm_nonempty x) (bddBelow_image_norm _)

/-- The norm on the quotient satisfies `‖-x‖ = ‖x‖`. -/
theorem quotient_norm_neg (x : SeparationQuotient M) : ‖-x‖ = ‖x‖ := by
  simp only [SeparationQuotient.norm_eq]
  congr 1 with r
  constructor <;> { rintro ⟨m, hm, rfl⟩; use -m; simpa [neg_eq_iff_eq_neg] using hm }

theorem quotient_norm_sub_rev (x y : SeparationQuotient M) : ‖x - y‖ = ‖y - x‖ := by
  rw [← neg_sub, quotient_norm_neg]

lemma norm_mk_eq_sInf (m : M) : ‖mk m‖ = sInf ((‖m + ·‖) '' @nullSpace M _) := by
  rw [norm_mk, sInf_image', ← infDist_image isometry_neg, image_neg]
  have : -(@nullSpace M _: Set M) = (@nullSpace M _: Set M) := by
    ext x
    rw [Set.mem_neg]
    constructor
    · intro hx
      rw [← neg_neg x]
      exact nullSpace.neg_mem' hx
    · intro hx
      exact nullSpace.neg_mem' hx
  rw [this, infDist_eq_iInf]
  simp only [dist_eq_norm', sub_neg_eq_add, add_comm]

/-- The norm of the projection is equal to the norm of the original element. -/
@[simp]
theorem quotient_norm_mk_eq (m : M) : ‖mk m‖ = ‖m‖ := by
  apply le_antisymm
  · exact csInf_le (bddBelow_image_norm _) <| Set.mem_image_of_mem _ rfl
  · rw [norm_mk_eq_sInf]
    apply le_csInf
    · use ‖m‖
      use 0
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        AddSubgroup.mem_toAddSubmonoid, add_zero]
      exact ⟨AddSubgroup.zero_mem nullSpace, trivial⟩
    · intro b hb
      obtain ⟨x, hx⟩ := hb
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        AddSubgroup.mem_toAddSubmonoid] at hx
      rw [← hx.2]
      calc ‖m‖ = ‖m + x - x‖ := by simp only [add_sub_cancel_right]
      _ ≤ ‖m + x‖ + ‖x‖ := by exact norm_sub_le (m + x) x
      _ = ‖m + x‖ + 0 := by rw [hx.1]
      _ = ‖m + x‖ := by exact AddMonoid.add_zero ‖m + x‖

/-- The quotient norm is nonnegative. -/
theorem quotient_norm_nonneg (x : SeparationQuotient M) : 0 ≤ ‖x‖ :=
  Real.sInf_nonneg _ <| forall_mem_image.2 fun _ _ ↦ norm_nonneg _

/-- The quotient norm is nonnegative. -/
theorem norm_mk_nonneg (m : M) : 0 ≤ ‖mk m‖ := quotient_norm_nonneg _

/-- The norm of the image of `m : M` in the quotient by the null space is zero if and only if `m`
belongs to the null space. -/
theorem quotient_norm_eq_zero_iff (m : M) :
    ‖mk m‖ = 0 ↔ m ∈ nullSpace := by
  rw [norm_mk]
  rw [← SetLike.mem_coe]
  nth_rw 2 [← IsClosed.closure_eq isClosed_nullSpace]
  rw [← mem_closure_iff_infDist_zero]
  exact ⟨0, nullSpace.zero_mem'⟩

theorem norm_lt_iff {x : SeparationQuotient M} {r : ℝ} :
    ‖x‖ < r ↔ ∃ m : M, mk m = x ∧ ‖m‖ < r := by
  rw [isGLB_lt_iff (isGLB_quotient_norm _), exists_mem_image]
  rfl

/-- For any `x : SeparationQuotient M` and any `0 < ε`, there is `m : M` such that `mk m = x`
and `‖m‖ < ‖x‖ + ε`. -/
theorem norm_mk_lt (x : SeparationQuotient M) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : M, mk m = x ∧ ‖m‖ < ‖x‖ + ε :=
  norm_lt_iff.1 <| lt_add_of_pos_right _ hε

/-- For any `m : M` and any `0 < ε`, there is `s ∈ nullSpace` such that `‖m + s‖ < ‖mk m‖ + ε`. -/
theorem norm_mk_lt' (m : M) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ nullSpace, ‖m + s‖ < ‖mk m‖ + ε := by
  obtain ⟨n : M, hn : mk n = mk m, hn' : ‖n‖ < ‖mk m‖ + ε⟩ :=
    norm_mk_lt (mk m) hε
  erw [eq_comm, SeparationQuotient.mk_eq_mk, inseparable_iff_norm_zero, ← norm_neg] at hn
  use -(m - n), hn
  simp only [neg_sub, add_sub_cancel]
  exact hn'

/-- The quotient norm satisfies the triangle inequality. -/
theorem quotient_norm_add_le (x y : SeparationQuotient M) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := by
  rcases And.intro (SeparationQuotient.surjective_mk x) (SeparationQuotient.surjective_mk y) with
    ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  simp only [← SeparationQuotient.mk_add, quotient_norm_mk_eq]
  exact norm_add_le x y

/-- The quotient norm of `0` is `0`. -/
theorem norm_mk_zero : ‖(0 : SeparationQuotient M)‖ = 0 := by
  erw [quotient_norm_eq_zero_iff]
  exact nullSpace.zero_mem

/-- If `(m : M)` has norm equal to `0` in `SeparationQuotient M`, then `m ∈ nullSpace`. -/
theorem norm_mk_eq_zero (m : M) (h : ‖mk m‖ = 0) : m ∈ nullSpace := by
  rwa [quotient_norm_eq_zero_iff] at h

/-- If for `(m : M)` it holds that `mk m = 0`, then `m  ∈ nullSpace`. -/
theorem mk_eq_zero_iff (m : M) : mk m = 0 ↔ m ∈ nullSpace := by
  constructor
  · intro h
    have : ‖mk m‖ = 0 := by
      rw [h]
      exact norm_mk_zero
    rw [quotient_norm_mk_eq] at this
    exact this
  · intro h
    have : mk (0 : M) = 0 := by exact rfl
    rw [← this, SeparationQuotient.mk_eq_mk, inseparable_iff_norm_zero]
    simp only [sub_zero]
    exact h

theorem quotient_nhd_basis :
    (𝓝 (0 : SeparationQuotient M)).HasBasis (fun ε ↦ 0 < ε) fun ε ↦ { x | ‖x‖ < ε } := by
  have : ∀ ε : ℝ, mk '' ball (0 : M) ε = { x : SeparationQuotient M | ‖x‖ < ε } := by
    intro ε
    ext x
    rw [ball_zero_eq, mem_setOf_eq, norm_lt_iff, mem_image]
    exact exists_congr fun _ ↦ and_comm
  rw [← SeparationQuotient.mk_zero, nhds_eq, ← funext this]
  exact .map _ Metric.nhds_basis_ball

/-- The seminormed group structure on the quotient by an additive subgroup. -/
noncomputable instance normedAddCommGroupQuotient :
    NormedAddCommGroup (SeparationQuotient M) where
  dist x y := ‖x - y‖
  dist_self x := by simp only [norm_mk_zero, sub_self]
  dist_comm := quotient_norm_sub_rev
  dist_triangle x y z := by
    refine le_trans ?_ (quotient_norm_add_le _ _)
    exact (congr_arg norm (sub_add_sub_cancel _ _ _).symm).le
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
  toUniformSpace := TopologicalAddGroup.toUniformSpace (SeparationQuotient M)
  uniformity_dist := by
    rw [uniformity_eq_comap_nhds_zero', ((quotient_nhd_basis).comap _).eq_biInf]
    simp only [dist, quotient_norm_sub_rev (Prod.fst _), preimage_setOf_eq]
  eq_of_dist_eq_zero {x} {y} hxy := by
    simp only at hxy
    obtain ⟨x', hx'⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨y', hy'⟩ := SeparationQuotient.surjective_mk y
    rw [← hx', ← hy', SeparationQuotient.mk_eq_mk, inseparable_iff_norm_zero]
    rw [← hx', ← hy', ← mk_sub, quotient_norm_eq_zero_iff] at hxy
    exact hxy

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example : (instTopologicalSpaceQuotient : TopologicalSpace <| SeparationQuotient M) =
      normedAddCommGroupQuotient.toUniformSpace.toTopologicalSpace :=
  rfl

end SeparationQuotient

namespace SeparationQuotientAddGroup

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by the null space. -/
noncomputable def normedMk : NormedAddGroupHom M (SeparationQuotient M) :=
  { mkAddGroupHom with
    bound' := ⟨1, fun m => by simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      mkAddGroupHom_apply, quotient_norm_mk_eq, one_mul, le_refl]⟩}

/-- `mkAddGroupHom` agrees with `QuotientAddGroup.mk`. -/
@[simp]
theorem normedMk.apply (m : M) : normedMk m = mk m := rfl

/-- `normedMk` is surjective. -/
theorem surjective_normedMk : Function.Surjective (@normedMk M _) :=
  surjective_quot_mk _

/-- The kernel of `S.normedMk` is `S`. -/
theorem ker_normedMk : (@normedMk M _).ker = nullSpace := by
  rw[ker, normedMk]
  simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mk_toAddMonoidHom]
  ext x
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, mkAddGroupHom_apply]
  exact mk_eq_zero_iff x

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normedMk_le : ‖(@normedMk M _)‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp [quotient_norm_mk_eq]

lemma eq_of_inseparable (f : NormedAddGroupHom M N) (hf : ∀ x ∈ nullSpace, f x = 0) :
    ∀ x y, Inseparable x y → f x = f y := by
  intro x y h
  rw [inseparable_iff_norm_zero] at h
  apply eq_of_sub_eq_zero
  rw [← map_sub f x y]
  exact hf (x - y) h

/-- The lift of a group hom to the separation quotient as a group hom. -/
noncomputable def liftNormedAddGroupHom (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ nullSpace, f x = 0) : NormedAddGroupHom (SeparationQuotient M) N where
  toFun := SeparationQuotient.lift f <| eq_of_inseparable f hf
  map_add' {x y} := by
    obtain ⟨x', hx'⟩ := surjective_mk x
    obtain ⟨y', hy'⟩ := surjective_mk y
    rw [← hx', ← hy', SeparationQuotient.lift_mk (eq_of_inseparable f hf) x',
      SeparationQuotient.lift_mk (eq_of_inseparable f hf) y', ← mk_add, lift_mk]
    exact map_add f x' y'
  bound' := by
    use ‖f‖
    intro v
    obtain ⟨v', hv'⟩ := surjective_mk v
    rw [← hv', SeparationQuotient.lift_mk (eq_of_inseparable f hf) v']
    simp only [quotient_norm_mk_eq]
    exact le_opNorm f v'

theorem CLM_lift_apply (f : NormedAddGroupHom M N) (hf : ∀ x ∈ nullSpace, f x = 0) (x : M) :
    liftNormedAddGroupHom f hf (mk x) = f x := rfl

theorem _root_.SeparationQuotient.norm_lift_apply_le (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ nullSpace, f x = 0) (x : SeparationQuotient M) :
        ‖lift f.toAddMonoidHom (eq_of_inseparable f hf) x‖ ≤ ‖f‖ * ‖x‖ := by
  cases (norm_nonneg f).eq_or_gt with
  | inl h =>
    rcases SeparationQuotient.surjective_mk x with ⟨x, rfl⟩
    simpa [h] using le_opNorm f x
  | inr h =>
    rw [← not_lt, ← _root_.lt_div_iff' h, norm_lt_iff]
    rintro ⟨x, rfl, hx⟩
    exact ((lt_div_iff' h).1 hx).not_le (le_opNorm f x)

/-- The operator norm of the projection is `1` if the null space is not dense. -/
theorem norm_normedMk (h : (@nullSpace M _ : Set M) ≠ univ) :
    ‖(@normedMk M _)‖ = 1 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simp only [normedMk.apply, one_mul]
    exact fun x => (le_of_eq <| quotient_norm_mk_eq x)
  · simp only [ge_iff_le, normedMk.apply]
    intro N hN hx
    simp_rw [quotient_norm_mk_eq] at hx
    rw [← nonempty_compl] at h
    obtain ⟨x, hxnn⟩ := h
    have : 0 < ‖x‖ := Ne.lt_of_le (Ne.symm hxnn) (norm_nonneg x)
    exact one_le_of_le_mul_right₀ this (hx x)

/-- The operator norm of the projection is `0` if the null space is dense. -/
theorem norm_trivial_separaationQuotient_mk (h : (@nullSpace M _ : Set M) = Set.univ) :
    ‖@normedMk M _‖ = 0 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ (le_refl 0)
  · intro x
    have : x ∈ nullSpace := by
      rw [← SetLike.mem_coe, h]
      exact trivial
    simp only [normedMk.apply, zero_mul, norm_le_zero_iff]
    exact (mk_eq_zero_iff x).mpr this
  · exact fun N => fun hN => fun _ => hN

end SeparationQuotientAddGroup

namespace SeparationQuotientAddGroup

/-- `IsQuotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of `M`
by the kernel of `f`. -/
structure IsQuotient (f : NormedAddGroupHom M N) : Prop where
  protected surjective : Function.Surjective f
  protected norm : ∀ x, ‖f x‖ = sInf ((fun m => ‖x + m‖) '' f.ker)

/-- Given `f : NormedAddGroupHom M N` such that `f s = 0` for all `s ∈ nullSpace`,
we define the induced morphism `NormedAddGroupHom (SeparationQuotient M) N`. -/
noncomputable def lift {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSpace, f s = 0) : NormedAddGroupHom (SeparationQuotient M) N :=
  { liftAddMonoidHom f (eq_of_inseparable f hf) with
    bound' := by
      use ‖f‖
      intro v
      obtain ⟨v', hv'⟩ := surjective_mk v
      rw [← hv']
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, AddCommMonoidHom_lift_apply,
        AddMonoidHom.coe_coe]
      rw [quotient_norm_mk_eq]
      exact NormedAddGroupHom.le_opNorm f v'}

theorem lift_mk {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSpace, f s = 0) (m : M) : lift f hf (normedMk m) = f m := rfl

theorem lift_unique {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSpace, f s = 0) (g : NormedAddGroupHom (SeparationQuotient M) N)
    (h : g.comp normedMk = f) : g = lift f hf := by
  ext x
  rcases surjective_normedMk x with ⟨x, rfl⟩
  change g.comp normedMk x = _
  simp only [h]
  rfl

/-- `normedMk` satisfies `IsQuotient`. -/
theorem isQuotientSeparationQuotient : IsQuotient (@normedMk M _) := by
  constructor
  · exact surjective_normedMk
  · rw [ker_normedMk]
    exact fun x => norm_mk_eq_sInf x

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

theorem norm_lift_le {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSpace, f s = 0) : ‖lift f hf‖ ≤ ‖f‖ :=
  NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg f) (norm_lift_apply_le f hf)

-- Porting note (#11215): TODO: deprecate?
theorem lift_norm_le {N : Type*} [SeminormedAddCommGroup N](f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSpace, f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) : ‖lift f hf‖ ≤ c :=
  (norm_lift_le f hf).trans fb

theorem lift_normNoninc {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSpace, f s = 0) (fb : f.NormNoninc) : (lift f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ (1 : ℝ≥0) := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using NormedAddGroupHom.le_of_opNorm_le _
    (SeparationQuotientAddGroup.lift_norm_le f _ fb') _

end SeparationQuotientAddGroup

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

section Module

variable {R S : Type*} [Semiring R] [Module R M] [Semiring S] [Module S N]
  [ContinuousConstSMul R M]

-- do we need these?
-- instance Submodule.SeparationQuotient.normedAddCommGroup :
--     NormedAddCommGroup (SeparationQuotient M) :=
--   SeparationQuotient.normedAddCommGroupQuotient

-- instance Submodule.SeparationQuotient.completeSpace [CompleteSpace M] :
--     CompleteSpace (SeparationQuotient M) := SeparationQuotient.instCompleteSpace

/-- For any `x : SeparationQuotient M` and any `0 < ε`, there is `m : M` such that
`mk m = x` and `‖m‖ < ‖x‖ + ε`. -/
nonrec theorem Submodule.SeparationQuotient.norm_mk_lt (x : SeparationQuotient M) {ε : ℝ}
    (hε : 0 < ε) : ∃ m : M, SeparationQuotient.mk m = x ∧ ‖m‖ < ‖x‖ + ε :=
  norm_mk_lt x hε

theorem Submodule.SeparationQuotient.norm_mk_eq (m : M) :
    ‖(SeparationQuotient.mk m : SeparationQuotient M)‖ = ‖m‖ := quotient_norm_mk_eq m

instance Submodule.SeparationQuotient.instBoundedSMul (𝕜 : Type*)
    [SeminormedCommRing 𝕜] [Module 𝕜 M] [BoundedSMul 𝕜 M] : BoundedSMul 𝕜 (SeparationQuotient M) :=
  .of_norm_smul_le fun k x =>
    -- Porting note: this is `QuotientAddGroup.norm_lift_apply_le` for `f : M → M / S` given by
    -- `x ↦ mk (k • x)`; todo: add scalar multiplication as `NormedAddGroupHom`, use it here
    _root_.le_of_forall_pos_le_add fun ε hε => by
      have := (nhds_basis_ball.tendsto_iff nhds_basis_ball).mp
        ((@Real.uniformContinuous_const_mul ‖k‖).continuous.tendsto ‖x‖) ε hε
      simp only [mem_ball, exists_prop, dist, abs_sub_lt_iff] at this
      rcases this with ⟨δ, hδ, h⟩
      obtain ⟨a, rfl, ha⟩ := Submodule.SeparationQuotient.norm_mk_lt x hδ
      specialize h ‖a‖ ⟨by linarith, by linarith [Submodule.SeparationQuotient.norm_mk_eq a]⟩
      calc
        _ ≤ ‖k‖ * ‖a‖ := (le_of_eq <| quotient_norm_mk_eq (k • a)).trans (norm_smul_le k a)
        _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

instance Submodule.SeparationQuotient.normedSpace (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 M] :
    NormedSpace 𝕜 (SeparationQuotient M) where
  norm_smul_le := norm_smul_le

instance instModule : Module R (SeparationQuotient M) :=
  surjective_mk.module R mkAddMonoidHom mk_smul

variable (R M)

/-- `SeparationQuotient.mk` as a continuous linear map. -/
@[simps]
def mkCLM : M →L[R] SeparationQuotient M where
  toFun := mk
  map_add' := mk_add
  map_smul' := mk_smul

variable {R M}

/-- The lift as a continuous linear map of `f` with `f x = f y` for `Inseparable x y`. -/
noncomputable def liftCLM {σ : R →+* S} (f : M →SL[σ] N) (hf : ∀ x y, Inseparable x y → f x = f y) :
    (SeparationQuotient M) →SL[σ] N where
  toFun := SeparationQuotient.lift f hf
  map_add' {x y} := by
    obtain ⟨x', hx'⟩ := surjective_mk x
    obtain ⟨y', hy'⟩ := surjective_mk y
    rw [← hx', ← hy', SeparationQuotient.lift_mk hf x', SeparationQuotient.lift_mk hf y', ← mk_add,
      lift_mk]
    exact ContinuousLinearMap.map_add f x' y'
  map_smul' {r x} := by
    obtain ⟨x', hx'⟩ := surjective_mk x
    rw [← hx', ← mk_smul]
    simp only [lift_mk]
    exact ContinuousLinearMap.map_smulₛₗ f r x'

theorem CLM_lift_apply {σ : R →+* S} (f : M →SL[σ] N) (hf : ∀ x y, Inseparable x y → f x = f y)
    (x : M) : SeparationQuotient.liftCLM f hf (mk x) = f x := rfl

end Module

section Ideal

variable {R : Type*} [SeminormedCommRing R]

nonrec theorem Ideal.SeparationQuotient.norm_mk_lt (x : SeparationQuotient R) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : R, SeparationQuotient.mk r = x ∧ ‖r‖ < ‖x‖ + ε :=
  norm_mk_lt x hε

theorem Ideal.SeparationQuotient.norm_mk_le (r : R) : ‖mk r‖ = ‖r‖ :=
  quotient_norm_mk_eq r

instance Ideal.SeparationQuotient.normedCommRing : NormedCommRing (SeparationQuotient R) where
  dist x y := ‖x - y‖
  dist_self x := by simp only [norm_mk_zero, sub_self]
  dist_comm := quotient_norm_sub_rev
  dist_triangle x y z := by
    refine le_trans ?_ (quotient_norm_add_le _ _)
    exact (congr_arg norm (sub_add_sub_cancel _ _ _).symm).le
  edist_dist x y := by exact ENNReal.coe_nnreal_eq _
  eq_of_dist_eq_zero {x} {y} hxy := by
    simp only at hxy
    obtain ⟨x', hx'⟩ := SeparationQuotient.surjective_mk x
    obtain ⟨y', hy'⟩ := SeparationQuotient.surjective_mk y
    rw [← hx', ← hy', SeparationQuotient.mk_eq_mk, inseparable_iff_norm_zero]
    rw [← hx', ← hy', ← mk_sub, quotient_norm_eq_zero_iff] at hxy
    exact hxy
  dist_eq x y := rfl
  mul_comm := _root_.mul_comm
  norm_mul x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, mem_ball, and_imp, Prod.forall, exists_prop, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := SeparationQuotient.norm_mk_lt x h₁,
      SeparationQuotient.norm_mk_lt y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [le_of_eq <| quotient_norm_mk_eq a]⟩
      ⟨by linarith, by linarith [quotient_norm_mk_eq b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ := (le_of_eq <| quotient_norm_mk_eq (a * b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

variable (𝕜 : Type*) [NormedField 𝕜]

-- TODO Ideal.SeparationQuotient.algebra does not exist

-- instance Ideal.SeparationQuotient.normedAlgebra [NormedAlgebra 𝕜 R]
--     : NormedAlgebra 𝕜 (SeparationQuotient R) :=
--   { Submodule.SeparationQuotient.normedSpace 𝕜, Ideal.SeparationQuotient.algebra 𝕜 with }

end Ideal
