/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Hom

-- TODO modify doc, check if instances are really needed, golf
-- IsQuotient should be here?
-- should `M` be implicit or explicit?
-- do we need the definition `nullSubgroup`?
-- we have `‖x‖ = ‖mk x‖`. some lemmas simplify. should we?


/-!
# Quotients of seminormed groups by the null space

For any `SeminormedAddCommGroup M`, we provide a `NormedAddCommGroup`, the group quotient
`SeparationQuotient M`, the quotient by the null subgroup.
On the separation quotient we define the quotient norm and the projection is a normed group
homomorphism which is norm non-increasing (better, it has operator norm exactly one unless the
null subgroup is equal to `M`). The corresponding universal property is that every normed group hom
defined on `M` which vanishes on the null space descends to a normed group hom defined on
`SeparationQuotient M`.

This file also introduces a predicate `IsQuotient` characterizing normed group homs that
are isomorphic to the canonical projection onto a normed group quotient.

In addition, this file also provides normed structures for quotients of modules by the null
submodules, and of (commutative) rings by null ideals. The `NormedAddCommGroup` instance described
above is transferred directly, but we also define instances of `NormedSpace`, `NormedCommRing` and
`NormedAlgebra` under appropriate type class assumptions on the original space. Moreover, while
`QuotientAddGroup.completeSpace` works out-of-the-box for quotients of `NormedAddCommGroup`s by
the null subgroup, we need to transfer this instance in `Submodule.Quotient.completeSpace` so that
it applies to these other quotients.

## Main definitions


We use `M` and `N` to denote seminormed groups.
All the following definitions are in the `NullSubgroup` namespace. Hence we can access
`NullSubgroup.normedMk` as `normedMk`.

* `normedAddCommGroupQuotient` : The normed group structure on the quotient by the null subgroup.
    This is an instance so there is no need to explicitly use it.

* `normedMk` : the normed group hom from `M` to `SeparationQuotient M`.

* `lift f hf`: implements the universal property of `SeparationQuotient M`. Here
    `(f : NormedAddGroupHom M N)`, `(hf : ∀ s ∈ nullSubgroup M, f s = 0)` and
    `lift f hf : NormedAddGroupHom (SeparationQuotient M) N`.

* `IsQuotient`: given `f : NormedAddGroupHom M N`, `IsQuotient f` means `N` is isomorphic
    to a quotient of `M` by the null subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

* `norm_normedMk` : the operator norm of the projection is `1` if the subspace is not dense.

* `IsQuotient.norm_lift`: Provided `f : normed_hom M N` satisfies `IsQuotient f`, for every
     `n : N` and positive `ε`, there exists `m` such that `f m = n ∧ ‖m‖ < ‖n‖ + ε`.


## Implementation details

For any `SeminormedAddCommGroup M`, we define a norm on `SeparationQuotient M` by
`‖x‖ = sInf (norm '' {m | mk' S m = x})`. This formula is really an implementation detail, it
shouldn't be needed outside of this file setting up the theory.

Since `SeparationQuotient M` is automatically a topological space (as any quotient of a topological
space), one needs to be careful while defining the `normedAddCommGroup` instance to avoid having two
different topologies on this quotient. This is not purely a technological issue.
Mathematically there is something to prove. The main point is proved in the auxiliary lemma
`quotient_nhd_basis` that has no use beyond this verification and states that zero in the quotient
admits as basis of neighborhoods in the quotient topology the sets `{x | ‖x‖ < ε}` for positive `ε`.

Once this mathematical point is settled, we have two topologies that are propositionally equal. This
is not good enough for the type class system. As usual we ensure *definitional* equality
using forgetful inheritance, see Note [forgetful inheritance]. A (semi)-normed group structure
includes a uniform space structure which includes a topological space structure, together
with propositional fields asserting compatibility conditions.
The usual way to define a `NormedAddCommGroup` is to let Lean build a uniform space structure
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

namespace SeparationQuotientAddGroup

/-- The null subgroup with respect to the norm. -/
def nullSubgroup : AddSubgroup M where
  carrier := {x : M | ‖x‖ = 0}
  add_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_add_le x y).trans_eq ?_
    rw [hx, hy, add_zero]
  zero_mem' := norm_zero
  neg_mem' {x} (hx : ‖x‖ = 0) := by
    simp only [mem_setOf_eq, norm_neg]
    exact hx

lemma inseparable_iff_norm_zero (x y : M) : Inseparable x y ↔ ‖x - y‖ = 0 := by
  rw [Metric.inseparable_iff, dist_eq_norm]

lemma isClosed_nullSubgroup : IsClosed (@nullSubgroup M _ : Set M) := by
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

instance : Nonempty (@nullSubgroup M _) := ⟨0⟩

variable (x : SeparationQuotient M)

variable (z : M)

/-- The norm of the image of `m : M` in the quotient by the null space is zero if and only if `m`
belongs to the null space. -/
theorem quotient_norm_eq_zero_iff (m : M) :
    ‖mk m‖ = 0 ↔ m ∈ nullSubgroup := by
  rw [norm_mk]
  exact Eq.to_iff rfl

/-- If for `(m : M)` it holds that `mk m = 0`, then `m  ∈ nullSubgroup`. -/
theorem mk_eq_zero_iff (m : M) : mk m = 0 ↔ m ∈ nullSubgroup := by
  rw [← quotient_norm_eq_zero_iff]
  exact Iff.symm norm_eq_zero

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by the null space. -/
noncomputable def normedMk : NormedAddGroupHom M (SeparationQuotient M) :=
  { mkAddGroupHom with
    bound' := ⟨1, fun m => by simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe,
      mkAddGroupHom_apply, norm_mk, one_mul, le_refl]⟩}

/-- `mkAddGroupHom` agrees with `QuotientAddGroup.mk`. -/
@[simp]
theorem normedMk.apply (m : M) : normedMk m = mk m := rfl

/-- `normedMk` is surjective. -/
theorem surjective_normedMk : Function.Surjective (@normedMk M _) :=
  surjective_quot_mk _

/-- The kernel of `normedMk` is `nullSubgroup`. -/
theorem ker_normedMk : (@normedMk M _).ker = nullSubgroup := by
  rw[ker, normedMk]
  simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, mk_toAddMonoidHom]
  ext x
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, mkAddGroupHom_apply]
  exact mk_eq_zero_iff x

/-- The operator norm of the projection is at most `1`. -/
theorem norm_normedMk_le : ‖(@normedMk M _)‖ ≤ 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp only [normedMk.apply, norm_mk,
    one_mul, le_refl]

lemma eq_of_inseparable (f : NormedAddGroupHom M N) (hf : ∀ x ∈ nullSubgroup, f x = 0) :
    ∀ x y, Inseparable x y → f x = f y := by
  intro x y h
  rw [inseparable_iff_norm_zero] at h
  apply eq_of_sub_eq_zero
  rw [← map_sub f x y]
  exact hf (x - y) h

/-- The lift of a group hom to the separation quotient as a group hom. -/
noncomputable def liftNormedAddGroupHom (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ nullSubgroup, f x = 0) : NormedAddGroupHom (SeparationQuotient M) N where
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
    exact le_opNorm f v'

theorem liftNormedAddGroupHom_apply (f : NormedAddGroupHom M N) (hf : ∀ x ∈ nullSubgroup, f x = 0)
    (x : M) : liftNormedAddGroupHom f hf (mk x) = f x := rfl

theorem norm_lift_apply_le (f : NormedAddGroupHom M N)
    (hf : ∀ x ∈ nullSubgroup, f x = 0) (x : SeparationQuotient M) :
        ‖lift f.toAddMonoidHom (eq_of_inseparable f hf) x‖ ≤ ‖f‖ * ‖x‖ := by
  cases (norm_nonneg f).eq_or_gt with
  | inl h =>
    rcases SeparationQuotient.surjective_mk x with ⟨x, rfl⟩
    simpa [h] using le_opNorm f x
  | inr h =>
    obtain ⟨x', hx'⟩ := surjective_mk x
    rw [← hx']
    simp only [coe_toAddMonoidHom, lift_mk, norm_mk]
    exact le_opNorm f x'

/-- The operator norm of the projection is `1` if the null space is not dense. -/
theorem norm_normedMk (h : (@nullSubgroup M _ : Set M) ≠ univ) :
    ‖(@normedMk M _)‖ = 1 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simp only [normedMk.apply, one_mul]
    exact fun x ↦ Preorder.le_refl ‖SeparationQuotient.mk x‖
  · simp only [ge_iff_le, normedMk.apply]
    intro N hN hx
    rw [← nonempty_compl] at h
    obtain ⟨x, hxnn⟩ := h
    have : 0 < ‖x‖ := Ne.lt_of_le (Ne.symm hxnn) (norm_nonneg x)
    exact one_le_of_le_mul_right₀ this (hx x)

/-- The operator norm of the projection is `0` if the null space is dense. -/
theorem norm_trivial_separaationQuotient_mk (h : (@nullSubgroup M _ : Set M) = Set.univ) :
    ‖@normedMk M _‖ = 0 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ (le_refl 0)
  · intro x
    have : x ∈ nullSubgroup := by
      rw [← SetLike.mem_coe, h]
      exact trivial
    simp only [normedMk.apply, zero_mul, norm_le_zero_iff]
    exact (mk_eq_zero_iff x).mpr this
  · exact fun N => fun hN => fun _ => hN

end SeparationQuotientAddGroup

namespace SeparationQuotientNormedAddGroupHom

open SeparationQuotientAddGroup

/-- Given `f : NormedAddGroupHom M N` such that `f s = 0` for all `s ∈ nullSubgroup`,
we define the induced morphism `NormedAddGroupHom (SeparationQuotient M) N`. -/
noncomputable def lift {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSubgroup, f s = 0) : NormedAddGroupHom (SeparationQuotient M) N :=
  { liftAddMonoidHom f (eq_of_inseparable f hf) with
    bound' := by
      use ‖f‖
      intro v
      obtain ⟨v', hv'⟩ := surjective_mk v
      rw [← hv']
      simp only [ZeroHom.toFun_eq_coe, AddMonoidHom.toZeroHom_coe, AddCommMonoidHom_lift_apply,
        AddMonoidHom.coe_coe]
      exact NormedAddGroupHom.le_opNorm f v'}

theorem lift_mk {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSubgroup, f s = 0) (m : M) : lift f hf (normedMk m) = f m := rfl

theorem lift_unique {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSubgroup, f s = 0) (g : NormedAddGroupHom (SeparationQuotient M) N)
    (h : g.comp normedMk = f) : g = lift f hf := by
  ext x
  rcases surjective_normedMk x with ⟨x, rfl⟩
  change g.comp normedMk x = _
  simp only [h]
  rfl

theorem norm_lift_le {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSubgroup, f s = 0) : ‖lift f hf‖ ≤ ‖f‖ :=
  NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg f) (norm_lift_apply_le f hf)

-- Porting note (#11215): TODO: deprecate?
theorem lift_norm_le {N : Type*} [SeminormedAddCommGroup N](f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSubgroup, f s = 0) {c : ℝ≥0} (fb : ‖f‖ ≤ c) : ‖lift f hf‖ ≤ c :=
  (norm_lift_le f hf).trans fb

theorem lift_normNoninc {N : Type*} [SeminormedAddCommGroup N] (f : NormedAddGroupHom M N)
    (hf : ∀ s ∈ nullSubgroup, f s = 0) (fb : f.NormNoninc) : (lift f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ ≤ (1 : ℝ≥0) := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  simpa using NormedAddGroupHom.le_of_opNorm_le _
    (lift_norm_le f _ fb') _

end SeparationQuotientNormedAddGroupHom

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

namespace SeparationQuotientModule

open SeparationQuotientAddGroup

variable {R S : Type*} [Semiring R] [Module R M] [Semiring S] [Module S N]
  [ContinuousConstSMul R M]

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

theorem liftCLM_apply {σ : R →+* S} (f : M →SL[σ] N) (hf : ∀ x y, Inseparable x y → f x = f y)
    (x : M) : SeparationQuotient.liftCLM f hf (mk x) = f x := rfl

end SeparationQuotientModule

end Module
