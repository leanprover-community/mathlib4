/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang

! This file was ported from Lean 3 source module algebra.direct_sum.internal
! leanprover-community/mathlib commit 9936c3dfc04e5876f4368aeb2e60f8d8358d095a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Operations
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.DirectSum.Algebra

/-!
# Internally graded rings and algebras

This module provides `gsemiring` and `gcomm_semiring` instances for a collection of subobjects `A`
when a `set_like.graded_monoid` instance is available:

* `set_like.gnon_unital_non_assoc_semiring`
* `set_like.gsemiring`
* `set_like.gcomm_semiring`

With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:

* `direct_sum.coe_ring_hom` (a `ring_hom` version of `direct_sum.coe_add_monoid_hom`)
* `direct_sum.coe_alg_hom` (an `alg_hom` version of `direct_sum.submodule_coe`)

Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : direct_sum.is_internal A) [set_like.graded_monoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`direct_sum.is_internal` for providing an explicit decomposition function.

When `complete_lattice.independent (set.range A)` (a weaker condition than
`direct_sum.is_internal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

internally graded ring
-/


open DirectSum BigOperators

variable {ι : Type _} {σ S R : Type _}

instance AddCommMonoid.ofSubmonoidOnSemiring [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) : ∀ i, AddCommMonoid (A i) := fun i => by infer_instance
#align add_comm_monoid.of_submonoid_on_semiring AddCommMonoid.ofSubmonoidOnSemiring

instance AddCommGroup.ofSubgroupOnRing [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ) :
    ∀ i, AddCommGroup (A i) := fun i => by infer_instance
#align add_comm_group.of_subgroup_on_ring AddCommGroup.ofSubgroupOnRing

theorem SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedOne A] (s : S) : algebraMap S R s ∈ A 0 :=
  by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (A 0).smul_mem s <| SetLike.one_mem_graded _
#align set_like.algebra_map_mem_graded SetLike.algebraMap_mem_graded

theorem SetLike.nat_cast_mem_graded [Zero ι] [AddMonoidWithOne R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedOne A] (n : ℕ) : (n : R) ∈ A 0 :=
  by
  induction n
  · rw [Nat.cast_zero]
    exact zero_mem (A 0)
  · rw [Nat.cast_succ]
    exact add_mem n_ih (SetLike.one_mem_graded _)
#align set_like.nat_cast_mem_graded SetLike.nat_cast_mem_graded

theorem SetLike.int_cast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R]
    [AddSubgroupClass σ R] (A : ι → σ) [SetLike.GradedOne A] (z : ℤ) : (z : R) ∈ A 0 :=
  by
  induction z
  · rw [Int.cast_ofNat]
    exact SetLike.nat_cast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.nat_cast_mem_graded _ _)
#align set_like.int_cast_mem_graded SetLike.int_cast_mem_graded

section DirectSum

variable [DecidableEq ι]

/-! #### From `add_submonoid`s and `add_subgroup`s -/


namespace SetLike

/-- Build a `gnon_unital_non_assoc_semiring` instance for a collection of additive submonoids. -/
instance gnonUnitalNonAssocSemiring [Add ι] [NonUnitalNonAssocSemiring R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedMul A] :
    DirectSum.GNonUnitalNonAssocSemiring fun i => A i :=
  {
    SetLike.gMul
      A with
    mul_zero := fun i j _ => Subtype.ext (MulZeroClass.mul_zero _)
    zero_mul := fun i j _ => Subtype.ext (MulZeroClass.zero_mul _)
    mul_add := fun i j _ _ _ => Subtype.ext (mul_add _ _ _)
    add_mul := fun i j _ _ _ => Subtype.ext (add_mul _ _ _) }
#align set_like.gnon_unital_non_assoc_semiring SetLike.gnonUnitalNonAssocSemiring

/-- Build a `gsemiring` instance for a collection of additive submonoids. -/
instance gsemiring [AddMonoid ι] [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GSemiring fun i => A i :=
  {
    SetLike.gMonoid
      A with
    mul_zero := fun i j _ => Subtype.ext (MulZeroClass.mul_zero _)
    zero_mul := fun i j _ => Subtype.ext (MulZeroClass.zero_mul _)
    mul_add := fun i j _ _ _ => Subtype.ext (mul_add _ _ _)
    add_mul := fun i j _ _ _ => Subtype.ext (add_mul _ _ _)
    natCast := fun n => ⟨n, SetLike.nat_cast_mem_graded _ _⟩
    natCast_zero := Subtype.ext Nat.cast_zero
    natCast_succ := fun n => Subtype.ext (Nat.cast_succ n) }
#align set_like.gsemiring SetLike.gsemiring

/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcommSemiring [AddCommMonoid ι] [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) [SetLike.GradedMonoid A] : DirectSum.GCommSemiring fun i => A i :=
  { SetLike.gCommMonoid A, SetLike.gsemiring A with }
#align set_like.gcomm_semiring SetLike.gcommSemiring

/-- Build a `gring` instance for a collection of additive subgroups. -/
instance gring [AddMonoid ι] [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GRing fun i => A i :=
  {
    SetLike.gsemiring
      A with
    intCast := fun z => ⟨z, SetLike.int_cast_mem_graded _ _⟩
    intCast_ofNat := fun n => Subtype.ext <| Int.cast_ofNat _
    intCast_negSucc := fun n => Subtype.ext <| Int.cast_negSucc n }
#align set_like.gring SetLike.gring

/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcommRing [AddCommMonoid ι] [CommRing R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GCommRing fun i => A i :=
  { SetLike.gCommMonoid A, SetLike.gring A with }
#align set_like.gcomm_ring SetLike.gcommRing

end SetLike

namespace DirectSum

section coe

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
def coeRingHom [AddMonoid ι] [SetLike.GradedMonoid A] : (⨁ i, A i) →+* R :=
  DirectSum.toSemiring (fun i => AddSubmonoidClass.Subtype (A i)) rfl fun _ _ _ _ => rfl
#align direct_sum.coe_ring_hom DirectSum.coeRingHom

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
@[simp]
theorem coeRingHom_of [AddMonoid ι] [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    (coeRingHom A : _ →+* R) (of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ _ _ _ _
#align direct_sum.coe_ring_hom_of DirectSum.coeRingHom_of

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem coe_mul_apply [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) =
      ∑ ij in (r.support ×ˢ r'.support).filterₓ fun ij : ι × ι => ij.1 + ij.2 = n,
        r ij.1 * r' ij.2 :=
  by
  rw [mul_eq_sum_support_ghas_mul, Dfinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  simp_rw [coe_of_apply, ← Finset.sum_filter, SetLike.coe_gMul]
#align direct_sum.coe_mul_apply DirectSum.coe_mul_apply

theorem coe_mul_apply_eq_dfinsupp_sum [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) = r.Sum fun i ri => r'.Sum fun j rj => if i + j = n then ri * rj else 0 :=
  by
  simp only [mul_eq_dfinsupp_sum, Dfinsupp.sum_apply]
  iterate 2 rw [Dfinsupp.sum, AddSubmonoidClass.coe_finset_sum]; congr ; ext
  dsimp only; split_ifs
  · subst h
    rw [of_eq_same]
    rfl
  · rw [of_eq_of_ne _ _ _ _ h]
    rfl
#align direct_sum.coe_mul_apply_eq_dfinsupp_sum DirectSum.coe_mul_apply_eq_dfinsupp_sum

theorem coe_of_mul_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) {j n : ι} (H : ∀ x : ι, i + x = n ↔ x = j) :
    ((of _ i r * r') n : R) = r * r' j := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum]
    apply (Dfinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, MulZeroClass.zero_mul, if_t_t]
      exact Dfinsupp.sum_zero
    simp_rw [Dfinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs
    rfl
    rw [dfinsupp.not_mem_support_iff.mp h, ZeroMemClass.coe_zero, MulZeroClass.mul_zero]
#align direct_sum.coe_of_mul_apply_aux DirectSum.coe_of_mul_apply_aux

theorem coe_mul_of_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i) {i : ι}
    (r' : A i) {j n : ι} (H : ∀ x : ι, x + i = n ↔ x = j) : ((r * of _ i r') n : R) = r j * r' := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum, Dfinsupp.sum_comm]
    apply (Dfinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, MulZeroClass.mul_zero, if_t_t]
      exact Dfinsupp.sum_zero
    simp_rw [Dfinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs
    rfl
    rw [dfinsupp.not_mem_support_iff.mp h, ZeroMemClass.coe_zero, MulZeroClass.zero_mul]
#align direct_sum.coe_mul_of_apply_aux DirectSum.coe_mul_of_apply_aux

theorem coe_of_mul_apply_add [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) (j : ι) : ((of _ i r * r') (i + j) : R) = r * r' j :=
  coe_of_mul_apply_aux _ _ _ fun x => ⟨fun h => add_left_cancel h, fun h => h ▸ rfl⟩
#align direct_sum.coe_of_mul_apply_add DirectSum.coe_of_mul_apply_add

theorem coe_mul_of_apply_add [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    {i : ι} (r' : A i) (j : ι) : ((r * of _ i r') (j + i) : R) = r j * r' :=
  coe_mul_of_apply_aux _ _ _ fun x => ⟨fun h => add_right_cancel h, fun h => h ▸ rfl⟩
#align direct_sum.coe_mul_of_apply_add DirectSum.coe_mul_of_apply_add

end coe

section CanonicallyOrderedAddMonoid

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

variable [CanonicallyOrderedAddMonoid ι] [SetLike.GradedMonoid A]

theorem coe_of_mul_apply_of_not_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i ≤ n) :
    ((of _ i r * r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum]
    apply (Dfinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, MulZeroClass.zero_mul, if_t_t]
      exact Dfinsupp.sum_zero
    · rw [Dfinsupp.sum, Finset.sum_ite_of_false _ _ fun x _ H => _, Finset.sum_const_zero]
      exact h ((self_le_add_right i x).trans_eq H)
#align direct_sum.coe_of_mul_apply_of_not_le DirectSum.coe_of_mul_apply_of_not_le

theorem coe_mul_of_apply_of_not_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i ≤ n) :
    ((r * of _ i r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum, Dfinsupp.sum_comm]
    apply (Dfinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, MulZeroClass.mul_zero, if_t_t]
      exact Dfinsupp.sum_zero
    · rw [Dfinsupp.sum, Finset.sum_ite_of_false _ _ fun x _ H => _, Finset.sum_const_zero]
      exact h ((self_le_add_left i x).trans_eq H)
#align direct_sum.coe_mul_of_apply_of_not_le DirectSum.coe_mul_of_apply_of_not_le

variable [Sub ι] [OrderedSub ι] [ContravariantClass ι ι (· + ·) (· ≤ ·)]

/- The following two lemmas only require the same hypotheses as `eq_tsub_iff_add_eq_of_le`, but we
  state them for `canonically_ordered_add_monoid` + the above three typeclasses for convenience. -/
theorem coe_mul_of_apply_of_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i ≤ n) :
    ((r * of _ i r') n : R) = r (n - i) * r' :=
  coe_mul_of_apply_aux _ _ _ fun x => (eq_tsub_iff_add_eq_of_le h).symm
#align direct_sum.coe_mul_of_apply_of_le DirectSum.coe_mul_of_apply_of_le

theorem coe_of_mul_apply_of_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i ≤ n) :
    ((of _ i r * r') n : R) = r * r' (n - i) :=
  coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h, add_comm]
#align direct_sum.coe_of_mul_apply_of_le DirectSum.coe_of_mul_apply_of_le

theorem coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [Decidable (i ≤ n)] :
    ((r * of _ i r') n : R) = if i ≤ n then r (n - i) * r' else 0 :=
  by
  split_ifs
  exacts[coe_mul_of_apply_of_le _ _ _ n h, coe_mul_of_apply_of_not_le _ _ _ n h]
#align direct_sum.coe_mul_of_apply DirectSum.coe_mul_of_apply

theorem coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [Decidable (i ≤ n)] :
    ((of _ i r * r') n : R) = if i ≤ n then r * r' (n - i) else 0 :=
  by
  split_ifs
  exacts[coe_of_mul_apply_of_le _ _ _ n h, coe_of_mul_apply_of_not_le _ _ _ n h]
#align direct_sum.coe_of_mul_apply DirectSum.coe_of_mul_apply

end CanonicallyOrderedAddMonoid

end DirectSum

/-! #### From `submodule`s -/


namespace Submodule

/-- Build a `galgebra` instance for a collection of `submodule`s. -/
instance galgebra [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R] (A : ι → Submodule S R)
    [SetLike.GradedMonoid A] : DirectSum.GAlgebra S fun i => A i
    where
  toFun :=
    ((Algebra.linearMap S R).codRestrict (A 0) <| SetLike.algebraMap_mem_graded A).toAddMonoidHom
  map_one := Subtype.ext <| (algebraMap S R).map_one
  map_mul x y := Sigma.subtype_ext (add_zero 0).symm <| (algebraMap S R).map_mul _ _
  commutes := fun r ⟨i, xi⟩ =>
    Sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) <| Algebra.commutes _ _
  smul_def := fun r ⟨i, xi⟩ => Sigma.subtype_ext (zero_add i).symm <| Algebra.smul_def _ _
#align submodule.galgebra Submodule.galgebra

@[simp]
theorem setLike.coe_galgebra_toFun [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (s : S) :
    ↑(@DirectSum.GAlgebra.toFun _ S (fun i => A i) _ _ _ _ _ _ _ s) = (algebraMap S R s : R) :=
  rfl
#align submodule.set_like.coe_galgebra_to_fun Submodule.setLike.coe_galgebra_toFun

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_gradedMonoid [CommSemiring S] [Semiring R] [Algebra S R] (p : Submodule S R) :
    SetLike.GradedMonoid fun i : ℕ => p ^ i
    where
  one_mem := by
    rw [← one_le, pow_zero]
    exact le_rfl
  mul_mem i j p q hp hq := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hp hq
#align submodule.nat_power_graded_monoid Submodule.nat_power_gradedMonoid

end Submodule

/-- The canonical algebra isomorphism between `⨁ i, A i` and `R`. -/
def DirectSum.coeAlgHom [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] : (⨁ i, A i) →ₐ[S] R :=
  DirectSum.toAlgebra S _ (fun i => (A i).Subtype) rfl (fun _ _ _ _ => rfl) fun _ => rfl
#align direct_sum.coe_alg_hom DirectSum.coeAlgHom

/-- The supremum of submodules that form a graded monoid is a subalgebra, and equal to the range of
`direct_sum.coe_alg_hom`. -/
theorem Submodule.iSup_eq_toSubmodule_range [AddMonoid ι] [CommSemiring S] [Semiring R]
    [Algebra S R] (A : ι → Submodule S R) [SetLike.GradedMonoid A] :
    (⨆ i, A i) = (DirectSum.coeAlgHom A).range.toSubmodule :=
  (Submodule.iSup_eq_range_dfinsupp_lsum A).trans <| SetLike.coe_injective rfl
#align submodule.supr_eq_to_submodule_range Submodule.iSup_eq_toSubmodule_range

@[simp]
theorem DirectSum.coeAlgHom_of [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    DirectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ rfl (fun _ _ _ _ => rfl) _ _
#align direct_sum.coe_alg_hom_of DirectSum.coeAlgHom_of

end DirectSum

section HomogeneousElement

theorem SetLike.homogeneous_zero_submodule [Zero ι] [Semiring S] [AddCommMonoid R] [Module S R]
    (A : ι → Submodule S R) : SetLike.Homogeneous A (0 : R) :=
  ⟨0, Submodule.zero_mem _⟩
#align set_like.is_homogeneous_zero_submodule SetLike.homogeneous_zero_submodule

theorem SetLike.Homogeneous.smul [CommSemiring S] [Semiring R] [Algebra S R] {A : ι → Submodule S R}
    {s : S} {r : R} (hr : SetLike.Homogeneous A r) : SetLike.Homogeneous A (s • r) :=
  let ⟨i, hi⟩ := hr
  ⟨i, Submodule.smul_mem _ _ hi⟩
#align set_like.is_homogeneous.smul SetLike.Homogeneous.smul

end HomogeneousElement

