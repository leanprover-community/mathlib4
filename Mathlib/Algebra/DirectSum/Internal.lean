/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.DirectSum.Algebra

#align_import algebra.direct_sum.internal from "leanprover-community/mathlib"@"9936c3dfc04e5876f4368aeb2e60f8d8358d095a"

/-!
# Internally graded rings and algebras

This module provides `DirectSum.GSemiring` and `DirectSum.GCommSemiring` instances for a collection
of subobjects `A` when a `SetLike.GradedMonoid` instance is available:

* `SetLike.gnonUnitalNonAssocSemiring`
* `SetLike.gsemiring`
* `SetLike.gcommSemiring`

With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:

* `DirectSum.coeRingHom` (a `RingHom` version of `DirectSum.coeAddMonoidHom`)
* `DirectSum.coeAlgHom` (an `AlgHom` version of `DirectSum.coeLinearMap`)

Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : DirectSum.IsInternal A) [SetLike.GradedMonoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`DirectSum.IsInternal` for providing an explicit decomposition function.

When `CompleteLattice.Independent (Set.range A)` (a weaker condition than
`DirectSum.IsInternal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`DirectSum.toAddMonoid (fun i ↦ AddSubmonoid.inclusion <| le_iSup A i)`.

## Tags

internally graded ring
-/


open DirectSum

variable {ι : Type*} {σ S R : Type*}

instance AddCommMonoid.ofSubmonoidOnSemiring [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) : ∀ i, AddCommMonoid (A i) := fun i => by infer_instance
#align add_comm_monoid.of_submonoid_on_semiring AddCommMonoid.ofSubmonoidOnSemiring

instance AddCommGroup.ofSubgroupOnRing [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ) :
    ∀ i, AddCommGroup (A i) := fun i => by infer_instance
#align add_comm_group.of_subgroup_on_ring AddCommGroup.ofSubgroupOnRing

theorem SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedOne A] (s : S) : algebraMap S R s ∈ A 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (A 0).smul_mem s <| SetLike.one_mem_graded _
#align set_like.algebra_map_mem_graded SetLike.algebraMap_mem_graded

theorem SetLike.natCast_mem_graded [Zero ι] [AddMonoidWithOne R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedOne A] (n : ℕ) : (n : R) ∈ A 0 := by
  induction' n with _ n_ih
  · rw [Nat.cast_zero]
    exact zero_mem (A 0)
  · rw [Nat.cast_succ]
    exact add_mem n_ih (SetLike.one_mem_graded _)
#align set_like.nat_cast_mem_graded SetLike.natCast_mem_graded

@[deprecated (since := "2024-04-17")]
alias SetLike.nat_cast_mem_graded := SetLike.natCast_mem_graded

theorem SetLike.intCast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R]
    [AddSubgroupClass σ R] (A : ι → σ) [SetLike.GradedOne A] (z : ℤ) : (z : R) ∈ A 0 := by
  induction z
  · rw [Int.ofNat_eq_coe, Int.cast_natCast]
    exact SetLike.natCast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.natCast_mem_graded _ _)
#align set_like.int_cast_mem_graded SetLike.intCast_mem_graded

@[deprecated (since := "2024-04-17")]
alias SetLike.int_cast_mem_graded := SetLike.intCast_mem_graded

section DirectSum

variable [DecidableEq ι]

/-! #### From `AddSubmonoid`s and `AddSubgroup`s -/


namespace SetLike

/-- Build a `DirectSum.GNonUnitalNonAssocSemiring` instance for a collection of additive
submonoids. -/
instance gnonUnitalNonAssocSemiring [Add ι] [NonUnitalNonAssocSemiring R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedMul A] :
    DirectSum.GNonUnitalNonAssocSemiring fun i => A i :=
  { SetLike.gMul A with
    mul_zero := fun _ => Subtype.ext (mul_zero _)
    zero_mul := fun _ => Subtype.ext (zero_mul _)
    mul_add := fun _ _ _ => Subtype.ext (mul_add _ _ _)
    add_mul := fun _ _ _ => Subtype.ext (add_mul _ _ _) }
#align set_like.gnon_unital_non_assoc_semiring SetLike.gnonUnitalNonAssocSemiring

/-- Build a `DirectSum.GSemiring` instance for a collection of additive submonoids. -/
instance gsemiring [AddMonoid ι] [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GSemiring fun i => A i :=
  { SetLike.gMonoid A with
    mul_zero := fun _ => Subtype.ext (mul_zero _)
    zero_mul := fun _ => Subtype.ext (zero_mul _)
    mul_add := fun _ _ _ => Subtype.ext (mul_add _ _ _)
    add_mul := fun _ _ _ => Subtype.ext (add_mul _ _ _)
    natCast := fun n => ⟨n, SetLike.natCast_mem_graded _ _⟩
    natCast_zero := Subtype.ext Nat.cast_zero
    natCast_succ := fun n => Subtype.ext (Nat.cast_succ n) }
#align set_like.gsemiring SetLike.gsemiring

/-- Build a `DirectSum.GCommSemiring` instance for a collection of additive submonoids. -/
instance gcommSemiring [AddCommMonoid ι] [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) [SetLike.GradedMonoid A] : DirectSum.GCommSemiring fun i => A i :=
  { SetLike.gCommMonoid A, SetLike.gsemiring A with }
#align set_like.gcomm_semiring SetLike.gcommSemiring

/-- Build a `DirectSum.GRing` instance for a collection of additive subgroups. -/
instance gring [AddMonoid ι] [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GRing fun i => A i :=
  { SetLike.gsemiring A with
    intCast := fun z => ⟨z, SetLike.intCast_mem_graded _ _⟩
    intCast_ofNat := fun _n => Subtype.ext <| Int.cast_natCast _
    intCast_negSucc_ofNat := fun n => Subtype.ext <| Int.cast_negSucc n }
#align set_like.gring SetLike.gring

/-- Build a `DirectSum.GCommRing` instance for a collection of additive submonoids. -/
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
  DirectSum.toSemiring (fun i => AddSubmonoidClass.subtype (A i)) rfl fun _ _ => rfl
#align direct_sum.coe_ring_hom DirectSum.coeRingHom

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
@[simp]
theorem coeRingHom_of [AddMonoid ι] [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    (coeRingHom A : _ →+* R) (of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ _ _ _ _
#align direct_sum.coe_ring_hom_of DirectSum.coeRingHom_of

theorem coe_mul_apply [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) =
      ∑ ij ∈ (r.support ×ˢ r'.support).filter (fun ij : ι × ι => ij.1 + ij.2 = n),
        (r ij.1 * r' ij.2 : R) := by
  rw [mul_eq_sum_support_ghas_mul, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  simp_rw [coe_of_apply, apply_ite, ZeroMemClass.coe_zero, ← Finset.sum_filter, SetLike.coe_gMul]
#align direct_sum.coe_mul_apply DirectSum.coe_mul_apply

theorem coe_mul_apply_eq_dfinsupp_sum [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) = r.sum fun i ri => r'.sum fun j rj => if i + j = n then (ri * rj : R)
      else 0 := by
  rw [mul_eq_dfinsupp_sum]
  iterate 2 rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finset_sum]; congr; ext
  dsimp only
  split_ifs with h
  · subst h
    rw [of_eq_same]
    rfl
  · rw [of_eq_of_ne _ _ _ _ h]
    rfl
#align direct_sum.coe_mul_apply_eq_dfinsupp_sum DirectSum.coe_mul_apply_eq_dfinsupp_sum

theorem coe_of_mul_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) {j n : ι} (H : ∀ x : ι, i + x = n ↔ x = j) :
    ((of (fun i => A i) i r * r') n : R) = r * r' j := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.not_mem_support_iff.mp h, ZeroMemClass.coe_zero, mul_zero]
#align direct_sum.coe_of_mul_apply_aux DirectSum.coe_of_mul_apply_aux

theorem coe_mul_of_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i) {i : ι}
    (r' : A i) {j n : ι} (H : ∀ x : ι, x + i = n ↔ x = j) :
    ((r * of (fun i => A i) i r') n : R) = r j * r' := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum, DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.not_mem_support_iff.mp h, ZeroMemClass.coe_zero, zero_mul]
#align direct_sum.coe_mul_of_apply_aux DirectSum.coe_mul_of_apply_aux

theorem coe_of_mul_apply_add [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) i r * r') (i + j) : R) = r * r' j :=
  coe_of_mul_apply_aux _ _ _ fun _x => ⟨fun h => add_left_cancel h, fun h => h ▸ rfl⟩
#align direct_sum.coe_of_mul_apply_add DirectSum.coe_of_mul_apply_add

theorem coe_mul_of_apply_add [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    {i : ι} (r' : A i) (j : ι) : ((r * of (fun i => A i) i r') (j + i) : R) = r j * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => ⟨fun h => add_right_cancel h, fun h => h ▸ rfl⟩
#align direct_sum.coe_mul_of_apply_add DirectSum.coe_mul_of_apply_add

end coe

section CanonicallyOrderedAddCommMonoid

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
variable [CanonicallyOrderedAddCommMonoid ι] [SetLike.GradedMonoid A]

theorem coe_of_mul_apply_of_not_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i ≤ n) :
    ((of (fun i => A i) i r * r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false _ _ fun x _ H => _, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_right i x).trans_eq H)
#align direct_sum.coe_of_mul_apply_of_not_le DirectSum.coe_of_mul_apply_of_not_le

theorem coe_mul_of_apply_of_not_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i ≤ n) :
    ((r * of (fun i => A i) i r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum, DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false _ _ fun x _ H => _, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_left i x).trans_eq H)
#align direct_sum.coe_mul_of_apply_of_not_le DirectSum.coe_mul_of_apply_of_not_le

variable [Sub ι] [OrderedSub ι] [ContravariantClass ι ι (· + ·) (· ≤ ·)]

/- The following two lemmas only require the same hypotheses as `eq_tsub_iff_add_eq_of_le`, but we
  state them for `CanonicallyOrderedAddCommMonoid` + the above three typeclasses for convenience. -/
theorem coe_mul_of_apply_of_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i ≤ n) :
    ((r * of (fun i => A i) i r') n : R) = r (n - i) * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => (eq_tsub_iff_add_eq_of_le h).symm
#align direct_sum.coe_mul_of_apply_of_le DirectSum.coe_mul_of_apply_of_le

theorem coe_of_mul_apply_of_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i ≤ n) :
    ((of (fun i => A i) i r * r') n : R) = r * r' (n - i) :=
  coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h, add_comm]
#align direct_sum.coe_of_mul_apply_of_le DirectSum.coe_of_mul_apply_of_le

theorem coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [Decidable (i ≤ n)] :
    ((r * of (fun i => A i) i r') n : R) = if i ≤ n then (r (n - i) : R) * r' else 0 := by
  split_ifs with h
  exacts [coe_mul_of_apply_of_le _ _ _ n h, coe_mul_of_apply_of_not_le _ _ _ n h]
#align direct_sum.coe_mul_of_apply DirectSum.coe_mul_of_apply

theorem coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [Decidable (i ≤ n)] :
    ((of (fun i => A i) i r * r') n : R) = if i ≤ n then (r * r' (n - i) : R) else 0 := by
  split_ifs with h
  exacts [coe_of_mul_apply_of_le _ _ _ n h, coe_of_mul_apply_of_not_le _ _ _ n h]
#align direct_sum.coe_of_mul_apply DirectSum.coe_of_mul_apply

end CanonicallyOrderedAddCommMonoid

end DirectSum

/-! #### From `Submodule`s -/


namespace Submodule

/-- Build a `DirectSum.GAlgebra` instance for a collection of `Submodule`s. -/
instance galgebra [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R] (A : ι → Submodule S R)
    [SetLike.GradedMonoid A] : DirectSum.GAlgebra S fun i => A i where
  toFun :=
    ((Algebra.linearMap S R).codRestrict (A 0) <| SetLike.algebraMap_mem_graded A).toAddMonoidHom
  map_one := Subtype.ext <| (algebraMap S R).map_one
  map_mul _x _y := Sigma.subtype_ext (add_zero 0).symm <| (algebraMap S R).map_mul _ _
  commutes := fun _r ⟨i, _xi⟩ =>
    Sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) <| Algebra.commutes _ _
  smul_def := fun _r ⟨i, _xi⟩ => Sigma.subtype_ext (zero_add i).symm <| Algebra.smul_def _ _
#align submodule.galgebra Submodule.galgebra

@[simp]
theorem setLike.coe_galgebra_toFun [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (s : S) :
    ↑(@DirectSum.GAlgebra.toFun _ S (fun i => A i) _ _ _ _ _ _ _ s) = (algebraMap S R s : R) :=
  rfl
#align submodule.set_like.coe_galgebra_to_fun Submodule.setLike.coe_galgebra_toFun

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_gradedMonoid [CommSemiring S] [Semiring R] [Algebra S R] (p : Submodule S R) :
    SetLike.GradedMonoid fun i : ℕ => p ^ i where
  one_mem := by
    rw [← one_le, pow_zero]
  mul_mem i j p q hp hq := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hp hq
#align submodule.nat_power_graded_monoid Submodule.nat_power_gradedMonoid

end Submodule

/-- The canonical algebra isomorphism between `⨁ i, A i` and `R`. -/
def DirectSum.coeAlgHom [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] : (⨁ i, A i) →ₐ[S] R :=
  DirectSum.toAlgebra S _ (fun i => (A i).subtype) rfl (fun _ _ => rfl)
#align direct_sum.coe_alg_hom DirectSum.coeAlgHom

/-- The supremum of submodules that form a graded monoid is a subalgebra, and equal to the range of
`DirectSum.coeAlgHom`. -/
theorem Submodule.iSup_eq_toSubmodule_range [AddMonoid ι] [CommSemiring S] [Semiring R]
    [Algebra S R] (A : ι → Submodule S R) [SetLike.GradedMonoid A] :
    ⨆ i, A i = Subalgebra.toSubmodule (DirectSum.coeAlgHom A).range :=
  (Submodule.iSup_eq_range_dfinsupp_lsum A).trans <| SetLike.coe_injective rfl
#align submodule.supr_eq_to_submodule_range Submodule.iSup_eq_toSubmodule_range

@[simp]
theorem DirectSum.coeAlgHom_of [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    DirectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ (by rfl) (fun _ _ => (by rfl)) _ _
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
