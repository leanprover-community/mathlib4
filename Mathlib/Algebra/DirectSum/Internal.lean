/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang, Fangming Li
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.DirectSum.Algebra

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

This file also provides some extra structure on `A 0`, namely:
* `SetLike.GradeZero.subsemiring`, which leads to
  * `SetLike.GradeZero.instSemiring`
  * `SetLike.GradeZero.instCommSemiring`
* `SetLike.GradeZero.subring`, which leads to
  * `SetLike.GradeZero.instRing`
  * `SetLike.GradeZero.instCommRing`
* `SetLike.GradeZero.subalgebra`, which leads to
  * `SetLike.GradeZero.instAlgebra`

## Tags

internally graded ring
-/


open DirectSum

variable {ι : Type*} {σ S R : Type*}

theorem SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedOne A] (s : S) : algebraMap S R s ∈ A 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (A 0).smul_mem s <| SetLike.one_mem_graded _

theorem SetLike.natCast_mem_graded [Zero ι] [AddMonoidWithOne R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedOne A] (n : ℕ) : (n : R) ∈ A 0 := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact zero_mem (A 0)
  | succ _ n_ih =>
    rw [Nat.cast_succ]
    exact add_mem n_ih (SetLike.one_mem_graded _)

@[deprecated (since := "2024-04-17")]
alias SetLike.nat_cast_mem_graded := SetLike.natCast_mem_graded

theorem SetLike.intCast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R]
    [AddSubgroupClass σ R] (A : ι → σ) [SetLike.GradedOne A] (z : ℤ) : (z : R) ∈ A 0 := by
  induction z
  · rw [Int.ofNat_eq_coe, Int.cast_natCast]
    exact SetLike.natCast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.natCast_mem_graded _ _)

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

/-- Build a `DirectSum.GCommSemiring` instance for a collection of additive submonoids. -/
instance gcommSemiring [AddCommMonoid ι] [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) [SetLike.GradedMonoid A] : DirectSum.GCommSemiring fun i => A i :=
  { SetLike.gCommMonoid A, SetLike.gsemiring A with }

/-- Build a `DirectSum.GRing` instance for a collection of additive subgroups. -/
instance gring [AddMonoid ι] [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GRing fun i => A i :=
  { SetLike.gsemiring A with
    intCast := fun z => ⟨z, SetLike.intCast_mem_graded _ _⟩
    intCast_ofNat := fun _n => Subtype.ext <| Int.cast_natCast _
    intCast_negSucc_ofNat := fun n => Subtype.ext <| Int.cast_negSucc n }

/-- Build a `DirectSum.GCommRing` instance for a collection of additive submonoids. -/
instance gcommRing [AddCommMonoid ι] [CommRing R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GCommRing fun i => A i :=
  { SetLike.gCommMonoid A, SetLike.gring A with }

end SetLike

namespace DirectSum

section coe

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
def coeRingHom [AddMonoid ι] [SetLike.GradedMonoid A] : (⨁ i, A i) →+* R :=
  DirectSum.toSemiring (fun i => AddSubmonoidClass.subtype (A i)) rfl fun _ _ => rfl

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
@[simp]
theorem coeRingHom_of [AddMonoid ι] [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    (coeRingHom A : _ →+* R) (of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ _ _ _ _

theorem coe_mul_apply [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) =
      ∑ ij ∈ (r.support ×ˢ r'.support).filter (fun ij : ι × ι => ij.1 + ij.2 = n),
        (r ij.1 * r' ij.2 : R) := by
  rw [mul_eq_sum_support_ghas_mul, DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  simp_rw [coe_of_apply, apply_ite, ZeroMemClass.coe_zero, ← Finset.sum_filter, SetLike.coe_gMul]

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
  · rw [of_eq_of_ne _ _ _ h]
    rfl

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

theorem coe_of_mul_apply_add [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) i r * r') (i + j) : R) = r * r' j :=
  coe_of_mul_apply_aux _ _ _ fun _x => ⟨fun h => add_left_cancel h, fun h => h ▸ rfl⟩

theorem coe_mul_of_apply_add [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    {i : ι} (r' : A i) (j : ι) : ((r * of (fun i => A i) i r') (j + i) : R) = r j * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => ⟨fun h => add_right_cancel h, fun h => h ▸ rfl⟩

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
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_right i x).trans_eq H)

theorem coe_mul_of_apply_of_not_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i ≤ n) :
    ((r * of (fun i => A i) i r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum, DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_left i x).trans_eq H)

variable [Sub ι] [OrderedSub ι] [ContravariantClass ι ι (· + ·) (· ≤ ·)]

/- The following two lemmas only require the same hypotheses as `eq_tsub_iff_add_eq_of_le`, but we
  state them for `CanonicallyOrderedAddCommMonoid` + the above three typeclasses for convenience. -/
theorem coe_mul_of_apply_of_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i ≤ n) :
    ((r * of (fun i => A i) i r') n : R) = r (n - i) * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => (eq_tsub_iff_add_eq_of_le h).symm

theorem coe_of_mul_apply_of_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i ≤ n) :
    ((of (fun i => A i) i r * r') n : R) = r * r' (n - i) :=
  coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h, add_comm]

theorem coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [Decidable (i ≤ n)] :
    ((r * of (fun i => A i) i r') n : R) = if i ≤ n then (r (n - i) : R) * r' else 0 := by
  split_ifs with h
  exacts [coe_mul_of_apply_of_le _ _ _ n h, coe_mul_of_apply_of_not_le _ _ _ n h]

theorem coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [Decidable (i ≤ n)] :
    ((of (fun i => A i) i r * r') n : R) = if i ≤ n then (r * r' (n - i) : R) else 0 := by
  split_ifs with h
  exacts [coe_of_mul_apply_of_le _ _ _ n h, coe_of_mul_apply_of_not_le _ _ _ n h]

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

@[simp]
theorem setLike.coe_galgebra_toFun {ι} [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (s : S) :
    (DirectSum.GAlgebra.toFun (A := fun i => A i) s) = (algebraMap S R s : R) :=
  rfl

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_gradedMonoid [CommSemiring S] [Semiring R] [Algebra S R] (p : Submodule S R) :
    SetLike.GradedMonoid fun i : ℕ => p ^ i where
  one_mem := by
    rw [← one_le, pow_zero]
  mul_mem i j p q hp hq := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hp hq

end Submodule

/-- The canonical algebra isomorphism between `⨁ i, A i` and `R`. -/
def DirectSum.coeAlgHom [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] : (⨁ i, A i) →ₐ[S] R :=
  DirectSum.toAlgebra S _ (fun i => (A i).subtype) rfl (fun _ _ => rfl)

/-- The supremum of submodules that form a graded monoid is a subalgebra, and equal to the range of
`DirectSum.coeAlgHom`. -/
theorem Submodule.iSup_eq_toSubmodule_range [AddMonoid ι] [CommSemiring S] [Semiring R]
    [Algebra S R] (A : ι → Submodule S R) [SetLike.GradedMonoid A] :
    ⨆ i, A i = Subalgebra.toSubmodule (DirectSum.coeAlgHom A).range :=
  (Submodule.iSup_eq_range_dfinsupp_lsum A).trans <| SetLike.coe_injective rfl

@[simp]
theorem DirectSum.coeAlgHom_of [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    DirectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ (by rfl) (fun _ _ => (by rfl)) _ _

end DirectSum

/-! ### Facts about grade zero -/

namespace SetLike.GradeZero

section Semiring
variable [Semiring R] [AddMonoid ι] [SetLike σ R] [AddSubmonoidClass σ R]
variable (A : ι → σ) [SetLike.GradedMonoid A]

/-- The subsemiring `A 0` of `R`. -/
def subsemiring : Subsemiring R where
  carrier := A 0
  __ := submonoid A
  add_mem' := add_mem
  zero_mem' := zero_mem (A 0)

-- TODO: it might be expensive to unify `A` in this instance in practice
/-- The semiring `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
instance instSemiring : Semiring (A 0) := (subsemiring A).toSemiring

/- The linter message "error: SetLike.GradeZero.coe_natCast.{u_4, u_2, u_1} Left-hand side
  does not simplify, when using the simp lemma on itself." is wrong. The LHS does simplify. -/
@[nolint simpNF, simp, norm_cast] theorem coe_natCast (n : ℕ) : (n : A 0) = (n : R) := rfl

/- The linter message "error: SetLike.GradeZero.coe_ofNat.{u_4, u_2, u_1} Left-hand side does
  not simplify, when using the simp lemma on itself." is wrong. The LHS does simplify. -/
@[nolint simpNF, simp, norm_cast] theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : A 0) = (OfNat.ofNat n : R) := rfl

end Semiring

section CommSemiring
variable [CommSemiring R] [AddCommMonoid ι] [SetLike σ R] [AddSubmonoidClass σ R]
variable (A : ι → σ) [SetLike.GradedMonoid A]

-- TODO: it might be expensive to unify `A` in this instance in practice
/--The commutative semiring `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`.-/
instance instCommSemiring : CommSemiring (A 0) := (subsemiring A).toCommSemiring

end CommSemiring

section Ring
variable [Ring R] [AddMonoid ι] [SetLike σ R] [AddSubgroupClass σ R]
variable (A : ι → σ) [SetLike.GradedMonoid A]

/-- The subring `A 0` of `R`. -/
def subring : Subring R where
  carrier := A 0
  __ := subsemiring A
  neg_mem' := neg_mem

-- TODO: it might be expensive to unify `A` in this instances in practice
/-- The ring `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
instance instRing : Ring (A 0) := (subring A).toRing

theorem coe_intCast (z : ℤ) : (z : A 0) = (z : R) := rfl

end Ring

section CommRing
variable [CommRing R] [AddCommMonoid ι] [SetLike σ R] [AddSubgroupClass σ R]
variable (A : ι → σ) [SetLike.GradedMonoid A]

-- TODO: it might be expensive to unify `A` in this instances in practice
/-- The commutative ring `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
instance instCommRing : CommRing (A 0) := (subring A).toCommRing

end CommRing

section Algebra
variable [CommSemiring S] [Semiring R] [Algebra S R] [AddMonoid ι]
variable (A : ι → Submodule S R) [SetLike.GradedMonoid A]

/-- The subalgebra `A 0` of `R`. -/
def subalgebra : Subalgebra S R where
  carrier := A 0
  __ := subsemiring A
  algebraMap_mem' := algebraMap_mem_graded A

-- TODO: it might be expensive to unify `A` in this instances in practice
/-- The `S`-algebra `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
instance instAlgebra : Algebra S (A 0) := inferInstanceAs <| Algebra S (subalgebra A)

/- The linter message "error: SetLike.GradeZero.coe_algebraMap.{u_4, u_3, u_1} Left-hand side
  does not simplify, when using the simp lemma on itself." is wrong. The LHS does simplify. -/
@[nolint simpNF, simp, norm_cast] theorem coe_algebraMap (s : S) :
    ↑(algebraMap _ (A 0) s) = algebraMap _ R s := rfl

end Algebra

end SetLike.GradeZero

section HomogeneousElement

theorem SetLike.homogeneous_zero_submodule [Zero ι] [Semiring S] [AddCommMonoid R] [Module S R]
    (A : ι → Submodule S R) : SetLike.Homogeneous A (0 : R) :=
  ⟨0, Submodule.zero_mem _⟩

theorem SetLike.Homogeneous.smul [CommSemiring S] [Semiring R] [Algebra S R] {A : ι → Submodule S R}
    {s : S} {r : R} (hr : SetLike.Homogeneous A r) : SetLike.Homogeneous A (s • r) :=
  let ⟨i, hi⟩ := hr
  ⟨i, Submodule.smul_mem _ _ hi⟩

end HomogeneousElement
