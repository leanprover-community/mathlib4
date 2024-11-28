/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen
-/
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.FinCases

/-!
# Ideal quotients

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `Algebra.RingQuot` for quotients of non-commutative rings.

## Main definitions

 - `Ideal.Quotient`: the quotient of a commutative ring `R` by an ideal `I : Ideal R`

-/


universe u v w

namespace Ideal

open Set

variable {R : Type u} [CommRing R] (I : Ideal R) {a b : R}
variable {S : Type v}

namespace Quotient

variable {I} {x y : R}

-- this instance is harder to find than the one via `Algebra α (R ⧸ I)`, so use a lower priority
instance (priority := 100) isScalarTower_right {α} [SMul α R] [IsScalarTower α R R] :
    IsScalarTower α (R ⧸ I) (R ⧸ I) :=
  (Quotient.ringCon I).isScalarTower_right

instance smulCommClass {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass α R R] :
    SMulCommClass α (R ⧸ I) (R ⧸ I) :=
  (Quotient.ringCon I).smulCommClass

instance smulCommClass' {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass R α R] :
    SMulCommClass (R ⧸ I) α (R ⧸ I) :=
  (Quotient.ringCon I).smulCommClass'

theorem eq_zero_iff_dvd (x y : R) : Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y = 0 ↔ x ∣ y := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

@[simp]
lemma mk_singleton_self (x : R) : mk (Ideal.span {x}) x = 0 := by
  rw [eq_zero_iff_dvd]

theorem zero_eq_one_iff {I : Ideal R} : (0 : R ⧸ I) = 1 ↔ I = ⊤ :=
  eq_comm.trans <| eq_zero_iff_mem.trans (eq_top_iff_one _).symm

theorem zero_ne_one_iff {I : Ideal R} : (0 : R ⧸ I) ≠ 1 ↔ I ≠ ⊤ :=
  not_congr zero_eq_one_iff

protected theorem nontrivial {I : Ideal R} (hI : I ≠ ⊤) : Nontrivial (R ⧸ I) :=
  ⟨⟨0, 1, zero_ne_one_iff.2 hI⟩⟩

theorem subsingleton_iff {I : Ideal R} : Subsingleton (R ⧸ I) ↔ I = ⊤ := by
  rw [eq_top_iff_one, ← subsingleton_iff_zero_eq_one, eq_comm, ← (mk I).map_one,
    Quotient.eq_zero_iff_mem]

instance : Unique (R ⧸ (⊤ : Ideal R)) :=
  ⟨⟨0⟩, by rintro ⟨x⟩; exact Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩

instance noZeroDivisors (I : Ideal R) [hI : I.IsPrime] : NoZeroDivisors (R ⧸ I) where
    eq_zero_or_eq_zero_of_mul_eq_zero {a b} := Quotient.inductionOn₂' a b fun {_ _} hab =>
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim (Or.inl ∘ eq_zero_iff_mem.2)
        (Or.inr ∘ eq_zero_iff_mem.2)

instance isDomain (I : Ideal R) [hI : I.IsPrime] : IsDomain (R ⧸ I) :=
  let _ := Quotient.nontrivial hI.1
  NoZeroDivisors.to_isDomain _

theorem isDomain_iff_prime (I : Ideal R) : IsDomain (R ⧸ I) ↔ I.IsPrime := by
  refine ⟨fun H => ⟨zero_ne_one_iff.1 ?_, fun {x y} h => ?_⟩, fun h => inferInstance⟩
  · haveI : Nontrivial (R ⧸ I) := ⟨H.2.1⟩
    exact zero_ne_one
  · simp only [← eq_zero_iff_mem, (mk I).map_mul] at h ⊢
    haveI := @IsDomain.to_noZeroDivisors (R ⧸ I) _ H
    exact eq_zero_or_eq_zero_of_mul_eq_zero h

theorem exists_inv {I : Ideal R} [hI : I.IsMaximal] :
    ∀ {a : R ⧸ I}, a ≠ 0 → ∃ b : R ⧸ I, a * b = 1 := by
  rintro ⟨a⟩ h
  rcases hI.exists_inv (mt eq_zero_iff_mem.2 h) with ⟨b, c, hc, abc⟩
  rw [mul_comm] at abc
  refine ⟨mk _ b, Quot.sound ?_⟩
  simp only [Submodule.quotientRel_def]
  rw [← eq_sub_iff_add_eq'] at abc
  rwa [abc, ← neg_mem_iff (G := R) (H := I), neg_sub] at hc

open Classical in
/-- The quotient by a maximal ideal is a group with zero. This is a `def` rather than `instance`,
since users will have computable inverses in some applications.

See note [reducible non-instances]. -/
protected noncomputable abbrev groupWithZero (I : Ideal R) [hI : I.IsMaximal] :
    GroupWithZero (R ⧸ I) :=
  { inv := fun a => if ha : a = 0 then 0 else Classical.choose (exists_inv ha)
    mul_inv_cancel := fun a (ha : a ≠ 0) =>
      show a * dite _ _ _ = _ by rw [dif_neg ha]; exact Classical.choose_spec (exists_inv ha)
    inv_zero := dif_pos rfl }

/-- The quotient by a maximal ideal is a field. This is a `def` rather than `instance`, since users
will have computable inverses (and `qsmul`, `ratCast`) in some applications.

See note [reducible non-instances]. -/
protected noncomputable abbrev field (I : Ideal R) [I.IsMaximal] : Field (R ⧸ I) where
  __ := commRing _
  __ := Quotient.groupWithZero _
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- If the quotient by an ideal is a field, then the ideal is maximal. -/
theorem maximal_of_isField (I : Ideal R) (hqf : IsField (R ⧸ I)) : I.IsMaximal := by
  apply Ideal.isMaximal_iff.2
  constructor
  · intro h
    rcases hqf.exists_pair_ne with ⟨⟨x⟩, ⟨y⟩, hxy⟩
    exact hxy (Ideal.Quotient.eq.2 (mul_one (x - y) ▸ I.mul_mem_left _ h))
  · intro J x hIJ hxnI hxJ
    rcases hqf.mul_inv_cancel (mt Ideal.Quotient.eq_zero_iff_mem.1 hxnI) with ⟨⟨y⟩, hy⟩
    rw [← zero_add (1 : R), ← sub_self (x * y), sub_add]
    exact J.sub_mem (J.mul_mem_right _ hxJ) (hIJ (Ideal.Quotient.eq.1 hy))

/-- The quotient of a ring by an ideal is a field iff the ideal is maximal. -/
theorem maximal_ideal_iff_isField_quotient (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I) :=
  ⟨fun h =>
    let _i := @Quotient.field _ _ I h
    Field.toIsField _,
    maximal_of_isField _⟩

end Quotient

section Pi

variable (ι : Type v)

/-- `R^n/I^n` is a `R/I`-module. -/
instance modulePi : Module (R ⧸ I) ((ι → R) ⧸ I.pi ι) where
  smul c m :=
    Quotient.liftOn₂' c m (fun r m => Submodule.Quotient.mk <| r • m) <| by
      intro c₁ m₁ c₂ m₂ hc hm
      apply Ideal.Quotient.eq.2
      rw [Submodule.quotientRel_def] at hc hm
      intro i
      exact I.mul_sub_mul_mem hc (hm i)
  one_smul := by
    rintro ⟨a⟩
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    congr with i; exact one_mul (a i)
  mul_smul := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    congr 1; funext i; exact mul_assoc a b (c i)
  smul_add := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    congr with i; exact mul_add a (b i) (c i)
  smul_zero := by
    rintro ⟨a⟩
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    congr with _; exact mul_zero a
  add_smul := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    congr with i; exact add_mul a b (c i)
  zero_smul := by
    rintro ⟨a⟩
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    congr with i; exact zero_mul (a i)

/-- `R^n/I^n` is isomorphic to `(R/I)^n` as an `R/I`-module. -/
noncomputable def piQuotEquiv : ((ι → R) ⧸ I.pi ι) ≃ₗ[R ⧸ I] ι → (R ⧸ I) where
  toFun := fun x ↦
      Quotient.liftOn' x (fun f i => Ideal.Quotient.mk I (f i)) fun _ _ hab =>
        funext fun i => (Submodule.Quotient.eq' _).2 (QuotientAddGroup.leftRel_apply.mp hab i)
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
  map_smul' := by rintro ⟨_⟩ ⟨_⟩; rfl
  invFun := fun x ↦ Ideal.Quotient.mk (I.pi ι) fun i ↦ Quotient.out (x i)
  left_inv := by
    rintro ⟨x⟩
    exact Ideal.Quotient.eq.2 fun i => Ideal.Quotient.eq.1 (Quotient.out_eq' _)
  right_inv := by
    intro x
    ext i
    obtain ⟨_, _⟩ := @Quot.exists_rep _ _ (x i)
    convert Quotient.out_eq' (x i)

/-- If `f : R^n → R^m` is an `R`-linear map and `I ⊆ R` is an ideal, then the image of `I^n` is
    contained in `I^m`. -/
theorem map_pi {ι : Type*} [Finite ι] {ι' : Type w} (x : ι → R) (hi : ∀ i, x i ∈ I)
    (f : (ι → R) →ₗ[R] ι' → R) (i : ι') : f x i ∈ I := by
  classical
    cases nonempty_fintype ι
    rw [pi_eq_sum_univ x]
    simp only [Finset.sum_apply, smul_eq_mul, map_sum, Pi.smul_apply, map_smul]
    exact I.sum_mem fun j _ => I.mul_mem_right _ (hi j)

end Pi

open scoped Pointwise in
/-- A ring is made up of a disjoint union of cosets of an ideal. -/
lemma univ_eq_iUnion_image_add {R : Type*} [Ring R] (I : Ideal R) :
    (Set.univ (α := R)) = ⋃ x : R ⧸ I, x.out +ᵥ (I : Set R) :=
  QuotientAddGroup.univ_eq_iUnion_vadd I.toAddSubgroup

lemma _root_.Finite.of_finite_quot_finite_ideal {R : Type*} [Ring R] {I : Ideal R}
    [hI : Finite I] [h : Finite (R ⧸ I)] : Finite R :=
  @Finite.of_finite_quot_finite_addSubgroup _ _ _ hI h

end Ideal
