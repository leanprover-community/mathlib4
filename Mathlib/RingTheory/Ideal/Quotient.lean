/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen
-/
import Mathlib.LinearAlgebra.Quotient
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.FinCases

/-!
# Ideal quotients

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `Algebra.RingQuot` for quotients of semirings.

## Main definitions

 - `Ideal.Quotient.Ring`: the quotient of a ring `R` by a two-sided ideal `I : Ideal R`

-/


universe u v w

namespace Ideal

open Set

variable {R : Type u} [Ring R] (I J : Ideal R) {a b : R}
variable {S : Type v}

namespace Quotient

variable {I} {x y : R}

instance one (I : Ideal R) : One (R ⧸ I) :=
  ⟨Submodule.Quotient.mk 1⟩

/-- On `Ideal`s, `Submodule.quotientRel` is a ring congruence. -/
protected def ringCon (I : Ideal R) [I.IsTwoSided] : RingCon R :=
  { QuotientAddGroup.con I.toAddSubgroup with
    mul' := fun {a₁ b₁ a₂ b₂} h₁ h₂ => by
      rw [Submodule.quotientRel_def] at h₁ h₂ ⊢
      convert I.add_mem (I.mul_mem_left a₁ h₂) (mul_mem_right b₂ _ h₁) using 1
      rw [mul_sub, sub_mul, sub_add_sub_cancel] }

instance ring (I : Ideal R) [I.IsTwoSided] : Ring (R ⧸ I) :=
    inferInstanceAs (Ring (Quotient.ringCon I).Quotient)

instance commRing {R} [CommRing R] (I : Ideal R) : CommRing (R ⧸ I) :=
    inferInstanceAs (CommRing (Quotient.ringCon I).Quotient)

protected theorem nontrivial (hI : I ≠ ⊤) : Nontrivial (R ⧸ I) :=
  Submodule.Quotient.nontrivial_of_lt_top _ hI.lt_top

theorem subsingleton_iff : Subsingleton (R ⧸ I) ↔ I = ⊤ :=
  Submodule.subsingleton_quotient_iff_eq_top

example : Unique (R ⧸ (⊤ : Ideal R)) := inferInstance

variable [I.IsTwoSided]

-- Sanity test to make sure no diamonds have emerged in `commRing`
example : (ring I).toAddCommGroup = Submodule.Quotient.addCommGroup I := rfl

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

variable (I) in
/-- The ring homomorphism from a ring `R` to a quotient ring `R/I`. -/
def mk : R →+* R ⧸ I where
  toFun a := Submodule.Quotient.mk a
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

instance : Coe R (R ⧸ I) :=
  ⟨Ideal.Quotient.mk I⟩

/-- Two `RingHom`s from the quotient by an ideal are equal if their
compositions with `Ideal.Quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
theorem ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ I →+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) :
    f = g :=
  RingHom.ext fun x => Quotient.inductionOn' x <| (RingHom.congr_fun h : _)

instance inhabited : Inhabited (R ⧸ I) :=
  ⟨mk I 37⟩

protected theorem eq : mk I x = mk I y ↔ x - y ∈ I :=
  Submodule.Quotient.eq I

@[simp]
theorem mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R ⧸ I) = mk I x := rfl

theorem eq_zero_iff_mem : mk I a = 0 ↔ a ∈ I :=
  Submodule.Quotient.mk_eq_zero _

theorem eq_zero_iff_dvd {R} [CommRing R] (x y : R) :
    Ideal.Quotient.mk (Ideal.span ({x} : Set R)) y = 0 ↔ x ∣ y := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

@[simp]
lemma mk_singleton_self {R} [CommRing R] (x : R) : mk (Ideal.span {x}) x = 0 := by
  rw [eq_zero_iff_dvd]

theorem mk_eq_mk_iff_sub_mem (x y : R) : mk I x = mk I y ↔ x - y ∈ I := by
  rw [← eq_zero_iff_mem, map_sub, sub_eq_zero]

theorem zero_eq_one_iff : (0 : R ⧸ I) = 1 ↔ I = ⊤ :=
  eq_comm.trans <| eq_zero_iff_mem.trans (eq_top_iff_one _).symm

theorem zero_ne_one_iff : (0 : R ⧸ I) ≠ 1 ↔ I ≠ ⊤ :=
  not_congr zero_eq_one_iff

theorem mk_surjective : Function.Surjective (mk I) := fun y =>
  Quotient.inductionOn' y fun x => Exists.intro x rfl

instance : RingHomSurjective (mk I) :=
  ⟨mk_surjective⟩

variable (I)

/-- If `I` is an ideal of a commutative ring `R`, if `q : R → R/I` is the quotient map, and if
`s ⊆ R` is a subset, then `q⁻¹(q(s)) = ⋃ᵢ(i + s)`, the union running over all `i ∈ I`. -/
theorem quotient_ring_saturate (s : Set R) :
    mk I ⁻¹' (mk I '' s) = ⋃ x : I, (fun y => x.1 + y) '' s := by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion, Ideal.Quotient.eq]
  exact
    ⟨fun ⟨a, a_in, h⟩ => ⟨⟨_, I.neg_mem h⟩, a, a_in, by simp⟩, fun ⟨⟨i, hi⟩, a, ha, Eq⟩ =>
      ⟨a, ha, by rw [← Eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub]; exact I.neg_mem hi⟩⟩

instance noZeroDivisors [hI : I.IsPrime] : NoZeroDivisors (R ⧸ I) where
    eq_zero_or_eq_zero_of_mul_eq_zero {a b} := Quotient.inductionOn₂' a b fun {_ _} hab =>
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim (Or.inl ∘ eq_zero_iff_mem.2)
        (Or.inr ∘ eq_zero_iff_mem.2)

instance isDomain [hI : I.IsPrime] : IsDomain (R ⧸ I) :=
  let _ := Quotient.nontrivial hI.1
  NoZeroDivisors.to_isDomain _

theorem isDomain_iff_prime : IsDomain (R ⧸ I) ↔ I.IsPrime := by
  refine ⟨fun H => ⟨zero_ne_one_iff.1 ?_, fun {x y} h => ?_⟩, fun h => inferInstance⟩
  · haveI : Nontrivial (R ⧸ I) := ⟨H.2.1⟩
    exact zero_ne_one
  · simp only [← eq_zero_iff_mem, (mk I).map_mul] at h ⊢
    haveI := @IsDomain.to_noZeroDivisors (R ⧸ I) _ H
    exact eq_zero_or_eq_zero_of_mul_eq_zero h

variable {I} in
theorem exists_inv [hI : I.IsMaximal] :
    ∀ {a : R ⧸ I}, a ≠ 0 → ∃ b : R ⧸ I, a * b = 1 := by
  apply exists_right_inv_of_exists_left_inv
  rintro ⟨a⟩ h
  rcases hI.exists_inv (mt eq_zero_iff_mem.2 h) with ⟨b, c, hc, abc⟩
  refine ⟨mk _ b, Quot.sound ?_⟩
  simp only [Submodule.quotientRel_def]
  rw [← eq_sub_iff_add_eq'] at abc
  rwa [abc, ← neg_mem_iff (G := R) (H := I), neg_sub] at hc

open Classical in
/-- The quotient by a maximal ideal is a group with zero. This is a `def` rather than `instance`,
since users will have computable inverses in some applications.

See note [reducible non-instances]. -/
protected noncomputable abbrev groupWithZero [hI : I.IsMaximal] :
    GroupWithZero (R ⧸ I) :=
  { inv := fun a => if ha : a = 0 then 0 else Classical.choose (exists_inv ha)
    mul_inv_cancel := fun a (ha : a ≠ 0) =>
      show a * dite _ _ _ = _ by rw [dif_neg ha]; exact Classical.choose_spec (exists_inv ha)
    inv_zero := dif_pos rfl
    __ := Quotient.nontrivial hI.out.1 }

/-- The quotient by a two-sided ideal that is maximal as a left ideal is a division ring.
This is a `def` rather than `instance`, since users
will have computable inverses (and `qsmul`, `ratCast`) in some applications.

See note [reducible non-instances]. -/
protected noncomputable abbrev divisionRing [I.IsMaximal] : DivisionRing (R ⧸ I) where
  __ := ring _
  __ := Quotient.groupWithZero _
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- The quotient of a commutative ring by a maximal ideal is a field.
This is a `def` rather than `instance`, since users
will have computable inverses (and `qsmul`, `ratCast`) in some applications.

See note [reducible non-instances]. -/
protected noncomputable abbrev field {R} [CommRing R] (I : Ideal R) [I.IsMaximal] :
    Field (R ⧸ I) where
  __ := commRing _
  __ := Quotient.groupWithZero _
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- If the quotient by an ideal is a field, then the ideal is maximal. -/
theorem maximal_of_isField {R} [CommRing R] (I : Ideal R) (hqf : IsField (R ⧸ I)) :
    I.IsMaximal := by
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
theorem maximal_ideal_iff_isField_quotient {R} [CommRing R] (I : Ideal R) :
    I.IsMaximal ↔ IsField (R ⧸ I) :=
  ⟨fun h =>
    let _i := @Quotient.field _ _ I h
    Field.toIsField _,
    maximal_of_isField _⟩

variable [Semiring S]

/-- Given a ring homomorphism `f : R →+* S` sending all elements of an ideal to zero,
lift it to the quotient by this ideal. -/
def lift (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) : R ⧸ I →+* S :=
  { QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom H with
    map_one' := f.map_one
    map_mul' := fun a₁ a₂ => Quotient.inductionOn₂' a₁ a₂ f.map_mul }

@[simp]
theorem lift_mk (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) :
    lift I f H (mk I a) = f a :=
  rfl

theorem lift_surjective_of_surjective {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hf : Function.Surjective f) : Function.Surjective (Ideal.Quotient.lift I f H) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  use Ideal.Quotient.mk I x
  simp only [Ideal.Quotient.lift_mk]

variable (S T : Ideal R) [S.IsTwoSided] [T.IsTwoSided]

/-- The ring homomorphism from the quotient by a smaller ideal to the quotient by a larger ideal.

This is the `Ideal.Quotient` version of `Quot.Factor` -/
def factor (H : S ≤ T) : R ⧸ S →+* R ⧸ T :=
  Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)

@[simp]
theorem factor_mk (H : S ≤ T) (x : R) : factor S T H (mk S x) = mk T x :=
  rfl

@[simp]
theorem factor_comp_mk (H : S ≤ T) : (factor S T H).comp (mk S) = mk T := by
  ext x
  rw [RingHom.comp_apply, factor_mk]

end Quotient

variable {I J} [I.IsTwoSided] [J.IsTwoSided]

/-- Quotienting by equal ideals gives equivalent rings.

See also `Submodule.quotEquivOfEq` and `Ideal.quotientEquivAlgOfEq`.
-/
def quotEquivOfEq (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  { Submodule.quotEquivOfEq I J h with
    map_mul' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl }

@[simp]
theorem quotEquivOfEq_mk (h : I = J) (x : R) :
    quotEquivOfEq h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl

@[simp]
theorem quotEquivOfEq_symm (h : I = J) :
    (Ideal.quotEquivOfEq h).symm = Ideal.quotEquivOfEq h.symm := by ext; rfl

section Pi

variable (I J) (ι : Type v)

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
  invFun := fun x ↦ Ideal.Quotient.mk (I.pi ι) fun i ↦ Quotient.out' (x i)
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

end Ideal
