/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen
-/
import Mathlib.Algebra.Ring.Fin
import Mathlib.Algebra.Ring.Prod
import Mathlib.LinearAlgebra.Quotient
import Mathlib.RingTheory.Congruence
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Tactic.FinCases

#align_import ring_theory.ideal.quotient from "leanprover-community/mathlib"@"949dc57e616a621462062668c9f39e4e17b64b69"

/-!
# Ideal quotients

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `Algebra.RingQuot` for quotients of non-commutative rings.

## Main definitions

 - `Ideal.Quotient`: the quotient of a commutative ring `R` by an ideal `I : Ideal R`

## Main results

 - `Ideal.quotientInfRingEquivPiQuotient`: the **Chinese Remainder Theorem**
-/


universe u v w

namespace Ideal

open Set
open BigOperators

variable {R : Type u} [CommRing R] (I : Ideal R) {a b : R}
variable {S : Type v}

-- Note that at present `Ideal` means a left-ideal,
-- so this quotient is only useful in a commutative ring.
-- We should develop quotients by two-sided ideals as well.
/-- The quotient `R/I` of a ring `R` by an ideal `I`.

The ideal quotient of `I` is defined to equal the quotient of `I` as an `R`-submodule of `R`.
This definition is marked `reducible` so that typeclass instances can be shared between
`Ideal.Quotient I` and `Submodule.Quotient I`.
-/
@[reducible]
instance : HasQuotient R (Ideal R) :=
  Submodule.hasQuotient

namespace Quotient

variable {I} {x y : R}

instance one (I : Ideal R) : One (R ⧸ I) :=
  ⟨Submodule.Quotient.mk 1⟩
#align ideal.quotient.has_one Ideal.Quotient.one

/-- On `Ideal`s, `Submodule.quotientRel` is a ring congruence. -/
protected def ringCon (I : Ideal R) : RingCon R :=
  { QuotientAddGroup.con I.toAddSubgroup with
    mul' := fun {a₁ b₁ a₂ b₂} h₁ h₂ => by
      rw [Submodule.quotientRel_r_def] at h₁ h₂ ⊢
      -- ⊢ a₁ * a₂ - b₁ * b₂ ∈ I
      have F := I.add_mem (I.mul_mem_left a₂ h₁) (I.mul_mem_right b₁ h₂)
      -- ⊢ a₁ * a₂ - b₁ * b₂ ∈ I
      have : a₁ * a₂ - b₁ * b₂ = a₂ * (a₁ - b₁) + (a₂ - b₂) * b₁ := by
        rw [mul_sub, sub_mul, sub_add_sub_cancel, mul_comm, mul_comm b₁]
      rwa [← this] at F }
      -- 🎉 no goals
#align ideal.quotient.ring_con Ideal.Quotient.ringCon

instance commRing (I : Ideal R) : CommRing (R ⧸ I) :=
    inferInstanceAs (CommRing (Quotient.ringCon I).Quotient)
#align ideal.quotient.comm_ring Ideal.Quotient.commRing

-- Sanity test to make sure no diamonds have emerged in `commRing`
example : (commRing I).toAddCommGroup = Submodule.Quotient.addCommGroup I := rfl

-- this instance is harder to find than the one via `Algebra α (R ⧸ I)`, so use a lower priority
instance (priority := 100) isScalarTower_right {α} [SMul α R] [IsScalarTower α R R] :
    IsScalarTower α (R ⧸ I) (R ⧸ I) :=
  (Quotient.ringCon I).isScalarTower_right
#align ideal.quotient.is_scalar_tower_right Ideal.Quotient.isScalarTower_right

instance smulCommClass {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass α R R] :
    SMulCommClass α (R ⧸ I) (R ⧸ I) :=
  (Quotient.ringCon I).smulCommClass
#align ideal.quotient.smul_comm_class Ideal.Quotient.smulCommClass

instance smulCommClass' {α} [SMul α R] [IsScalarTower α R R] [SMulCommClass R α R] :
    SMulCommClass (R ⧸ I) α (R ⧸ I) :=
  (Quotient.ringCon I).smulCommClass'
#align ideal.quotient.smul_comm_class' Ideal.Quotient.smulCommClass'

/-- The ring homomorphism from a ring `R` to a quotient ring `R/I`. -/
def mk (I : Ideal R) : R →+* R ⧸ I where
  toFun a := Submodule.Quotient.mk a
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
#align ideal.quotient.mk Ideal.Quotient.mk

instance {I : Ideal R} : Coe R (R ⧸ I) :=
  ⟨Ideal.Quotient.mk I⟩

/-- Two `RingHom`s from the quotient by an ideal are equal if their
compositions with `Ideal.Quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
theorem ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ I →+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) :
    f = g :=
  RingHom.ext fun x => Quotient.inductionOn' x <| (RingHom.congr_fun h : _)
#align ideal.quotient.ring_hom_ext Ideal.Quotient.ringHom_ext

instance inhabited : Inhabited (R ⧸ I) :=
  ⟨mk I 37⟩
#align ideal.quotient.inhabited Ideal.Quotient.inhabited

protected theorem eq : mk I x = mk I y ↔ x - y ∈ I :=
  Submodule.Quotient.eq I
#align ideal.quotient.eq Ideal.Quotient.eq

@[simp]
theorem mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R ⧸ I) = mk I x := rfl
#align ideal.quotient.mk_eq_mk Ideal.Quotient.mk_eq_mk

theorem eq_zero_iff_mem {I : Ideal R} : mk I a = 0 ↔ a ∈ I :=
  Submodule.Quotient.mk_eq_zero _
#align ideal.quotient.eq_zero_iff_mem Ideal.Quotient.eq_zero_iff_mem

-- Porting note: new theorem
theorem mk_eq_mk_iff_sub_mem (x y : R) : mk I x = mk I y ↔ x - y ∈ I := by
  rw [← eq_zero_iff_mem, map_sub, sub_eq_zero]
  -- 🎉 no goals

theorem zero_eq_one_iff {I : Ideal R} : (0 : R ⧸ I) = 1 ↔ I = ⊤ :=
  eq_comm.trans <| eq_zero_iff_mem.trans (eq_top_iff_one _).symm
#align ideal.quotient.zero_eq_one_iff Ideal.Quotient.zero_eq_one_iff

theorem zero_ne_one_iff {I : Ideal R} : (0 : R ⧸ I) ≠ 1 ↔ I ≠ ⊤ :=
  not_congr zero_eq_one_iff
#align ideal.quotient.zero_ne_one_iff Ideal.Quotient.zero_ne_one_iff

protected theorem nontrivial {I : Ideal R} (hI : I ≠ ⊤) : Nontrivial (R ⧸ I) :=
  ⟨⟨0, 1, zero_ne_one_iff.2 hI⟩⟩
#align ideal.quotient.nontrivial Ideal.Quotient.nontrivial

theorem subsingleton_iff {I : Ideal R} : Subsingleton (R ⧸ I) ↔ I = ⊤ := by
  rw [eq_top_iff_one, ← subsingleton_iff_zero_eq_one, eq_comm, ← (mk I).map_one,
    Quotient.eq_zero_iff_mem]
#align ideal.quotient.subsingleton_iff Ideal.Quotient.subsingleton_iff

instance : Unique (R ⧸ (⊤ : Ideal R)) :=
  ⟨⟨0⟩, by rintro ⟨x⟩; exact Quotient.eq_zero_iff_mem.mpr Submodule.mem_top⟩
           -- ⊢ Quot.mk Setoid.r x = default
                       -- 🎉 no goals

theorem mk_surjective : Function.Surjective (mk I) := fun y =>
  Quotient.inductionOn' y fun x => Exists.intro x rfl
#align ideal.quotient.mk_surjective Ideal.Quotient.mk_surjective

instance : RingHomSurjective (mk I) :=
  ⟨mk_surjective⟩

/-- If `I` is an ideal of a commutative ring `R`, if `q : R → R/I` is the quotient map, and if
`s ⊆ R` is a subset, then `q⁻¹(q(s)) = ⋃ᵢ(i + s)`, the union running over all `i ∈ I`. -/
theorem quotient_ring_saturate (I : Ideal R) (s : Set R) :
    mk I ⁻¹' (mk I '' s) = ⋃ x : I, (fun y => x.1 + y) '' s := by
  ext x
  -- ⊢ x ∈ ↑(mk I) ⁻¹' (↑(mk I) '' s) ↔ x ∈ ⋃ (x : { x // x ∈ I }), (fun y => ↑x +  …
  simp only [mem_preimage, mem_image, mem_iUnion, Ideal.Quotient.eq]
  -- ⊢ (∃ x_1, x_1 ∈ s ∧ x_1 - x ∈ I) ↔ ∃ i x_1, x_1 ∈ s ∧ ↑i + x_1 = x
  exact
    ⟨fun ⟨a, a_in, h⟩ => ⟨⟨_, I.neg_mem h⟩, a, a_in, by simp⟩, fun ⟨⟨i, hi⟩, a, ha, Eq⟩ =>
      ⟨a, ha, by rw [← Eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub]; exact I.neg_mem hi⟩⟩
#align ideal.quotient.quotient_ring_saturate Ideal.Quotient.quotient_ring_saturate

instance noZeroDivisors (I : Ideal R) [hI : I.IsPrime] : NoZeroDivisors (R ⧸ I) where
    eq_zero_or_eq_zero_of_mul_eq_zero {a b} := Quotient.inductionOn₂' a b fun {_ _} hab =>
      (hI.mem_or_mem (eq_zero_iff_mem.1 hab)).elim (Or.inl ∘ eq_zero_iff_mem.2)
        (Or.inr ∘ eq_zero_iff_mem.2)
#align ideal.quotient.no_zero_divisors Ideal.Quotient.noZeroDivisors

instance isDomain (I : Ideal R) [hI : I.IsPrime] : IsDomain (R ⧸ I) :=
  let _ := Quotient.nontrivial hI.1
  NoZeroDivisors.to_isDomain _
#align ideal.quotient.is_domain Ideal.Quotient.isDomain

theorem isDomain_iff_prime (I : Ideal R) : IsDomain (R ⧸ I) ↔ I.IsPrime := by
  refine' ⟨fun H => ⟨zero_ne_one_iff.1 _, fun {x y} h => _⟩, fun h => inferInstance⟩
  -- ⊢ 0 ≠ 1
  · haveI : Nontrivial (R ⧸ I) := ⟨H.2.1⟩
    -- ⊢ 0 ≠ 1
    exact zero_ne_one
    -- 🎉 no goals
  · simp only [← eq_zero_iff_mem, (mk I).map_mul] at h ⊢
    -- ⊢ ↑(mk I) x = 0 ∨ ↑(mk I) y = 0
    haveI := @IsDomain.to_noZeroDivisors (R ⧸ I) _ H
    -- ⊢ ↑(mk I) x = 0 ∨ ↑(mk I) y = 0
    exact eq_zero_or_eq_zero_of_mul_eq_zero h
    -- 🎉 no goals
#align ideal.quotient.is_domain_iff_prime Ideal.Quotient.isDomain_iff_prime

theorem exists_inv {I : Ideal R} [hI : I.IsMaximal] :
    ∀ {a : R ⧸ I}, a ≠ 0 → ∃ b : R ⧸ I, a * b = 1 := by
  rintro ⟨a⟩ h
  -- ⊢ ∃ b, Quot.mk Setoid.r a * b = 1
  rcases hI.exists_inv (mt eq_zero_iff_mem.2 h) with ⟨b, c, hc, abc⟩
  -- ⊢ ∃ b, Quot.mk Setoid.r a * b = 1
  rw [mul_comm] at abc
  -- ⊢ ∃ b, Quot.mk Setoid.r a * b = 1
  refine' ⟨mk _ b, Quot.sound _⟩
  -- ⊢ Setoid.r ((fun x x_1 => x * x_1) a b) 1
  simp only [Submodule.quotientRel_r_def]
  -- ⊢ a * b - 1 ∈ I
  rw [← eq_sub_iff_add_eq'] at abc
  -- ⊢ a * b - 1 ∈ I
  rwa [abc, ← neg_mem_iff (G := R) (H := I), neg_sub] at hc
  -- 🎉 no goals
#align ideal.quotient.exists_inv Ideal.Quotient.exists_inv

open Classical

/-- The quotient by a maximal ideal is a group with zero. This is a `def` rather than `instance`,
since users will have computable inverses in some applications.

See note [reducible non-instances]. -/
@[reducible]
protected noncomputable def groupWithZero (I : Ideal R) [hI : I.IsMaximal] :
    GroupWithZero (R ⧸ I) :=
  { inv := fun a => if ha : a = 0 then 0 else Classical.choose (exists_inv ha)
    mul_inv_cancel := fun a (ha : a ≠ 0) =>
      show a * dite _ _ _ = _ by rw [dif_neg ha]; exact Classical.choose_spec (exists_inv ha)
                                 -- ⊢ a * choose (_ : ∃ b, a * b = 1) = 1
                                                  -- 🎉 no goals
    inv_zero := dif_pos rfl }
#align ideal.quotient.group_with_zero Ideal.Quotient.groupWithZero

/-- The quotient by a maximal ideal is a field. This is a `def` rather than `instance`, since users
will have computable inverses (and `qsmul`, `rat_cast`) in some applications.

See note [reducible non-instances]. -/
@[reducible]
protected noncomputable def field (I : Ideal R) [hI : I.IsMaximal] : Field (R ⧸ I) :=
  { Quotient.commRing I, Quotient.groupWithZero I with }
#align ideal.quotient.field Ideal.Quotient.field

/-- If the quotient by an ideal is a field, then the ideal is maximal. -/
theorem maximal_of_isField (I : Ideal R) (hqf : IsField (R ⧸ I)) : I.IsMaximal := by
  apply Ideal.isMaximal_iff.2
  -- ⊢ ¬1 ∈ I ∧ ∀ (J : Ideal R) (x : R), I ≤ J → ¬x ∈ I → x ∈ J → 1 ∈ J
  constructor
  -- ⊢ ¬1 ∈ I
  · intro h
    -- ⊢ False
    rcases hqf.exists_pair_ne with ⟨⟨x⟩, ⟨y⟩, hxy⟩
    -- ⊢ False
    exact hxy (Ideal.Quotient.eq.2 (mul_one (x - y) ▸ I.mul_mem_left _ h))
    -- 🎉 no goals
  · intro J x hIJ hxnI hxJ
    -- ⊢ 1 ∈ J
    rcases hqf.mul_inv_cancel (mt Ideal.Quotient.eq_zero_iff_mem.1 hxnI) with ⟨⟨y⟩, hy⟩
    -- ⊢ 1 ∈ J
    rw [← zero_add (1 : R), ← sub_self (x * y), sub_add]
    -- ⊢ x * y - (x * y - 1) ∈ J
    refine' J.sub_mem (J.mul_mem_right _ hxJ) (hIJ (Ideal.Quotient.eq.1 hy))
    -- 🎉 no goals
#align ideal.quotient.maximal_of_is_field Ideal.Quotient.maximal_of_isField

/-- The quotient of a ring by an ideal is a field iff the ideal is maximal. -/
theorem maximal_ideal_iff_isField_quotient (I : Ideal R) : I.IsMaximal ↔ IsField (R ⧸ I) :=
  ⟨fun h =>
    let _i := @Quotient.field _ _ I h
    Field.toIsField _,
    maximal_of_isField _⟩
#align ideal.quotient.maximal_ideal_iff_is_field_quotient Ideal.Quotient.maximal_ideal_iff_isField_quotient

variable [CommRing S]

/-- Given a ring homomorphism `f : R →+* S` sending all elements of an ideal to zero,
lift it to the quotient by this ideal. -/
def lift (I : Ideal R) (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) : R ⧸ I →+* S :=
  { QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom H with
    map_one' := f.map_one
    map_zero' := f.map_zero
    map_add' := fun a₁ a₂ => Quotient.inductionOn₂' a₁ a₂ f.map_add
    map_mul' := fun a₁ a₂ => Quotient.inductionOn₂' a₁ a₂ f.map_mul }
#align ideal.quotient.lift Ideal.Quotient.lift

@[simp]
theorem lift_mk (I : Ideal R) (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) :
    lift I f H (mk I a) = f a :=
  rfl
#align ideal.quotient.lift_mk Ideal.Quotient.lift_mk

theorem lift_surjective_of_surjective (I : Ideal R) {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hf : Function.Surjective f) : Function.Surjective (Ideal.Quotient.lift I f H) := by
  intro y
  -- ⊢ ∃ a, ↑(lift I f H) a = y
  obtain ⟨x, rfl⟩ := hf y
  -- ⊢ ∃ a, ↑(lift I f H) a = ↑f x
  use Ideal.Quotient.mk I x
  -- ⊢ ↑(lift I f H) (↑(mk I) x) = ↑f x
  simp only [Ideal.Quotient.lift_mk]
  -- 🎉 no goals
#align ideal.quotient.lift_surjective_of_surjective Ideal.Quotient.lift_surjective_of_surjective

/-- The ring homomorphism from the quotient by a smaller ideal to the quotient by a larger ideal.

This is the `Ideal.Quotient` version of `Quot.Factor` -/
def factor (S T : Ideal R) (H : S ≤ T) : R ⧸ S →+* R ⧸ T :=
  Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)
#align ideal.quotient.factor Ideal.Quotient.factor

@[simp]
theorem factor_mk (S T : Ideal R) (H : S ≤ T) (x : R) : factor S T H (mk S x) = mk T x :=
  rfl
#align ideal.quotient.factor_mk Ideal.Quotient.factor_mk

@[simp]
theorem factor_comp_mk (S T : Ideal R) (H : S ≤ T) : (factor S T H).comp (mk S) = mk T := by
  ext x
  -- ⊢ ↑(RingHom.comp (factor S T H) (mk S)) x = ↑(mk T) x
  rw [RingHom.comp_apply, factor_mk]
  -- 🎉 no goals
#align ideal.quotient.factor_comp_mk Ideal.Quotient.factor_comp_mk

end Quotient

/-- Quotienting by equal ideals gives equivalent rings.

See also `Submodule.quotEquivOfEq` and `Ideal.quotientEquivAlgOfEq`.
-/
def quotEquivOfEq {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  { Submodule.quotEquivOfEq I J h with
    map_mul' := by
      rintro ⟨x⟩ ⟨y⟩
      -- ⊢ Equiv.toFun { toFun := src✝.toFun, invFun := src✝.invFun, left_inv := (_ : F …
      rfl }
      -- 🎉 no goals
#align ideal.quot_equiv_of_eq Ideal.quotEquivOfEq

@[simp]
theorem quotEquivOfEq_mk {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) (x : R) :
    quotEquivOfEq h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl
#align ideal.quot_equiv_of_eq_mk Ideal.quotEquivOfEq_mk

@[simp]
theorem quotEquivOfEq_symm {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) :
    (Ideal.quotEquivOfEq h).symm = Ideal.quotEquivOfEq h.symm := by ext; rfl
                                                                    -- ⊢ ↑(RingEquiv.symm (quotEquivOfEq h)) x✝ = ↑(quotEquivOfEq (_ : J = I)) x✝
                                                                         -- 🎉 no goals
#align ideal.quot_equiv_of_eq_symm Ideal.quotEquivOfEq_symm

section Pi

variable (ι : Type v)

/-- `R^n/I^n` is a `R/I`-module. -/
instance modulePi : Module (R ⧸ I) ((ι → R) ⧸ I.pi ι) where
  smul c m :=
    Quotient.liftOn₂' c m (fun r m => Submodule.Quotient.mk <| r • m) $ by
      intro c₁ m₁ c₂ m₂ hc hm
      -- ⊢ (fun r m => Submodule.Quotient.mk (r • m)) c₁ m₁ = (fun r m => Submodule.Quo …
      apply Ideal.Quotient.eq.2
      -- ⊢ c₁ • m₁ - c₂ • m₂ ∈ pi I ι
      rw [Submodule.quotientRel_r_def] at hc hm
      -- ⊢ c₁ • m₁ - c₂ • m₂ ∈ pi I ι
      intro i
      -- ⊢ (c₁ • m₁ - c₂ • m₂) i ∈ I
      exact I.mul_sub_mul_mem hc (hm i)
      -- 🎉 no goals
  one_smul := by
    rintro ⟨a⟩
    -- ⊢ 1 • Quot.mk Setoid.r a = Quot.mk Setoid.r a
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    -- ⊢ ↑(Quotient.mk (pi I ι)) (1 • a) = ↑(Quotient.mk (pi I ι)) a
    congr with i; exact one_mul (a i)
    -- ⊢ (1 • a) i = a i
                  -- 🎉 no goals
  mul_smul := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    -- ⊢ (Quot.mk Setoid.r a * Quot.mk Setoid.r b) • Quot.mk Setoid.r c = Quot.mk Set …
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    -- ⊢ ↑(Quotient.mk (pi I ι)) ((fun x x_1 => x * x_1) a b • c) = ↑(Quotient.mk (pi …
    congr 1; funext i; exact mul_assoc a b (c i)
    -- ⊢ (fun x x_1 => x * x_1) a b • c = a • b • c
             -- ⊢ ((fun x x_1 => x * x_1) a b • c) i = (a • b • c) i
                       -- 🎉 no goals
  smul_add := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    -- ⊢ Quot.mk Setoid.r a • (Quot.mk Setoid.r b + Quot.mk Setoid.r c) = Quot.mk Set …
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    -- ⊢ ↑(Quotient.mk (pi I ι)) (a • (fun x x_1 => x + x_1) b c) = ↑(Quotient.mk (pi …
    congr with i; exact mul_add a (b i) (c i)
    -- ⊢ Quot.mk Setoid.r a • 0 = 0
    -- ⊢ (a • (fun x x_1 => x + x_1) b c) i = (fun x x_1 => x + x_1) (a • b) (a • c) i
    -- ⊢ ↑(Quotient.mk (pi I ι)) (a • 0) = ↑(Quotient.mk (pi I ι)) 0
                  -- 🎉 no goals
    -- ⊢ (a • 0) x✝ = OfNat.ofNat 0 x✝
                  -- 🎉 no goals
  smul_zero := by
    rintro ⟨a⟩
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    congr with _; exact mul_zero a
  add_smul := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    -- ⊢ (Quot.mk Setoid.r a + Quot.mk Setoid.r b) • Quot.mk Setoid.r c = Quot.mk Set …
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    -- ⊢ ↑(Quotient.mk (pi I ι)) ((fun x x_1 => x + x_1) a b • c) = ↑(Quotient.mk (pi …
    congr with i; exact add_mul a b (c i)
    -- ⊢ ((fun x x_1 => x + x_1) a b • c) i = (fun x x_1 => x + x_1) (a • c) (b • c) i
                  -- 🎉 no goals
  zero_smul := by
    rintro ⟨a⟩
    -- ⊢ 0 • Quot.mk Setoid.r a = 0
    convert_to Ideal.Quotient.mk (I.pi ι) _ = Ideal.Quotient.mk (I.pi ι) _
    -- ⊢ ↑(Quotient.mk (pi I ι)) (0 • a) = ↑(Quotient.mk (pi I ι)) 0
    congr with i; exact zero_mul (a i)
    -- ⊢ (0 • a) i = OfNat.ofNat 0 i
                  -- 🎉 no goals
#align ideal.module_pi Ideal.modulePi

/-- `R^n/I^n` is isomorphic to `(R/I)^n` as an `R/I`-module. -/
noncomputable def piQuotEquiv : ((ι → R) ⧸ I.pi ι) ≃ₗ[R ⧸ I] ι → (R ⧸ I) where
  toFun := fun x ↦
      Quotient.liftOn' x (fun f i => Ideal.Quotient.mk I (f i)) fun a b hab =>
        funext fun i => (Submodule.Quotient.eq' _).2 (QuotientAddGroup.leftRel_apply.mp hab i)
  map_add' := by rintro ⟨_⟩ ⟨_⟩; rfl
                 -- ⊢ (fun x => Quotient.liftOn' x (fun f i => ↑(Quotient.mk I) (f i)) (_ : ∀ (a b …
                                 -- 🎉 no goals
  map_smul' := by rintro ⟨_⟩ ⟨_⟩; rfl
                  -- ⊢ AddHom.toFun { toFun := fun x => Quotient.liftOn' x (fun f i => ↑(Quotient.m …
                                  -- 🎉 no goals
  invFun := fun x ↦ Ideal.Quotient.mk (I.pi ι) fun i ↦ Quotient.out' (x i)
  left_inv := by
    rintro ⟨x⟩
    -- ⊢ (fun x => ↑(Quotient.mk (pi I ι)) fun i => Quotient.out' (x i)) (AddHom.toFu …
    exact Ideal.Quotient.eq.2 fun i => Ideal.Quotient.eq.1 (Quotient.out_eq' _)
    -- 🎉 no goals
  right_inv := by
    intro x
    -- ⊢ AddHom.toFun { toAddHom := { toFun := fun x => Quotient.liftOn' x (fun f i = …
    ext i
    -- ⊢ AddHom.toFun { toAddHom := { toFun := fun x => Quotient.liftOn' x (fun f i = …
    obtain ⟨_, _⟩ := @Quot.exists_rep _ _ (x i)
    -- ⊢ AddHom.toFun { toAddHom := { toFun := fun x => Quotient.liftOn' x (fun f i = …
    convert Quotient.out_eq' (x i)
    -- 🎉 no goals
#align ideal.pi_quot_equiv Ideal.piQuotEquiv

/-- If `f : R^n → R^m` is an `R`-linear map and `I ⊆ R` is an ideal, then the image of `I^n` is
    contained in `I^m`. -/
theorem map_pi {ι : Type*} [Finite ι] {ι' : Type w} (x : ι → R) (hi : ∀ i, x i ∈ I)
    (f : (ι → R) →ₗ[R] ι' → R) (i : ι') : f x i ∈ I := by
  classical
    cases nonempty_fintype ι
    rw [pi_eq_sum_univ x]
    simp only [Finset.sum_apply, smul_eq_mul, LinearMap.map_sum, Pi.smul_apply, LinearMap.map_smul]
    exact I.sum_mem fun j _ => I.mul_mem_right _ (hi j)
#align ideal.map_pi Ideal.map_pi

end Pi

section ChineseRemainder

variable {ι : Type v}

theorem exists_sub_one_mem_and_mem (s : Finset ι) {f : ι → Ideal R}
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ⊔ f j = ⊤) (i : ι) (his : i ∈ s) :
    ∃ r : R, r - 1 ∈ f i ∧ ∀ j ∈ s, j ≠ i → r ∈ f j := by
  have : ∀ j ∈ s, j ≠ i → ∃ r : R, ∃ _ : r - 1 ∈ f i, r ∈ f j := by
    intro j hjs hji
    specialize hf i his j hjs hji.symm
    rw [eq_top_iff_one, Submodule.mem_sup] at hf
    rcases hf with ⟨r, hri, s, hsj, hrs⟩
    refine' ⟨1 - r, _, _⟩
    · rw [sub_right_comm, sub_self, zero_sub]
      exact (f i).neg_mem hri
    · rw [← hrs, add_sub_cancel']
      exact hsj
  classical
    have : ∃ g : ι → R, (∀ j, g j - 1 ∈ f i) ∧ ∀ j ∈ s, j ≠ i → g j ∈ f j := by
      choose g hg1 hg2 using this
      refine' ⟨fun j => if H : j ∈ s ∧ j ≠ i then g j H.1 H.2 else 1, fun j => _, fun j => _⟩
      · dsimp only
        split_ifs with h
        · apply hg1
        rw [sub_self]
        exact (f i).zero_mem
      · intro hjs hji
        dsimp only
        rw [dif_pos]
        · apply hg2
        exact ⟨hjs, hji⟩
    rcases this with ⟨g, hgi, hgj⟩
    use ∏ x in s.erase i, g x
    constructor
    · rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, map_one, map_prod]
      apply Finset.prod_eq_one
      intros
      rw [← RingHom.map_one, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      apply hgi
    · intro j hjs hji
      rw [← Quotient.eq_zero_iff_mem, map_prod]
      refine' Finset.prod_eq_zero (Finset.mem_erase_of_ne_of_mem hji hjs) _
      rw [Quotient.eq_zero_iff_mem]
      exact hgj j hjs hji
#align ideal.exists_sub_one_mem_and_mem Ideal.exists_sub_one_mem_and_mem

theorem exists_sub_mem [Finite ι] {f : ι → Ideal R} (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤)
    (g : ι → R) : ∃ r : R, ∀ i, r - g i ∈ f i := by
  cases nonempty_fintype ι
  -- ⊢ ∃ r, ∀ (i : ι), r - g i ∈ f i
  have : ∃ φ : ι → R, (∀ i, φ i - 1 ∈ f i) ∧ ∀ i j, i ≠ j → φ i ∈ f j := by
    have := exists_sub_one_mem_and_mem (Finset.univ : Finset ι) fun i _ j _ hij => hf i j hij
    choose φ hφ using this
    exists fun i => φ i (Finset.mem_univ i)
    exact ⟨fun i => (hφ i _).1, fun i j hij => (hφ i _).2 j (Finset.mem_univ j) hij.symm⟩
  rcases this with ⟨φ, hφ1, hφ2⟩
  -- ⊢ ∃ r, ∀ (i : ι), r - g i ∈ f i
  use ∑ i, g i * φ i
  -- ⊢ ∀ (i : ι), ∑ i : ι, g i * φ i - g i ∈ f i
  intro i
  -- ⊢ ∑ i : ι, g i * φ i - g i ∈ f i
  rw [← Quotient.mk_eq_mk_iff_sub_mem, map_sum]
  -- ⊢ ∑ x : ι, ↑(Quotient.mk (f i)) (g x * φ x) = ↑(Quotient.mk (f i)) (g i)
  refine' Eq.trans (Finset.sum_eq_single i _ _) _
  · intro j _ hji
    -- ⊢ ↑(Quotient.mk (f i)) (g j * φ j) = 0
    rw [Quotient.eq_zero_iff_mem]
    -- ⊢ g j * φ j ∈ f i
    exact (f i).mul_mem_left _ (hφ2 j i hji)
    -- 🎉 no goals
  · intro hi
    -- ⊢ ↑(Quotient.mk (f i)) (g i * φ i) = 0
    exact (hi <| Finset.mem_univ i).elim
    -- 🎉 no goals
  specialize hφ1 i
  -- ⊢ ↑(Quotient.mk (f i)) (g i * φ i) = ↑(Quotient.mk (f i)) (g i)
  rw [← Quotient.mk_eq_mk_iff_sub_mem, RingHom.map_one] at hφ1
  -- ⊢ ↑(Quotient.mk (f i)) (g i * φ i) = ↑(Quotient.mk (f i)) (g i)
  rw [RingHom.map_mul, hφ1, mul_one]
  -- 🎉 no goals
#align ideal.exists_sub_mem Ideal.exists_sub_mem

/-- The homomorphism from `R/(⋂ i, f i)` to `∏ i, (R / f i)` featured in the Chinese
  Remainder Theorem. It is bijective if the ideals `f i` are comaximal. -/
def quotientInfToPiQuotient (f : ι → Ideal R) : (R ⧸ ⨅ i, f i) →+* ∀ i, R ⧸ f i :=
  Quotient.lift (⨅ i, f i) (Pi.ringHom fun i : ι => (Quotient.mk (f i) : _)) fun r hr => by
    rw [Submodule.mem_iInf] at hr
    -- ⊢ ↑(Pi.ringHom fun i => Quotient.mk (f i)) r = 0
    ext i
    -- ⊢ ↑(Pi.ringHom fun i => Quotient.mk (f i)) r i = OfNat.ofNat 0 i
    exact Quotient.eq_zero_iff_mem.2 (hr i)
    -- 🎉 no goals
#align ideal.quotient_inf_to_pi_quotient Ideal.quotientInfToPiQuotient

theorem quotientInfToPiQuotient_bijective [Finite ι] {f : ι → Ideal R}
    (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) : Function.Bijective (quotientInfToPiQuotient f) :=
  ⟨fun x y =>
    Quotient.inductionOn₂' x y fun r s hrs =>
      Quotient.eq.2 <|
        (Submodule.mem_iInf _).2 fun i =>
          Quotient.eq.1 <|
            show quotientInfToPiQuotient f (Quotient.mk'' r) i = _ by rw [hrs]; rfl,
                                                                      -- ⊢ ↑(quotientInfToPiQuotient f) (Quotient.mk'' s) i = ↑(Quotient.mk (f i)) s
                                                                                -- 🎉 no goals
    fun g =>
    let ⟨r, hr⟩ := exists_sub_mem hf fun i => Quotient.out' (g i)
    ⟨Quotient.mk _ r, funext fun i => Quotient.out_eq' (g i) ▸ Quotient.eq.2 (hr i)⟩⟩
#align ideal.quotient_inf_to_pi_quotient_bijective Ideal.quotientInfToPiQuotient_bijective

/-- Chinese Remainder Theorem. Eisenbud Ex.2.6. Similar to Atiyah-Macdonald 1.10 and Stacks 00DT -/
noncomputable def quotientInfRingEquivPiQuotient [Finite ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) : (R ⧸ ⨅ i, f i) ≃+* ∀ i, R ⧸ f i :=
  { Equiv.ofBijective _ (quotientInfToPiQuotient_bijective hf), quotientInfToPiQuotient f with }
#align ideal.quotient_inf_ring_equiv_pi_quotient Ideal.quotientInfRingEquivPiQuotient

end ChineseRemainder

/-- **Chinese remainder theorem**, specialized to two ideals. -/
noncomputable def quotientInfEquivQuotientProd (I J : Ideal R) (coprime : I ⊔ J = ⊤) :
    R ⧸ I ⊓ J ≃+* (R ⧸ I) × R ⧸ J :=
  let f : Fin 2 → Ideal R := ![I, J]
  have hf : ∀ i j : Fin 2, i ≠ j → f i ⊔ f j = ⊤ := by
    intro i j h
    -- ⊢ f i ⊔ f j = ⊤
    fin_cases i <;> fin_cases j <;> try contradiction
    -- ⊢ f { val := 0, isLt := (_ : 0 < 2) } ⊔ f j = ⊤
                    -- ⊢ f { val := 0, isLt := (_ : 0 < 2) } ⊔ f { val := 0, isLt := (_ : 0 < 2) } = ⊤
                    -- ⊢ f { val := 1, isLt := (_ : (fun a => a < 2) 1) } ⊔ f { val := 0, isLt := (_  …
                                    -- 🎉 no goals
                                    -- ⊢ f { val := 0, isLt := (_ : 0 < 2) } ⊔ f { val := 1, isLt := (_ : (fun a => a …
                                    -- ⊢ f { val := 1, isLt := (_ : (fun a => a < 2) 1) } ⊔ f { val := 0, isLt := (_  …
                                    -- 🎉 no goals
    · assumption
      -- 🎉 no goals
    · rwa [sup_comm]
      -- 🎉 no goals
  (Ideal.quotEquivOfEq (by simp [iInf, inf_comm])).trans <|
                           -- 🎉 no goals
            (Ideal.quotientInfRingEquivPiQuotient f hf).trans <| RingEquiv.piFinTwo fun i => R ⧸ f i
#align ideal.quotient_inf_equiv_quotient_prod Ideal.quotientInfEquivQuotientProd

@[simp]
theorem quotientInfEquivQuotientProd_fst (I J : Ideal R) (coprime : I ⊔ J = ⊤) (x : R ⧸ I ⊓ J) :
    (quotientInfEquivQuotientProd I J coprime x).fst =
      Ideal.Quotient.factor (I ⊓ J) I inf_le_left x :=
  Quot.inductionOn x fun _ => rfl
#align ideal.quotient_inf_equiv_quotient_prod_fst Ideal.quotientInfEquivQuotientProd_fst

@[simp]
theorem quotientInfEquivQuotientProd_snd (I J : Ideal R) (coprime : I ⊔ J = ⊤) (x : R ⧸ I ⊓ J) :
    (quotientInfEquivQuotientProd I J coprime x).snd =
      Ideal.Quotient.factor (I ⊓ J) J inf_le_right x :=
  Quot.inductionOn x fun _ => rfl
#align ideal.quotient_inf_equiv_quotient_prod_snd Ideal.quotientInfEquivQuotientProd_snd

@[simp]
theorem fst_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : I ⊔ J = ⊤) :
    (RingHom.fst _ _).comp
        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor (I ⊓ J) I inf_le_left := by
  apply Quotient.ringHom_ext; ext; rfl
  -- ⊢ RingHom.comp (RingHom.comp (RingHom.fst (R ⧸ I) (R ⧸ J)) ↑(quotientInfEquivQ …
                              -- ⊢ ↑(RingHom.comp (RingHom.comp (RingHom.fst (R ⧸ I) (R ⧸ J)) ↑(quotientInfEqui …
                                   -- 🎉 no goals
#align ideal.fst_comp_quotient_inf_equiv_quotient_prod Ideal.fst_comp_quotientInfEquivQuotientProd

@[simp]
theorem snd_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : I ⊔ J = ⊤) :
    (RingHom.snd _ _).comp
        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J →+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor (I ⊓ J) J inf_le_right := by
  apply Quotient.ringHom_ext; ext; rfl
  -- ⊢ RingHom.comp (RingHom.comp (RingHom.snd (R ⧸ I) (R ⧸ J)) ↑(quotientInfEquivQ …
                              -- ⊢ ↑(RingHom.comp (RingHom.comp (RingHom.snd (R ⧸ I) (R ⧸ J)) ↑(quotientInfEqui …
                                   -- 🎉 no goals
#align ideal.snd_comp_quotient_inf_equiv_quotient_prod Ideal.snd_comp_quotientInfEquivQuotientProd

end Ideal
