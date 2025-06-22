/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen
-/
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Congruence.Defs
import Mathlib.RingTheory.Ideal.Defs

/-!
# Ideal quotients

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `Algebra.RingQuot` for quotients of non-commutative rings.

## Main definitions

- `Ideal.instHasQuotient`: the quotient of a commutative ring `R` by an ideal `I : Ideal R`
- `Ideal.Quotient.commRing`: the ring structure of the ideal quotient
- `Ideal.Quotient.mk`: map an element of `R` to the quotient `R ⧸ I`
- `Ideal.Quotient.lift`: turn a map `R → S` into a map `R ⧸ I → S`
- `Ideal.quotEquivOfEq`: quotienting by equal ideals gives isomorphic rings
-/


universe u v w

namespace Ideal

open Set

variable {R : Type u} [Ring R] (I J : Ideal R) {a b : R}
variable {S : Type v}

/-- The quotient `R/I` of a ring `R` by an ideal `I`,
defined to equal the quotient of `I` as an `R`-submodule of `R`. -/
instance instHasQuotient : HasQuotient R (Ideal R) := Submodule.hasQuotient

/-- Shortcut instance for commutative rings. -/
instance {R} [CommRing R] : HasQuotient R (Ideal R) := inferInstance

namespace Quotient

variable {I} {x y : R}

instance one (I : Ideal R) : One (R ⧸ I) :=
  ⟨Submodule.Quotient.mk 1⟩

/-- On `Ideal`s, `Submodule.quotientRel` is a ring congruence. -/
protected def ringCon (I : Ideal R) [I.IsTwoSided] : RingCon R where
  __ := QuotientAddGroup.con I.toAddSubgroup
  mul' {a₁ b₁ a₂ b₂} h₁ h₂ := by
    rw [Submodule.quotientRel_def] at h₁ h₂ ⊢
    exact mul_sub_mul_mem I h₁ h₂

instance ring (I : Ideal R) [I.IsTwoSided] : Ring (R ⧸ I) := fast_instance%
  { __ : AddCommGroup (R ⧸ I) := inferInstance
    __ : Ring (Quotient.ringCon I).Quotient := inferInstance }

instance commRing {R} [CommRing R] (I : Ideal R) : CommRing (R ⧸ I) := fast_instance%
  { mul_comm := by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (mul_comm a b) }

instance {R} [CommRing R] (I : Ideal R) : Ring (R ⧸ I) := fast_instance% inferInstance
instance commSemiring {R} [CommRing R] (I : Ideal R) : CommSemiring (R ⧸ I) := fast_instance%
  inferInstance
instance semiring {R} [CommRing R] (I : Ideal R) : Semiring (R ⧸ I) := fast_instance% inferInstance

variable [I.IsTwoSided]

-- Sanity test to make sure no diamonds have emerged in `commRing`
example : (ring I).toAddCommGroup = Submodule.Quotient.addCommGroup I := rfl

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
  RingHom.ext fun x => Quotient.inductionOn' x <| (RingHom.congr_fun h :)

instance : Nonempty (R ⧸ I) :=
  ⟨mk I 37⟩

protected theorem eq : mk I x = mk I y ↔ x - y ∈ I :=
  Submodule.Quotient.eq I

@[simp]
theorem mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R ⧸ I) = mk I x := rfl

theorem eq_zero_iff_mem : mk I a = 0 ↔ a ∈ I :=
  Submodule.Quotient.mk_eq_zero _

theorem mk_eq_mk_iff_sub_mem (x y : R) : mk I x = mk I y ↔ x - y ∈ I := by
  rw [← eq_zero_iff_mem, map_sub, sub_eq_zero]

@[simp]
theorem mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotient.out x) = x :=
  Quotient.out_eq x

theorem mk_surjective : Function.Surjective (mk I) := fun y =>
  Quotient.inductionOn' y fun x => Exists.intro x rfl

instance : RingHomSurjective (mk I) :=
  ⟨mk_surjective⟩

/-- If `I` is an ideal of a commutative ring `R`, if `q : R → R/I` is the quotient map, and if
`s ⊆ R` is a subset, then `q⁻¹(q(s)) = ⋃ᵢ(i + s)`, the union running over all `i ∈ I`. -/
theorem quotient_ring_saturate (s : Set R) :
    mk I ⁻¹' (mk I '' s) = ⋃ x : I, (fun y => x.1 + y) '' s := by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion, Ideal.Quotient.eq]
  exact
    ⟨fun ⟨a, a_in, h⟩ => ⟨⟨_, I.neg_mem h⟩, a, a_in, by simp⟩, fun ⟨⟨i, hi⟩, a, ha, Eq⟩ =>
      ⟨a, ha, by rw [← Eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub]; exact I.neg_mem hi⟩⟩

variable [Semiring S] (I)

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

lemma lift_comp_mk (f : R →+* S) (H : ∀ a : R, a ∈ I → f a = 0) :
    (lift I f H).comp (mk I) = f := rfl

theorem lift_surjective_of_surjective {f : R →+* S} (H : ∀ a : R, a ∈ I → f a = 0)
    (hf : Function.Surjective f) : Function.Surjective (Ideal.Quotient.lift I f H) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  use Ideal.Quotient.mk I x
  simp only [Ideal.Quotient.lift_mk]

variable {S T U : Ideal R} [S.IsTwoSided] [T.IsTwoSided] [U.IsTwoSided]

/-- The ring homomorphism from the quotient by a smaller ideal to the quotient by a larger ideal.

This is the `Ideal.Quotient` version of `Quot.Factor`

When the two ideals are of the form `I^m` and `I^n` and `n ≤ m`,
please refer to the dedicated version `Ideal.Quotient.factorPow`. -/
def factor (H : S ≤ T) : R ⧸ S →+* R ⧸ T :=
  Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)

@[simp]
theorem factor_mk (H : S ≤ T) (x : R) : factor H (mk S x) = mk T x :=
  rfl

@[simp]
theorem factor_eq : factor (le_refl S) = RingHom.id _ := by
  ext
  simp

@[simp]
theorem factor_comp_mk (H : S ≤ T) : (factor H).comp (mk S) = mk T := by
  ext x
  rw [RingHom.comp_apply, factor_mk]

@[simp]
theorem factor_comp (H1 : S ≤ T) (H2 : T ≤ U) :
    (factor H2).comp (factor H1) = factor (H1.trans H2) := by
  ext
  simp

@[simp]
theorem factor_comp_apply (H1 : S ≤ T) (H2 : T ≤ U) (x : R ⧸ S) :
    factor H2 (factor H1 x) = factor (H1.trans H2) x := by
  rw [← RingHom.comp_apply]
  simp

lemma factor_surjective (H : S ≤ T) : Function.Surjective (factor H) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _ Ideal.Quotient.mk_surjective

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

end Ideal
