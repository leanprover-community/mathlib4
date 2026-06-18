/-
Copyright (c) 2025 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.WithOne.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Maps

/-!
# Grothendieck group

The Grothendieck group of a commutative semigroup `S` is the "smallest" commutative group `G`
containing `S`, in the sense that mul homs `S →ₙ* H` are in bijection with group homs `G →* H`
for any commutative group `H`.

Note that "Grothendieck group" also refers to the analogous construction in an abelian category
obtained by formally making the last term of each short exact sequence invertible.

### References

* [*Grothendieck group*, Wikipedia](https://en.wikipedia.org/wiki/Grothendieck_group#Grothendieck_group_of_a_commutative_monoid)
-/

@[expose] public section

open Function Localization

namespace Algebra
variable {S G : Type*} [CommSemigroup S] [CommGroup G]

variable (S) in
/-- The Grothendieck group of a semigroup `S` is the localization at its top submonoid, after
adjoining one. -/
@[to_additive
/-- The Grothendieck group of an additive semigroup `S` is the localization at its top
submonoid, after adjoining zero. -/]
abbrev GrothendieckGroup : Type _ := Localization (⊤ : Submonoid (WithOne S))

namespace GrothendieckGroup

/-- The inclusion from a commutative semigroup `S` to its Grothendieck group.

Note that this is only injective if `S` is cancellative. -/
@[to_additive
/-- The inclusion from an additive commutative semigroup `S` to its Grothendieck group.

Note that this is only injective if `S` is cancellative. -/]
def of : S →ₙ* GrothendieckGroup S := WithOne.lift.symm (monoidOf ⊤).toMonoidHom

@[to_additive]
lemma of_injective [IsCancelMul S] : Injective (of (S := S)) := fun _ _ h ↦ by
  simp only [of, WithOne.lift_symm_apply, Submonoid.LocalizationMap.toMonoidHom_apply,
    ← mk_one_eq_monoidOf_mk, mk_eq_mk_iff, r_iff_exists, OneMemClass.coe_one, one_mul,
    Subtype.exists, Submonoid.mem_top, exists_const] at h
  obtain ⟨c, hc⟩ := h
  induction c <;>
  simpa [← WithOne.coe_mul] using hc

@[to_additive]
instance : Inv (GrothendieckGroup S) where
  inv := rec (fun m s ↦ (.mk s ⟨m, Subsemigroup.mem_top m⟩ : GrothendieckGroup S))
    fun {m₁ m₂ s₁ s₂} h ↦ by simpa [r_iff_exists, mk_eq_mk_iff, eq_comm, mul_comm] using h

@[to_additive (attr := simp)]
lemma inv_mk_coe (m : S) (s : (⊤ : Submonoid (WithOne S))) :
    (mk (m : WithOne S) s)⁻¹ = .mk s ⟨m, Submonoid.mem_top _⟩ := rfl

@[to_additive (attr := simp)]
lemma inv_one (s : (⊤ : Submonoid (WithOne S))) :
    (mk (1 : WithOne S) s)⁻¹ = .mk s 1 := rfl

@[to_additive (attr := simp)]
lemma of_one {M : Type*} [CommMonoid M] : of (1 : M) = 1 := by
  simp only [of, WithOne.lift_symm_apply, Submonoid.LocalizationMap.toMonoidHom_apply]
  rw [← @mk_one_eq_monoidOf_mk, ← mk_one, mk_eq_mk_iff, r_iff_exists]
  simp only [OneMemClass.coe_one, one_mul, mul_one, Subtype.exists, Submonoid.mem_top, exists_const]
  use (1 : M)
  simp [← WithOne.coe_mul]

/-- The Grothendieck group is a group. -/
@[to_additive /-- The Grothendieck group is a group. -/]
instance instCommGroup : CommGroup (GrothendieckGroup S) where
  __ : CommMonoid (GrothendieckGroup S) := inferInstance
  inv_mul_cancel a := by
    induction a using ind with
    | H s =>
      rcases s with ⟨m, s⟩
      induction m
      · simp only [inv_one]
        rw [mk_eq_monoidOf_mk'_apply, mk_eq_monoidOf_mk'_apply, ← Submonoid.LocalizationMap.mk'_mul]
        simp
      · simp only [inv_mk_coe]
        rw [mk_eq_monoidOf_mk'_apply, mk_eq_monoidOf_mk'_apply, ← Submonoid.LocalizationMap.mk'_mul]
        convert! Submonoid.LocalizationMap.mk'_self' _ _
        simp [mul_comm]

@[to_additive (attr := simp)]
lemma mk_coe_div_mk_coe (m₁ m₂ : S) (s₁ s₂ : (⊤ : Submonoid (WithOne S))) :
    mk (m₁ : WithOne S) s₁ / mk (m₂ : WithOne S) s₂ =
      .mk (m₁ * s₂) ⟨s₁ * m₂, Submonoid.mem_top _⟩ := by
  simp [div_eq_mul_inv, mk_mul]; rfl

@[to_additive (attr := elab_as_elim, induction_eliminator, cases_eliminator)]
theorem ind [Nonempty S] {p : GrothendieckGroup S → Prop}
    (hof : ∀ s : S, p (of s)) (hinv : ∀ s : S, p (of s)⁻¹) (hdiv : ∀ s t : S, p (of s / of t))
    (x) : p x := by
  rcases eq_or_ne x 1 with (rfl | hx)
  · simpa using hdiv (Classical.arbitrary S) (Classical.arbitrary S)
  obtain ⟨⟨s, t, ht⟩, h⟩ := (monoidOf ⊤).surj x
  rw [eq_comm, ← div_eq_iff_eq_mul] at h
  subst h
  induction s <;> induction t
  · simp at hx
  · simpa [of] using hinv _
  · simpa [of] using hof _
  · simpa [of] using hdiv _ _

/-- Over a nonempty semigroup, every element of the Grothendieck group is either of the form
`of s`, `(of s)⁻¹`, or `of s / of t`. -/
@[to_additive /-- Over a nonempty additive semigroup, every element of the additive Grothendieck
group is either of the form `of s`, `-(of s)`, or `of s - of t`. -/]
lemma surjₙ [Nonempty S] (x : GrothendieckGroup S) :
    ∃ s : S, x = of s ∨ x = (of s)⁻¹ ∨ ∃ t, x = of s / of t := by
  induction x <;> grind

/-- Over a monoid, every element of the Grothendieck group is of the form `of s / of t`. -/
@[to_additive
/-- Over a nonempty additive monoid, every element of the additive Grothendieck group is of the form
`of s - of t`. -/]
lemma surj {M : Type*} [CommMonoid M] (x : GrothendieckGroup M) :
    ∃ s t : M, x = of s / of t := by
  obtain ⟨s, rfl | rfl | hs⟩ := surjₙ x
  · use s, 1
    simp
  · use 1, s
    simp
  · use s

/-- A monoid homomorphism from a monoid formed by `WithOne S` to a group `G` lifts to a
group homomorphism from the Grothendieck group of `S` to `G`. -/
 @[to_additive (attr := simps symm_apply)]
noncomputable def liftWithOne : (WithOne S →* G) ≃ (GrothendieckGroup S →* G) where
  toFun f := (monoidOf ⊤).lift (g := f) fun _ ↦ Group.isUnit _
  invFun f := f.comp (monoidOf ⊤).toMonoidHom
  left_inv f := by ext; simp only [Submonoid.LocalizationMap.lift_comp]
  right_inv f := by ext; simp only [Submonoid.LocalizationMap.lift_of_comp]

/-- A mul homomorphism from a semigroup `S` to a group `G` lifts to a group homomorphism from the
Grothendieck group of `S` to `G`. -/
@[to_additive (attr := simps! symm_apply)
/-- A add homomorphism from an additive semigroup `S` to an additive group `G` lifts to an
additive group homomorphism from the additive Grothendieck group of `S` to `G`. -/]
noncomputable def lift : (S →ₙ* G) ≃ (GrothendieckGroup S →* G) :=
  WithOne.lift.trans liftWithOne

@[to_additive (attr := simp)]
lemma lift_of (f : S →ₙ* G) (s : S) : lift f (of s) = f s := by
  simp [lift, liftWithOne, of]

/-- The Grothendieck group of a group is isomorphic to the group itself. -/
@[to_additive
 /-- The Grothendieck group of an additive group is isomorphic to the group itself. -/]
noncomputable def groupMulEquiv : GrothendieckGroup G ≃* G :=
  (lift (MulHom.id G)).toMulHom.toMulEquiv of (by
    ext x
    simp only [MulHom.coe_comp, MulHom.coe_mk, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      comp_apply, MulHom.id_apply]
    induction x <;> simp)
    (by ext; simp)

end Algebra.GrothendieckGroup
