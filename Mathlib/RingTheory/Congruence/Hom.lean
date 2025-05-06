/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.GroupTheory.Congruence.Hom

/-!
# Congruence relations and homomorphisms

This file contains elementary definitions involving congruence relations and morphisms.

## Main definitions

 * `RingCon.ker`: the kernel of a ring homomorphism as a congruence relation
 * `RingCon.mk'`: the map from a ring to its quotient by a congruence relation
 * `RingCon.lift`: the homomorphism on the quotient given that the congruence is in the kernel
 * `RingCon.map`: homomorphism from a smaller to a larger quotient

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, ring,
quotient ring
-/


variable (R : Type*) {N : Type*} {P : Type*} {F : Type*}

open Function Setoid

variable {R}

namespace RingCon

section Semiring

variable [NonAssocSemiring R] [NonAssocSemiring N] [NonAssocSemiring P] {c : RingCon R}
variable [FunLike F R P] [RingHomClass F R P]

/-- The kernel of a ring homomorphism as a congruence relation. -/
def ker (f : F) : RingCon R where
  __ := Con.ker f
  __ := AddCon.ker f

@[norm_cast]
theorem ker_coeRingHom (f : F) : ker (f : R →+*P) = ker f := rfl

/-- The definition of the congruence relation defined by a ring homomorphism's kernel. -/
theorem ker_rel (f : F) {x y} : ker f x y ↔ f x = f y :=
  Iff.rfl

variable (c)

/-- The natural homomorphism from a ring to its quotient by a congruence relation. -/
def mk' [NonAssocSemiring R] (c : RingCon R) : R →+* c.Quotient where
  toFun := toQuotient
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

variable (x y : R)

/-- The kernel of the natural homomorphism from a ring to its quotient by a congruence
relation `c` equals `c`. -/
theorem mk'_ker : ker c.mk' = c :=
  ext fun _ _ => c.eq

variable {c}

/-- The natural homomorphism from a ring to its quotient by a congruence relation is
surjective. -/
theorem mk'_surjective : Surjective c.mk' :=
  Quotient.mk''_surjective

theorem coe_mk' : (c.mk' : R → c.Quotient) = ((↑) : R → c.Quotient) :=
  rfl

theorem ker_apply {f : R →+* P} {x y} : ker f x y ↔ f x = f y := Iff.rfl

/-- Given a ring homomorphism `f : N → R` and a congruence relation `c` on `R`, the congruence
relation induced on `N` by `f` equals the kernel of `c`'s quotient homomorphism composed with
`f`. -/
theorem comap_eq {f : N →+* R} : comap c f = ker (c.mk'.comp f) :=
  ext fun x y => show c _ _ ↔ c.mk' _ = c.mk' _ by rw [← c.eq]; rfl

variable (c) (f : R →+* P)

/-- The homomorphism on the quotient of a ring by a congruence relation `c` induced by a
homomorphism constant on `c`'s equivalence classes. -/
def lift (H : c ≤ ker f) : c.Quotient →+* P where
  toFun x := (RingCon.liftOn x f) fun _ _ h => H h
  map_zero' := by rw [← f.map_zero]; rfl
  map_one' := by rw [← f.map_one]; rfl
  map_add' x y := Quotient.inductionOn₂ x y fun m n => by simp [← coe_add]
  map_mul' x y := Quotient.inductionOn₂ x y fun m n => by simp [← coe_mul]

variable {c f}

/-- The diagram describing the universal property for quotients of rings commutes. -/
theorem lift_mk' (H : c ≤ ker f) (x) : c.lift f H (c.mk' x) = f x :=
  rfl

/-- The diagram describing the universal property for quotients of rings commutes. -/
theorem lift_coe (H : c ≤ ker f) (x : R) : c.lift f H x = f x :=
  rfl

/-- The diagram describing the universal property for quotients of rings commutes. -/
theorem lift_comp_mk' (H : c ≤ ker f) : (c.lift f H).comp c.mk' = f := by ext; rfl

/-- Given a homomorphism `f` from the quotient of a ring by a congruence relation, `f` equals the
homomorphism on the quotient induced by `f` composed with the natural map from the ring to
the quotient. -/
theorem lift_apply_mk' (f : c.Quotient →+* P) :
    (c.lift (f.comp c.mk') fun x y h => show f ↑x = f ↑y by rw [c.eq.2 h]) = f := by
  ext x; rcases x with ⟨⟩; rfl

/-- Homomorphisms on the quotient of a ring by a congruence relation are equal if they
are equal on elements that are coercions from the ring. -/
theorem lift_funext (f g : c.Quotient →+* P) (h : ∀ a : R, f a = g a) : f = g := by
  rw [← lift_apply_mk' f, ← lift_apply_mk' g]
  congr 1
  exact DFunLike.ext_iff.2 h

/-- The uniqueness part of the universal property for quotients of rings. -/
theorem lift_unique (H : c ≤ ker f) (g : c.Quotient →+* P) (Hg : g.comp c.mk' = f) :
    g = c.lift f H :=
  (lift_funext g (c.lift f H)) fun x => by
    subst f
    rfl

/-- Surjective ring homomorphisms constant on a congruence relation `c`'s equivalence classes
induce a surjective homomorphism on `c`'s quotient. -/
theorem lift_surjective_of_surjective (h : c ≤ ker f) (hf : Surjective f) :
    Surjective (c.lift f h) := fun y =>
  (Exists.elim (hf y)) fun w hw => ⟨w, (lift_mk' h w).symm ▸ hw⟩

variable (c f)

/-- Given a ring homomorphism `f` from `R` to `P`, the kernel of `f` is the unique congruence
relation on `R` whose induced map from the quotient of `R` to `P` is injective. -/
theorem ker_eq_lift_of_injective (H : c ≤ ker f) (h : Injective (c.lift f H)) : ker f = c :=
  toCon_injective <| Con.toSetoid_inj <| Setoid.ker_eq_lift_of_injective f H h

variable {c}

/-- The homomorphism induced on the quotient of a ring by the kernel of a ring homomorphism. -/
def kerLift : (ker f).Quotient →+* P :=
  ((ker f).lift f) fun _ _ => id

variable {f}

/-- The diagram described by the universal property for quotients of rings, when the congruence
relation is the kernel of the homomorphism, commutes. -/
theorem kerLift_mk (x : R) : kerLift f x = f x :=
  rfl

/-- A ring homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
theorem kerLift_injective (f : R →+* P) : Injective (kerLift f) := fun x y =>
  Quotient.inductionOn₂' x y fun _ _ => (ker f).eq.2

/-- Given congruence relations `c, d` on a ring such that `d` contains `c`, `d`'s quotient
map induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
def map (c d : RingCon R) (h : c ≤ d) : c.Quotient →+* d.Quotient :=
  (c.lift d.mk') fun x y hc => show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc

/-- Given congruence relations `c, d` on a ring such that `d` contains `c`, the definition of
the homomorphism from the quotient by `c` to the quotient by `d` induced by `d`'s quotient
map. -/
theorem map_apply {c d : RingCon R} (h : c ≤ d) (x) :
    c.map d h x = c.lift d.mk' (fun _ _ hc => d.eq.2 <| h hc) x :=
  rfl

end Semiring

end RingCon
