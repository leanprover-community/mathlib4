/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.GroupTheory.Congruence.Defs

/-!
# Congruence relations and homomorphisms

This file contains elementary definitions involving congruence relations and morphisms.

## Main definitions

* `Con.ker`: the kernel of a monoid homomorphism as a congruence relation
* `Con.mk'`: the map from a monoid to its quotient by a congruence relation
* `Con.lift`: the homomorphism on the quotient given that the congruence is in the kernel
* `Con.map`: homomorphism from a smaller to a larger quotient

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid
-/


variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

variable {M}

namespace Con

section Mul
variable {F} [Mul M] [Mul N] [Mul P] [FunLike F M N] [MulHomClass F M N]


/-- The natural homomorphism from a magma to its quotient by a congruence relation. -/
@[to_additive (attr := simps) /-- The natural homomorphism from an additive magma to its quotient by
an additive congruence relation. -/]
def mkMulHom (c : Con M) : MulHom M c.Quotient where
  toFun := (↑)
  map_mul' _ _ := rfl
/-- The kernel of a multiplicative homomorphism as a congruence relation. -/
@[to_additive /-- The kernel of an additive homomorphism as an additive congruence relation. -/]
def ker (f : F) : Con M where
  toSetoid := Setoid.ker f
  mul' h1 h2 := by
    dsimp [Setoid.ker, onFun] at *
    rw [map_mul, h1, h2, map_mul]

@[to_additive (attr := norm_cast)]
theorem ker_coeMulHom (f : F) : ker (f : MulHom M N) = ker f := rfl

/-- The definition of the congruence relation defined by a monoid homomorphism's kernel. -/
@[to_additive (attr := simp) /-- The definition of the additive congruence relation defined by an
`AddMonoid` homomorphism's kernel. -/]
theorem ker_rel (f : F) {x y} : ker f x y ↔ f x = f y :=
  Iff.rfl

@[to_additive (attr := simp) /-- The kernel of the quotient map induced by an additive congruence
relation `c` equals `c`. -/]
theorem ker_mkMulHom_eq (c : Con M) : ker (mkMulHom c) = c :=
  ext fun _ _ => Quotient.eq''

/-- Given a function `f`, the smallest congruence relation containing the binary relation on `f`'s
image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)`
by a congruence relation `c`.' -/
@[to_additive /-- Given a function `f`, the smallest additive congruence relation containing the
binary relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the
elements of `f⁻¹(y)` by an additive congruence relation `c`.' -/]
def mapGen {c : Con M} (f : M → N) : Con N :=
  conGen <| Relation.Map c f f

/-- Given a surjective multiplicative-preserving function `f` whose kernel is contained in a
congruence relation `c`, the congruence relation on `f`'s codomain defined by '`x ≈ y` iff the
elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/
@[to_additive /-- Given a surjective addition-preserving function `f` whose kernel is contained in
an additive congruence relation `c`, the additive congruence relation on `f`'s codomain defined
by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/]
def mapOfSurjective {c : Con M} (f : F) (h : ker f ≤ c) (hf : Surjective f) : Con N where
  __ := c.toSetoid.mapOfSurjective f h hf
  mul' h₁ h₂ := by
    rcases h₁ with ⟨a, b, h1, rfl, rfl⟩
    rcases h₂ with ⟨p, q, h2, rfl, rfl⟩
    exact ⟨a * p, b * q, c.mul h1 h2, map_mul f _ _, map_mul f _ _⟩

/-- A specialization of 'the smallest congruence relation containing a congruence relation `c`
equals `c`'. -/
@[to_additive /-- A specialization of 'the smallest additive congruence relation containing
an additive congruence relation `c` equals `c`'. -/]
theorem mapOfSurjective_eq_mapGen {c : Con M} {f : F} (h : ker f ≤ c) (hf : Surjective f) :
    c.mapGen f = c.mapOfSurjective f h hf := by
  rw [← conGen_of_con (c.mapOfSurjective f h hf)]; rfl

/-- Given a congruence relation `c` on a type `M` with a multiplication, the order-preserving
bijection between the set of congruence relations containing `c` and the congruence relations
on the quotient of `M` by `c`. -/
@[to_additive /-- Given an additive congruence relation `c` on a type `M` with an addition,
the order-preserving bijection between the set of additive congruence relations containing `c` and
the additive congruence relations on the quotient of `M` by `c`. -/]
def correspondence {c : Con M} : { d // c ≤ d } ≃o Con c.Quotient where
  toFun d :=
    d.1.mapOfSurjective (mkMulHom c) (by rw [Con.ker_mkMulHom_eq]; exact d.2) <|
      Quotient.mk_surjective
  invFun d :=
    ⟨comap ((↑) : M → c.Quotient) (fun _ _ => rfl) d, fun x y h =>
      show d x y by rw [c.eq.2 h]; exact d.refl _⟩
  left_inv d :=
    Subtype.ext_iff.2 <|
      ext fun x y =>
        ⟨fun ⟨a, b, H, hx, hy⟩ =>
          d.1.trans (d.1.symm <| d.2 <| c.eq.1 hx) <| d.1.trans H <| d.2 <| c.eq.1 hy,
          fun h => ⟨_, _, h, rfl, rfl⟩⟩
  right_inv d :=
    ext fun x y =>
      ⟨fun ⟨_, _, H, hx, hy⟩ =>
        hx ▸ hy ▸ H,
        Con.induction_on₂ x y fun w z h => ⟨w, z, h, rfl, rfl⟩⟩
  map_rel_iff' {s t} := by
    constructor
    · intro h x y hs
      rcases h ⟨x, y, hs, rfl, rfl⟩ with ⟨a, b, ht, hx, hy⟩
      exact t.1.trans (t.1.symm <| t.2 <| c.eq.1 hx) (t.1.trans ht (t.2 <| c.eq.1 hy))
    · exact Relation.map_mono

end Mul

section MulOneClass

variable [MulOneClass M] [MulOneClass N] [MulOneClass P] {c : Con M}

variable (c)

/-- The natural homomorphism from a monoid to its quotient by a congruence relation. -/
@[to_additive /-- The natural homomorphism from an `AddMonoid` to its quotient by an additive
congruence relation. -/]
def mk' : M →* c.Quotient where
  __ := mkMulHom c
  map_one' := rfl

variable (x y : M)

/-- The kernel of the natural homomorphism from a monoid to its quotient by a congruence
relation `c` equals `c`. -/
@[to_additive (attr := simp) /-- The kernel of the natural homomorphism from an `AddMonoid` to its
quotient by an additive congruence relation `c` equals `c`. -/]
theorem mk'_ker : ker c.mk' = c :=
  ext fun _ _ => c.eq

variable {c}

/-- The natural homomorphism from a monoid to its quotient by a congruence relation is
surjective. -/
@[to_additive /-- The natural homomorphism from an `AddMonoid` to its quotient by a congruence
relation is surjective. -/]
theorem mk'_surjective : Surjective c.mk' :=
  Quotient.mk''_surjective

@[to_additive (attr := simp)]
theorem coe_mk' : (c.mk' : M → c.Quotient) = ((↑) : M → c.Quotient) :=
  rfl

@[to_additive]
theorem ker_apply {f : M →* P} {x y} : ker f x y ↔ f x = f y := Iff.rfl

/-- Given a monoid homomorphism `f : N → M` and a congruence relation `c` on `M`, the congruence
relation induced on `N` by `f` equals the kernel of `c`'s quotient homomorphism composed with
`f`. -/
@[to_additive /-- Given an `AddMonoid` homomorphism `f : N → M` and an additive congruence relation
`c` on `M`, the additive congruence relation induced on `N` by `f` equals the kernel of `c`'s
quotient homomorphism composed with `f`. -/]
theorem comap_eq {f : N →* M} : comap f f.map_mul c = ker (c.mk'.comp f) :=
  ext fun x y => show c _ _ ↔ c.mk' _ = c.mk' _ by rw [← c.eq]; rfl

variable (c) (f : M →* P)

/-- The homomorphism on the quotient of a monoid by a congruence relation `c` induced by a
homomorphism constant on `c`'s equivalence classes. -/
@[to_additive /-- The homomorphism on the quotient of an `AddMonoid` by an additive congruence
relation `c` induced by a homomorphism constant on `c`'s equivalence classes. -/]
def lift (H : c ≤ ker f) : c.Quotient →* P where
  toFun x := (Con.liftOn x f) fun _ _ h => H h
  map_one' := by rw [← f.map_one]; rfl
  map_mul' x y := Con.induction_on₂ x y fun m n => by
    dsimp only [← coe_mul, Con.liftOn_coe]
    rw [map_mul]

variable {c f}

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive /-- The diagram describing the universal property for quotients of `AddMonoid`s
commutes. -/]
theorem lift_mk' (H : c ≤ ker f) (x) : c.lift f H (c.mk' x) = f x :=
  rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive (attr := simp) /-- The diagram describing the universal property for quotients of
`AddMonoid`s commutes. -/]
theorem lift_coe (H : c ≤ ker f) (x : M) : c.lift f H x = f x :=
  rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[to_additive (attr := simp) /-- The diagram describing the universal property for quotients of
`AddMonoid`s commutes. -/]
theorem lift_comp_mk' (H : c ≤ ker f) : (c.lift f H).comp c.mk' = f := by ext; rfl

/-- Given a homomorphism `f` from the quotient of a monoid by a congruence relation, `f` equals the
homomorphism on the quotient induced by `f` composed with the natural map from the monoid to
the quotient. -/
@[to_additive (attr := simp) /-- Given a homomorphism `f` from the quotient of an `AddMonoid` by an
additive congruence relation, `f` equals the homomorphism on the quotient induced by `f` composed
with the natural map from the `AddMonoid` to the quotient. -/]
theorem lift_apply_mk' (f : c.Quotient →* P) :
    (c.lift (f.comp c.mk') fun x y h => show f ↑x = f ↑y by rw [c.eq.2 h]) = f := by
  ext x; rcases x with ⟨⟩; rfl

/-- Homomorphisms on the quotient of a monoid by a congruence relation `c` are equal if their
compositions with `c.mk'` are equal. -/
@[to_additive (attr := ext) /-- Homomorphisms on the quotient of an `AddMonoid` by an additive
congruence relation `c` are equal if their compositions with `c.mk'` are equal. -/]
lemma hom_ext {f g : c.Quotient →* P} (h : f.comp c.mk' = g.comp c.mk') : f = g := by
  rw [← lift_apply_mk' f, ← lift_apply_mk' g]
  congr 1

/-- Homomorphisms on the quotient of a monoid by a congruence relation are equal if they
are equal on elements that are coercions from the monoid. -/
@[to_additive /-- Homomorphisms on the quotient of an `AddMonoid` by an additive congruence relation
are equal if they are equal on elements that are coercions from the `AddMonoid`. -/]
theorem lift_funext (f g : c.Quotient →* P) (h : ∀ a : M, f a = g a) : f = g :=
  hom_ext <| DFunLike.ext _ _ h

/-- The uniqueness part of the universal property for quotients of monoids. -/
@[to_additive /-- The uniqueness part of the universal property for quotients of `AddMonoid`s. -/]
theorem lift_unique (H : c ≤ ker f) (g : c.Quotient →* P) (Hg : g.comp c.mk' = f) :
    g = c.lift f H :=
  hom_ext Hg

/-- Surjective monoid homomorphisms constant on a congruence relation `c`'s equivalence classes
induce a surjective homomorphism on `c`'s quotient. -/
@[to_additive /-- Surjective `AddMonoid` homomorphisms constant on an additive congruence
relation `c`'s equivalence classes induce a surjective homomorphism on `c`'s quotient. -/]
theorem lift_surjective_of_surjective (h : c ≤ ker f) (hf : Surjective f) :
    Surjective (c.lift f h) := fun y =>
  (Exists.elim (hf y)) fun w hw => ⟨w, (lift_mk' h w).symm ▸ hw⟩

variable (c f)

/-- Given a monoid homomorphism `f` from `M` to `P`, the kernel of `f` is the unique congruence
relation on `M` whose induced map from the quotient of `M` to `P` is injective. -/
@[to_additive /-- Given an `AddMonoid` homomorphism `f` from `M` to `P`, the kernel of `f`
is the unique additive congruence relation on `M` whose induced map from the quotient of `M`
to `P` is injective. -/]
theorem ker_eq_lift_of_injective (H : c ≤ ker f) (h : Injective (c.lift f H)) : ker f = c :=
  toSetoid_inj <| Setoid.ker_eq_lift_of_injective f H h

variable {c}

/-- The homomorphism induced on the quotient of a monoid by the kernel of a monoid homomorphism. -/
@[to_additive /-- The homomorphism induced on the quotient of an `AddMonoid` by the kernel
of an `AddMonoid` homomorphism. -/]
def kerLift : (ker f).Quotient →* P :=
  ((ker f).lift f) fun _ _ => id

variable {f}

/-- The diagram described by the universal property for quotients of monoids, when the congruence
relation is the kernel of the homomorphism, commutes. -/
@[to_additive (attr := simp) /-- The diagram described by the universal property for quotients
of `AddMonoid`s, when the additive congruence relation is the kernel of the homomorphism,
commutes. -/]
theorem kerLift_mk (x : M) : kerLift f x = f x :=
  rfl

/-- A monoid homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
@[to_additive /-- An `AddMonoid` homomorphism `f` induces an injective homomorphism on the quotient
by `f`'s kernel. -/]
theorem kerLift_injective (f : M →* P) : Injective (kerLift f) := fun x y =>
  Quotient.inductionOn₂' x y fun _ _ => (ker f).eq.2

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, `d`'s quotient
map induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
@[to_additive /-- Given additive congruence relations `c, d` on an `AddMonoid` such that `d`
contains `c`, `d`'s quotient map induces a homomorphism from the quotient by `c` to the quotient
by `d`. -/]
def map (c d : Con M) (h : c ≤ d) : c.Quotient →* d.Quotient :=
  (c.lift d.mk') fun x y hc => show (ker d.mk') x y from (mk'_ker d).symm ▸ h hc

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, the definition of
the homomorphism from the quotient by `c` to the quotient by `d` induced by `d`'s quotient map. -/
@[to_additive /-- Given additive congruence relations `c, d` on an `AddMonoid` such that `d`
contains `c`, the definition of the homomorphism from the quotient by `c` to the quotient by `d`
induced by `d`'s quotient map. -/]
theorem map_apply {c d : Con M} (h : c ≤ d) (x) :
    c.map d h x = c.lift d.mk' (fun _ _ hc => d.eq.2 <| h hc) x :=
  rfl

end MulOneClass

end Con
