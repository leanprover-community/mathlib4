/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz

! This file was ported from Lean 3 source module algebra.free_algebra
! leanprover-community/mathlib commit 6623e6af705e97002a9054c1c05a980180276fc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.MonoidAlgebra.Basic

/-!
# Free Algebras

Given a commutative semiring `R`, and a type `X`, we construct the free unital, associative
`R`-algebra on `X`.

## Notation

1. `free_algebra R X` is the free algebra itself. It is endowed with an `R`-algebra structure.
2. `free_algebra.ι R` is the function `X → free_algebra R X`.
3. Given a function `f : X → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
  `R`-algebra morphism `free_algebra R X → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : free_algebra R X → A` is
  given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.
5. `equiv_monoid_algebra_free_monoid : free_algebra R X ≃ₐ[R] monoid_algebra R (free_monoid X)`
6. An inductive principle `induction`.

## Implementation details

We construct the free algebra on `X` as a quotient of an inductive type `free_algebra.pre` by an
inductively defined relation `free_algebra.rel`. Explicitly, the construction involves three steps:
1. We construct an inductive type `free_algebra.pre R X`, the terms of which should be thought
  of as representatives for the elements of `free_algebra R X`.
  It is the free type with maps from `R` and `X`, and with two binary operations `add` and `mul`.
2. We construct an inductive relation `free_algebra.rel R X` on `free_algebra.pre R X`.
  This is the smallest relation for which the quotient is an `R`-algebra where addition resp.
  multiplication are induced by `add` resp. `mul` from 1., and for which the map from `R` is the
  structure map for the algebra.
3. The free algebra `free_algebra R X` is the quotient of `free_algebra.pre R X` by
  the relation `free_algebra.rel R X`.
-/


variable (R : Type _) [CommSemiring R]

variable (X : Type _)

namespace FreeAlgebra

/-- This inductive type is used to express representatives of the free algebra.
-/
inductive Pre
  | of : X → pre
  | of_scalar : R → pre
  | add : pre → pre → pre
  | mul : pre → pre → pre
#align free_algebra.pre FreeAlgebra.Pre

namespace Pre

instance : Inhabited (Pre R X) :=
  ⟨of_scalar 0⟩

-- Note: These instances are only used to simplify the notation.
/-- Coercion from `X` to `pre R X`. Note: Used for notation only. -/
def hasCoeGenerator : Coe X (Pre R X) :=
  ⟨of⟩
#align free_algebra.pre.has_coe_generator FreeAlgebra.Pre.hasCoeGenerator

/-- Coercion from `R` to `pre R X`. Note: Used for notation only. -/
def hasCoeSemiring : Coe R (Pre R X) :=
  ⟨of_scalar⟩
#align free_algebra.pre.has_coe_semiring FreeAlgebra.Pre.hasCoeSemiring

/-- Multiplication in `pre R X` defined as `pre.mul`. Note: Used for notation only. -/
def hasMul : Mul (Pre R X) :=
  ⟨mul⟩
#align free_algebra.pre.has_mul FreeAlgebra.Pre.hasMul

/-- Addition in `pre R X` defined as `pre.add`. Note: Used for notation only. -/
def hasAdd : Add (Pre R X) :=
  ⟨add⟩
#align free_algebra.pre.has_add FreeAlgebra.Pre.hasAdd

/-- Zero in `pre R X` defined as the image of `0` from `R`. Note: Used for notation only. -/
def hasZero : Zero (Pre R X) :=
  ⟨of_scalar 0⟩
#align free_algebra.pre.has_zero FreeAlgebra.Pre.hasZero

/-- One in `pre R X` defined as the image of `1` from `R`. Note: Used for notation only. -/
def hasOne : One (Pre R X) :=
  ⟨of_scalar 1⟩
#align free_algebra.pre.has_one FreeAlgebra.Pre.hasOne

/-- Scalar multiplication defined as multiplication by the image of elements from `R`.
Note: Used for notation only.
-/
def hasSmul : SMul R (Pre R X) :=
  ⟨fun r m => mul (of_scalar r) m⟩
#align free_algebra.pre.has_smul FreeAlgebra.Pre.hasSmul

end Pre

attribute [local instance]
  pre.has_coe_generator pre.has_coe_semiring pre.has_mul pre.has_add pre.has_zero pre.has_one pre.has_smul

/-- Given a function from `X` to an `R`-algebra `A`, `lift_fun` provides a lift of `f` to a function
from `pre R X` to `A`. This is mainly used in the construction of `free_algebra.lift`.
-/
def liftFun {A : Type _} [Semiring A] [Algebra R A] (f : X → A) : Pre R X → A := fun t =>
  Pre.recOn t f (algebraMap _ _) (fun _ _ => (· + ·)) fun _ _ => (· * ·)
#align free_algebra.lift_fun FreeAlgebra.liftFun

/-- An inductively defined relation on `pre R X` used to force the initial algebra structure on
the associated quotient.
-/
inductive Rel : Pre R X → Pre R X → Prop-- force `of_scalar` to be a central semiring morphism

  | add_scalar {r s : R} : Rel (↑(r + s)) (↑r + ↑s)
  | mul_scalar {r s : R} : Rel (↑(r * s)) (↑r * ↑s)
  | central_scalar {r : R} {a : Pre R X} : Rel (r * a) (a * r)-- commutative additive semigroup

  | add_assoc {a b c : Pre R X} : Rel (a + b + c) (a + (b + c))
  | add_comm {a b : Pre R X} : Rel (a + b) (b + a)
  | zero_add {a : Pre R X} : Rel (0 + a) a-- multiplicative monoid

  | mul_assoc {a b c : Pre R X} : Rel (a * b * c) (a * (b * c))
  | one_mul {a : Pre R X} : Rel (1 * a) a
  | mul_one {a : Pre R X} : Rel (a * 1) a-- distributivity

  | left_distrib {a b c : Pre R X} : Rel (a * (b + c)) (a * b + a * c)
  |
  right_distrib {a b c : Pre R X} :
    Rel ((a + b) * c) (a * c + b * c)-- other relations needed for semiring

  | MulZeroClass.zero_mul {a : Pre R X} : Rel (0 * a) 0
  | MulZeroClass.mul_zero {a : Pre R X} : Rel (a * 0) 0-- compatibility

  | add_compat_left {a b c : Pre R X} : Rel a b → Rel (a + c) (b + c)
  | add_compat_right {a b c : Pre R X} : Rel a b → Rel (c + a) (c + b)
  | mul_compat_left {a b c : Pre R X} : Rel a b → Rel (a * c) (b * c)
  | mul_compat_right {a b c : Pre R X} : Rel a b → Rel (c * a) (c * b)
#align free_algebra.rel FreeAlgebra.Rel

end FreeAlgebra

/-- The free algebra for the type `X` over the commutative semiring `R`.
-/
def FreeAlgebra :=
  Quot (FreeAlgebra.Rel R X)
#align free_algebra FreeAlgebra

namespace FreeAlgebra

attribute [local instance]
  pre.has_coe_generator pre.has_coe_semiring pre.has_mul pre.has_add pre.has_zero pre.has_one pre.has_smul

instance : Semiring (FreeAlgebra R X)
    where
  add := Quot.map₂ (· + ·) (fun _ _ _ => Rel.add_compat_right) fun _ _ _ => Rel.add_compat_left
  add_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound rel.add_assoc
  zero := Quot.mk _ 0
  zero_add := by
    rintro ⟨⟩
    exact Quot.sound rel.zero_add
  add_zero := by
    rintro ⟨⟩
    change Quot.mk _ _ = _
    rw [Quot.sound rel.add_comm, Quot.sound rel.zero_add]
  add_comm := by
    rintro ⟨⟩ ⟨⟩
    exact Quot.sound rel.add_comm
  mul := Quot.map₂ (· * ·) (fun _ _ _ => Rel.mul_compat_right) fun _ _ _ => Rel.mul_compat_left
  mul_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound rel.mul_assoc
  one := Quot.mk _ 1
  one_mul := by
    rintro ⟨⟩
    exact Quot.sound rel.one_mul
  mul_one := by
    rintro ⟨⟩
    exact Quot.sound rel.mul_one
  left_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound rel.left_distrib
  right_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound rel.right_distrib
  zero_mul := by
    rintro ⟨⟩
    exact Quot.sound rel.zero_mul
  mul_zero := by
    rintro ⟨⟩
    exact Quot.sound rel.mul_zero

instance : Inhabited (FreeAlgebra R X) :=
  ⟨0⟩

instance : SMul R (FreeAlgebra R X)
    where smul r := Quot.map ((· * ·) ↑r) fun a b => Rel.mul_compat_right

instance : Algebra R (FreeAlgebra R X)
    where
  toFun r := Quot.mk _ r
  map_one' := rfl
  map_mul' _ _ := Quot.sound Rel.mul_scalar
  map_zero' := rfl
  map_add' _ _ := Quot.sound Rel.add_scalar
  commutes' _ := by
    rintro ⟨⟩
    exact Quot.sound rel.central_scalar
  smul_def' _ _ := rfl

instance {S : Type _} [CommRing S] : Ring (FreeAlgebra S X) :=
  Algebra.semiringToRing S

variable {X}

/-- The canonical function `X → free_algebra R X`.
-/
irreducible_def ι : X → FreeAlgebra R X := fun m => Quot.mk _ m
#align free_algebra.ι FreeAlgebra.ι

@[simp]
theorem quot_mk_eq_ι (m : X) : Quot.mk (FreeAlgebra.Rel R X) m = ι R m := by rw [ι]
#align free_algebra.quot_mk_eq_ι FreeAlgebra.quot_mk_eq_ι

variable {A : Type _} [Semiring A] [Algebra R A]

/-- Internal definition used to define `lift` -/
private def lift_aux (f : X → A) : FreeAlgebra R X →ₐ[R] A
    where
  toFun a :=
    Quot.liftOn a (liftFun _ _ f) fun a b h =>
      by
      induction h
      · exact (algebraMap R A).map_add h_r h_s
      · exact (algebraMap R A).map_mul h_r h_s
      · apply Algebra.commutes
      · change _ + _ + _ = _ + (_ + _)
        rw [add_assoc]
      · change _ + _ = _ + _
        rw [add_comm]
      · change algebraMap _ _ _ + lift_fun R X f _ = lift_fun R X f _
        simp
      · change _ * _ * _ = _ * (_ * _)
        rw [mul_assoc]
      · change algebraMap _ _ _ * lift_fun R X f _ = lift_fun R X f _
        simp
      · change lift_fun R X f _ * algebraMap _ _ _ = lift_fun R X f _
        simp
      · change _ * (_ + _) = _ * _ + _ * _
        rw [left_distrib]
      · change (_ + _) * _ = _ * _ + _ * _
        rw [right_distrib]
      · change algebraMap _ _ _ * _ = algebraMap _ _ _
        simp
      · change _ * algebraMap _ _ _ = algebraMap _ _ _
        simp
      repeat'
        change lift_fun R X f _ + lift_fun R X f _ = _
        rw [h_ih]
        rfl
      repeat'
        change lift_fun R X f _ * lift_fun R X f _ = _
        rw [h_ih]
        rfl
  map_one' := by
    change algebraMap _ _ _ = _
    simp
  map_mul' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  map_zero' := by
    change algebraMap _ _ _ = _
    simp
  map_add' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  commutes' := by tauto
#align free_algebra.lift_aux free_algebra.lift_aux

/-- Given a function `f : X → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `free_algebra R X → A`.
-/
irreducible_def lift : (X → A) ≃ (FreeAlgebra R X →ₐ[R] A) :=
  { toFun := liftAux R
    invFun := fun F => F ∘ ι R
    left_inv := fun f => by
      ext
      rw [ι]
      rfl
    right_inv := fun F => by
      ext x
      rcases x with ⟨⟩
      induction x
      case of =>
        change ((F : FreeAlgebra R X → A) ∘ ι R) _ = _
        rw [ι]
        rfl
      case of_scalar =>
        change algebraMap _ _ x = F (algebraMap _ _ x)
        rw [AlgHom.commutes F x]
      case
        add a b ha hb =>
        change lift_aux R (F ∘ ι R) (Quot.mk _ _ + Quot.mk _ _) = F (Quot.mk _ _ + Quot.mk _ _)
        rw [AlgHom.map_add, AlgHom.map_add, ha, hb]
      case
        mul a b ha hb =>
        change lift_aux R (F ∘ ι R) (Quot.mk _ _ * Quot.mk _ _) = F (Quot.mk _ _ * Quot.mk _ _)
        rw [AlgHom.map_mul, AlgHom.map_mul, ha, hb] }
#align free_algebra.lift FreeAlgebra.lift

@[simp]
theorem liftAux_eq (f : X → A) : liftAux R f = lift R f :=
  by
  rw [lift]
  rfl
#align free_algebra.lift_aux_eq FreeAlgebra.liftAux_eq

@[simp]
theorem lift_symm_apply (F : FreeAlgebra R X →ₐ[R] A) : (lift R).symm F = F ∘ ι R :=
  by
  rw [lift]
  rfl
#align free_algebra.lift_symm_apply FreeAlgebra.lift_symm_apply

variable {R X}

@[simp]
theorem ι_comp_lift (f : X → A) : (lift R f : FreeAlgebra R X → A) ∘ ι R = f :=
  by
  ext
  rw [ι, lift]
  rfl
#align free_algebra.ι_comp_lift FreeAlgebra.ι_comp_lift

@[simp]
theorem lift_ι_apply (f : X → A) (x) : lift R f (ι R x) = f x :=
  by
  rw [ι, lift]
  rfl
#align free_algebra.lift_ι_apply FreeAlgebra.lift_ι_apply

@[simp]
theorem lift_unique (f : X → A) (g : FreeAlgebra R X →ₐ[R] A) :
    (g : FreeAlgebra R X → A) ∘ ι R = f ↔ g = lift R f :=
  by
  rw [← (lift R).symm_apply_eq, lift]
  rfl
#align free_algebra.lift_unique FreeAlgebra.lift_unique

/-!
Since we have set the basic definitions as `@[irreducible]`, from this point onwards one
should only use the universal properties of the free algebra, and consider the actual implementation
as a quotient of an inductive type as completely hidden. -/


-- Marking `free_algebra` irreducible makes `ring` instances inaccessible on quotients.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.
@[simp]
theorem lift_comp_ι (g : FreeAlgebra R X →ₐ[R] A) : lift R ((g : FreeAlgebra R X → A) ∘ ι R) = g :=
  by
  rw [← lift_symm_apply]
  exact (lift R).apply_symm_apply g
#align free_algebra.lift_comp_ι FreeAlgebra.lift_comp_ι

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {f g : FreeAlgebra R X →ₐ[R] A}
    (w : (f : FreeAlgebra R X → A) ∘ ι R = (g : FreeAlgebra R X → A) ∘ ι R) : f = g :=
  by
  rw [← lift_symm_apply, ← lift_symm_apply] at w
  exact (lift R).symm.Injective w
#align free_algebra.hom_ext FreeAlgebra.hom_ext

/-- The free algebra on `X` is "just" the monoid algebra on the free monoid on `X`.

This would be useful when constructing linear maps out of a free algebra,
for example.
-/
noncomputable def equivMonoidAlgebraFreeMonoid :
    FreeAlgebra R X ≃ₐ[R] MonoidAlgebra R (FreeMonoid X) :=
  AlgEquiv.ofAlgHom (lift R fun x => (MonoidAlgebra.of R (FreeMonoid X)) (FreeMonoid.of x))
    ((MonoidAlgebra.lift R (FreeMonoid X) (FreeAlgebra R X)) (FreeMonoid.lift (ι R)))
    (by
      apply MonoidAlgebra.algHom_ext; intro x
      apply FreeMonoid.recOn x
      · simp
        rfl
      · intro x y ih
        simp at ih
        simp [ih])
    (by
      ext
      simp)
#align free_algebra.equiv_monoid_algebra_free_monoid FreeAlgebra.equivMonoidAlgebraFreeMonoid

instance [Nontrivial R] : Nontrivial (FreeAlgebra R X) :=
  equivMonoidAlgebraFreeMonoid.Surjective.Nontrivial

section

/-- The left-inverse of `algebra_map`. -/
def algebraMapInv : FreeAlgebra R X →ₐ[R] R :=
  lift R (0 : X → R)
#align free_algebra.algebra_map_inv FreeAlgebra.algebraMapInv

theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X) := fun x => by
  simp [algebra_map_inv]
#align free_algebra.algebra_map_left_inverse FreeAlgebra.algebraMap_leftInverse

@[simp]
theorem algebraMap_inj (x y : R) :
    algebraMap R (FreeAlgebra R X) x = algebraMap R (FreeAlgebra R X) y ↔ x = y :=
  algebraMap_leftInverse.Injective.eq_iff
#align free_algebra.algebra_map_inj FreeAlgebra.algebraMap_inj

@[simp]
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) algebraMap_leftInverse.Injective
#align free_algebra.algebra_map_eq_zero_iff FreeAlgebra.algebraMap_eq_zero_iff

@[simp]
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) algebraMap_leftInverse.Injective
#align free_algebra.algebra_map_eq_one_iff FreeAlgebra.algebraMap_eq_one_iff

-- this proof is copied from the approach in `free_abelian_group.of_injective`
theorem ι_injective [Nontrivial R] : Function.Injective (ι R : X → FreeAlgebra R X) :=
  fun x y hoxy =>
  by_contradiction <| by
    classical exact fun hxy : x ≠ y =>
        let f : FreeAlgebra R X →ₐ[R] R := lift R fun z => if x = z then (1 : R) else 0
        have hfx1 : f (ι R x) = 1 := (lift_ι_apply _ _).trans <| if_pos rfl
        have hfy1 : f (ι R y) = 1 := hoxy ▸ hfx1
        have hfy0 : f (ι R y) = 0 := (lift_ι_apply _ _).trans <| if_neg hxy
        one_ne_zero <| hfy1.symm.trans hfy0
#align free_algebra.ι_injective FreeAlgebra.ι_injective

@[simp]
theorem ι_inj [Nontrivial R] (x y : X) : ι R x = ι R y ↔ x = y :=
  ι_injective.eq_iff
#align free_algebra.ι_inj FreeAlgebra.ι_inj

@[simp]
theorem ι_ne_algebraMap [Nontrivial R] (x : X) (r : R) : ι R x ≠ algebraMap R _ r := fun h =>
  by
  let f0 : FreeAlgebra R X →ₐ[R] R := lift R 0
  let f1 : FreeAlgebra R X →ₐ[R] R := lift R 1
  have hf0 : f0 (ι R x) = 0 := lift_ι_apply _ _
  have hf1 : f1 (ι R x) = 1 := lift_ι_apply _ _
  rw [h, f0.commutes, Algebra.id.map_eq_self] at hf0
  rw [h, f1.commutes, Algebra.id.map_eq_self] at hf1
  exact zero_ne_one (hf0.symm.trans hf1)
#align free_algebra.ι_ne_algebra_map FreeAlgebra.ι_ne_algebraMap

@[simp]
theorem ι_ne_zero [Nontrivial R] (x : X) : ι R x ≠ 0 :=
  ι_ne_algebraMap x 0
#align free_algebra.ι_ne_zero FreeAlgebra.ι_ne_zero

@[simp]
theorem ι_ne_one [Nontrivial R] (x : X) : ι R x ≠ 1 :=
  ι_ne_algebraMap x 1
#align free_algebra.ι_ne_one FreeAlgebra.ι_ne_one

end

end FreeAlgebra

/- There is something weird in the above namespace that breaks the typeclass resolution of
`has_coe_to_sort` below. Closing it and reopening it fixes it... -/
namespace FreeAlgebra

/-- An induction principle for the free algebra.

If `C` holds for the `algebra_map` of `r : R` into `free_algebra R X`, the `ι` of `x : X`, and is
preserved under addition and muliplication, then it holds for all of `free_algebra R X`.
-/
@[elab_as_elim]
theorem induction {C : FreeAlgebra R X → Prop}
    (h_grade0 : ∀ r, C (algebraMap R (FreeAlgebra R X) r)) (h_grade1 : ∀ x, C (ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b)) (h_add : ∀ a b, C a → C b → C (a + b))
    (a : FreeAlgebra R X) : C a :=
  by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from X
  let s : Subalgebra R (FreeAlgebra R X) :=
    { carrier := C
      mul_mem' := h_mul
      add_mem' := h_add
      algebraMap_mem' := h_grade0 }
  let of : X → s := Subtype.coind (ι R) h_grade1
  -- the mapping through the subalgebra is the identity
  have of_id : AlgHom.id R (FreeAlgebra R X) = s.val.comp (lift R of) :=
    by
    ext
    simp [of, Subtype.coind]
  -- finding a proof is finding an element of the subalgebra
  convert Subtype.prop (lift R of a)
  simp [AlgHom.ext_iff] at of_id
  exact of_id a
#align free_algebra.induction FreeAlgebra.induction

end FreeAlgebra

