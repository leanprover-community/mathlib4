/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Free

#align_import algebra.free_algebra from "leanprover-community/mathlib"@"6623e6af705e97002a9054c1c05a980180276fc1"

/-!
# Free Algebras

Given a commutative semiring `R`, and a type `X`, we construct the free unital, associative
`R`-algebra on `X`.

## Notation

1. `FreeAlgebra R X` is the free algebra itself. It is endowed with an `R`-algebra structure.
2. `FreeAlgebra.ι R` is the function `X → FreeAlgebra R X`.
3. Given a function `f : X → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
  `R`-algebra morphism `FreeAlgebra R X → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : FreeAlgebra R X → A` is
  given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.
5. `equivMonoidAlgebraFreeMonoid : FreeAlgebra R X ≃ₐ[R] MonoidAlgebra R (FreeMonoid X)`
6. An inductive principle `induction`.

## Implementation details

We construct the free algebra on `X` as a quotient of an inductive type `FreeAlgebra.Pre` by an
inductively defined relation `FreeAlgebra.Rel`. Explicitly, the construction involves three steps:
1. We construct an inductive type `FreeAlgebra.Pre R X`, the terms of which should be thought
  of as representatives for the elements of `FreeAlgebra R X`.
  It is the free type with maps from `R` and `X`, and with two binary operations `add` and `mul`.
2. We construct an inductive relation `FreeAlgebra.Rel R X` on `FreeAlgebra.Pre R X`.
  This is the smallest relation for which the quotient is an `R`-algebra where addition resp.
  multiplication are induced by `add` resp. `mul` from 1., and for which the map from `R` is the
  structure map for the algebra.
3. The free algebra `FreeAlgebra R X` is the quotient of `FreeAlgebra.Pre R X` by
  the relation `FreeAlgebra.Rel R X`.
-/


variable (R : Type*) [CommSemiring R]

variable (X : Type*)

namespace FreeAlgebra

/-- This inductive type is used to express representatives of the free algebra.
-/
inductive Pre
  | of : X → Pre
  | of_scalar : R → Pre
  | add : Pre → Pre → Pre
  | mul : Pre → Pre → Pre
#align free_algebra.pre FreeAlgebra.Pre

namespace Pre

instance : Inhabited (Pre R X) := ⟨of_scalar 0⟩

-- Note: These instances are only used to simplify the notation.
/-- Coercion from `X` to `Pre R X`. Note: Used for notation only. -/
def hasCoeGenerator : Coe X (Pre R X) := ⟨of⟩
#align free_algebra.pre.has_coe_generator FreeAlgebra.Pre.hasCoeGenerator

/-- Coercion from `R` to `Pre R X`. Note: Used for notation only. -/
def hasCoeSemiring : Coe R (Pre R X) := ⟨of_scalar⟩
#align free_algebra.pre.has_coe_semiring FreeAlgebra.Pre.hasCoeSemiring

/-- Multiplication in `Pre R X` defined as `Pre.mul`. Note: Used for notation only. -/
def hasMul : Mul (Pre R X) := ⟨mul⟩
#align free_algebra.pre.has_mul FreeAlgebra.Pre.hasMul

/-- Addition in `Pre R X` defined as `Pre.add`. Note: Used for notation only. -/
def hasAdd : Add (Pre R X) := ⟨add⟩
#align free_algebra.pre.has_add FreeAlgebra.Pre.hasAdd

/-- Zero in `Pre R X` defined as the image of `0` from `R`. Note: Used for notation only. -/
def hasZero : Zero (Pre R X) := ⟨of_scalar 0⟩
#align free_algebra.pre.has_zero FreeAlgebra.Pre.hasZero

/-- One in `Pre R X` defined as the image of `1` from `R`. Note: Used for notation only. -/
def hasOne : One (Pre R X) := ⟨of_scalar 1⟩
#align free_algebra.pre.has_one FreeAlgebra.Pre.hasOne

/-- Scalar multiplication defined as multiplication by the image of elements from `R`.
Note: Used for notation only.
-/
def hasSmul : SMul R (Pre R X) := ⟨fun r m ↦ mul (of_scalar r) m⟩
#align free_algebra.pre.has_smul FreeAlgebra.Pre.hasSmul

end Pre

attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul Pre.hasAdd
  Pre.hasZero Pre.hasOne Pre.hasSmul

/-- Given a function from `X` to an `R`-algebra `A`, `lift_fun` provides a lift of `f` to a function
from `Pre R X` to `A`. This is mainly used in the construction of `FreeAlgebra.lift`.
-/
-- Porting note: recOn was replaced to preserve computability, see lean4#2049
def liftFun {A : Type*} [Semiring A] [Algebra R A] (f : X → A) :
    Pre R X → A
  | .of t => f t
  | .add a b => liftFun f a + liftFun f b
  | .mul a b => liftFun f a * liftFun f b
  | .of_scalar c => algebraMap _ _ c
#align free_algebra.lift_fun FreeAlgebra.liftFun

/-- An inductively defined relation on `Pre R X` used to force the initial algebra structure on
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
  | right_distrib {a b c : Pre R X} :
      Rel ((a + b) * c) (a * c + b * c)-- other relations needed for semiring

  | zero_mul {a : Pre R X} : Rel (0 * a) 0
  | mul_zero {a : Pre R X} : Rel (a * 0) 0-- compatibility

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

attribute [local instance] Pre.hasCoeGenerator Pre.hasCoeSemiring Pre.hasMul Pre.hasAdd
  Pre.hasZero Pre.hasOne Pre.hasSmul

/-! Define the basic operations-/

instance instSMul {A} [CommSemiring A] [Algebra R A] : SMul R (FreeAlgebra A X) where
  smul r := Quot.map (HMul.hMul (algebraMap R A r : Pre A X)) fun _ _ ↦ Rel.mul_compat_right

instance instZero : Zero (FreeAlgebra R X) where zero := Quot.mk _ 0

instance instOne : One (FreeAlgebra R X) where one := Quot.mk _ 1

instance instAdd : Add (FreeAlgebra R X) where
  add := Quot.map₂ HAdd.hAdd (fun _ _ _ ↦ Rel.add_compat_right) fun _ _ _ ↦ Rel.add_compat_left

instance instMul : Mul (FreeAlgebra R X) where
  mul := Quot.map₂ HMul.hMul (fun _ _ _ ↦ Rel.mul_compat_right) fun _ _ _ ↦ Rel.mul_compat_left

-- `Quot.mk` is an implementation detail of `FreeAlgebra`, so this lemma is private
private theorem mk_mul (x y : Pre R X) :
    Quot.mk (Rel R X) (x * y) = (HMul.hMul (self := instHMul (α := FreeAlgebra R X))
    (Quot.mk (Rel R X) x) (Quot.mk (Rel R X) y)) :=
  rfl

/-! Build the semiring structure. We do this one piece at a time as this is convenient for proving
the `nsmul` fields. -/

instance instMonoidWithZero : MonoidWithZero (FreeAlgebra R X) where
  mul_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    -- ⊢ Quot.mk (Rel R X) a✝² * Quot.mk (Rel R X) a✝¹ * Quot.mk (Rel R X) a✝ = Quot. …
    exact Quot.sound Rel.mul_assoc
    -- 🎉 no goals
  one := Quot.mk _ 1
  one_mul := by
    rintro ⟨⟩
    -- ⊢ 1 * Quot.mk (Rel R X) a✝ = Quot.mk (Rel R X) a✝
    exact Quot.sound Rel.one_mul
    -- 🎉 no goals
  mul_one := by
    rintro ⟨⟩
    -- ⊢ Quot.mk (Rel R X) a✝ * 1 = Quot.mk (Rel R X) a✝
    exact Quot.sound Rel.mul_one
    -- 🎉 no goals
  zero_mul := by
    rintro ⟨⟩
    -- ⊢ 0 * Quot.mk (Rel R X) a✝ = 0
    exact Quot.sound Rel.zero_mul
    -- 🎉 no goals
  mul_zero := by
    rintro ⟨⟩
    -- ⊢ Quot.mk (Rel R X) a✝ * 0 = 0
    exact Quot.sound Rel.mul_zero
    -- 🎉 no goals

instance instDistrib : Distrib (FreeAlgebra R X) where
  left_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    -- ⊢ Quot.mk (Rel R X) a✝² * (Quot.mk (Rel R X) a✝¹ + Quot.mk (Rel R X) a✝) = Quo …
    exact Quot.sound Rel.left_distrib
    -- 🎉 no goals
  right_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    -- ⊢ (Quot.mk (Rel R X) a✝² + Quot.mk (Rel R X) a✝¹) * Quot.mk (Rel R X) a✝ = Quo …
    exact Quot.sound Rel.right_distrib
    -- 🎉 no goals

instance instAddCommMonoid : AddCommMonoid (FreeAlgebra R X) where
  add_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    -- ⊢ Quot.mk (Rel R X) a✝² + Quot.mk (Rel R X) a✝¹ + Quot.mk (Rel R X) a✝ = Quot. …
    exact Quot.sound Rel.add_assoc
    -- 🎉 no goals
  zero_add := by
    rintro ⟨⟩
    -- ⊢ 0 + Quot.mk (Rel R X) a✝ = Quot.mk (Rel R X) a✝
    exact Quot.sound Rel.zero_add
    -- 🎉 no goals
  add_zero := by
    rintro ⟨⟩
    -- ⊢ Quot.mk (Rel R X) a✝ + 0 = Quot.mk (Rel R X) a✝
    change Quot.mk _ _ = _
    -- ⊢ Quot.mk (Rel R X) (a✝ + 0) = Quot.mk (Rel R X) a✝
    rw [Quot.sound Rel.add_comm, Quot.sound Rel.zero_add]
    -- 🎉 no goals
  add_comm := by
    rintro ⟨⟩ ⟨⟩
    -- ⊢ Quot.mk (Rel R X) a✝¹ + Quot.mk (Rel R X) a✝ = Quot.mk (Rel R X) a✝ + Quot.m …
    exact Quot.sound Rel.add_comm
    -- 🎉 no goals
  nsmul := (· • ·)
    -- ⊢ (fun x x_1 => x • x_1) 0 (Quot.mk (Rel R X) a✝) = 0
  nsmul_zero := by
    -- ⊢ Quot.mk (Rel R X) (Pre.of_scalar (↑(algebraMap ℕ R) 0) * a✝) = 0
    rintro ⟨⟩
    -- ⊢ Quot.mk (Rel R X) (Pre.of_scalar 0 * a✝) = 0
    change Quot.mk _ (_ * _) = _
    -- 🎉 no goals
    rw [map_zero]
    exact Quot.sound Rel.zero_mul
    -- ⊢ (fun x x_1 => x • x_1) (n + 1) (Quot.mk (Rel R X) a) = Quot.mk (Rel R X) a + …
  nsmul_succ n := by
    -- ⊢ Quot.mk (Rel R X) (Pre.of_scalar (↑(algebraMap ℕ R) (n + 1)) * a) = Quot.mk  …
    rintro ⟨a⟩
    -- ⊢ Quot.mk (Rel R X) (Pre.of_scalar (1 + ↑(algebraMap ℕ R) n)) * Quot.mk (Rel R …
    dsimp only [HSMul.hSMul, instSMul, Quot.map]
    -- ⊢ Quot.mk (Rel R X) (Pre.of_scalar (1 + ↑(algebraMap ℕ R) n)) = 1 + Quot.mk (R …
    rw [map_add, map_one, add_comm, mk_mul, mk_mul, ←one_add_mul (_ : FreeAlgebra R X)]
    -- 🎉 no goals
    congr 1
    exact Quot.sound Rel.add_scalar

instance : Semiring (FreeAlgebra R X) where
  __ := instMonoidWithZero R X
  __ := instAddCommMonoid R X
  __ := instDistrib R X
  natCast n := Quot.mk _ (n : R)
  natCast_zero := by simp; rfl
                     -- ⊢ Quot.mk (Rel R X) (Pre.of_scalar 0) = 0
                           -- 🎉 no goals
  natCast_succ n := by simp; exact Quot.sound Rel.add_scalar
                       -- ⊢ Quot.mk (Rel R X) (Pre.of_scalar (↑n + 1)) = Quot.mk (Rel R X) (Pre.of_scala …
                             -- 🎉 no goals

instance : Inhabited (FreeAlgebra R X) :=
  ⟨0⟩

instance instAlgebra {A} [CommSemiring A] [Algebra R A] : Algebra R (FreeAlgebra A X) where
  toRingHom := ({
      toFun := fun r => Quot.mk _ r
      map_one' := rfl
      map_mul' := fun _ _ => Quot.sound Rel.mul_scalar
      map_zero' := rfl
      map_add' := fun _ _ => Quot.sound Rel.add_scalar } : A →+* FreeAlgebra A X).comp
      (algebraMap R A)
  commutes' _ := by
    rintro ⟨⟩
    -- ⊢ ↑(RingHom.comp { toMonoidHom := { toOneHom := { toFun := fun r => Quot.mk (R …
    exact Quot.sound Rel.central_scalar
    -- 🎉 no goals
  smul_def' _ _ := rfl

-- verify there is no diamond
variable (S : Type) [CommSemiring S] in
example : (algebraNat : Algebra ℕ (FreeAlgebra S X)) = instAlgebra _ _ := rfl

instance {R S A} [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [SMul R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] :
    IsScalarTower R S (FreeAlgebra A X) where
  smul_assoc r s x := by
    change algebraMap S A (r • s) • x = algebraMap R A _ • (algebraMap S A _ • x)
    -- ⊢ ↑(algebraMap S A) (r • s) • x = ↑(algebraMap R A) r • ↑(algebraMap S A) s • x
    rw [←smul_assoc]
    -- ⊢ ↑(algebraMap S A) (r • s) • x = (↑(algebraMap R A) r • ↑(algebraMap S A) s)  …
    congr
    -- ⊢ ↑(algebraMap S A) (r • s) = ↑(algebraMap R A) r • ↑(algebraMap S A) s
    simp only [Algebra.algebraMap_eq_smul_one, smul_eq_mul]
    -- ⊢ (r • s) • 1 = r • 1 * s • 1
    rw [smul_assoc, ←smul_one_mul]
    -- 🎉 no goals

instance {R S A} [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [Algebra R A] [Algebra S A] [SMulCommClass R S A] :
    SMulCommClass R S (FreeAlgebra A X) where
  smul_comm r s x := smul_comm (algebraMap R A r) (algebraMap S A s) x

instance {S : Type*} [CommRing S] : Ring (FreeAlgebra S X) :=
  Algebra.semiringToRing S

-- verify there is no diamond
variable (S : Type) [CommRing S] in
example : (algebraInt _ : Algebra ℤ (FreeAlgebra S X)) = instAlgebra _ _ := rfl

variable {X}

/-- The canonical function `X → FreeAlgebra R X`.
-/
irreducible_def ι : X → FreeAlgebra R X := fun m ↦ Quot.mk _ m
#align free_algebra.ι FreeAlgebra.ι

@[simp]
theorem quot_mk_eq_ι (m : X) : Quot.mk (FreeAlgebra.Rel R X) m = ι R m := by rw [ι_def]
                                                                             -- 🎉 no goals
#align free_algebra.quot_mk_eq_ι FreeAlgebra.quot_mk_eq_ι

variable {A : Type*} [Semiring A] [Algebra R A]

/-- Internal definition used to define `lift` -/
private def liftAux (f : X → A) : FreeAlgebra R X →ₐ[R] A where
  toFun a :=
    Quot.liftOn a (liftFun _ _ f) fun a b h ↦ by
      induction' h
      · exact (algebraMap R A).map_add _ _
        -- 🎉 no goals
      · exact (algebraMap R A).map_mul _ _
        -- 🎉 no goals
      · apply Algebra.commutes
        -- 🎉 no goals
      · change _ + _ + _ = _ + (_ + _)
        -- ⊢ liftFun R X f a✝ + liftFun R X f b✝ + liftFun R X f c✝ = liftFun R X f a✝ +  …
        rw [add_assoc]
        -- 🎉 no goals
      · change _ + _ = _ + _
        -- ⊢ liftFun R X f a✝ + liftFun R X f b✝ = liftFun R X f b✝ + liftFun R X f a✝
        rw [add_comm]
        -- 🎉 no goals
      · change algebraMap _ _ _ + liftFun R X f _ = liftFun R X f _
        -- ⊢ ↑(algebraMap R A) 0 + liftFun R X f a✝ = liftFun R X f a✝
        simp
        -- 🎉 no goals
      · change _ * _ * _ = _ * (_ * _)
        -- ⊢ liftFun R X f a✝ * liftFun R X f b✝ * liftFun R X f c✝ = liftFun R X f a✝ *  …
        rw [mul_assoc]
        -- 🎉 no goals
      · change algebraMap _ _ _ * liftFun R X f _ = liftFun R X f _
        -- ⊢ ↑(algebraMap R A) 1 * liftFun R X f a✝ = liftFun R X f a✝
        simp
        -- 🎉 no goals
      · change liftFun R X f _ * algebraMap _ _ _ = liftFun R X f _
        -- ⊢ liftFun R X f a✝ * ↑(algebraMap R A) 1 = liftFun R X f a✝
        simp
        -- 🎉 no goals
      · change _ * (_ + _) = _ * _ + _ * _
        -- ⊢ liftFun R X f a✝ * (liftFun R X f b✝ + liftFun R X f c✝) = liftFun R X f a✝  …
        rw [left_distrib]
        -- 🎉 no goals
      · change (_ + _) * _ = _ * _ + _ * _
        -- ⊢ (liftFun R X f a✝ + liftFun R X f b✝) * liftFun R X f c✝ = liftFun R X f a✝  …
        rw [right_distrib]
        -- 🎉 no goals
      · change algebraMap _ _ _ * _ = algebraMap _ _ _
        -- ⊢ ↑(algebraMap R A) 0 * liftFun R X f a✝ = ↑(algebraMap R A) 0
        simp
        -- 🎉 no goals
      · change _ * algebraMap _ _ _ = algebraMap _ _ _
        -- ⊢ liftFun R X f a✝ * ↑(algebraMap R A) 0 = ↑(algebraMap R A) 0
        simp
        -- 🎉 no goals
      repeat
        change liftFun R X f _ + liftFun R X f _ = _
        simp only [*]
        rfl
      repeat
        change liftFun R X f _ * liftFun R X f _ = _
        simp only [*]
        rfl
  map_one' := by
    change algebraMap _ _ _ = _
    -- ⊢ ↑(algebraMap R A) 1 = 1
    simp
    -- 🎉 no goals
  map_mul' := by
    rintro ⟨⟩ ⟨⟩
    -- ⊢ OneHom.toFun { toFun := fun a => Quot.liftOn a (liftFun R X f) (_ : ∀ (a b : …
    rfl
    -- 🎉 no goals
  map_zero' := by
    dsimp
    -- ⊢ Quot.liftOn 0 (liftFun R X f) (_ : ∀ (a b : Pre R X), Rel R X a b → liftFun  …
    change algebraMap _ _ _ = _
    -- ⊢ ↑(algebraMap R A) 0 = 0
    simp
    -- 🎉 no goals
  map_add' := by
    rintro ⟨⟩ ⟨⟩
    -- ⊢ OneHom.toFun (↑{ toOneHom := { toFun := fun a => Quot.liftOn a (liftFun R X  …
    rfl
    -- 🎉 no goals
  commutes' := by tauto
                  -- 🎉 no goals
-- Porting note: removed #align declaration since it is a private lemma

/-- Given a function `f : X → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `FreeAlgebra R X → A`.
-/
@[irreducible]
def lift : (X → A) ≃ (FreeAlgebra R X →ₐ[R] A) :=
  { toFun := liftAux R
    invFun := fun F ↦ F ∘ ι R
    left_inv := fun f ↦ by
      ext
      -- ⊢ (fun F => ↑F ∘ ι R) (FreeAlgebra.liftAux R f) x✝ = f x✝
      simp only [Function.comp_apply, ι_def]
      -- ⊢ ↑(FreeAlgebra.liftAux R f) (Quot.mk (Rel R X) (Pre.of x✝)) = f x✝
      rfl
      -- 🎉 no goals
    right_inv := fun F ↦ by
      ext t
      -- ⊢ ↑(FreeAlgebra.liftAux R ((fun F => ↑F ∘ ι R) F)) t = ↑F t
      rcases t with ⟨x⟩
      -- ⊢ ↑(FreeAlgebra.liftAux R ((fun F => ↑F ∘ ι R) F)) (Quot.mk (Rel R X) x) = ↑F  …
      induction x
      case of =>
        change ((F : FreeAlgebra R X → A) ∘ ι R) _ = _
        simp only [Function.comp_apply, ι_def]
      case of_scalar x =>
        change algebraMap _ _ x = F (algebraMap _ _ x)
        rw [AlgHom.commutes F _]
      case add a b ha hb =>
        -- Porting note: it is necessary to declare fa and fb explicitly otherwise Lean refuses
        -- to consider `Quot.mk (Rel R X) ·` as element of FreeAlgebra R X
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa + fb) = F (fa + fb)
        rw [AlgHom.map_add, AlgHom.map_add, ha, hb]
      case mul a b ha hb =>
        let fa : FreeAlgebra R X := Quot.mk (Rel R X) a
        let fb : FreeAlgebra R X := Quot.mk (Rel R X) b
        change liftAux R (F ∘ ι R) (fa * fb) = F (fa * fb)
        rw [AlgHom.map_mul, AlgHom.map_mul, ha, hb] }
#align free_algebra.lift FreeAlgebra.lift

@[simp]
theorem liftAux_eq (f : X → A) : liftAux R f = lift R f := by
  rw [lift]
  -- ⊢ FreeAlgebra.liftAux R f = ↑{ toFun := FreeAlgebra.liftAux R, invFun := fun F …
  rfl
  -- 🎉 no goals
#align free_algebra.lift_aux_eq FreeAlgebra.liftAux_eq

@[simp]
theorem lift_symm_apply (F : FreeAlgebra R X →ₐ[R] A) : (lift R).symm F = F ∘ ι R := by
  rw [lift]
  -- ⊢ ↑{ toFun := FreeAlgebra.liftAux R, invFun := fun F => ↑F ∘ ι R, left_inv :=  …
  rfl
  -- 🎉 no goals
#align free_algebra.lift_symm_apply FreeAlgebra.lift_symm_apply

variable {R}

@[simp]
theorem ι_comp_lift (f : X → A) : (lift R f : FreeAlgebra R X → A) ∘ ι R = f := by
  ext
  -- ⊢ (↑(↑(lift R) f) ∘ ι R) x✝ = f x✝
  rw [Function.comp_apply, ι_def, lift]
  -- ⊢ ↑(↑{ toFun := FreeAlgebra.liftAux R, invFun := fun F => ↑F ∘ ι R, left_inv : …
  rfl
  -- 🎉 no goals
#align free_algebra.ι_comp_lift FreeAlgebra.ι_comp_lift

@[simp]
theorem lift_ι_apply (f : X → A) (x) : lift R f (ι R x) = f x := by
  rw [ι_def, lift]
  -- ⊢ ↑(↑{ toFun := FreeAlgebra.liftAux R, invFun := fun F => ↑F ∘ ι R, left_inv : …
  rfl
  -- 🎉 no goals
#align free_algebra.lift_ι_apply FreeAlgebra.lift_ι_apply

@[simp]
theorem lift_unique (f : X → A) (g : FreeAlgebra R X →ₐ[R] A) :
    (g : FreeAlgebra R X → A) ∘ ι R = f ↔ g = lift R f := by
  rw [← (lift R).symm_apply_eq, lift]
  -- ⊢ ↑g ∘ ι R = f ↔ ↑{ toFun := FreeAlgebra.liftAux R, invFun := fun F => ↑F ∘ ι  …
  rfl
  -- 🎉 no goals
#align free_algebra.lift_unique FreeAlgebra.lift_unique

/-!
Since we have set the basic definitions as `@[Irreducible]`, from this point onwards one
should only use the universal properties of the free algebra, and consider the actual implementation
as a quotient of an inductive type as completely hidden. -/


-- Marking `FreeAlgebra` irreducible makes `Ring` instances inaccessible on quotients.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.
@[simp]
theorem lift_comp_ι (g : FreeAlgebra R X →ₐ[R] A) :
    lift R ((g : FreeAlgebra R X → A) ∘ ι R) = g := by
  rw [← lift_symm_apply]
  -- ⊢ ↑(lift R) (↑(lift R).symm g) = g
  exact (lift R).apply_symm_apply g
  -- 🎉 no goals
#align free_algebra.lift_comp_ι FreeAlgebra.lift_comp_ι

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
theorem hom_ext {f g : FreeAlgebra R X →ₐ[R] A}
    (w : (f : FreeAlgebra R X → A) ∘ ι R = (g : FreeAlgebra R X → A) ∘ ι R) : f = g := by
  rw [← lift_symm_apply, ← lift_symm_apply] at w
  -- ⊢ f = g
  exact (lift R).symm.injective w
  -- 🎉 no goals
#align free_algebra.hom_ext FreeAlgebra.hom_ext

/-- The free algebra on `X` is "just" the monoid algebra on the free monoid on `X`.

This would be useful when constructing linear maps out of a free algebra,
for example.
-/
noncomputable def equivMonoidAlgebraFreeMonoid :
    FreeAlgebra R X ≃ₐ[R] MonoidAlgebra R (FreeMonoid X) :=
  AlgEquiv.ofAlgHom (lift R fun x ↦ (MonoidAlgebra.of R (FreeMonoid X)) (FreeMonoid.of x))
    ((MonoidAlgebra.lift R (FreeMonoid X) (FreeAlgebra R X)) (FreeMonoid.lift (ι R)))
    (by
      apply MonoidAlgebra.algHom_ext; intro x
      -- ⊢ ∀ (x : FreeMonoid X), ↑(AlgHom.comp (↑(lift R) fun x => ↑(MonoidAlgebra.of R …
                                      -- ⊢ ↑(AlgHom.comp (↑(lift R) fun x => ↑(MonoidAlgebra.of R (FreeMonoid X)) (Free …
      refine FreeMonoid.recOn x ?_ ?_
      -- ⊢ ↑(AlgHom.comp (↑(lift R) fun x => ↑(MonoidAlgebra.of R (FreeMonoid X)) (Free …
      · simp
        -- ⊢ 1 = MonoidAlgebra.single 1 1
        rfl
        -- 🎉 no goals
      · intro x y ih
        -- ⊢ ↑(AlgHom.comp (↑(lift R) fun x => ↑(MonoidAlgebra.of R (FreeMonoid X)) (Free …
        simp at ih
        -- ⊢ ↑(AlgHom.comp (↑(lift R) fun x => ↑(MonoidAlgebra.of R (FreeMonoid X)) (Free …
        simp [ih])
        -- 🎉 no goals
    (by
      ext
      -- ⊢ (↑(AlgHom.comp (↑(MonoidAlgebra.lift R (FreeMonoid X) (FreeAlgebra R X)) (↑F …
      simp)
      -- 🎉 no goals
#align free_algebra.equiv_monoid_algebra_free_monoid FreeAlgebra.equivMonoidAlgebraFreeMonoid

instance [Nontrivial R] : Nontrivial (FreeAlgebra R X) :=
  equivMonoidAlgebraFreeMonoid.surjective.nontrivial

section

/-- The left-inverse of `algebraMap`. -/
def algebraMapInv : FreeAlgebra R X →ₐ[R] R :=
  lift R (0 : X → R)
#align free_algebra.algebra_map_inv FreeAlgebra.algebraMapInv

theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X) := fun x ↦ by
  simp [algebraMapInv]
  -- 🎉 no goals
#align free_algebra.algebra_map_left_inverse FreeAlgebra.algebraMap_leftInverse

@[simp]
theorem algebraMap_inj (x y : R) :
    algebraMap R (FreeAlgebra R X) x = algebraMap R (FreeAlgebra R X) y ↔ x = y :=
  algebraMap_leftInverse.injective.eq_iff
#align free_algebra.algebra_map_inj FreeAlgebra.algebraMap_inj

@[simp]
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) algebraMap_leftInverse.injective
#align free_algebra.algebra_map_eq_zero_iff FreeAlgebra.algebraMap_eq_zero_iff

@[simp]
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) algebraMap_leftInverse.injective
#align free_algebra.algebra_map_eq_one_iff FreeAlgebra.algebraMap_eq_one_iff

-- this proof is copied from the approach in `FreeAbelianGroup.of_injective`
theorem ι_injective [Nontrivial R] : Function.Injective (ι R : X → FreeAlgebra R X) :=
  fun x y hoxy ↦
  by_contradiction <| by
    classical exact fun hxy : x ≠ y ↦
        let f : FreeAlgebra R X →ₐ[R] R := lift R fun z ↦ if x = z then (1 : R) else 0
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
theorem ι_ne_algebraMap [Nontrivial R] (x : X) (r : R) : ι R x ≠ algebraMap R _ r := fun h ↦ by
  let f0 : FreeAlgebra R X →ₐ[R] R := lift R 0
  -- ⊢ False
  let f1 : FreeAlgebra R X →ₐ[R] R := lift R 1
  -- ⊢ False
  have hf0 : f0 (ι R x) = 0 := lift_ι_apply _ _
  -- ⊢ False
  have hf1 : f1 (ι R x) = 1 := lift_ι_apply _ _
  -- ⊢ False
  rw [h, f0.commutes, Algebra.id.map_eq_self] at hf0
  -- ⊢ False
  rw [h, f1.commutes, Algebra.id.map_eq_self] at hf1
  -- ⊢ False
  exact zero_ne_one (hf0.symm.trans hf1)
  -- 🎉 no goals
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
`CoeSort` below. Closing it and reopening it fixes it... -/
namespace FreeAlgebra

/-- An induction principle for the free algebra.

If `C` holds for the `algebraMap` of `r : R` into `FreeAlgebra R X`, the `ι` of `x : X`, and is
preserved under addition and muliplication, then it holds for all of `FreeAlgebra R X`.
-/
@[elab_as_elim]
theorem induction {C : FreeAlgebra R X → Prop}
    (h_grade0 : ∀ r, C (algebraMap R (FreeAlgebra R X) r)) (h_grade1 : ∀ x, C (ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b)) (h_add : ∀ a b, C a → C b → C (a + b))
    (a : FreeAlgebra R X) : C a := by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from X
  let s : Subalgebra R (FreeAlgebra R X) :=
    { carrier := C
      mul_mem' := h_mul _ _
      add_mem' := h_add _ _
      algebraMap_mem' := h_grade0 }
  let of : X → s := Subtype.coind (ι R) h_grade1
  -- ⊢ C a
  -- the mapping through the subalgebra is the identity
  have of_id : AlgHom.id R (FreeAlgebra R X) = s.val.comp (lift R of) := by
    ext
    simp [Subtype.coind]
  -- finding a proof is finding an element of the subalgebra
  suffices : a = lift R of a
  -- ⊢ C a
  · rw [this]
    -- ⊢ C ↑(↑(↑(lift R) of) a)
    exact Subtype.prop (lift R of a)
    -- 🎉 no goals
  simp [AlgHom.ext_iff] at of_id
  -- ⊢ a = ↑(↑(↑(lift R) of) a)
  exact of_id a
  -- 🎉 no goals
#align free_algebra.induction FreeAlgebra.induction

end FreeAlgebra
