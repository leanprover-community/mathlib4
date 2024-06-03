/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Functor.Const

/-!
# Fibers of functors
In this file we develop the theory of fibers of functors. Given a functor `p : 𝒳 ⥤ 𝒮`, we define
the fiber categories `Fiber p S` for every `S : 𝒮` as follows:
- An object in `Fiber p S` is a pair `(a, ha)` where `a : 𝒳` and `ha : p.obj a = S`.
- A morphism in `Fiber p S` is a morphism `φ : a ⟶ b` in 𝒳 such that `p.map φ = 𝟙 S`.

We also introduce a typeclass `HasFibers` for a functor `p : 𝒳 ⥤ 𝒮`, consisting of:
- A collection of categories `Fib S` for every `S` in `𝒮` (the fiber categories)
- Functors `ι : Fib S ⥤ 𝒳` such that `ι ⋙ p = const (Fib S) S
- The induced functor `Fib S ⥤ Fiber p S` is an equivalence.

The reason for introducing this typeclass is that in practice, when working with fibered categories
one often already has a collection of categories `Fib S` for every `S` that are equivalent to the fibers
`Fiber p S`. One would then like to use these categories `Fib S` directly, instead of working through this
equivalence of categories. By developing an API for the `HasFibers` typeclass, this will be possible.
For example, we develop the following lemmas:
- `HasFibersEssSurj` any object `a : 𝒳` lying over some `S : 𝒮` is isomorphic to the image of some `a' : Fib S`
- `HasFibersPullback` allows one to take pullbacks such that the codomain lies in one of the fibers `Fib S`.
- `HasFibersFactorization` (TODO: maybe call it `HasFibersInducedMap`, and the next `HasFibersFactorization`)
- `fiber_factorization` any morphism in `𝒳` can be factored as a morphism in some fiber `Fib S` followed by
  a pullback. (TODO: rename this lemma)

Here is an example of when this typeclass is useful. Suppose we have a presheaf of types `F : 𝒮ᵒᵖ ⥤ Type _`.
The associated fibered category then has objects `(S, a)` where `S : 𝒮` and `a` is an element of `F(S)`.
The fiber category `Fiber p S` is then equivalent to the discrete category `Fib S` with objects `a` in `F(S)`.
In this case, the `HasFibers` instance is given by the categories `F(S)` and the functor `ι` sends
`a : F(S)` to `(S, a)` in the fibered category. See `Presheaf.lean` for more details.
-/

-- TODO: port this to use `BasedCategory` later.
-- FiberCat should then be defined in this file, move out any `IsFibered` propoerties to `FiberedCat.lean`

universe u₁ v₁ u₂ v₂ u₃ w

open CategoryTheory Functor Category IsCartesian IsHomLift Fiber

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

-- TODO: should it be this namespace?fiber

/-- HasFibers is an exttrinsic notion of fibers on a functor p : 𝒳 ⥤ 𝒮. It is given by a collection
of categories Fib S for every S in 𝒮 (the fiber categories), equiped with functors ι : Fib S ⥤ 𝒳
which map constantly to S on the base such that the induced functor Fib S ⥤ Fiber p S is an equivalence. -/
class HasFibers (p : 𝒳 ⥤ 𝒮) where
  Fib (S : 𝒮) : Type _
  [isCategory (S : 𝒮) : Category (Fib S)]
  (ι (S : 𝒮) : (Fib S) ⥤ 𝒳)
  (comp_const (S : 𝒮) : (ι S) ⋙ p = (const (Fib S)).obj S)
  [equiv (S : 𝒮) : Functor.IsEquivalence (FiberInducedFunctor (comp_const S))]

instance {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} : Category (hp.Fib S) := hp.isCategory S

namespace HasFibers

@[simps!]
def InducedFunctor (p : 𝒳 ⥤ 𝒮) [hp : HasFibers p] (S : 𝒮) : hp.Fib S ⥤ Fiber p S :=
  FiberInducedFunctor (hp.comp_const S)

def InducedFunctorNat (p : 𝒳 ⥤ 𝒮) [hp : HasFibers p] (S : 𝒮) :
    hp.ι S ≅ (hp.InducedFunctor S) ⋙ (FiberInclusion p S) :=
  FiberInducedFunctorNat (hp.comp_const S)

lemma InducedFunctorComp (p : 𝒳 ⥤ 𝒮) [hp : HasFibers p] (S : 𝒮) :
    hp.ι S = (hp.InducedFunctor S) ⋙ (FiberInclusion p S) :=
  FiberInducedFunctorComp (hp.comp_const S)

-- TODO: state these in terms of InducedFunctor
instance {p : 𝒳 ⥤ 𝒮} [HasFibers p] {S : 𝒮} : Functor.IsEquivalence (InducedFunctor p S) :=
  equiv S

instance {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} : Functor.Faithful (hp.ι S) :=
  Functor.Faithful.of_iso (hp.InducedFunctorNat S).symm

-- BASIC API CONSTRUCTIONS
def HasFibersProj {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S R : 𝒮} {a : hp.Fib S} {b : hp.Fib R}
  (φ : (hp.ι S).obj a ⟶ (hp.ι R).obj b) : S ⟶ R := sorry

@[simp]
lemma HasFibersObjLift {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} (a : hp.Fib S) : p.obj ((hp.ι S).obj a) = S :=
  by simp only [←comp_obj, hp.comp_const, const_obj_obj]

/-- For any homomorphism φ in a fiber Fib S, its image under ι S lies over 𝟙 S -/
instance HasFibersHomLift {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a b : hp.Fib S}
    (φ : a ⟶ b) : IsHomLift p (𝟙 S) ((hp.ι S).map φ) := by
  apply of_fac p _ _ (HasFibersObjLift a) (HasFibersObjLift b)
  rw [←Functor.comp_map, Functor.congr_hom (hp.comp_const S)] -- Can easily be replaced if we decide to work up to iso
  simp

/- Now we define the standard/canonical fiber associated to a fibered category.
When the user does not wish to supply specific fiber categories, this will be the default choice. -/
def Fiber.comp_const_nat (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (FiberInclusion p S) ⋙ p ≅ (const (Fiber p S)).obj S where
  hom := {
    app := fun x => eqToHom x.prop
    naturality := fun x y φ => by simpa using (commSq p (𝟙 S) φ.val).w}
  inv := {
    app := fun x => eqToHom (x.prop).symm
    naturality := fun x y φ =>  by
      -- TODO: add this have into API?
      have := by simpa [comp_eqToHom_iff] using (commSq p (𝟙 S) φ.val).w
      simp [this] }

lemma Fiber.comp_const (p : 𝒳 ⥤ 𝒮) (S : 𝒮) : (FiberInclusion p S) ⋙ p = (const (Fiber p S)).obj S := by
  apply Functor.ext_of_iso (Fiber.comp_const_nat p S)
  all_goals intro x; simp [comp_const_nat, x.2]

@[default_instance]
instance canonical (p : 𝒳 ⥤ 𝒮) : HasFibers p where
  Fib := Fiber p
  ι := FiberInclusion p
  comp_const := Fiber.comp_const p
  equiv S := by sorry -- could this be simp + inferinstance??

  -- fun S => {
  --   inverse :=  𝟭 (Fiber p S)
  --   unitIso := {
  --     hom := { app := fun x => ⟨𝟙 x.1, IsHomLift.id x.2⟩ }
  --     inv := { app := fun x => ⟨𝟙 x.1, IsHomLift.id x.2⟩ } }
  --   counitIso := {
  --     hom := { app := fun x => ⟨𝟙 x.1, IsHomLift.id x.2⟩}
  --     inv := { app := fun x => ⟨𝟙 x.1, IsHomLift.id x.2⟩} } }

/-- A version of fullness of the functor `Fib S ⥤ Fiber p S` that can be used inside the category `𝒳` -/
lemma HasFibersFull {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a b : hp.Fib S}
    (φ : (hp.ι S).obj a ⟶ (hp.ι S).obj b) [IsHomLift p (𝟙 S) φ] :
    ∃ (ψ : a ⟶ b), (hp.ι S).map ψ = φ := by

  let a' : Fiber p S := (InducedFunctor p S).obj a
  let b' : Fiber p S := (InducedFunctor p S).obj b
  let ψ : a' ⟶ b' := ⟨φ, inferInstance⟩
  use (InducedFunctor _ S).preimage ψ

  rw [←NatIso.naturality_2 (FiberInducedFunctorNat (hp.comp_const S))]
  -- TODO: this should all be simp after appropriate `@[simp]s`
  simp
  rw [congr_hom (InducedFunctorComp p S)]
  simp

/-- Any isomorphism `Φ : (hp.ι S).obj a ≅ (hp.ι S).obj b` lying over `𝟙 S` can be lifted to an isomorphism in `Fib S` -/
noncomputable def HasFibersPreimageIso {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a b : hp.Fib S}
    (Φ : (hp.ι S).obj a ≅ (hp.ι S).obj b) (hΦ : IsHomLift p (𝟙 S) Φ.hom) : a ≅ b := by
  let a' : Fiber p S := (InducedFunctor p S).obj a
  let b' : Fiber p S := (InducedFunctor p S).obj b
  let Φ' : a' ≅ b' := {
    hom := ⟨Φ.hom, hΦ⟩
    inv := ⟨Φ.inv, sorry⟩ -- THIS SHOULD BE INFERINSTANCE
  }
  exact ((hp.InducedFunctor S).preimageIso Φ')


/-- A version of essential surjectivity of the functor `Fib S ⥤ FiberI'm not convinced about using IsHomLift as a class anymore, basically for the following two reasons:

    IsHomLift p f φ makes it so that I can leave parameters p, f, φ implicit, which makes it slightly more convenient to apply lemmas which has it as a parameter. Especially in situations where the expressions for f and φ are somewhat complicated (involving eqToHoms ) it would be quite convenient to not have to write them down explicitly.
    There are often situations where type-class inference can't infer IsHomLift, and having it as a class makes it quite inconvenient to try and give this instance explicitly. For example the following lemma is very simple, but can't be inferred by type-class inference:
    protected lemma id {p : 𝒳 ⥤ 𝒮} {R : 𝒮} {a : 𝒳} (ha : p.obj a = R) : p.IsHomLift (𝟙 R) (𝟙 a) := .
    So whenever I want to use this instance, I have to either have another line before with a have statement, which feels inconvenient for such a simple lemma, or use @ notation.

Also, I havn't felt many of the benefits of having it as a class, I think the only noticeable thing to me is that IsHomLift.comp can be inferred can be quite nice.

It is very possible that I am not fully using the benefits of having a class (and that these issues shouldn't arise if I use it correctly), so please take what I say with a  p S` that can be used inside the category `𝒳` -/
lemma HasFibersEssSurj {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
  ∃ (b : hp.Fib S) (φ : (hp.ι S).obj b ⟶ a), IsIso φ ∧ IsHomLift p (𝟙 S) φ := by
  -- This will be easy to inline
  use Functor.objPreimage (InducedFunctor p S) (Fiber.mk_obj ha)
  let Φ := Functor.objObjPreimageIso (InducedFunctor p S) (Fiber.mk_obj ha)
  use (FiberInclusion p S).map Φ.hom
  refine ⟨inferInstance, Φ.hom.2⟩

lemma HasFibersEssSurj' {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    ∃ (b : hp.Fib S) (φ : (hp.ι S).obj b ≅ a), IsHomLift p (𝟙 S) φ.hom := by
  -- This will be easy to inline
  use Functor.objPreimage (InducedFunctor p S) (Fiber.mk_obj ha)
  let Φ := Functor.objObjPreimageIso (InducedFunctor p S) (Fiber.mk_obj ha)
  refine ⟨(FiberInclusion p S).mapIso Φ, Φ.hom.2⟩

-- MIGHT NOT NEED....
def HasFibersMap {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] {R S : 𝒮} {a : hp.Fib S}
    {b : hp.Fib R} (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a) : R ⟶ S :=
  eqToHom (HasFibersObjLift b).symm ≫ (p.map φ) ≫ eqToHom (HasFibersObjLift a)

/-- Given a `HasFibers` instance and a diagram
```
           a
           -
           |
           v
  R --f--> S
```
with a in Fib S, we can take a pullback b = `R ×_S a` in Fib R -/
lemma HasFibersPullback {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮} (a : hp.Fib S)
    (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a), IsStronglyCartesian p f φ := by
  obtain ⟨b, φ, hφ⟩ := IsPreFibered.has_pullbacks (HasFibersObjLift a) f
  obtain ⟨b', ψ, ⟨_, hψ⟩⟩ := HasFibersEssSurj (domain_eq p f φ)
  use b', ψ ≫ φ
  rw [←id_comp f]
  exact IsStronglyCartesian.comp p

-- TODO MAYBE REPLACE THE ABOVE WITH THIS LEMMA
lemma HasFibersPullback' {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮} {a : 𝒳}
    (ha : p.obj a = S) (f : R ⟶ S) : ∃ (b : hp.Fib R) (φ : (hp.ι R).obj b ⟶ a),
      IsStronglyCartesian p f φ := by
  rcases IsPreFibered.has_pullbacks ha f with ⟨b, φ, hφ⟩
  rcases HasFibersEssSurj (domain_eq p f φ) with ⟨b', ψ, ⟨_, hψ⟩⟩
  use b', ψ ≫ φ
  rw [←id_comp f]
  exact IsStronglyCartesian.comp p

/-- Given a fibered category p, b' b in Fib R, an a pullback ψ : b ⟶ a in 𝒳, i.e.
```
b'       b --ψ--> a
|        |        |
v        v        v
R ====== R --f--> S
```
Then the induced map τ : b' ⟶ b to lies in the fiber over R -/
lemma HasFibersFactorization {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮}
    {a : 𝒳} {b b' : hp.Fib R} (f : R ⟶ S) (φ : (hp.ι R).obj b ⟶ a)
    [IsHomLift p f φ] (ψ : (hp.ι R).obj b' ⟶ a) [IsStronglyCartesian p f ψ] :
      ∃ (τ : b ⟶ b'), (hp.ι R).map τ ≫ ψ = φ := by
  -- By fullness, we can pull back τ to the fiber over R
  obtain ⟨τ, hτ⟩ := HasFibersFull (inducedMap p f ψ φ) --(InducedMap_isHomLift hψ (id_comp f).symm hφ)
  use τ
  rw [hτ]
  exact (inducedMap_comp p f ψ φ)

noncomputable def HasFibersInducedMap {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮}
    {a : 𝒳} {b b' : hp.Fib R} (f : R ⟶ S) (φ : (hp.ι R).obj b ⟶ a)
    [IsHomLift p f φ] (ψ : (hp.ι R).obj b' ⟶ a) [IsStronglyCartesian p f ψ] : b ⟶ b' :=
  Classical.choose (HasFibersFactorization f φ ψ)

-- TODO FORMULATE...
/- lemma HasFibersFactorizationUnique {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮}
  {a : 𝒳} {b b' : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ a}
  (hφ : IsHomLift p f φ) {ψ : (hp.ι R).obj b' ⟶ a} (hψ : IsPullback p f ψ) : -/


-- TODO: In this lemma, should maybe just require that a lies over S (not necc in the fiber)
/-- Given a in Fib S, b in Fib R, and a diagram
```
  b --φ--> a
  -        -
  |        |
  v        v
  R --f--> S
```
It can be factorized as
```
  b --τ--> b'--ψ--> a
  -        -        -
  |        |        |
  v        v        v
  R ====== R --f--> S
```
with ψ a pullback of f and τ a map in Fib R -/
lemma fiber_factorization {p : 𝒳 ⥤ 𝒮} [hp : HasFibers p] [IsFibered p] {R S : 𝒮}
    {a : hp.Fib S} {b : hp.Fib R} {f : R ⟶ S} {φ : (hp.ι R).obj b ⟶ (hp.ι S).obj a}
    [IsHomLift p f φ] : ∃ (b' : hp.Fib R) (τ : b ⟶ b') (ψ : (hp.ι R).obj b' ⟶ (hp.ι S).obj a),
      IsStronglyCartesian p f ψ ∧ (((hp.ι R).map τ) ≫ ψ = φ) := by
  obtain ⟨b', ψ, hψ⟩ := (HasFibersPullback a f)
  obtain ⟨τ, hτ⟩ := HasFibersFactorization f φ ψ
  use b', τ, ψ, hψ

end HasFibers
