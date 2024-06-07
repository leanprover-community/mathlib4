/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/

import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!

# Fibers of functors

In this file we introduce a typeclass `HasFibers` for a functor `p : 𝒳 ⥤ 𝒮`, consisting of:
- A collection of categories `Fib S` for every `S` in `𝒮` (the fiber categories)
- Functors `ι : Fib S ⥤ 𝒳` such that `ι ⋙ p = const (Fib S) S
- The induced functor `Fib S ⥤ Fiber p S` is an equivalence.

The reason for introducing this typeclass is that in practice, when working with (pre)fibered
categories one often already has a collection of categories `Fib S` for every `S` that are
equivalent to the fibers `Fiber p S`. One would then like to use these categories `Fib S` directly,
instead of working through this equivalence of categories. By developing an API for the `HasFibers`
typeclass, this will be possible.


TODO: fix this comment based on new changes
For example, we develop the following lemmas:
- `HasFibersEssSurj` any object `a : 𝒳` lying over some `S : 𝒮` is isomorphic to the image of some
`a' : Fib S`
- `HasFibersPullback` allows one to take pullbacks such that the codomain lies in one of the fibers
`Fib S`.
- `HasFibersFactorization` (TODO: maybe call it `HasFibersInducedMap`, and the next
`HasFibersFactorization`)
- `fiber_factorization` any morphism in `𝒳` can be factored as a morphism in some fiber `Fib S`
followed by a pullback. (TODO: rename this lemma)

Here is an example of when this typeclass is useful. Suppose we have a presheaf of types
`F : 𝒮ᵒᵖ ⥤ Type _`. The associated fibered category then has objects `(S, a)` where `S : 𝒮` and `a`
is an element of `F(S)`. The fiber category `Fiber p S` is then equivalent to the discrete category
`Fib S` with objects `a` in `F(S)`. In this case, the `HasFibers` instance is given by the
categories `F(S)` and the functor `ι` sends `a : F(S)` to `(S, a)` in the fibered category. See
`Presheaf.lean` for more details.

-/

universe v₁ u₁ v₂ u₂

open CategoryTheory Functor Category IsCartesian IsHomLift Fiber

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- HasFibers is an extrinsic notion of fibers on a functor `p : 𝒳 ⥤ 𝒮`. It is given by a
collection of categories `Fib S` for every `S : 𝒮` (the fiber categories), each equiped with a
functors `ι : Fib S ⥤ 𝒳` which map constantly to `S` on the base such that the induced functor
`Fib S ⥤ Fiber p S` is an equivalence. -/
class HasFibers (p : 𝒳 ⥤ 𝒮) where
  /-- The type of objects of the category `Fib S` for each `S`. -/
  Fib (S : 𝒮) : Type _
  /-- `Fib S` is a category. -/
  isCategory (S : 𝒮) : Category (Fib S)
  /-- The functor `ι : Fib S ⥤ 𝒳`. -/
  ι (S : 𝒮) : (Fib S) ⥤ 𝒳
  /-- The composition with the functor `p` is *equal* to the constant functor mapping to `S`. -/
  comp_const (S : 𝒮) : (ι S) ⋙ p = (const (Fib S)).obj S
  /-- The induced functor from `Fib S` to the fiber of `𝒳 ⥤ 𝒮` over `S` is an equivalence. -/
  equiv (S : 𝒮) : Functor.IsEquivalence (InducedFunctor (comp_const S))

namespace HasFibers

/-- The `HasFibers` on `p : 𝒳 ⥤ 𝒮` given by the fibers of `p` -/
@[default_instance]
instance canonical (p : 𝒳 ⥤ 𝒮) : HasFibers p where
  Fib := Fiber p
  ι := FiberInclusion p
  comp_const := FiberInclusion.comp_const p
  equiv S := by
    apply isEquivalence_of_iso (F := 𝟭 (Fiber p S))
    exact {
      hom := { app := fun x ↦ ⟨𝟙 x.1, IsHomLift.id x.2⟩ }
      inv := { app := fun x ↦ ⟨𝟙 x.1, IsHomLift.id x.2⟩ }
    }

section

variable (p : 𝒳 ⥤ 𝒮) [HasFibers p] (S : 𝒮)

instance : Category (Fib p S) := isCategory S

/-- The induced functor from `Fib p S` to the standard fiber. -/
@[simps!]
def InducedFunctor : Fib p S ⥤ Fiber p S :=
  Fiber.InducedFunctor (comp_const S)

/-- The natural transformation `ι S ≅ (InducedFunctor p S) ⋙ (FiberInclusion p S)` -/
def InducedFunctor.NatIso : ι S ≅ (InducedFunctor p S) ⋙ (FiberInclusion p S) :=
  Fiber.InducedFunctor.NatIso (comp_const S)

lemma inducedFunctor_comp : ι S = (InducedFunctor p S) ⋙ (FiberInclusion p S) :=
  Fiber.inducedFunctor_comp (comp_const S)

instance : Functor.IsEquivalence (InducedFunctor p S) := equiv S

instance : Functor.Faithful (ι (p:=p) S) :=
  Functor.Faithful.of_iso (InducedFunctor.NatIso p S).symm

end

section

variable {p : 𝒳 ⥤ 𝒮} [HasFibers p]

@[simp]
lemma proj_eq {S : 𝒮} (a : Fib p S) : p.obj ((ι S).obj a) = S :=
  by simp only [← comp_obj, comp_const, const_obj_obj]

/-- The morphism `R ⟶ S` in `𝒮` obtained by projecting a morphism
`φ : (ι R).obj a ⟶ (ι S).obj b`. -/
def proj_map {R S : 𝒮} {a : Fib p R} {b : Fib p S}
    (φ : (ι R).obj a ⟶ (ι S).obj b) : R ⟶ S :=
  eqToHom (proj_eq a).symm ≫ (p.map φ) ≫ eqToHom (proj_eq b)

/-- For any homomorphism φ in a fiber Fib S, its image under ι S lies over 𝟙 S -/
instance homLift {S : 𝒮} {a b : Fib p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) ((ι S).map φ) := by
  apply of_fac p _ _ (proj_eq a) (proj_eq b)
  rw [← Functor.comp_map, Functor.congr_hom (comp_const S)]
  simp

/-- A version of fullness of the functor `Fib S ⥤ Fiber p S` that can be used inside the category
`𝒳`. -/
@[simp]
noncomputable def mapPreimage {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
    [IsHomLift p (𝟙 S) φ] : a ⟶ b :=
  (InducedFunctor _ S).preimage (mk_map p S φ)

@[simp]
lemma mapPreimage_eq {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
    [IsHomLift p (𝟙 S) φ] : (ι S).map (mapPreimage φ) = φ := by
  simp [congr_hom (inducedFunctor_comp p S)]

/-- The lift of an isomorphism `Φ : (ι S).obj a ≅ (ι S).obj b` lying over `𝟙 S` to an isomorphism
in `Fib S`. -/
noncomputable def LiftIso {S : 𝒮} {a b : Fib p S}
    (Φ : (ι S).obj a ≅ (ι S).obj b) (hΦ : IsHomLift p (𝟙 S) Φ.hom) : a ≅ b := by
  let a' : Fiber p S := (InducedFunctor p S).obj a
  let b' : Fiber p S := (InducedFunctor p S).obj b
  let Φ' : a' ≅ b' := {
    hom := ⟨Φ.hom, hΦ⟩
    inv := ⟨Φ.inv, inferInstance⟩ }
  exact ((InducedFunctor p S).preimageIso Φ')

/-- An object in `Fib p S` isomorphic in `𝒳` to a given object `a : 𝒳` such that `p(a) = S`. -/
noncomputable def objPreimage {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fib p S :=
  Functor.objPreimage (InducedFunctor p S) (Fiber.mk_obj ha)

/-- Applying `ι S` to the preimage of `a : 𝒳` in `Fib p S` yields an object isomorphic to `a`. -/
noncomputable def objObjPreimageIso {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    (ι S).obj (objPreimage ha) ≅ a :=
  (FiberInclusion p S).mapIso (Functor.objObjPreimageIso (InducedFunctor p S) (Fiber.mk_obj ha))

instance objObjPreimageIso.IsHomLift {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    IsHomLift p (𝟙 S) (objObjPreimageIso ha).hom :=
  (Functor.objObjPreimageIso (InducedFunctor p S) (Fiber.mk_obj ha)).hom.2

section

variable [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (f : R ⟶ S) (ha : p.obj a = S)

/-- The domain, taken in `Fib p R`, of some cartesian morphism lifting a given
`f : R ⟶ S` in `𝒮` -/
noncomputable def pullbackObj : Fib p R :=
  objPreimage (domain_eq p f (IsPreFibered.pullbackMap ha f))

/-- A cartesian morphism lifting `f : R ⟶ S` with domain in the image of `Fib p R` -/
noncomputable def pullbackMap : (ι R).obj (pullbackObj f ha) ⟶ a :=
  (objObjPreimageIso (domain_eq p f (IsPreFibered.pullbackMap ha f))).hom ≫
    (IsPreFibered.pullbackMap ha f)

instance pullbackMap.isCartesian : IsCartesian p f (pullbackMap f ha) := by
  conv => congr; rfl; rw [← id_comp f]
  simp only [id_comp, pullbackMap]
  infer_instance

end

section

variable [IsFibered p] {R S : 𝒮} {a : 𝒳} {b b' : Fib p R} (f : R ⟶ S) (ψ : (ι R).obj b' ⟶ a)
    [IsCartesian p f ψ] (φ : (ι R).obj b ⟶ a) [IsHomLift p f φ]

/-- Given a fibered category p, b' b in Fib R, and a pullback ψ : b ⟶ a in 𝒳, i.e.
```
b'       b --ψ--> a
|        |        |
v        v        v
R ====== R --f--> S
```
Then the induced map τ : b' ⟶ b can be lifted to the fiber over R -/
noncomputable def inducedMap : b ⟶ b' :=
  mapPreimage (IsCartesian.inducedMap p f ψ φ)

lemma inducedMap_comp : (ι R).map (inducedMap f ψ φ) ≫ ψ = φ := by
  simp only [inducedMap, mapPreimage_eq, IsCartesian.inducedMap_comp]

end

section

variable [IsFibered p] {R S : 𝒮} {a : 𝒳} (ha : p.obj a = S) {b : Fib p R} (f : R ⟶ S)
  (φ : (ι R).obj b ⟶ a) [IsHomLift p f φ]

/-- Given `a : 𝒳`, `b : Fib p R`, and a diagram
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
with `ψ` cartesian over `f` and `τ` a map in `Fib p R`. -/
lemma fiber_factorization : ∃ (b' : Fib p R) (τ : b ⟶ b') (ψ : (ι R).obj b' ⟶ a),
    IsStronglyCartesian p f ψ ∧ (((ι R).map τ) ≫ ψ = φ) :=
  let ψ := pullbackMap f ha
  ⟨pullbackObj f ha, inducedMap f ψ φ, ψ, inferInstance, inducedMap_comp f ψ φ⟩

end

end

end HasFibers
