/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Paul Lezeau
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Util.CompileInductive

/-!

# Fibers of functors

In this file we introduce a typeclass `HasFibers` for a functor `p : 𝒳 ⥤ 𝒮`, consisting of:
- A collection of categories `Fib S` for every `S` in `𝒮` (the fiber categories)
- Functors `ι : Fib S ⥤ 𝒳` such that `ι ⋙ p = const (Fib S) S`
- The induced functor `Fib S ⥤ Fiber p S` is an equivalence.

We also provide a canonical `HasFibers` instance, which uses the standard fibers `Fiber p S`
(see `Mathlib/CategoryTheory/FiberedCategory/Fiber.lean`). This makes it so that any result proven
about `HasFibers` can be used for the standard fibers as well.

The reason for introducing this typeclass is that in practice, when working with (pre)fibered
categories one often already has a collection of categories `Fib S` for every `S` that are
equivalent to the fibers `Fiber p S`. One would then like to use these categories `Fib S` directly,
instead of working through this equivalence of categories. By developing an API for the `HasFibers`
typeclass, this will be possible.

Here is an example of when this typeclass is useful. Suppose we have a presheaf of types
`F : 𝒮ᵒᵖ ⥤ Type _`. The associated fibered category then has objects `(S, a)` where `S : 𝒮` and `a`
is an element of `F(S)`. The fiber category `Fiber p S` is then equivalent to the discrete category
`Fib S` with objects `a` in `F(S)`. In this case, the `HasFibers` instance is given by the
categories `F(S)` and the functor `ι` sends `a : F(S)` to `(S, a)` in the fibered category.

## Main API
The following API is developed so that the fibers from a `HasFibers` instance can be used
analogously to the standard fibers.

- `Fib.homMk φ` is a lift of a morphism `φ : (ι S).obj a ⟶ (ι S).obj b` in `𝒳`, which lies over
  `𝟙 S`, to a morphism in the fiber over `S`.
- `Fib.mk` gives an object in the fiber over `S` which is isomorphic to a given `a : 𝒳` that
  satisfies `p(a) = S`. The isomorphism is given by `Fib.mkIsoSelf`.
- `HasFibers.mkPullback` is a version of `IsPreFibered.mkPullback` which ensures that the object
  lies in a given fiber. The corresponding Cartesian morphism is given by `HasFibers.pullbackMap`.
- `HasFibers.inducedMap` is a version of `IsCartesian.inducedMap` which gives the corresponding
  morphism in the fiber category.
- `fiber_factorization` is the statement that any morphism in `𝒳` can be factored as a morphism in
  some fiber followed by a pullback.

-/

@[expose] public section

universe v₃ u₃ v₂ u₂ v₁ u₁

open CategoryTheory Functor Category IsCartesian IsHomLift Fiber

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- HasFibers is an extrinsic notion of fibers on a functor `p : 𝒳 ⥤ 𝒮`. It is given by a
collection of categories `Fib S` for every `S : 𝒮` (the fiber categories), each equipped with a
functors `ι : Fib S ⥤ 𝒳` which map constantly to `S` on the base such that the induced functor
`Fib S ⥤ Fiber p S` is an equivalence. -/
@[nolint checkUnivs]
class HasFibers (p : 𝒳 ⥤ 𝒮) where
  /-- The type of objects of the category `Fib S` for each `S`. -/
  Fib (S : 𝒮) : Type u₃
  /-- `Fib S` is a category. -/
  category (S : 𝒮) : Category.{v₃} (Fib S) := by infer_instance
  /-- The functor `ι : Fib S ⥤ 𝒳`. -/
  ι (S : 𝒮) : Fib S ⥤ 𝒳
  /-- The composition with the functor `p` is *equal* to the constant functor mapping to `S`. -/
  comp_const (S : 𝒮) : ι S ⋙ p = (const (Fib S)).obj S
  /-- The induced functor from `Fib S` to the fiber of `𝒳 ⥤ 𝒮` over `S` is an equivalence. -/
  equiv (S : 𝒮) : Functor.IsEquivalence (inducedFunctor (comp_const S)) := by infer_instance

namespace HasFibers

/-- The `HasFibers` on `p : 𝒳 ⥤ 𝒮` given by the fibers of `p` -/
@[implicit_reducible]
def canonical (p : 𝒳 ⥤ 𝒮) : HasFibers p where
  Fib := Fiber p
  ι S := fiberInclusion
  comp_const S := fiberInclusion_comp_eq_const
  equiv S := by exact isEquivalence_of_iso (F := 𝟭 (Fiber p S)) (Iso.refl _)

section

variable (p : 𝒳 ⥤ 𝒮) [HasFibers p] (S : 𝒮)

attribute [instance_reducible, instance] category

/-- The induced functor from `Fib p S` to the standard fiber. -/
@[simps!]
def inducedFunctor : Fib p S ⥤ Fiber p S :=
  Fiber.inducedFunctor (comp_const S)

/-- The natural transformation `ι S ≅ (inducedFunctor p S) ⋙ (fiberInclusion p S)` -/
def inducedFunctor.natIso : ι S ≅ (inducedFunctor p S) ⋙ fiberInclusion :=
  Fiber.inducedFunctorCompIsoSelf (comp_const S)

lemma inducedFunctor_comp : ι S = (inducedFunctor p S) ⋙ fiberInclusion :=
  Fiber.inducedFunctor_comp (comp_const S)

instance : Functor.IsEquivalence (inducedFunctor p S) := equiv S

instance : Functor.Faithful (ι (p := p) S) :=
  Functor.Faithful.of_iso (inducedFunctor.natIso p S).symm

end

section

variable {p : 𝒳 ⥤ 𝒮} [HasFibers p]

@[simp]
lemma proj_eq {S : 𝒮} (a : Fib p S) : p.obj ((ι S).obj a) = S := by
  simp only [← comp_obj, comp_const, const_obj_obj]

/-- The morphism `R ⟶ S` in `𝒮` obtained by projecting a morphism
`φ : (ι R).obj a ⟶ (ι S).obj b`. -/
def projMap {R S : 𝒮} {a : Fib p R} {b : Fib p S}
    (φ : (ι R).obj a ⟶ (ι S).obj b) : R ⟶ S :=
  eqToHom (proj_eq a).symm ≫ (p.map φ) ≫ eqToHom (proj_eq b)

/-- For any homomorphism `φ` in a fiber `Fib S`, its image under `ι S` lies over `𝟙 S`. -/
instance homLift {S : 𝒮} {a b : Fib p S} (φ : a ⟶ b) : IsHomLift p (𝟙 S) ((ι S).map φ) := by
  apply of_fac p _ _ (proj_eq a) (proj_eq b)
  rw [← Functor.comp_map, Functor.congr_hom (comp_const S)]
  simp

/-- A version of fullness of the functor `Fib S ⥤ Fiber p S` that can be used inside the category
`𝒳`. -/
noncomputable def Fib.homMk {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
    [IsHomLift p (𝟙 S) φ] : a ⟶ b :=
  (inducedFunctor _ S).preimage (Fiber.homMk p S φ)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma Fib.map_homMk {S : 𝒮} {a b : Fib p S} (φ : (ι S).obj a ⟶ (ι S).obj b)
    [IsHomLift p (𝟙 S) φ] : (ι S).map (homMk φ) = φ := by
  simp [Fib.homMk, congr_hom (inducedFunctor_comp p S)]

@[ext]
lemma Fib.hom_ext {S : 𝒮} {a b : Fib p S} {f g : a ⟶ b}
    (h : (ι S).map f = (ι S).map g) : f = g :=
  (ι S).map_injective h

/-- The lift of an isomorphism `Φ : (ι S).obj a ≅ (ι S).obj b` lying over `𝟙 S` to an isomorphism
in `Fib S`. -/
@[simps]
noncomputable def Fib.isoMk {S : 𝒮} {a b : Fib p S}
    (Φ : (ι S).obj a ≅ (ι S).obj b) (hΦ : IsHomLift p (𝟙 S) Φ.hom) : a ≅ b where
  hom := Fib.homMk Φ.hom
  inv := Fib.homMk Φ.inv

/-- An object in `Fib p S` isomorphic in `𝒳` to a given object `a : 𝒳` such that `p(a) = S`. -/
noncomputable def Fib.mk {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) : Fib p S :=
  Functor.objPreimage (inducedFunctor p S) (Fiber.mk ha)

/-- Applying `ι S` to the preimage of `a : 𝒳` in `Fib p S` yields an object isomorphic to `a`. -/
noncomputable def Fib.mkIsoSelf {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    (ι S).obj (Fib.mk ha) ≅ a :=
  fiberInclusion.mapIso (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha))

instance Fib.mkIsoSelfIsHomLift {S : 𝒮} {a : 𝒳} (ha : p.obj a = S) :
    IsHomLift p (𝟙 S) (Fib.mkIsoSelf ha).hom :=
  (Functor.objObjPreimageIso (inducedFunctor p S) (Fiber.mk ha)).hom.2

section

variable [IsPreFibered p] {R S : 𝒮} {a : 𝒳} (f : R ⟶ S) (ha : p.obj a = S)

/-- The domain, taken in `Fib p R`, of some Cartesian morphism lifting a given
`f : R ⟶ S` in `𝒮` -/
noncomputable def mkPullback : Fib p R :=
  Fib.mk (domain_eq p f (IsPreFibered.pullbackMap ha f))

/-- A Cartesian morphism lifting `f : R ⟶ S` with domain in the image of `Fib p R` -/
noncomputable def pullbackMap : (ι R).obj (mkPullback f ha) ⟶ a :=
  (Fib.mkIsoSelf (domain_eq p f (IsPreFibered.pullbackMap ha f))).hom ≫
    (IsPreFibered.pullbackMap ha f)

set_option backward.isDefEq.respectTransparency false in
instance pullbackMap.isCartesian : IsCartesian p f (pullbackMap f ha) := by
  conv in f => rw [← id_comp f]
  simp only [id_comp, pullbackMap]
  infer_instance

end

section

variable {R S : 𝒮} {a : 𝒳} {b b' : Fib p R} (f : R ⟶ S) (ψ : (ι R).obj b' ⟶ a)
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
  Fib.homMk (IsCartesian.map p f ψ φ)

@[reassoc]
lemma inducedMap_comp : (ι R).map (inducedMap f ψ φ) ≫ ψ = φ := by
  simp only [inducedMap, Fib.map_homMk, IsCartesian.fac]

end

section

variable [IsFibered p] {R S : 𝒮} {a : 𝒳} {b : Fib p R}

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
with `ψ` Cartesian over `f` and `τ` a map in `Fib p R`. -/
lemma fiber_factorization (ha : p.obj a = S) {b : Fib p R} (f : R ⟶ S) (φ : (ι R).obj b ⟶ a)
    [IsHomLift p f φ] : ∃ (b' : Fib p R) (τ : b ⟶ b') (ψ : (ι R).obj b' ⟶ a),
      IsStronglyCartesian p f ψ ∧ (((ι R).map τ) ≫ ψ = φ) :=
  let ψ := pullbackMap f ha
  ⟨mkPullback f ha, inducedMap f ψ φ, ψ, inferInstance, inducedMap_comp f ψ φ⟩

end

end

end HasFibers
