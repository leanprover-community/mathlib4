/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Construction for the small object argument

Given a family of morphisms `f i : A i ⟶ B i` in a category `C`,
we define a functor
`SmallObject.functor f : Arrow S ⥤ Arrow S` which sends
an object given by arrow `πX : X ⟶ S` to the pushout `functorObj f πX`:
```
∐ functorObjSrcFamily f πX ⟶       X

            |                      |
            |                      |
            v                      v

∐ functorObjTgtFamily f πX ⟶ functorObj f πX
```
where the morphism on the left is a coproduct (of copies of maps `f i`)
indexed by a type `FunctorObjIndex f πX` which parametrizes the
diagrams of the form
```
A i ⟶ X
 |    |
 |    |
 v    v
B i ⟶ S
```

The morphism `ιFunctorObj f πX : X ⟶ functorObj f πX` is part of
a natural transformation `SmallObject.ε f : 𝟭 (Arrow C) ⟶ functor f S`.
The main idea in this construction is that for any commutative square
as above, there may not exist a lifting `B i ⟶ X`, but the construction
provides a tautological morphism `B i ⟶ functorObj f πX`
(see `SmallObject.ιFunctorObj_extension`).

## TODO

* Show that `ιFunctorObj f πX : X ⟶ functorObj f πX` has the
left lifting property with respect to the class of morphisms that
have the right lifting property with respect to the morphisms `f i`.

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/
universe w v u

namespace CategoryTheory

open Category Limits

namespace SmallObject

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I → C} (f : ∀ i, A i ⟶ B i)

section

variable {S X : C} (πX : X ⟶ S)

/-- Given a family of morphisms `f i : A i ⟶ B i` and a morphism `πX : X ⟶ S`,
this type parametrizes the commutative squares with a morphism `f i` on the left
and `πX` in the right. -/
structure FunctorObjIndex where
  /-- an element in the index type -/
  i : I
  /-- the top morphism in the square -/
  t : A i ⟶ X
  /-- the bottom morphism in the square -/
  b : B i ⟶ S
  w : t ≫ πX = f i ≫ b

attribute [reassoc (attr := simp)] FunctorObjIndex.w

variable [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]

/-- The family of objects `A x.i` parametrized by `x : FunctorObjIndex f πX`. -/
abbrev functorObjSrcFamily (x : FunctorObjIndex f πX) : C := A x.i

/-- The family of objects `B x.i` parametrized by `x : FunctorObjIndex f πX`. -/
abbrev functorObjTgtFamily (x : FunctorObjIndex f πX) : C := B x.i

/-- The family of the morphisms `f x.i : A x.i ⟶ B x.i`
parametrized by `x : FunctorObjIndex f πX`. -/
abbrev functorObjLeftFamily (x : FunctorObjIndex f πX) :
    functorObjSrcFamily f πX x ⟶ functorObjTgtFamily f πX x := f x.i

/-- The top morphism in the pushout square in the definition of `pushoutObj f πX`. -/
noncomputable abbrev functorObjTop : ∐ functorObjSrcFamily f πX ⟶ X :=
  Limits.Sigma.desc (fun x => x.t)

/-- The left morphism in the pushout square in the definition of `pushoutObj f πX`. -/
noncomputable abbrev functorObjLeft :
    ∐ functorObjSrcFamily f πX ⟶ ∐ functorObjTgtFamily f πX :=
  Limits.Sigma.map (functorObjLeftFamily f πX)

variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]

/-- The functor `SmallObject.functor f : Arrow C ⥤ Arrow C` that is part of
the small object argument for a family of morphisms `f`, on an object given
as a morphism `πX : X ⟶ S`. -/
noncomputable abbrev functorObj : C :=
  pushout (functorObjTop f πX) (functorObjLeft f πX)

/-- The canonical morphism `X ⟶ functorObj f πX`. -/
noncomputable abbrev ιFunctorObj : X ⟶ functorObj f πX := pushout.inl _ _

/-- The canonical morphism `∐ (functorObjTgtFamily f πX) ⟶ functorObj f πX`. -/
noncomputable abbrev ρFunctorObj : ∐ functorObjTgtFamily f πX ⟶ functorObj f πX := pushout.inr _ _

@[reassoc]
lemma functorObj_comm :
    functorObjTop f πX ≫ ιFunctorObj f πX = functorObjLeft f πX ≫ ρFunctorObj f πX :=
  pushout.condition

@[reassoc]
lemma FunctorObjIndex.comm (x : FunctorObjIndex f πX) :
    f x.i ≫ Sigma.ι (functorObjTgtFamily f πX) x ≫ ρFunctorObj f πX = x.t ≫ ιFunctorObj f πX := by
  simpa using (Sigma.ι (functorObjSrcFamily f πX) x ≫= functorObj_comm f πX).symm

/-- The canonical projection on the base object. -/
noncomputable abbrev π'FunctorObj : ∐ functorObjTgtFamily f πX ⟶ S := Sigma.desc (fun x => x.b)

/-- The canonical projection on the base object. -/
noncomputable def πFunctorObj : functorObj f πX ⟶ S :=
  pushout.desc πX (π'FunctorObj f πX) (by ext; simp [π'FunctorObj])

@[reassoc (attr := simp)]
lemma ρFunctorObj_π : ρFunctorObj f πX ≫ πFunctorObj f πX = π'FunctorObj f πX := by
  simp [πFunctorObj]

@[reassoc (attr := simp)]
lemma ιFunctorObj_πFunctorObj : ιFunctorObj f πX ≫ πFunctorObj f πX = πX := by
  simp [ιFunctorObj, πFunctorObj]

section

variable {S T X Y : C} {πX : X ⟶ S} {πY : Y ⟶ T} (τ : Arrow.mk πX ⟶ Arrow.mk πY)
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πY)) C]

/-- The canonical morphism `∐ (functorObjSrcFamily f πX) ⟶ ∐ (functorObjSrcFamily f πY)`
induced by a morphism `Arrow.mk πX ⟶ Arrow.mk πY`. -/
noncomputable def functorMapSrc :
    ∐ (functorObjSrcFamily f πX) ⟶ ∐ functorObjSrcFamily f πY :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

@[reassoc]
lemma ι_functorMapSrc (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (b' : B i ⟶ T) (hb' : b ≫ τ.right = b')
    (t' : A i ⟶ Y) (ht' : t ≫ τ.left = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapSrc f τ =
      Sigma.ι (functorObjSrcFamily f πY)
        (FunctorObjIndex.mk i t' b' (by
          have := τ.w
          dsimp at this
          rw [← hb', ← reassoc_of% w, ← ht', assoc, this])) := by
  subst hb' ht'
  simp [functorMapSrc]

@[reassoc (attr := simp)]
lemma functorMapSrc_functorObjTop :
    functorMapSrc f τ ≫ functorObjTop f πY = functorObjTop f πX ≫ τ.left := by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapSrc_assoc f τ i t b w _ rfl]

/-- The canonical morphism `∐ functorObjTgtFamily f πX ⟶ ∐ functorObjTgtFamily f πY`
induced by a morphism `Arrow.mk πX ⟶ Arrow.mk πY`. -/
noncomputable def functorMapTgt :
    ∐ functorObjTgtFamily f πX ⟶ ∐ functorObjTgtFamily f πY :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

@[reassoc]
lemma ι_functorMapTgt (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (b' : B i ⟶ T) (hb' : b ≫ τ.right = b')
    (t' : A i ⟶ Y) (ht' : t ≫ τ.left = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapTgt f τ =
      Sigma.ι (functorObjTgtFamily f πY)
        (FunctorObjIndex.mk i t' b' (by
          have := τ.w
          dsimp at this
          rw [← hb', ← reassoc_of% w, ← ht', assoc, this])) := by
  subst hb' ht'
  simp [functorMapTgt]

lemma functorMap_comm :
    functorObjLeft f πX ≫ functorMapTgt f τ =
      functorMapSrc f τ ≫ functorObjLeft f πY := by
  ext ⟨i, t, b, w⟩
  simp only [ι_colimMap_assoc, Discrete.natTrans_app, ι_colimMap,
    ι_functorMapTgt f τ i t b w _ rfl,
    ι_functorMapSrc_assoc f τ i t b w _ rfl]

variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]
  [HasPushout (functorObjTop f πY) (functorObjLeft f πY)]

/-- The functor `SmallObject.functor f S : Arrow S ⥤ Arrow S` that is part of
the small object argument for a family of morphisms `f`, on morphisms. -/
noncomputable def functorMap : functorObj f πX ⟶ functorObj f πY :=
  pushout.map _ _ _ _ τ.left (functorMapTgt f τ) (functorMapSrc f τ) (by simp)
    (functorMap_comm f τ)

@[reassoc (attr := simp)]
lemma functorMap_π : functorMap f τ ≫ πFunctorObj f πY = πFunctorObj f πX ≫ τ.right := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap, ι_functorMapTgt_assoc f τ i t b w _ rfl]

variable (X) in
@[simp]
lemma functorMap_id : functorMap f (𝟙 (Arrow.mk πX)) = 𝟙 _ := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap,
      ι_functorMapTgt_assoc f (𝟙 (Arrow.mk πX)) i t b w b (by simp) t (by simp)]

@[reassoc (attr := simp)]
lemma ιFunctorObj_naturality :
    ιFunctorObj f πX ≫ functorMap f τ = τ.left ≫ ιFunctorObj f πY := by
  simp [ιFunctorObj, functorMap]

lemma ιFunctorObj_extension {i : I} (t : A i ⟶ X) (b : B i ⟶ S)
    (sq : CommSq t (f i) πX b) :
    ∃ (l : B i ⟶ functorObj f πX), f i ≫ l = t ≫ ιFunctorObj f πX ∧
      l ≫ πFunctorObj f πX = b :=
  ⟨Sigma.ι (functorObjTgtFamily f πX) (FunctorObjIndex.mk i t b sq.w) ≫
    ρFunctorObj f πX, (FunctorObjIndex.mk i t b _).comm, by simp⟩

end

variable [HasPushouts C]
  [∀ {X S : C} (πX : X ⟶ S), HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]

/-- The functor `Arrow C ⥤ Arrow C` that is constructed in order to apply the small
object argument to a family of morphisms `f i : A i ⟶ B i`, see the introduction
of the file `Mathlib.CategoryTheory.SmallObject.Construction` -/
@[simps! obj map]
noncomputable def functor : Arrow C ⥤ Arrow C where
  obj π := Arrow.mk (πFunctorObj f π.hom)
  map {π₁ π₂} τ := Arrow.homMk (functorMap f τ) τ.right
  map_id g := by
    ext
    · apply functorMap_id
    · dsimp
  map_comp {π₁ π₂ π₃} τ τ' := by
    ext
    · dsimp
      simp [functorMap]
      ext ⟨i, t, b, w⟩
      · simp
      · simp [ι_functorMapTgt_assoc f τ i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f (τ ≫ τ') i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f τ' i (t ≫ τ.left) (b ≫ τ.right)
            (by simp [reassoc_of% w]) (b ≫ τ.right ≫ τ'.right) (by simp)
            (t ≫ (τ ≫ τ').left) (by simp)]
    · dsimp

/-- The canonical natural transformation `𝟭 (Arrow C) ⟶ functor f`. -/
@[simps app]
noncomputable def ε : 𝟭 (Arrow C) ⟶ functor f where
  app π := Arrow.homMk (ιFunctorObj f π.hom) (𝟙 _)

end

end SmallObject

end CategoryTheory
