import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
-- import Mathlib
noncomputable section -- Let's do some maths.

/-!
# Category theory in Mathlib
-/

/-!
## Basics
-/

-- To talk about an arbitrary category, we write something like:

open CategoryTheory

variable (C : Type) [Category C]

/-- And now we can prove a trivial fact:

If the two squares in
```
  X₁ --f₁--> X₂ --f₂--> X₃
  |          |          |
  g₁         g₂         g₃
  |          |          |
  v          v          v
  Y₁ --h₁--> Y₂ --h₂--> Y₃
```
commutes, then the outer rectangle commutes as well.
-/
example {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
    {g₁ : X₁ ⟶ Y₁} {g₂ : X₂ ⟶ Y₂} {g₃ : X₃ ⟶ Y₃}
    {h₁ : Y₁ ⟶ Y₂} {h₂ : Y₂ ⟶ Y₃}
    (comm₁ : g₁ ≫ h₁ = f₁ ≫ g₂) (comm₂ : g₂ ≫ h₂ = f₂ ≫ g₃) :
    g₁ ≫ h₁ ≫ h₂ = f₁ ≫ f₂ ≫ g₃ := by
  rw [← Category.assoc]
  rw [comm₁]
  rw [Category.assoc]
  rw [comm₂]

/-
For people who've already seen this, here are two alternative proofs of the same fact:
```
  simp [reassoc_of% comm₁, comm₂]
```
or
```
  slice_lhs 1 2 => rw [comm₁]
  slice_lhs 2 3 => rw [comm₂]
```
How do these work?
-/

/-!
Sometimes we want to talk about the category consisting of all algebraic structures of some flavour.
Most of these are set up already in Mathlib.

Typically, for each algebraic typeclass `Foo`, there is a category `FooCat` of "bundled foos",
i.e. a pair consisting of a type, and the typeclass instance for it.
-/

/-- Let's build the forgetful functor from commutative rings to rings. -/
def forget : CommRingCat ⥤ RingCat where
  obj R := RingCat.of R -- Any object `X : CommRingCat` can automatically be coerced to a type
                        -- (the elements of that ring), and that type has `CommRing` instance.
                        -- When `X` is any type, `RingCat.of X` asks Lean to see if there is a
                        -- ring structure available on `X`
                        -- Since Lean can knows that any `CommRing` is also a `Ring`, we're done.
  map f := f -- A morphism of commutative rings is just a morphism of rings!

-- Why didn't we need to prove anything about this actually being functorial
-- (preserving identities and composition)?
-- Most categorical structures in Mathlib are set up so that the proof fields have a default value
-- which will be filled in by tactics. Since most proofs in category theory are really boring,
-- this saves us a lot of typing! A lot of the design of the category theory library is based around
-- making this automation effective.
-- If we want to provide the functoriality proofs by hand we can:
def forget' : CommRingCat ⥤ RingCat where
  obj R := RingCat.of R
  map f := f
  map_id := by
    intros
    rfl
  map_comp := by
    intros
    rfl

-- This is so horrible, what has happened?!
-- def free : Type ⥤ CommRingCat where
--   obj X := CommRingCat.of (MvPolynomial X ℤ)
--   map {X Y} f := (↑(MvPolynomial.rename f : _ →ₐ[ℤ] _) : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)
--   map_id := by
--     intros X
--     ext x
--     simp at *
--     sorry
--   map_comp := by
--     intros X Y Z f g
--     ext x
--     simp at *
--     sorry

-- def abelianize : GroupCat ⥤ CommGroupCat where
--   obj G := CommGroupCat.of (Abelianization G)
--   map f := Abelianization.lift (Abelianization.of.comp f)
--   map_id := by
--     intros; simp only [MonoidHom.mk_coe, coe_id]
--     apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl
--   map_comp := by
--     intros; simp only [coe_comp];
--     apply (Equiv.apply_eq_iff_eq_symm_apply Abelianization.lift).mpr; rfl

structure PointedSpace where
  X : Type
  base : X
  [inst : TopologicalSpace X]

attribute [instance] PointedSpace.inst

namespace PointedSpace

structure Hom (X Y : PointedSpace) where
  map : ContinuousMap X.X Y.X
  base : map X.base = Y.base

attribute [simp] Hom.base

namespace Hom

-- @[simps]
def id (X : PointedSpace) : Hom X X := ⟨ContinuousMap.id _, rfl⟩

-- @[simps]
def comp {X Y Z : PointedSpace} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
   ⟨g.map.comp f.map, by simp⟩

end Hom

instance : Category PointedSpace where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp] theorem map_base {X Y : PointedSpace} (f : X ⟶ Y) : f.map X.base = Y.base := f.base
@[simp] theorem map_base' {X Y : PointedSpace} (f : X ⟶ Y) : f.map X.base = Y.base := f.base
-- @[simp] theorem id_map {X : PointedSpace} : Hom.map (𝟙 X) = ContinuousMap.id X.X := rfl
-- @[simp] theorem comp_map {X Y Z : PointedSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
--   Hom.map (f ≫ g) = g.map.comp f.map := rfl

-- @[ext] theorem hom_ext {X Y : PointedSpace} (f g : X ⟶ Y) (w : ∀ x : X.X, f.map x = g.map x) : f = g := sorry

end PointedSpace


universe u
namespace TopCat

-- @[simp] theorem hom_eq {X Y : TopCat} : (X ⟶ Y) = C(X, Y) := rfl

-- @[simp] theorem coe_id (X : TopCat) :
--     @DFunLike.coe C(X, X) X (fun _ ↦ X) ContinuousMap.funLike (𝟙 X) = id := rfl
-- @[simp] theorem coe_id' (X : Type u) [TopologicalSpace X] :
--     @DFunLike.coe C(X, X) X (fun _ ↦ X) ContinuousMap.funLike (𝟙 (TopCat.of X)) = id := rfl

-- @[simp] theorem coe_comp {X Y Z : Type u}
--     [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
--     @DFunLike.coe C(X, Z) X (fun _ => Z) ContinuousMap.funLike
--     (@CategoryStruct.comp TopCat _ (TopCat.of X) (TopCat.of Y) (TopCat.of Z) f g) = g ∘ f := rfl

-- @[simp] theorem fpp {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {toFun} {h} {x} :
-- @DFunLike.coe (TopCat.of X ⟶ TopCat.of Y) ((CategoryTheory.forget TopCat).obj (TopCat.of X))
--   (fun _ ↦ (CategoryTheory.forget TopCat).obj (TopCat.of Y)) ConcreteCategory.instFunLike
--   no_index { toFun := toFun, continuous_toFun := h } x = toFun x := rfl

@[simp] theorem fpp' {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : C(X, Y)} {x} :
@DFunLike.coe (TopCat.of X ⟶ TopCat.of Y) ((CategoryTheory.forget TopCat).obj (TopCat.of X))
  (fun _ ↦ (CategoryTheory.forget TopCat).obj (TopCat.of Y)) ConcreteCategory.instFunLike
  f x =
@DFunLike.coe C(X, Y) X
  (fun _ ↦ Y) _
  f x := rfl

end TopCat

set_option maxHeartbeats 400000 in
def equiv : PointedSpace ≌ Under (TopCat.of Unit) where
  functor :=
  { obj := fun X => Under.mk (Y := TopCat.of X.X) (ContinuousMap.mk fun _ => X.base)
    map := fun f => Under.homMk f.map --(by intros; ext; dsimp; simp)
    -- map_id := sorry
    -- map_comp := sorry
    }
  inverse :=
  { obj := fun X =>
    { X := X.right
      base := X.hom ()
       }
    map := fun f =>
    { map := f.right
      base := by
        have := f.w
        simp [- Under.w] at this
        simp
        have := DFunLike.congr_fun this ()
        exact this.symm
         }
    -- map_id := by intros; ext; simp
    -- map_comp := by intros; ext; simp
    }
  unitIso := NatIso.ofComponents (fun X => Iso.refl _) --sorry
  counitIso := NatIso.ofComponents (fun X => Iso.refl _) --sorry
  -- functor_unitIso_comp := by
  --   intros
  --   ext
  --   -- dsimp -- Without this we end up in a terrible state..
  --   simp
