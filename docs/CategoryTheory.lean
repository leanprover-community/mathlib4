import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.GroupTheory.Abelianization
import Mathlib.Algebra.MvPolynomial.CommRing

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

section

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


end

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

universe u

attribute [local simp] types_id types_comp in
def free : Type ⥤ CommRingCat where
  obj X := CommRingCat.of (MvPolynomial X ℤ)
  map {X Y} f := (MvPolynomial.rename (R := ℤ) f : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)
  map_id := by
    -- aesop_cat
    intros X
    ext x
    simp at *
  map_comp := by
    -- aesop_cat
    intros X Y Z f g
    ext x
    simp at *

attribute [local simp] types_id types_comp in
def free' : Type ⥤ CommRingCat where
  obj X := CommRingCat.of (MvPolynomial X ℤ)
  map {X Y} f := (MvPolynomial.rename (R := ℤ) f : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)

-- PR'd as https://github.com/leanprover-community/mathlib4/pull/13109
@[simp] theorem MonoidHom.comp_id_groupCat {G : GroupCat.{u}} {H : Type u} [Group H] (f : G →* H) :
    f.comp (𝟙 G) = f :=
  Category.id_comp (GroupCat.ofHom f)
@[simp] theorem MonoidHom.id_groupCat_comp {G : Type u} [Group G] {H : GroupCat.{u}} (f : G →* H) :
    MonoidHom.comp (𝟙 H) f = f :=
  Category.comp_id (GroupCat.ofHom f)

-- PR'd as https://github.com/leanprover-community/mathlib4/pull/13055
attribute [local simp] CommGroupCat.coe_of in
attribute [local simp] CommGroupCat.comp_def GroupCat.comp_def in
def abelianize : GroupCat.{u} ⥤ CommGroupCat.{u} where
  obj G := CommGroupCat.of (Abelianization G)
  map f := Abelianization.lift (Abelianization.of.comp f)
  map_id := by
    aesop_cat
    -- intros--; simp only [MonoidHom.mk_coe, coe_id]
    -- ext x
    -- -- dsimp at x ⊢  -- but doesn't work `at *`!
    -- simp
  map_comp := by
    aesop_cat
    -- intros G H K f g
    -- ext
    -- simp
    -- simp [CommGroupCat.comp_def, GroupCat.comp_def]

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

def id (X : PointedSpace) : Hom X X := ⟨ContinuousMap.id _, rfl⟩

def comp {X Y Z : PointedSpace} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
   ⟨g.map.comp f.map, by simp⟩

end Hom

instance : Category PointedSpace where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

end PointedSpace


def PointedSpaceEquiv_functor : PointedSpace ⥤ Under (TopCat.of Unit) where
  obj := fun X => Under.mk (Y := TopCat.of X.X) (ContinuousMap.mk fun _ => X.base)
  map := fun f => Under.homMk f.map

def PointedSpaceEquiv_inverse : Under (TopCat.of Unit) ⥤ PointedSpace where
  obj := fun X =>
  { X := X.right
    base := X.hom () }
  map := fun f =>
  { map := f.right
    base := by
      have := f.w
      replace this := DFunLike.congr_fun this ()
      simp [- Under.w] at this    -- Because `simp at this` gives us an unhelpful `True`!
      simp
      exact this.symm }

def equiv : PointedSpace ≌ Under (TopCat.of Unit) where
  functor := PointedSpaceEquiv_functor
  inverse := PointedSpaceEquiv_inverse
  unitIso := NatIso.ofComponents fun X => Iso.refl _
  counitIso := NatIso.ofComponents fun X => Iso.refl _
