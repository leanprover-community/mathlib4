import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.GroupTheory.Abelianization
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

noncomputable section -- Much of the category theory library is noncomputable,
                      -- so lets get this out of the way at the beginning!

/-!
# Category theory in Mathlib

* Basics
* Constructing functors
  * Forgetful functors
  * Free commutative ring on a type
  * Abelianization of a group
* Constructing the category of pointed spaces
  * Prove the equivalence between `PointedSpace` and `Under (TopCat.of Unit)`


Further ideas:
* Simplicial homology?
* An `Ext` calculation??
* Something about complexes and abelian categories?
* Schemes? Group schemes??
-/

/-!
## Basics
-/

/-!
Much of Mathlib happily takes over the root namespace.
Category theory is nearly all in the `CategoryTheory` namespace, so we need:
-/
open CategoryTheory

section

/-! To talk about an arbitrary category, we write something like: -/
variable (C : Type) [Category C]

/-- We start by proving an easy fact:

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
example {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} -- Copilot will write the theorem statement, given the doc-string!
    {f₁ : X₁ ⟶ X₂} {f₂ : X₂ ⟶ X₃}
    {g₁ : X₁ ⟶ Y₁} {g₂ : X₂ ⟶ Y₂} {g₃ : X₃ ⟶ Y₃}
    {h₁ : Y₁ ⟶ Y₂} {h₂ : Y₂ ⟶ Y₃}
    (comm₁ : g₁ ≫ h₁ = f₁ ≫ g₂) (comm₂ : g₂ ≫ h₂ = f₂ ≫ g₃) :
    g₁ ≫ h₁ ≫ h₂ = f₁ ≫ f₂ ≫ g₃ := by
  -- Now a simple rewriting proof:
  rw [← Category.assoc]
  rw [comm₁]
  rw [Category.assoc]
  rw [comm₂]

/-!
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
## Constructing functors.
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

/-!
### Example: the free commutative ring on a type.

This should send each `X : Type` to
multivariable polynomials with integer coefficients in `X` variables.

A function between types `X → Y` should induce a ring homomorphism given be renaming variables.
-/

/-- Let's get started specifying it at object level. -/
example : Type ⥤ CommRingCat where
  obj X := CommRingCat.of (MvPolynomial X ℤ)
  map {X Y} f := sorry

#check MvPolynomial.rename  -- Looks promising!
  -- I would find this either by https://www.moogle.ai/search/raw?q=Rename%20variables%20in%20multivariable%20polynomials
  -- or by typing `polynomial.*rename` in the search bar in VS Code,

-- /-- First attempt at the morphism level: -/
-- example : Type ⥤ CommRingCat where
--   obj X := CommRingCat.of (MvPolynomial X ℤ)
--   map {X Y} f := MvPolynomial.rename f

/-!
There are some messages from `aesop` here, prematurely trying to prove functoriality,
but the important message is
```
type mismatch
  MvPolynomial.rename f
has type
  MvPolynomial X ?m →ₐ[?m] MvPolynomial Y ?m : Type ?u
but is expected to have type
  (fun X ↦ CommRingCat.of (MvPolynomial X ℤ)) X ⟶ (fun X ↦ CommRingCat.of (MvPolynomial X ℤ)) Y : Type
```
This is telling us that Lean expects a morphism in `CommRingCat`,
but we're giving it at algebra homomorphism (that's the `→ₐ[?m]` in the type),
and moreover it can't work out which ring the coefficients should be in.
-/

-- /-- Second attempt at the morphism level. Let's remind Lean we're working over `ℤ`. -/
-- example : Type ⥤ CommRingCat where
--   obj X := CommRingCat.of (MvPolynomial X ℤ)
--   map {X Y} f := MvPolynomial.rename (R := ℤ) f

/-!
Pretty much the same error message:
let's explicit coerce from an algebra homomorphism to a ring homomorphism to help out.
-/

-- /-- Third attempt. -/
-- example : Type ⥤ CommRingCat where
--   obj X := CommRingCat.of (MvPolynomial X ℤ)
--   map {X Y} f := (MvPolynomial.rename (R := ℤ) f : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)

/-!
Now Lean accepts our definitions, but there are unsolved goals errors after `aesop` tries
to discharge the functoriality proofs.

`aesop` got stuck at
```
tactic 'aesop' failed, failed to prove the goal after exhaustive search.
X : Type
x✝ : MvPolynomial X ℤ
m✝ : X →₀ ℕ
⊢ MvPolynomial.coeff m✝ ((MvPolynomial.rename (𝟙 X)) x✝) = MvPolynomial.coeff m✝ x✝
```
which suggests that the problem may just be that `simp` won't unfold the definition `𝟙 X`
as the identity function!

To find the relevant theorem, I would use:
```
example (X : Type) : 𝟙 X = id := by rw?
```
which suggests the lemma `types_id`.

(Actually, first I tried `by exact?` above, but that is too powerful and just suggests `rfl`.)

-/
attribute [local simp] types_id in
def free : Type ⥤ CommRingCat where
  obj X := CommRingCat.of (MvPolynomial X ℤ)
  map {X Y} f := (MvPolynomial.rename (R := ℤ) f : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)

/-!
### Example: the abelianization of a group.

We send each group to it abelianization.

Given a morphism `G → H` of groups, we can build a morphism `Abelianization G ⟶ Abelianization H`
using the adjunction `Abelianization.lift : (G →* A) ≃ (Abelianization G →* A)` and
the projection `Abelianization.of : G →* Abelianization G`.
-/

universe u

-- /-- First attempt: -/
-- example : GroupCat.{u} ⥤ CommGroupCat.{u} where
--   obj G := CommGroupCat.of (Abelianization G)
--   map f := Abelianization.lift (Abelianization.of.comp f)

/-!
This fails when `aesop` gets stuck at
`⊢ Abelianization.map (f ≫ g) = Abelianization.map f ≫ Abelianization.map g`.
Since `Abelianization.map` is about `→*`, i.e. unbundled group homomorphisms, probably this
already exists as a theorem, we just need to convert the categorical compositions `≫`
into `MulHom.comp`.
-/

#check Abelianization.map_comp -- Looks promising!

attribute [local simp] CommGroupCat.comp_def GroupCat.comp_def in
def abelianize : GroupCat.{u} ⥤ CommGroupCat.{u} where
  obj G := CommGroupCat.of (Abelianization G)
  map f := Abelianization.lift (Abelianization.of.comp f)

/-!
## Example: Constructing the category of pointed spaces.
-/

/--
A `PointedSpace` consists of
* an underlying type `X`
* the topological space structure on `X`
* and a distinguished point `base : X`.
-/
structure PointedSpace where
  carrier : Type
  [inst : TopologicalSpace carrier] -- We use `[]` so that Lean can infer this automatically
                                    -- What breaks below, and why, if we remove this?
  base : carrier

attribute [instance] PointedSpace.inst -- If `M : PointedSpace`,  this makes the topological space
                                       -- instance on `M.carrier` available.
                                       -- Check what breaks below if we remove it!

namespace PointedSpace

/--
A morphism of `PointedSpace`s is a continuous map between the underlying topological spaces,
which takes the base point to the base point.
-/
structure Hom (X Y : PointedSpace) where
  map : ContinuousMap X.carrier Y.carrier
  base : map X.base = Y.base

attribute [simp] Hom.base -- Allow `simp` to use the fact that morphisms are base-preserving.

namespace Hom

/-- The identity morphism on a `PointedSpace`. -/
def id (X : PointedSpace) : Hom X X := ⟨ContinuousMap.id _, rfl⟩

/-- Composition of morphisms of `PointedSpace`s. -/
def comp {X Y Z : PointedSpace} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
   ⟨g.map.comp f.map, by simp⟩ -- Check that if we remove the `simp` attribute on `Hom.base`
                               -- then this stops working!
                               -- Exercise: set up an `auto_param` to `base`,
                               -- so you can omit this proof entirely.

end Hom

instance : Category PointedSpace where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  -- 🎉 No proofs required!

end PointedSpace

/-!
### We next construct the equivalence between `PointedSpace` and `Under (TopCat.of Unit)`.

`Under (TopCat.of Unit)` means "topological spaces equipped with a map from the one-point space".
-/

/-- The forward direction. -/
def PointedSpaceEquiv_functor : PointedSpace ⥤ Under (TopCat.of Unit) where
  obj := fun X => Under.mk (Y := TopCat.of X.carrier) (ContinuousMap.mk fun _ => X.base)
  map := fun f => Under.homMk f.map

/-- The reverse direction. -/
def PointedSpaceEquiv_inverse : Under (TopCat.of Unit) ⥤ PointedSpace where
  obj := fun X =>
  { carrier := X.right -- The `Under` category is implemented as a `Comma` category.
                       -- An object `X` consists of
                       -- `X.left : PUnit` (unrelated to our 1-point space! what is it?)
                       -- `X.right : TopCat` (the topological space)
                       -- `X.hom`, the continuous map.
                       -- Here we're using the coercion of `X.right` from a `TopCat` to a type,
                       -- and Lean can automatically find the topological space instance.
    base := X.hom () }
  map := fun f =>
  { map := f.right -- A morphism `f` in an `Under` category consists of
                  -- `f.left` (uninteresting)
                  -- `f.right` (a continuous map)
                  -- `f.w` (a proof that the diagram commutes)
    base := by
      -- Our first proof today!
      -- We just need to take `f.w`, which is an equation of continuous maps,
      -- and evaluate both sides at the unique point in `TopCat.of Unit`,
      -- and then massage things into shape.
      have := f.w
      replace this := DFunLike.congr_fun this ()
      simp [- Under.w] at this    -- Because `simp at this` gives us an unhelpful `True`!
      simp
      exact this.symm }

/-- Putting it all together. -/
def equiv : PointedSpace ≌ Under (TopCat.of Unit) where
  functor := PointedSpaceEquiv_functor
  inverse := PointedSpaceEquiv_inverse
  unitIso := NatIso.ofComponents fun X => Iso.refl _ -- 🎉 naturality is checked by automation
  counitIso := NatIso.ofComponents fun X => Iso.refl _
  -- 🎉 the triangle identity is checked by automation!
  -- Aside: categorical equivalences in Mathlib are "half-adjoint equivalences".
  -- Jump to definition on `≌` and read the doc-string for details.

/-!
## Advanced topic: Setting up singular homology

Someone should PR parts of this section to Mathlib, but it's not me!
Even though it is definitions, and no theorems, they are the right definitions,
and may provoke someone into starting on the theory!

If you're excited about this section, see the `tuesday_9am` branch of the old mathlib 3 repository,
which contains some more in this direction.
-/

namespace TopCat

open AlgebraicTopology

variable (R : Type) [Ring R]

/--
Turn a topological space into a simplicial R-module, by composing the simplicial set with
the free R-module functor.
-/
def toSModule : TopCat.{0} ⥤ SimplicialObject (ModuleCat R) :=
  toSSet ⋙ -- The functor `TopCat ⥤ SSet`
    (SimplicialObject.whiskering _ _).obj (ModuleCat.free R)
    -- The free functor from simplicial sets to simplicial modules.

/-- Compute the singular chain complex of a topological space,
by using the "alternating face map" functor. -/
def singularChains : TopCat.{0} ⥤ ChainComplex (ModuleCat R) ℕ :=
  toSModule R ⋙ alternatingFaceMapComplex _

def singularHomology (n : ℕ) : TopCat.{0} ⥤ ModuleCat R :=
(singularChains R ⋙ HomotopyCategory.quotient _ _) ⋙ HomotopyCategory.homologyFunctor _ _ n

-- Challenge: do any computation at all, e.g.
example : (singularHomology ℤ 0).obj (TopCat.of Unit) ≅ ModuleCat.of ℤ ℤ := sorry
-- This one might be doable via the isomorphisms:
example : toSSet.obj (TopCat.of Unit) ≅ (SimplicialObject.const _).obj Unit := sorry
example :
    (toSModule R).obj (TopCat.of Unit) ≅ (SimplicialObject.const _).obj (ModuleCat.of R R) :=
  sorry
example (X : ModuleCat R) :
    (alternatingFaceMapComplex _).obj ((SimplicialObject.const _).obj X) ≅
    (ChainComplex.single₀ _).obj X :=
  sorry
example (X : ModuleCat R) :
    (HomologicalComplex.homologyFunctor _ _ 0).obj ((ChainComplex.single₀ _).obj X) ≅ X :=
  sorry

-- One day we would like to have lots of theory, e.g. the Kunneth formula.
-- The code below is far from everything needed for Kunneth, but starts describing how
-- `toSSet`, `toSModule`, and `alternatingFaceMapComplex` interact with the monoidal structures.


open MonoidalCategory

section

variable (C : Type u) [Category C] [MonoidalCategory C]

@[simps!]
instance : MonoidalCategory (SimplicialObject C) :=
  inferInstanceAs <| MonoidalCategory (SimplexCategoryᵒᵖ ⥤ C)

instance : MonoidalCategory SSet := inferInstanceAs <| MonoidalCategory (SimplexCategoryᵒᵖ ⥤ Type)

-- TODO: use `ChosenFiniteProducts`

instance : MonoidalCategory TopCat.{u} :=
  monoidalOfChosenFiniteProducts
    ⟨{ pt := TopCat.of PUnit, π := sorry }, sorry⟩
    fun X Y => ⟨{ pt := TopCat.of (X × Y), π := sorry }, sorry⟩

@[simp] theorem forget_tensorObj {X Y : TopCat} : (forget TopCat).obj (X ⊗ Y) = (X × Y) := rfl

instance : SymmetricCategory TopCat := symmetricOfChosenFiniteProducts _ _
end

@[simp]
theorem forget_of (X : Type _) [TopologicalSpace X] : (forget TopCat).obj (of X) = X := rfl

@[simp] theorem coe_continuousMap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} :
    @DFunLike.coe (@Quiver.Hom TopCat _ no_index (of X) no_index (of Y)) X (fun _ ↦ Y) _ f =
    @DFunLike.coe C(X, Y) X (fun _ ↦ Y) _ f :=
  rfl

-- This is really aggressive.
@[simp] theorem continuousMap_comp {X : Type u} [TopologicalSpace X] {Y Z : TopCat} (f : C(X, Y)) (g : Y ⟶ Z) :
  @CategoryStruct.comp TopCat _ (of X) Y Z f g = ContinuousMap.comp g f := rfl

@[simp] theorem of_hom {X : Type u} [TopologicalSpace X] {Y : TopCat.{u}} : (of X ⟶ Y) = C(X, Y) := rfl
@[simp] theorem hom_of {X : TopCat.{u}} {Y : Type u} [TopologicalSpace Y] : (X ⟶ of Y) = C(X, Y) := rfl

attribute [local simp] toSSet in
def toSSet_monoidal : MonoidalFunctor TopCat SSet :=
{ TopCat.toSSet with
  ε := { app := fun n x => ContinuousMap.const _ x }
  μ := fun X Y => { app := fun n x => ContinuousMap.prodMk x.1 x.2 }
  ε_isIso := sorry
  μ_isIso := sorry
  μ_natural_left := sorry
  μ_natural_right := sorry
  associativity := sorry -- These subgoals are hiding some horrors;
                         -- Ask me if you're interested in examples of dependent type theory hell,
                         -- or solve them to become an expert in concrete categories in Mathlib!
                         -- Ideally with the right `simp` and `ext` lemmas these are all handled
                         -- by `aesop`.
  left_unitality := sorry
  right_unitality := sorry }

-- This has no dependencies: you could fill in the sorries here and PR just this declaration!
def whiskeringRight_monoidal
  (C : Type*) [Category C]
  (D : Type*) [Category D] [MonoidalCategory D]
  (E : Type*) [Category E] [MonoidalCategory E] :
  (MonoidalFunctor D E) ⥤ (MonoidalFunctor (C ⥤ D) (C ⥤ E)) :=
{ obj := fun F =>
  { (whiskeringRight C D E).obj F.toFunctor with
    ε :=
    { app := fun X => F.ε, },
    μ := fun G H =>
    { app := fun X => F.μ _ _ },
    ε_isIso := sorry
    μ_isIso := sorry },
  map := sorry, }

def SimplicialObject.map_monoidal
    (C : Type u) [Category C] [MonoidalCategory C] (D : Type u) [Category D] [MonoidalCategory D] :
    (MonoidalFunctor C D) ⥤ MonoidalFunctor (SimplicialObject C) (SimplicialObject D) :=
  whiskeringRight_monoidal _ _ _

def toSModule_monoidal (R : Type) [CommRing R] :
    MonoidalFunctor TopCat.{0} (SimplicialObject (ModuleCat.{0} R)) :=
  toSSet_monoidal ⊗⋙ ((SimplicialObject.map_monoidal _ _).obj (ModuleCat.monoidalFree R))

open Limits MonoidalCategory

variable {C : Type _} [Category C] [MonoidalCategory C]
  [Preadditive C] [HasFiniteBiproducts C] (X Y : SimplicialObject C)

-- This one is a lot of work: Joël Riou has been working towards it.
-- He's detouring via bicomplexes.
instance : MonoidalCategory (ChainComplex C ℕ) := sorry

-- Once you have this, we'd still need to describe how homology behaves:
-- it's a lax monoidal functor.

set_option quotPrecheck false in
notation "C" => (alternatingFaceMapComplex C).obj

def alexanderWhitney : C (X ⊗ Y) ⟶ C X ⊗ C Y := sorry
def eilenbergZilber : C X ⊗ C Y ⟶ C (X ⊗ Y) := sorry

def homotopy_1 : Homotopy (eilenbergZilber X Y ≫ alexanderWhitney X Y) (𝟙 _) := sorry
def homotopy_2 : Homotopy (alexanderWhitney X Y ≫ eilenbergZilber X Y) (𝟙 _) := sorry

end TopCat
