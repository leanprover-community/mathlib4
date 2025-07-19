/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.EqToHom

/-!
# Mono Factorizations

A `MonoFactorisation` is a factorisation `f = e ≫ m`, where `m` is a monomorphism.

## Future work
* TODO: Connect definitions with `CategoryTheory/MorphismProperty/Factorization.lean`

-/


noncomputable section

universe v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : X ⟶ Y)

/-- A factorisation of a morphism `f = e ≫ m`, with `m` monic. -/
structure MonoFactorisation (f : X ⟶ Y) where
  I : C -- Porting note: violates naming conventions but can't think a better replacement
  m : I ⟶ Y
  [m_mono : Mono m]
  e : X ⟶ I
  fac : e ≫ m = f := by aesop_cat

attribute [inherit_doc MonoFactorisation] MonoFactorisation.I MonoFactorisation.m
  MonoFactorisation.m_mono MonoFactorisation.e MonoFactorisation.fac

attribute [reassoc (attr := simp)] MonoFactorisation.fac

attribute [instance] MonoFactorisation.m_mono

namespace MonoFactorisation

/-- The obvious factorisation of a monomorphism through itself. -/
def self [Mono f] : MonoFactorisation f where
  I := X
  m := f
  e := 𝟙 X

-- I'm not sure we really need this, but the linter says that an inhabited instance
-- ought to exist...
instance [Mono f] : Inhabited (MonoFactorisation f) := ⟨self f⟩

variable {f}

/-- The morphism `m` in a factorisation `f = e ≫ m` through a monomorphism is uniquely
determined. -/
@[ext (iff := false)]
theorem ext {F F' : MonoFactorisation f} (hI : F.I = F'.I)
    (hm : F.m = eqToHom hI ≫ F'.m) : F = F' := by
  obtain ⟨_, Fm, _, Ffac⟩ := F; obtain ⟨_, Fm', _, Ffac'⟩ := F'
  cases hI
  simp? at hm says simp only [eqToHom_refl, Category.id_comp] at hm
  congr
  apply (cancel_mono Fm).1
  rw [Ffac, hm, Ffac']

/-- Any mono factorisation of `f` gives a mono factorisation of `f ≫ g` when `g` is a mono. -/
@[simps]
def compMono (F : MonoFactorisation f) {Y' : C} (g : Y ⟶ Y') [Mono g] :
    MonoFactorisation (f ≫ g) where
  I := F.I
  m := F.m ≫ g
  m_mono := mono_comp _ _
  e := F.e

/-- A mono factorisation of `f ≫ g`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
def ofCompIso {Y' : C} {g : Y ⟶ Y'} [IsIso g] (F : MonoFactorisation (f ≫ g)) :
    MonoFactorisation f where
  I := F.I
  m := F.m ≫ inv g
  m_mono := mono_comp _ _
  e := F.e

/-- Any mono factorisation of `f` gives a mono factorisation of `g ≫ f`. -/
@[simps]
def isoComp (F : MonoFactorisation f) {X' : C} (g : X' ⟶ X) : MonoFactorisation (g ≫ f) where
  I := F.I
  m := F.m
  e := g ≫ F.e

/-- A mono factorisation of `g ≫ f`, where `g` is an isomorphism,
gives a mono factorisation of `f`. -/
@[simps]
def ofIsoComp {X' : C} (g : X' ⟶ X) [IsIso g] (F : MonoFactorisation (g ≫ f)) :
    MonoFactorisation f where
  I := F.I
  m := F.m
  e := inv g ≫ F.e

/-- If `f` and `g` are isomorphic arrows, then a mono factorisation of `f`
gives a mono factorisation of `g` -/
@[simps]
def ofArrowIso {f g : Arrow C} (F : MonoFactorisation f.hom) (sq : f ⟶ g) [IsIso sq] :
    MonoFactorisation g.hom where
  I := F.I
  m := F.m ≫ sq.right
  e := inv sq.left ≫ F.e
  m_mono := mono_comp _ _
  fac := by simp only [fac_assoc, Arrow.w, IsIso.inv_comp_eq, Category.assoc]

end CategoryTheory.Limits.MonoFactorisation
