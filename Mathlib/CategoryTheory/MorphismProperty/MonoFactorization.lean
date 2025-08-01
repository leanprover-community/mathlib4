/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Markus Himmel
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.EqToHom

/-!
# Mono Factorizations

A `MonoFactorization` is a factorization `f = e ≫ m`, where `m` is a monomorphism.

## Future work
* TODO: Connect definitions with `CategoryTheory/MorphismProperty/Factorization.lean`

-/

noncomputable section

universe v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : X ⟶ Y)

/-- A factorization of a morphism `f = e ≫ m`, with `m` monic. -/
structure MonoFactorization where
  I : C
  m : I ⟶ Y
  [m_mono : Mono m]
  e : X ⟶ I
  fac : e ≫ m = f := by aesop_cat

attribute [inherit_doc MonoFactorization] MonoFactorization.I MonoFactorization.m
  MonoFactorization.m_mono MonoFactorization.e MonoFactorization.fac

attribute [reassoc (attr := simp)] MonoFactorization.fac

attribute [instance] MonoFactorization.m_mono

@[deprecated (since := "2025-08-01")] alias MonoFactorisation := MonoFactorization

namespace MonoFactorization

/-- The obvious factorization of a monomorphism through itself. -/
def self [Mono f] : MonoFactorization f where
  I := X
  m := f
  e := 𝟙 X

instance [Mono f] : Inhabited (MonoFactorization f) := ⟨self f⟩

variable {f}

/-- The morphism `m` in a factorization `f = e ≫ m` through a monomorphism is uniquely
determined. -/
@[ext (iff := false)]
theorem ext {F F' : MonoFactorization f} (hI : F.I = F'.I)
    (hm : F.m = eqToHom hI ≫ F'.m) : F = F' := by
  obtain ⟨_, Fm, _, Ffac⟩ := F; obtain ⟨_, Fm', _, Ffac'⟩ := F'
  cases hI
  simp? at hm says simp only [eqToHom_refl, Category.id_comp] at hm
  congr
  apply (cancel_mono Fm).1
  rw [Ffac, hm, Ffac']

/-- Any mono factorization of `f` gives a mono factorization of `f ≫ g` when `g` is a mono. -/
@[simps]
def compMono (F : MonoFactorization f) {Y' : C} (g : Y ⟶ Y') [Mono g] :
    MonoFactorization (f ≫ g) where
  I := F.I
  m := F.m ≫ g
  m_mono := mono_comp _ _
  e := F.e

/-- A mono factorization of `f ≫ g`, where `g` is an isomorphism,
gives a mono factorization of `f`. -/
@[simps]
def ofCompIso {Y' : C} {g : Y ⟶ Y'} [IsIso g] (F : MonoFactorization (f ≫ g)) :
    MonoFactorization f where
  I := F.I
  m := F.m ≫ inv g
  m_mono := mono_comp _ _
  e := F.e

/-- Any mono factorization of `f` gives a mono factorization of `g ≫ f`. -/
@[simps]
def isoComp (F : MonoFactorization f) {X' : C} (g : X' ⟶ X) : MonoFactorization (g ≫ f) where
  I := F.I
  m := F.m
  e := g ≫ F.e

/-- A mono factorization of `g ≫ f`, where `g` is an isomorphism,
gives a mono factorization of `f`. -/
@[simps]
def ofIsoComp {X' : C} (g : X' ⟶ X) [IsIso g] (F : MonoFactorization (g ≫ f)) :
    MonoFactorization f where
  I := F.I
  m := F.m
  e := inv g ≫ F.e

/-- If `f` and `g` are isomorphic arrows, then a mono factorization of `f`
gives a mono factorization of `g` -/
@[simps]
def ofArrowIso {f g : Arrow C} (F : MonoFactorization f.hom) (sq : f ⟶ g) [IsIso sq] :
    MonoFactorization g.hom where
  I := F.I
  m := F.m ≫ sq.right
  e := inv sq.left ≫ F.e
  m_mono := mono_comp _ _
  fac := by simp only [fac_assoc, Arrow.w, IsIso.inv_comp_eq, Category.assoc]

end CategoryTheory.Limits.MonoFactorization
