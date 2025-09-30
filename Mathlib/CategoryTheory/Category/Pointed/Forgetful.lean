import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Category.Pointed.Basic

open CategoryTheory

universe u

@[simps]
def Grp.forgetToPointed : Grp.{u} ⥤ Pointed.{u} where
  obj X := ⟨X, 1⟩
  map f := ⟨f, f.hom.map_one⟩

@[simps]
def CommGrp.forgetToPointed : CommGrp.{u} ⥤ Pointed.{u} where
  obj X := ⟨X, 1⟩
  map f := ⟨f, f.hom.map_one⟩
