import Mathlib.Algebra.Category.GroupCat.Adjunctions
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Condensed.Abelian

universe u

open CategoryTheory

def Condensed.abToSet : CondensedAb ⥤ CondensedSet := sheafCompose _ (forget AddCommGroupCat)

noncomputable
def Condensed.setToAb : CondensedSet ⥤ CondensedAb :=
  Sheaf.composeAndSheafify _ AddCommGroupCat.free

noncomputable
def Condensed.setAbAdjunction : setToAb ⊣ abToSet := Sheaf.adjunction _ AddCommGroupCat.adj
