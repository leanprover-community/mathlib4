import Mathlib.Condensed.Abelian
import Mathlib.Condensed.Discrete
import Mathlib.Condensed.Equivalence
import Mathlib.Condensed.Light.Adjunctions
import Mathlib.Condensed.Light.Discrete

noncomputable section

universe u

open CategoryTheory Opposite

namespace CondensedSets

/-!

# (Light) condensed sets

We can let our sheaves take values in abelian groups.
-/

/-- I want my condensed sets to be defined on profinite spaces, not all compact Hausdorff spaces -/
abbrev CondensedSet' := Sheaf (coherentTopology Profinite.{u}) (Type (u+1))

/-- Fortunately they are equivalent to mathlib's condensed sets. -/
def eq : CondensedSet' ≌ CondensedSet := Condensed.ProfiniteCompHaus.equivalence _

variable (S : Profinite.{u}) (X : CondensedSet'.{u})

#check X.val.obj ⟨S⟩
#check X.cond

variable (T : LightProfinite.{u}) (Y : LightCondSet.{u})

#check Y.val.obj (op T)
#check Y.cond

/- Given a presheaf `F` on light profinite spaces... -/
variable (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)

/-- ...we can sheafify it -/
def Fs : LightCondSet.{u} := (presheafToSheaf _ _).obj F

-- def SmallCondensedSet := Sheaf (coherentTopology Profinite.{u}) (Type u)
-- variable (G : Profinite.{u}ᵒᵖ ⥤ Type u)
-- def Gs : SmallCondensedSet.{u} := (presheafToSheaf _ _).obj G

-- variable (G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
-- def Gs : CondensedSet'.{u} := (presheafToSheaf _ _).obj G

end CondensedSets









namespace CondensedAbs

/-!

# (Light) condensed abelian groups

We can let our sheaves take values in abelian groups.
-/

abbrev CondensedAb' := Sheaf (coherentTopology Profinite.{u}) AddCommGroupCat.{u+1}

def eq : CondensedAb' ≌ CondensedAb := Condensed.ProfiniteCompHaus.equivalence AddCommGroupCat


variable (S : Profinite.{u}) (X : CondensedAb'.{u})

#check X.val.obj ⟨S⟩
#check X.cond


variable (T : LightProfinite.{u}) (Y : LightCondAb.{u})

#check Y.val.obj (op T)
#check Y.cond


variable (F : LightProfinite.{u}ᵒᵖ ⥤ AddCommGroupCat.{u})
def Fs : LightCondAb.{u} := (presheafToSheaf _ _).obj F


variable (G : Profinite.{u}ᵒᵖ ⥤ AddCommGroupCat.{u+1})
def Gs : CondensedAb'.{u} := (presheafToSheaf _ _).obj G





end CondensedAbs
