import Mathlib.Condensed.Abelian
import Mathlib.Condensed.Discrete
import Mathlib.Condensed.Equivalence
import Mathlib.Condensed.Light.Adjunctions
import Mathlib.Condensed.Light.Discrete

noncomputable section

universe u

open CategoryTheory

section One

/-!

# (Light) condensed sets
-/

/-- I want my condensed sets to be defined on profinite spaces, not all compact Hausdorff spaces -/
abbrev CondensedSet' := Sheaf (coherentTopology Profinite.{u}) (Type (u+1))

/-- Fortunately they are equivalent to mathlib's condensed sets. -/
example : CondensedSet' ≌ CondensedSet := Condensed.ProfiniteCompHaus.equivalence _

variable (S : Profinite.{u}) (X : CondensedSet'.{u})

#check X.val
#check X.val.obj ⟨S⟩
#check X.cond

variable (T : LightProfinite.{u}) (Y : LightCondSet.{u})

#check Y.val.obj ⟨T⟩
#check Y.cond

/- Given a presheaf `F` on light profinite spaces... -/
variable (F : LightProfinite.{u}ᵒᵖ ⥤ Type u)

/-- ...we can sheafify it -/
example : LightCondSet.{u} := (presheafToSheaf _ _).obj F

-- abbrev SmallCondensedSet := Sheaf (coherentTopology Profinite.{u}) (Type u)
-- variable (G : Profinite.{u}ᵒᵖ ⥤ Type u)
-- example : SmallCondensedSet.{u} := (presheafToSheaf _ _).obj G

variable (G : Profinite.{u}ᵒᵖ ⥤ Type (u + 1))
example : CondensedSet'.{u} := (presheafToSheaf _ _).obj G

end One









section Two

/-!

# (Light) condensed abelian groups

We can let our sheaves take values in abelian groups.
-/

abbrev CondensedAb' := Sheaf (coherentTopology Profinite.{u}) AddCommGroupCat.{u+1}

example : CondensedAb' ≌ CondensedAb := Condensed.ProfiniteCompHaus.equivalence AddCommGroupCat


variable (S : Profinite.{u}) (X : CondensedAb'.{u})

#check X.val.obj ⟨S⟩
#check X.cond


variable (T : LightProfinite.{u}) (Y : LightCondAb.{u})

#check Y.val.obj ⟨T⟩
#check Y.cond


variable (F : LightProfinite.{u}ᵒᵖ ⥤ AddCommGroupCat.{u})
example : LightCondAb.{u} := (presheafToSheaf _ _).obj F


variable (G : Profinite.{u}ᵒᵖ ⥤ AddCommGroupCat.{u+1})
example : CondensedAb'.{u} := (presheafToSheaf _ _).obj G

example : Abelian CondensedAb := inferInstance

example : Abelian LightCondAb := inferInstance

end Two









section Three

/-!

# Benefits of light condensed objects
-/

#check Condensed.discrete

def CondensedIntegers : CondensedAb :=
  (Condensed.discrete AddCommGroupCat).obj (AddCommGroupCat.of (ULift ℤ))

#check LightCondensed.discrete

def LightCondensedIntegers : LightCondAb :=
  (LightCondensed.discrete AddCommGroupCat).obj (AddCommGroupCat.of ℤ)



end Three
















section Four

/-!
# Categorical foundations for condensed mathematics
-/

#check coherentTopology
#check regularCoverage
#check extensiveCoverage

end Four
