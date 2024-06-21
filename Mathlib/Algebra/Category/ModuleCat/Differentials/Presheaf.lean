/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The presheaf of differentials of a presheaf of modules

-/


universe v v₁ v₂ u₁ u₂ u

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}} {F : C ⥤ D} {S' R : Dᵒᵖ ⥤ CommRingCat.{u}}
   (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))
   (φ : S ⟶ F.op ⋙ R) (φ' : S' ⟶ R)

/-- Given a morphism of presheaves of commutative rings `φ : S ⟶ F.op ⋙ R`,
this is the type of relative `φ`-derivation of a presheaf of `R`-modules `M`. -/
structure Derivation where
  /-- the underlying additive map `R.obj X →+ M.obj X` of a derivation -/
  d {X : Dᵒᵖ} : R.obj X →+ M.obj X
  d_mul {X : Dᵒᵖ} (a b : R.obj X) : d (a * b) = a • d b + b • d a := by aesop_cat
  d_map {X Y : Dᵒᵖ} (f : X ⟶ Y) (x : R.obj X) :
    d (R.map f x) = M.map f (d x) := by aesop_cat
  d_app {X : Cᵒᵖ} (a : S.obj X) : d (φ.app X a) = 0 := by aesop_cat

namespace Derivation

-- Note: `d_app` cannot be a simp lemma because `dsimp` would
-- simplify the composition of functors `R ⋙ forget₂ _ _`
attribute [simp] d_mul d_map

variable {M N φ}
variable (d : M.Derivation φ)

@[simp] lemma d_one (X : Dᵒᵖ) : d.d (X := X) 1 = 0 := by
  simpa using d.d_mul (X := X) 1 1

/-- The postcomposition of a derivation by a morphism of presheaves of modules. -/
@[simps! d_apply]
def postcomp (f : M ⟶ N) : N.Derivation φ where
  d := (f.app _).toAddMonoidHom.comp d.d
  d_map _ _ := by simp [naturality_apply]
  d_app {X} a := by
    dsimp
    erw [d_app, map_zero]

/-- The universal property that a derivation `d : M.Derivation φ` must
satisfy so that the presheaf of modules `M` can be considered as the presheaf of
(relative) differentials of a presheaf of commutative rings `φ : S ⟶ F.op ⋙ R`. -/
structure Universal where
  /-- An absolyte derivation of `M'` descends as a morphism `M ⟶ M'`. -/
  desc {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.Derivation φ) : M ⟶ M'
  fac {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (d' : M'.Derivation φ) : d.postcomp (desc d') = d' := by aesop_cat
  postcomp_injective {M' : PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat)}
    (φ φ' : M ⟶ M') (h : d.postcomp φ = d.postcomp φ') : φ = φ' := by aesop_cat

end Derivation

class HasDifferentials : Prop where
  exists_universal_derivation : ∃ (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _))
      (d : M.Derivation φ), Nonempty d.Universal

/-- Given a morphism of presheaves of commutative rings `φ : S ⟶ R`,
this is the type of relative `φ`-derivation of a presheaf of `R`-modules `M`. -/
abbrev Derivation' : Type _ := M.Derivation (F := 𝟭 D) φ'

namespace Derivation'

@[simp]
nonrec lemma d_app (d : M.Derivation' φ') {X : Dᵒᵖ} (a : S'.obj X) :
    d.d (φ'.app X a) = 0 :=
  d.d_app _

end Derivation'

namespace DifferentialsConstruction

noncomputable def relativeDifferentials'BundledCore :
    BundledCorePresheafOfModules.{u} (R ⋙ forget₂ _ _) where
  obj X :=
    letI := (φ'.app X).toAlgebra
    ModuleCat.of (R.obj X) (Ω[(R.obj X)⁄(S'.obj X)])
  map {X Y} f :=
    letI := (φ'.app X).toAlgebra
    letI := (φ'.app Y).toAlgebra
    letI := (R.map f).toAlgebra
    letI := (S'.map f).toAlgebra
    letI := ((φ'.app Y).comp (S'.map f)).toAlgebra
    have : IsScalarTower (S'.obj X) (R.obj X) (R.obj Y) := sorry
    have : IsScalarTower ↑(S'.obj X) ↑(S'.obj Y) ↑(R.obj Y) := sorry
    have : SMulCommClass ↑(S'.obj Y) ↑(R.obj X) ↑(R.obj Y) := sorry
    KaehlerDifferential.map (S'.obj X) (S'.obj Y) (R.obj X) (R.obj Y)
  map_id := sorry
  map_comp := sorry

noncomputable def relativeDifferentials' :
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) :=
  (relativeDifferentials'BundledCore φ').toPresheafOfModules

def derivation' : (relativeDifferentials' φ').Derivation' φ' := sorry

end DifferentialsConstruction

end PresheafOfModules
