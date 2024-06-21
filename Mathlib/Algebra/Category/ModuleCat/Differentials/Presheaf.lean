/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.RingTheory.Kaehler.Basic

/-!
# The presheaf of differentials of a presheaf of modules

In this file, we define the type `M.Derivation φ` of derivations
with values in a presheaf of `R`-modules `M` relative to
a morphism of `φ : S ⟶ F.op ⋙ R` of presheaves of commutative rings
over categories `C` and `D` that are related by a functor `F : C ⥤ D`.
We formalize the notion of universal derivation.

Geometrically, if `f : X ⟶ S` is a morphisms of schemes (or more generally
a morphism of commutative ringed spaces), we would like to apply
these definitions where `F` is the pullback functors from open subsets of `S`
to open subsets of `X` and `φ` is the morphism $O_S ⟶ f_* O_X$.

In order to prove that there exists a universal derivation, the target
of which shall be called the presheaf of relative differentials of `φ`,
we shall first study the case where `F` is the identity functor.
Then, the general case (TODO) shall be obtained by observing that
derivations for `S ⟶ F.op ⋙ R` identify to derivations
for `S' ⟶ R` where `S'` is the pullback of presheaf of
commutative rings `S` via `F` (the data is the same: it suffices
to show that the two vanishing conditions `d_app` are equivalent).

-/


universe v v₁ v₂ u₁ u₂ u

open CategoryTheory

-- should be moved to `Algebra.Algebra.Defs`
section

lemma RingHom.isScalarTower_toAlgebra_comp {A B C : Type*}
    [CommSemiring A] [CommSemiring B] [CommSemiring C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) (fac : g.comp f = h) :
    letI := RingHom.toAlgebra f
    letI := RingHom.toAlgebra g
    letI := RingHom.toAlgebra h
    IsScalarTower A B C := by
  letI := RingHom.toAlgebra f
  letI := RingHom.toAlgebra g
  letI := RingHom.toAlgebra h
  constructor
  intro a b c
  change g (f a * b) * c = h a * (g b * c)
  simp only [← fac, map_mul, coe_comp, Function.comp_apply, mul_assoc]

lemma RingHom.smulCommClass_toAlgebra
    {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]
    (g : B →+* C) (h : A →+* C)  :
    letI := RingHom.toAlgebra g
    letI := RingHom.toAlgebra h
    SMulCommClass A B C := by
  letI := RingHom.toAlgebra g
  letI := RingHom.toAlgebra h
  constructor
  intro a b c
  change h a * (g b * c) = g b * (h a * c)
  rw [← mul_assoc, mul_comm (h a) (g b), mul_assoc]

end

-- should be moved a new file `Algebra.Category.ModuleCat.Differentials.Basic`
namespace CommRingCat

variable {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
  {g : A ⟶ A'} {g' : B ⟶ B'} (fac : g ≫ f' = f ≫ g')

-- TODO(?): Define `ModuleCat.Derivation M f`

variable (f) in
noncomputable def KaehlerDifferential : ModuleCat.{u} B :=
  letI := f.toAlgebra
  ModuleCat.of B (_root_.KaehlerDifferential A B)

namespace KaehlerDifferential

noncomputable def d (b : B) : KaehlerDifferential f :=
  letI := f.toAlgebra
  KaehlerDifferential.D A B b

@[ext]
lemma ext {M : ModuleCat B} {α β : KaehlerDifferential f ⟶ M}
    (h : ∀ (b : B), α (d b) = β (d b)) : α = β := by
  sorry

noncomputable def map :
    KaehlerDifferential f ⟶
      (ModuleCat.restrictScalars g').obj (KaehlerDifferential f') :=
  letI := f.toAlgebra
  letI := f'.toAlgebra
  letI := g.toAlgebra
  letI := g'.toAlgebra
  letI := (g ≫ f').toAlgebra
  have := RingHom.isScalarTower_toAlgebra_comp g f' _ rfl
  have := RingHom.isScalarTower_toAlgebra_comp f g' _ fac.symm
  have := RingHom.smulCommClass_toAlgebra g' f'
  { toFun := fun x ↦ _root_.KaehlerDifferential.map A A' B B' x
    map_add' := by simp
    map_smul' := by simp }

@[simp]
lemma map_d (b : B) : map fac (d b) = d (g' b) := by
  letI := f.toAlgebra
  letI := f'.toAlgebra
  letI := g.toAlgebra
  letI := g'.toAlgebra
  letI := (f'.comp g).toAlgebra
  have := RingHom.isScalarTower_toAlgebra_comp g f' _ rfl
  have := RingHom.isScalarTower_toAlgebra_comp f g' _ fac.symm
  have := RingHom.smulCommClass_toAlgebra g' f'
  apply _root_.KaehlerDifferential.map_D

end KaehlerDifferential

end CommRingCat

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

/-- The property that there exists a universal derivation for
a morphism of presheaves of commutative rings `S ⟶ F.op ⋙ R`. -/
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

/-- Auxiliary definition for `relativeDifferentials'`. -/
noncomputable def relativeDifferentials'BundledCore :
    BundledCorePresheafOfModules.{u} (R ⋙ forget₂ _ _) where
  obj X := CommRingCat.KaehlerDifferential (φ'.app X)
  map f := CommRingCat.KaehlerDifferential.map (φ'.naturality f)

/-- The presheaf of relative differentials of a morphism of presheaves of
commutative rings. -/
noncomputable def relativeDifferentials' :
    PresheafOfModules.{u} (R ⋙ forget₂ _ _) :=
  (relativeDifferentials'BundledCore φ').toPresheafOfModules

/-- The universal derivation. -/
noncomputable def derivation' : (relativeDifferentials' φ').Derivation' φ' where
  d {X} := AddMonoidHom.mk' (fun x =>
    letI := (φ'.app X).toAlgebra
    KaehlerDifferential.D (S'.obj X) (R.obj X) x) (by simp)
  d_map {X Y} f x := sorry
  d_app := sorry

/-- The derivation `derivation' φ'` is universal. -/
def isUniversal' : (derivation' φ').Universal := sorry

instance : HasDifferentials (F := 𝟭 D) φ' := ⟨_, _,  ⟨isUniversal' φ'⟩⟩

end DifferentialsConstruction

end PresheafOfModules
