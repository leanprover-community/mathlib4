/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.Logic.UnivLE
/-!

# Families of morphisms with fixed target
-/

universe v u w

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] {X : C}

/-- A family of arrows all with codomain `X`. -/
structure FamilyOfArrows (X : C) : Type max (w+1) u v where
  /-- The indexing set. -/
  I : Type w
  /-- The domains of the arrows. -/
  domains : I → C
  /-- The arrows. -/
  arrows : (i : I) → domains i ⟶ X

namespace FamilyOfArrows

class hasPullbacks (F : FamilyOfArrows X) : Prop where
  has_pullback : ∀ i j, HasPullback (F.arrows i) (F.arrows j)

attribute [instance] FamilyOfArrows.hasPullbacks.has_pullback

-- variable (F : FamilyOfArrows X) (R : Presieve X)

-- #check FamilyOfArrows.{u, u+1, u}
-- #check Presieve X
-- #check R.hasPullbacks

def toSieve (F : FamilyOfArrows X) := Sieve.generate (Presieve.ofArrows F.domains F.arrows)

def FamilyOfElements (P : Cᵒᵖ ⥤ Type*) (F : FamilyOfArrows X) := ∀ i, P.obj (op (F.domains i))

@[simps]
def _root_.CategoryTheory.Sieve.toFamily (S : Sieve X) : FamilyOfArrows X where
  I := ΣY, { f : Y ⟶ X // S f }
  domains := fun i ↦ i.fst
  arrows := fun i ↦ i.snd.val

theorem _root_.CategoryTheory.Sieve.arrowsPresentation (S : Sieve X) : S =
    Presieve.ofArrows S.toFamily.domains S.toFamily.arrows := by
  funext Y f
  refine eq_iff_iff.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact Presieve.ofArrows.mk (⟨Y, f, h⟩ : ΣY, { f : Y ⟶ X // S f })
  · cases h with
    | mk i => exact i.snd.prop

namespace FamilyOfElements

variable {P : Cᵒᵖ ⥤ Type*} {F : FamilyOfArrows X}

def Compatible (x : FamilyOfElements P F) : Prop :=
  ∀ ⦃Z⦄ i j (gi : Z ⟶ F.domains i) (gj : Z ⟶ F.domains j), gi ≫ F.arrows i = gj ≫ F.arrows j →
    P.map gi.op (x i) = P.map gj.op (x j)

def PullbackCompatible (x : FamilyOfElements P F) [F.hasPullbacks] : Prop :=
  ∀ i j, have := hasPullbacks.has_pullback i j
    P.map (pullback.fst (f := F.arrows i) (g := F.arrows j)).op (x i) = P.map pullback.snd.op (x j)

theorem pullbackCompatible_iff (x : FamilyOfElements P F) [F.hasPullbacks] :
    x.Compatible ↔ x.PullbackCompatible := by
  refine ⟨fun t i j ↦ ?_, fun t Z i j gi gj comm ↦ ?_⟩
  · apply t
    exact pullback.condition
  · rw [← pullback.lift_fst _ _ comm, op_comp, FunctorToTypes.map_comp_apply, t i j,
      ← FunctorToTypes.map_comp_apply, ← op_comp, pullback.lift_snd]

def IsAmalgamation (x : FamilyOfElements P F) (t : P.obj (op X)) : Prop :=
  ∀ i, P.map (F.arrows i).op t = x i

variable {S : Sieve X}

def SieveCompatible (x : FamilyOfElements P S.toFamily) : Prop :=
  ∀ ⦃Y Z⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (hf),
    x ⟨Z, (g ≫ f), (S.downward_closed hf g)⟩ = P.map g.op (x ⟨Y, f, hf⟩)

theorem compatible_iff_sieveCompatible (x : FamilyOfElements P S.toFamily) :
    x.Compatible ↔ x.SieveCompatible := by
  constructor
  · intro h Y Z f g hf
    simpa using h ⟨_, g ≫ f, (S.downward_closed hf g)⟩ ⟨_, f, hf⟩ (𝟙 _) g (Category.id_comp _)
  · intro h Z ⟨Y₁, f₁, hf₁⟩ ⟨Y₂, f₂, hf₂⟩ gi gj comp
    simp only [Sieve.toFamily_domains, Sieve.toFamily_arrows] at comp
    rw [← h f₁ gi hf₁, ← h f₂ gj hf₂]
    congr

theorem Compatible.to_sieveCompatible {x : FamilyOfElements P S.toFamily}
    (t : x.Compatible) : x.SieveCompatible :=
  (compatible_iff_sieveCompatible x).1 t

end FamilyOfElements

def IsSeparatedFor (P : Cᵒᵖ ⥤ Type w) (F : FamilyOfArrows X) : Prop :=
  ∀ (x : FamilyOfElements P F) (t₁ t₂), x.IsAmalgamation t₁ → x.IsAmalgamation t₂ → t₁ = t₂

def IsSheafFor (P : Cᵒᵖ ⥤ Type w) (F : FamilyOfArrows X) : Prop :=
  ∀ x : FamilyOfElements P F, x.Compatible → ∃! t, x.IsAmalgamation t

variable {P : Cᵒᵖ ⥤ Type v} {S : Sieve X}

open Presieve

def YonedaSheafCondition (P : Cᵒᵖ ⥤ Type v) (S : Sieve X) : Prop :=
  ∀ f : S.functor ⟶ P, ∃! g, S.functorInclusion ≫ g = f

@[simps]
def natTransEquivCompatibleFamily :
    (S.functor ⟶ P) ≃ { x : FamilyOfElements P S.toFamily // x.Compatible } where
  toFun α := by
    refine ⟨fun i => ?_, ?_⟩
    · apply α.app (op (S.toFamily.domains i)) i.snd
    · rw [FamilyOfElements.compatible_iff_sieveCompatible]
      intro Y Z f g hf
      simp only [Sieve.toFamily_domains]
      rw [← FunctorToTypes.naturality _ _ α g.op]
      rfl
  invFun t :=
    { app := fun Y f => t.1 ⟨_, f.1, f.2⟩
      naturality := fun Y Z g => by
        ext ⟨f, hf⟩
        apply t.2.to_sieveCompatible _ }
  left_inv α := by aesop
  right_inv := fun _ ↦ rfl

theorem extension_iff_amalgamation (x : S.functor ⟶ P) (g : yoneda.obj X ⟶ P) :
    S.functorInclusion ≫ g = x ↔
      (natTransEquivCompatibleFamily x).1.IsAmalgamation (yonedaEquiv g) := by
  constructor
  · rintro rfl ⟨Y, f, hf⟩
    rw [yonedaEquiv_naturality]
    simp
  · intro h
    ext Y ⟨f, hf⟩
    convert h ⟨unop Y, f, hf⟩
    rw [yonedaEquiv_naturality]
    simp [yonedaEquiv]

theorem isSheafFor_iff_yonedaSheafCondition {P : Cᵒᵖ ⥤ Type v} {S : Sieve X} :
    IsSheafFor P S.toFamily ↔ YonedaSheafCondition P S := by
  rw [IsSheafFor, YonedaSheafCondition]
  simp_rw [extension_iff_amalgamation]
  rw [Equiv.forall_congr_left' natTransEquivCompatibleFamily]
  rw [Subtype.forall]
  apply ball_congr
  intro x hx
  rw [Equiv.exists_unique_congr_left _]
  simp

end FamilyOfArrows

end CategoryTheory
