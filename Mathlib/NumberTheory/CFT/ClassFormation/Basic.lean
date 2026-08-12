/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryEquivalence
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCategoryOver
public import Mathlib.NumberTheory.CFT.ClassFormation.GaloisCover
public import Mathlib.NumberTheory.CFT.ClassFormation.GrothendieckTopology
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Class formations

-/

-- depends on: #42397, #42396, #42320, #42568

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite
open scoped FintypeCatDiscrete

namespace CategoryTheory
variable {C : Type*} [Category* C]

/-- If `f ≫ g = fg`, this is the morphism between the group of automorphisms
of `Over.mk f` to the group of automorphism of `Over.mk fg`. -/
@[implicit_reducible]
def Aut.overMap {Z Y X : C} (f : Z ⟶ Y) (g : Y ⟶ X) (fg : Z ⟶ X)
    (fac : f ≫ g = fg := by cat_disch) :
    Aut (Over.mk f) →* Aut (Over.mk fg) where
  toFun σ := Over.isoMk ((Over.forget ..).mapIso σ)
    (by simp [← fac, Functor.mapIso, dsimp% σ.hom.w_assoc])
  map_one' := rfl
  map_mul' _ _ := rfl

end CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open PreGaloisCategory GaloisCategory

namespace GaloisCategory

open PreGaloisCategory

/-- The degree of an object `X` in a Galois category. This is the cardinality
of `F.obj X` for any fiber functor `F`, see the lemma `deg_eq_card_fiber` below. -/
@[no_expose]
noncomputable def deg [GaloisCategory C] (X : C) : ℕ :=
  Nat.card ((getFiberFunctor C).obj X)

lemma card_fiber_eq_zero [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] {X : C}
    (hX : IsInitial X) :
    Nat.card (F.obj X) = 0 := by
  have := (initial_iff_fiber_empty F X).1 ⟨hX⟩
  exact Nat.card_of_isEmpty

instance [GaloisCategory C] {Y X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) : Epi f :=
  epi_of_nonempty_of_isConnected (getFiberFunctor C) f

lemma card_fiber_eq_card_hom [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] {Y X : C}
    [PreGaloisCategory.IsConnected X] [IsGalois Y] (f : Y ⟶ X) :
    Nat.card (F.obj X) = Nat.card (Y ⟶ X) := by
  let y : F.obj Y := Classical.arbitrary _
  refine (Nat.card_eq_of_bijective (fun g ↦ F.map g y)
    ⟨fun g₁ g₂ h ↦ hom_ext_of_isConnected F y h, fun x ↦ ?_⟩).symm
  obtain ⟨z, rfl⟩ := surjective_of_epi ((forget _).map (F.map f)) x
  obtain ⟨γ, rfl⟩ := (isPretransitive_of_isGalois F Y).exists_smul_eq y z
  exact ⟨γ.hom ≫ f, by cat_disch⟩

lemma has_decomp_of_not_isConnected [PreGaloisCategory C] (X : C)
    (hX₁ : ¬ PreGaloisCategory.IsConnected X) (hX₂ : IsInitial X → False) :
    ∃ (X₁ X₂ : C) (_ : IsInitial X₁ → False) (_ : IsInitial X₂ → False)
      (inl : X₁ ⟶ X) (inr : X₂ ⟶ X),
        Nonempty (IsColimit (BinaryCofan.mk inl inr)) := by
  -- from `has_decomp_connected_components_aux` in `Decomposition.lean`
  obtain ⟨X₁, inl, hX₁, _, h⟩ :=
    has_non_trivial_subobject_of_not_isConnected_of_not_initial X hX₁ hX₂
  obtain ⟨X₂, inr, ⟨H⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand inl
  refine ⟨X₁, X₂, hX₁, fun hX₂ ↦ h ?_, inl, inr, ⟨H⟩⟩
  obtain ⟨l : X ⟶ X₁, hl : inl ≫ l = 𝟙 X₁, _⟩ := BinaryCofan.IsColimit.desc' H (𝟙 X₁) (hX₂.to _)
  refine ⟨l, hl, BinaryCofan.IsColimit.hom_ext H ?_ (hX₂.hom_ext _ _)⟩
  change inl ≫ l ≫ inl = inl ≫ 𝟙 X
  simp [reassoc_of% hl]

lemma obj_rec [GaloisCategory C] {motive : C → Prop}
    (of_isInitial : ∀ (X : C), IsInitial X → motive X)
    (of_isConnected : ∀ (X : C), PreGaloisCategory.IsConnected X → motive X)
    (of_isColimit : ∀ (X Y : C) (b : BinaryCofan X Y) (_ : IsColimit b),
      motive X → motive Y → motive b.pt) (X : C) :
      motive X := by
  let F := getFiberFunctor C
  generalize hn : Nat.card (F.obj X) = n
  induction n using Nat.strongRecOn generalizing X with | _ n hi
  by_cases h₁ : Nonempty (IsInitial X)
  · exact of_isInitial _ h₁.some
  · by_cases h₂ : PreGaloisCategory.IsConnected X
    · exact of_isConnected _ h₂
    · obtain ⟨X₁, X₂, h₁, h₂, inl, inr, ⟨h⟩⟩ :=
        has_decomp_of_not_isConnected X h₂ (fun h ↦ h₁ ⟨h⟩)
      have := card_fiber_eq_add_of_isColimit F h
      simp only [BinaryCofan.mk_pt, hn] at this
      have := non_zero_card_fiber_of_not_initial F _ h₁
      have := non_zero_card_fiber_of_not_initial F _ h₂
      exact of_isColimit _ _ _ h (hi _ (by lia) _ rfl) (hi _ (by lia) _ rfl)

lemma deg_eq_card_fiber [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (X : C) :
    deg X = Nat.card (F.obj X) := by
  induction X using obj_rec with
  | of_isInitial X hX =>
    simp [deg, card_fiber_eq_zero _ hX]
  | of_isConnected X hX =>
    obtain ⟨Y, f, _⟩ := exists_hom_from_galois_of_connected X
    simp [deg, card_fiber_eq_card_hom _ f]
  | of_isColimit X Y b hb hX hY =>
    simp only [deg] at hX hY
    simp [deg, card_fiber_eq_add_of_isColimit _ hb, hX, hY]

/-- The degree of a morphism `f : Y ⟶ X` in a Galois category, where `X`
is connected. -/
noncomputable def degMap [GaloisCategory C] {Y X : C}
    [PreGaloisCategory.IsConnected X] (f : Y ⟶ X) : ℕ :=
  deg (Over.mk f)

-- TODO: show the multiplicativity of degrees

end GaloisCategory

open GaloisCategory

variable (C) in
/-- A formation for a Galois category `C` is a sheaf of abelian groups
on the category of connected objects in `C` (equipped with the regular topology). -/
structure Formation [GaloisCategory C] [EssentiallySmall.{v} C] where
  /-- the underlying sheaf on the category of connected objects on the Galois category -/
  sheaf : Sheaf (isConnectedTopology C) Ab.{v}

namespace Formation

variable [GaloisCategory C] [EssentiallySmall.{v} C] (Φ : Formation C)

section

variable {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
  [PreGaloisCategory.IsConnected Y]

/-- If `Φ` is a formation and `f : Y ⟶ X` is a Galois cover, this is the induced
representation of the group of automorphisms of `Over.mk f`. -/
@[nolint unusedArguments]
def representation [IsGaloisCover f] :
    Representation (ULift.{v} ℤ) (Aut (Over.mk f)) (Φ.sheaf.obj.obj (op ⟨Y, inferInstance⟩)) where
  toFun g :=
    { toFun := (Φ.sheaf.obj.map (ObjectProperty.homMk g.inv.left).op).hom.toFun
      map_add' := by simp
      map_smul' := by simp }
  map_one' := by
    ext : 1
    dsimp [Aut.one_def]
    rw [ObjectProperty.homMk_id]
    simp
  map_mul' g h := by
    ext : 1
    dsimp
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl

variable [IsGaloisCover f]

/-- If `Φ` is a formation and `f : Y ⟶ X` is a Galois cover, this is the induced
representation of the group of automorphisms of `Over.mk f`, as an object
in `Rep`. -/
abbrev rep : Rep.{v} (ULift.{v} ℤ) (Aut (Over.mk f)) := Rep.of (Φ.representation f)

section

variable {Y X' X : C}
  [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X']
  [PreGaloisCategory.IsConnected X]
  (f : Y ⟶ X') (g : X' ⟶ X) (fg : Y ⟶ X)
  [IsGaloisCover fg] [IsGaloisCover f]

/-- Auxiliary definition for `resRep`. -/
abbrev resIntertwiningMap (fac : f ≫ g = fg := by cat_disch) :
  Representation.IntertwiningMap (MonoidHom.comp (Φ.rep fg).ρ (Aut.overMap f g fg))
    (Φ.representation f) where
  toLinearMap := .id
  isIntertwining' _ := rfl

/-- If `Φ` is a formation, and `f ≫ g = fg`, when this is the morphism
from the restriction of `Φ.rep fg` to `Φ.rep f`. -/
abbrev resRep (fac : f ≫ g = fg := by cat_disch) :
    Rep.res (Aut.overMap f g fg) (Φ.rep fg) ⟶ Φ.rep f :=
  Rep.ofHom (Φ.resIntertwiningMap f g fg)

end

/-- The cohomology of a Galois cover for a formation. -/
noncomputable abbrev H (n : ℕ) := groupCohomology (Φ.rep f) n

end

/-- The inflation morphisms on the cohomology of a formation. -/
def inflation {Y' Y X : C}
    [PreGaloisCategory.IsConnected Y'] [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X]
    (f : Y' ⟶ Y) (g : Y ⟶ X) (fg : Y' ⟶ X)
    [IsGaloisCover g] [IsGaloisCover fg] (n : ℕ)
    (fac : f ≫ g = fg := by cat_disch) :
    Φ.H g n ⟶ Φ.H fg n := by
  sorry

/-- The restriction morphisms on the cohomology of a formation. -/
noncomputable def restriction {Y X' X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X']
    [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X') (g : X' ⟶ X) (fg : Y ⟶ X)
    [IsGaloisCover fg] [IsGaloisCover f] (n : ℕ)
    (fac : f ≫ g = fg := by cat_disch) :
    Φ.H fg n ⟶ Φ.H f n :=
  groupCohomology.map (Aut.overMap f g fg) (Φ.resRep f g fg) n

/-def corestriction {Y X' X : C}
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X']
    [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X') (g : X' ⟶ X) (fg : Y ⟶ X)
    [IsGaloisCover fg] [IsGaloisCover f] (n : ℕ)
    (fac : f ≫ g = fg := by cat_disch) :
    Φ.H f n ⟶ Φ.H fg n := by
  sorry-/

end Formation

section

variable [GaloisCategory C] [EssentiallySmall.{v} C]

variable (C) in
/-- A field formation is a formation which which the cohomology is trivial
in degree `1`. -/
structure FieldFormation extends Formation C where
  isZero_H_one {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] [IsGaloisCover f] :
      IsZero (toFormation.H f 1)

/-! The definition below is suggested by Serre in _Corps locaux_ p. 176
(this is chosen in order to involve only group cohomology of finite
groups rather than any "colimit" of these groups, which could also
be interpreted here as the cohomology for the Grothendieck
topology `isConnectedTopology C`). With these axioms, when taking a
suitable colimit, we should get a subgroup of `ℚ / ℤ` which may
not be the whole `ℚ / ℤ`. If we want that the invariant is an isomorphism
with `ℚ / ℤ`, an extra condition on `C` should be done. -/

variable (C) in
/-- A class formation is a field formation for which the cohomology
in degree `2` of a Galois cover `f : Y ⟶ X` identifies to `ℤ / dℤ` where
`d` is the degree of `f`, and the isomorphisms should satisfy compatibilities
with inflation and restriction maps. In this implementation,
the isomorphisms are given by the data of the fundamental class in `H f 2`. -/
structure ClassFormation extends FieldFormation C where
  /-- The fundamental class attached to a Galois cover -/
  u {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] [IsGaloisCover f] : toFormation.H f 2
  addOrderOf_u {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] [IsGaloisCover f] :
    addOrderOf (u f) = degMap f
  zmultiples_u {Y X : C} (f : Y ⟶ X) [PreGaloisCategory.IsConnected X]
    [PreGaloisCategory.IsConnected Y] [IsGaloisCover f] :
    AddSubgroup.zmultiples (u f) = ⊤
  inflation_u {Y' Y X : C} [PreGaloisCategory.IsConnected Y']
    [PreGaloisCategory.IsConnected Y] [PreGaloisCategory.IsConnected X]
    (f : Y' ⟶ Y) (g : Y ⟶ X) (fg : Y' ⟶ X)
    [IsGaloisCover g] [IsGaloisCover fg]
    (fac : f ≫ g = fg := by cat_disch) :
    (toFormation.inflation f g fg 2) (u g) = degMap f • u fg
  restriction_u {Y X' X : C} [PreGaloisCategory.IsConnected Y]
    [PreGaloisCategory.IsConnected X'] [PreGaloisCategory.IsConnected X]
    (f : Y ⟶ X') (g : X' ⟶ X) (fg : Y ⟶ X)
    [IsGaloisCover f] [IsGaloisCover fg]
    (fac : f ≫ g = fg := by cat_disch) :
    (toFormation.restriction f g fg 2) (u fg) = u f

end

end CategoryTheory
