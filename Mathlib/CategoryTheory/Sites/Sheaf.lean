/-
Copyright (c) 2020 Kevin Buzzard, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bhavik Mehta

! This file was ported from Lean 3 source module category_theory.sites.sheaf
! leanprover-community/mathlib commit a67ec23dd8dc08195d77b6df2cd21f9c64989131
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathbin.CategoryTheory.Limits.Yoneda
import Mathbin.CategoryTheory.Preadditive.FunctorCategory
import Mathbin.CategoryTheory.Sites.SheafOfTypes

/-!
# Sheaves taking values in a category

If C is a category with a Grothendieck topology, we define the notion of a sheaf taking values in
an arbitrary category `A`. We follow the definition in https://stacks.math.columbia.edu/tag/00VR,
noting that the presheaf of sets "defined above" can be seen in the comments between tags 00VQ and
00VR on the page <https://stacks.math.columbia.edu/tag/00VL>. The advantage of this definition is
that we need no assumptions whatsoever on `A` other than the assumption that the morphisms in `C`
and `A` live in the same universe.

* An `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is defined to be a sheaf (for the topology `J`) iff for
  every `E : A`, the type-valued presheaves of sets given by sending `U : Cᵒᵖ` to `Hom_{A}(E, P U)`
  are all sheaves of sets, see `category_theory.presheaf.is_sheaf`.
* When `A = Type`, this recovers the basic definition of sheaves of sets, see
  `category_theory.is_sheaf_iff_is_sheaf_of_type`.
* An alternate definition when `C` is small, has pullbacks and `A` has products is given by an
  equalizer condition `category_theory.presheaf.is_sheaf'`. This is equivalent to the earlier
  definition, shown in `category_theory.presheaf.is_sheaf_iff_is_sheaf'`.
* When `A = Type`, this is *definitionally* equal to the equalizer condition for presieves in
  `category_theory.sites.sheaf_of_types`.
* When `A` has limits and there is a functor `s : A ⥤ Type` which is faithful, reflects isomorphisms
  and preserves limits, then `P : Cᵒᵖ ⥤ A` is a sheaf iff the underlying presheaf of types
  `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf (`category_theory.presheaf.is_sheaf_iff_is_sheaf_forget`).
  Cf https://stacks.math.columbia.edu/tag/0073, which is a weaker version of this statement (it's
  only over spaces, not sites) and https://stacks.math.columbia.edu/tag/00YR (a), which
  additionally assumes filtered colimits.
-/


universe w v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C]

variable {A : Type u₂} [Category.{v₂} A]

variable (J : GrothendieckTopology C)

-- We follow https://stacks.math.columbia.edu/tag/00VL definition 00VR
/-- A sheaf of A is a presheaf P : Cᵒᵖ => A such that for every E : A, the
presheaf of types given by sending U : C to Hom_{A}(E, P U) is a sheaf of types.

https://stacks.math.columbia.edu/tag/00VR
-/
def IsSheaf (P : Cᵒᵖ ⥤ A) : Prop :=
  ∀ E : A, Presieve.IsSheaf J (P ⋙ coyoneda.obj (op E))
#align category_theory.presheaf.is_sheaf CategoryTheory.Presheaf.IsSheaf

section LimitSheafCondition

open Presieve Presieve.FamilyOfElements Limits

variable (P : Cᵒᵖ ⥤ A) {X : C} (S : Sieve X) (R : Presieve X) (E : Aᵒᵖ)

/-- Given a sieve `S` on `X : C`, a presheaf `P : Cᵒᵖ ⥤ A`, and an object `E` of `A`,
    the cones over the natural diagram `S.arrows.diagram.op ⋙ P` associated to `S` and `P`
    with cone point `E` are in 1-1 correspondence with sieve_compatible family of elements
    for the sieve `S` and the presheaf of types `Hom (E, P -)`. -/
@[simps]
def conesEquivSieveCompatibleFamily :
    (S.arrows.diagram.op ⋙ P).cones.obj E ≃
      { x : FamilyOfElements (P ⋙ coyoneda.obj E) S // x.SieveCompatible }
    where
  toFun π :=
    ⟨fun Y f h => π.app (op ⟨Over.mk f, h⟩), fun _ =>
      by
      intros
      apply (id_comp _).symm.trans
      dsimp
      convert π.naturality (Quiver.Hom.op (over.hom_mk _ _)) <;> dsimp <;> rfl⟩
  invFun x :=
    { app := fun f => x.1 f.unop.1.Hom f.unop.2
      naturality' := fun f f' g =>
        by
        refine' Eq.trans _ (x.2 f.unop.1.Hom g.unop.left f.unop.2)
        erw [id_comp]
        congr
        rw [over.w g.unop] }
  left_inv π := by
    ext
    dsimp
    congr
    rw [op_eq_iff_eq_unop]
    ext
    symm
    apply costructured_arrow.eq_mk
  right_inv x := by
    ext
    rfl
#align category_theory.presheaf.cones_equiv_sieve_compatible_family CategoryTheory.Presheaf.conesEquivSieveCompatibleFamily

variable {P S E} {x : FamilyOfElements (P ⋙ coyoneda.obj E) S} (hx : x.SieveCompatible)

/-- The cone corresponding to a sieve_compatible family of elements, dot notation enabled. -/
@[simp]
def CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone : Cone (S.arrows.diagram.op ⋙ P)
    where
  pt := E.unop
  π := (conesEquivSieveCompatibleFamily P S E).invFun ⟨x, hx⟩
#align category_theory.presieve.family_of_elements.sieve_compatible.cone CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone

/-- Cone morphisms from the cone corresponding to a sieve_compatible family to the natural
    cone associated to a sieve `S` and a presheaf `P` are in 1-1 correspondence with amalgamations
    of the family. -/
def homEquivAmalgamation : (hx.Cone ⟶ P.mapCone S.arrows.Cocone.op) ≃ { t // x.IsAmalgamation t }
    where
  toFun l := ⟨l.Hom, fun Y f hf => l.w (op ⟨Over.mk f, hf⟩)⟩
  invFun t := ⟨t.1, fun f => t.2 f.unop.1.Hom f.unop.2⟩
  left_inv l := by
    ext
    rfl
  right_inv t := by
    ext
    rfl
#align category_theory.presheaf.hom_equiv_amalgamation CategoryTheory.Presheaf.homEquivAmalgamation

variable (P S)

/-- Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone is a limit cone
    iff `Hom (E, P -)` is a sheaf of types for the sieve `S` and all `E : A`. -/
theorem isLimit_iff_isSheafFor :
    Nonempty (IsLimit (P.mapCone S.arrows.Cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) S :=
  by
  dsimp [is_sheaf_for]; simp_rw [compatible_iff_sieve_compatible]
  rw [((cone.is_limit_equiv_is_terminal _).trans (is_terminal_equiv_unique _ _)).nonempty_congr]
  rw [Classical.nonempty_pi]; constructor
  · intro hu E x hx
    specialize hu hx.cone
    erw [(hom_equiv_amalgamation hx).uniqueCongr.nonempty_congr] at hu
    exact (unique_subtype_iff_exists_unique _).1 hu
  · rintro h ⟨E, π⟩
    let eqv := cones_equiv_sieve_compatible_family P S (op E)
    rw [← eqv.left_inv π]
    erw [(hom_equiv_amalgamation (eqv π).2).uniqueCongr.nonempty_congr]
    rw [unique_subtype_iff_exists_unique]
    exact h _ _ (eqv π).2
#align category_theory.presheaf.is_limit_iff_is_sheaf_for CategoryTheory.Presheaf.isLimit_iff_isSheafFor

/-- Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone admits at most one
    morphism from every cone in the same category (i.e. over the same diagram),
    iff `Hom (E, P -)`is separated for the sieve `S` and all `E : A`. -/
theorem subsingleton_iff_isSeparatedFor :
    (∀ c, Subsingleton (c ⟶ P.mapCone S.arrows.Cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSeparatedFor (P ⋙ coyoneda.obj E) S :=
  by
  constructor
  · intro hs E x t₁ t₂ h₁ h₂
    have hx := is_compatible_of_exists_amalgamation x ⟨t₁, h₁⟩
    rw [compatible_iff_sieve_compatible] at hx
    specialize hs hx.cone
    cases hs
    have := (hom_equiv_amalgamation hx).symm.Injective
    exact Subtype.ext_iff.1 (@this ⟨t₁, h₁⟩ ⟨t₂, h₂⟩ (hs _ _))
  · rintro h ⟨E, π⟩
    let eqv := cones_equiv_sieve_compatible_family P S (op E)
    constructor
    rw [← eqv.left_inv π]
    intro f₁ f₂
    let eqv' := hom_equiv_amalgamation (eqv π).2
    apply eqv'.injective
    ext
    apply h _ (eqv π).1 <;> exact (eqv' _).2
#align category_theory.presheaf.subsingleton_iff_is_separated_for CategoryTheory.Presheaf.subsingleton_iff_isSeparatedFor

/-- A presheaf `P` is a sheaf for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` is a limit cone. -/
theorem isSheaf_iff_isLimit :
    IsSheaf J P ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → Nonempty (IsLimit (P.mapCone S.arrows.Cocone.op)) :=
  ⟨fun h X S hS => (isLimit_iff_isSheafFor P S).2 fun E => h E.unop S hS, fun h E X S hS =>
    (isLimit_iff_isSheafFor P S).1 (h S hS) (op E)⟩
#align category_theory.presheaf.is_sheaf_iff_is_limit CategoryTheory.Presheaf.isSheaf_iff_isLimit

/-- A presheaf `P` is separated for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` admits at most one morphism from every
    cone in the same category. -/
theorem isSeparated_iff_subsingleton :
    (∀ E : A, IsSeparated J (P ⋙ coyoneda.obj (op E))) ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → ∀ c, Subsingleton (c ⟶ P.mapCone S.arrows.Cocone.op) :=
  ⟨fun h X S hS => (subsingleton_iff_isSeparatedFor P S).2 fun E => h E.unop S hS, fun h E X S hS =>
    (subsingleton_iff_isSeparatedFor P S).1 (h S hS) (op E)⟩
#align category_theory.presheaf.is_separated_iff_subsingleton CategoryTheory.Presheaf.isSeparated_iff_subsingleton

/-- Given presieve `R` and presheaf `P : Cᵒᵖ ⥤ A`, the natural cone associated to `P` and
    the sieve `sieve.generate R` generated by `R` is a limit cone iff `Hom (E, P -)` is a
    sheaf of types for the presieve `R` and all `E : A`. -/
theorem isLimit_iff_isSheafFor_presieve :
    Nonempty (IsLimit (P.mapCone (generate R).arrows.Cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) R :=
  (isLimit_iff_isSheafFor P _).trans (forall_congr' fun _ => (isSheafFor_iff_generate _).symm)
#align category_theory.presheaf.is_limit_iff_is_sheaf_for_presieve CategoryTheory.Presheaf.isLimit_iff_isSheafFor_presieve

/-- A presheaf `P` is a sheaf for the Grothendieck topology generated by a pretopology `K`
    iff for every covering presieve `R` of `K`, the natural cone associated to `P` and
    `sieve.generate R` is a limit cone. -/
theorem isSheaf_iff_isLimit_pretopology [HasPullbacks C] (K : Pretopology C) :
    IsSheaf (K.toGrothendieck C) P ↔
      ∀ ⦃X : C⦄ (R : Presieve X),
        R ∈ K X → Nonempty (IsLimit (P.mapCone (generate R).arrows.Cocone.op)) :=
  by
  dsimp [is_sheaf]
  simp_rw [is_sheaf_pretopology]
  exact
    ⟨fun h X R hR => (is_limit_iff_is_sheaf_for_presieve P R).2 fun E => h E.unop R hR,
      fun h E X R hR => (is_limit_iff_is_sheaf_for_presieve P R).1 (h R hR) (op E)⟩
#align category_theory.presheaf.is_sheaf_iff_is_limit_pretopology CategoryTheory.Presheaf.isSheaf_iff_isLimit_pretopology

end LimitSheafCondition

variable {J}

/-- This is a wrapper around `presieve.is_sheaf_for.amalgamate` to be used below.
  If `P`s a sheaf, `S` is a cover of `X`, and `x` is a collection of morphisms from `E`
  to `P` evaluated at terms in the cover which are compatible, then we can amalgamate
  the `x`s to obtain a single morphism `E ⟶ P.obj (op X)`. -/
def IsSheaf.amalgamate {A : Type u₂} [Category.{max v₁ u₁} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.cover X) (x : ∀ I : S.arrow, E ⟶ P.obj (op I.y))
    (hx : ∀ I : S.Relation, x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op) : E ⟶ P.obj (op X) :=
  (hP _ _ S.condition).amalgamate (fun Y f hf => x ⟨Y, f, hf⟩) fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w =>
    hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩
#align category_theory.presheaf.is_sheaf.amalgamate CategoryTheory.Presheaf.IsSheaf.amalgamate

@[simp, reassoc.1]
theorem IsSheaf.amalgamate_map {A : Type u₂} [Category.{max v₁ u₁} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.cover X) (x : ∀ I : S.arrow, E ⟶ P.obj (op I.y))
    (hx : ∀ I : S.Relation, x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op) (I : S.arrow) :
    hP.amalgamate S x hx ≫ P.map I.f.op = x _ :=
  by
  rcases I with ⟨Y, f, hf⟩
  apply
    @presieve.is_sheaf_for.valid_glue _ _ _ _ _ _ (hP _ _ S.condition) (fun Y f hf => x ⟨Y, f, hf⟩)
      (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w => hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩) f hf
#align category_theory.presheaf.is_sheaf.amalgamate_map CategoryTheory.Presheaf.IsSheaf.amalgamate_map

theorem IsSheaf.hom_ext {A : Type u₂} [Category.{max v₁ u₁} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.cover X) (e₁ e₂ : E ⟶ P.obj (op X))
    (h : ∀ I : S.arrow, e₁ ≫ P.map I.f.op = e₂ ≫ P.map I.f.op) : e₁ = e₂ :=
  (hP _ _ S.condition).IsSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩
#align category_theory.presheaf.is_sheaf.hom_ext CategoryTheory.Presheaf.IsSheaf.hom_ext

theorem isSheaf_of_iso_iff {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P' :=
  forall_congr' fun a =>
    ⟨Presieve.isSheaf_iso J (isoWhiskerRight e _),
      Presieve.isSheaf_iso J (isoWhiskerRight e.symm _)⟩
#align category_theory.presheaf.is_sheaf_of_iso_iff CategoryTheory.Presheaf.isSheaf_of_iso_iff

variable (J)

theorem isSheaf_of_isTerminal {X : A} (hX : IsTerminal X) :
    Presheaf.IsSheaf J ((CategoryTheory.Functor.const _).obj X) := fun _ _ _ _ _ _ =>
  ⟨hX.from _, fun _ _ _ => hX.hom_ext _ _, fun _ _ => hX.hom_ext _ _⟩
#align category_theory.presheaf.is_sheaf_of_is_terminal CategoryTheory.Presheaf.isSheaf_of_isTerminal

end Presheaf

variable {C : Type u₁} [Category.{v₁} C]

variable (J : GrothendieckTopology C)

variable (A : Type u₂) [Category.{v₂} A]

/-- The category of sheaves taking values in `A` on a grothendieck topology. -/
structure Sheaf where
  val : Cᵒᵖ ⥤ A
  cond : Presheaf.IsSheaf J val
#align category_theory.Sheaf CategoryTheory.Sheaf

namespace Sheaf

variable {J A}

/-- Morphisms between sheaves are just morphisms of presheaves. -/
@[ext]
structure Hom (X Y : Sheaf J A) where
  val : X.val ⟶ Y.val
#align category_theory.Sheaf.hom CategoryTheory.Sheaf.Hom

@[simps]
instance : Category (Sheaf J A) where
  Hom := Hom
  id X := ⟨𝟙 _⟩
  comp X Y Z f g := ⟨f.val ≫ g.val⟩
  id_comp' X Y f := Hom.ext _ _ <| id_comp _
  comp_id' X Y f := Hom.ext _ _ <| comp_id _
  assoc' X Y Z W f g h := Hom.ext _ _ <| assoc _ _ _

-- Let's make the inhabited linter happy...
instance (X : Sheaf J A) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩

end Sheaf

/-- The inclusion functor from sheaves to presheaves. -/
@[simps]
def sheafToPresheaf : Sheaf J A ⥤ Cᵒᵖ ⥤ A
    where
  obj := Sheaf.val
  map _ _ f := f.val
  map_id' X := rfl
  map_comp' X Y Z f g := rfl
#align category_theory.Sheaf_to_presheaf CategoryTheory.sheafToPresheaf

instance : Full (sheafToPresheaf J A) where preimage X Y f := ⟨f⟩

instance : Faithful (sheafToPresheaf J A) where

/-- This is stated as a lemma to prevent class search from forming a loop since a sheaf morphism is
monic if and only if it is monic as a presheaf morphism (under suitable assumption).-/
theorem Sheaf.Hom.mono_of_presheaf_mono {F G : Sheaf J A} (f : F ⟶ G) [h : Mono f.1] : Mono f :=
  (sheafToPresheaf J A).mono_of_mono_map h
#align category_theory.Sheaf.hom.mono_of_presheaf_mono CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono

instance Sheaf.Hom.epi_of_presheaf_epi {F G : Sheaf J A} (f : F ⟶ G) [h : Epi f.1] : Epi f :=
  (sheafToPresheaf J A).epi_of_epi_map h
#align category_theory.Sheaf.hom.epi_of_presheaf_epi CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi

/-- The sheaf of sections guaranteed by the sheaf condition. -/
@[simps]
def sheafOver {A : Type u₂} [Category.{v₂} A] {J : GrothendieckTopology C} (ℱ : Sheaf J A) (E : A) :
    SheafOfTypes J :=
  ⟨ℱ.val ⋙ coyoneda.obj (op E), ℱ.cond E⟩
#align category_theory.sheaf_over CategoryTheory.sheafOver

theorem isSheaf_iff_isSheaf_of_type (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P :=
  by
  constructor
  · intro hP
    refine' presieve.is_sheaf_iso J _ (hP PUnit)
    exact iso_whisker_left _ coyoneda.punit_iso ≪≫ P.right_unitor
  · intro hP X Y S hS z hz
    refine' ⟨fun x => (hP S hS).amalgamate (fun Z f hf => z f hf x) _, _, _⟩
    · intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      exact congr_fun (hz g₁ g₂ hf₁ hf₂ h) x
    · intro Z f hf
      ext x
      apply presieve.is_sheaf_for.valid_glue
    · intro y hy
      ext x
      apply (hP S hS).IsSeparatedFor.ext
      intro Y' f hf
      rw [presieve.is_sheaf_for.valid_glue _ _ _ hf, ← hy _ hf]
      rfl
#align category_theory.is_sheaf_iff_is_sheaf_of_type CategoryTheory.isSheaf_iff_isSheaf_of_type

/-- The category of sheaves taking values in Type is the same as the category of set-valued sheaves.
-/
@[simps]
def sheafEquivSheafOfTypes : Sheaf J (Type w) ≌ SheafOfTypes J
    where
  Functor :=
    { obj := fun S => ⟨S.val, (isSheaf_iff_isSheaf_of_type _ _).1 S.2⟩
      map := fun S T f => ⟨f.val⟩ }
  inverse :=
    { obj := fun S => ⟨S.val, (isSheaf_iff_isSheaf_of_type _ _).2 S.2⟩
      map := fun S T f => ⟨f.val⟩ }
  unitIso := NatIso.ofComponents (fun X => ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by tidy, by tidy⟩) (by tidy)
  counitIso := NatIso.ofComponents (fun X => ⟨⟨𝟙 _⟩, ⟨𝟙 _⟩, by tidy, by tidy⟩) (by tidy)
#align category_theory.Sheaf_equiv_SheafOfTypes CategoryTheory.sheafEquivSheafOfTypes

instance : Inhabited (Sheaf (⊥ : GrothendieckTopology C) (Type w)) :=
  ⟨(sheafEquivSheafOfTypes _).inverse.obj default⟩

variable {J} {A}

/-- If the empty sieve is a cover of `X`, then `F(X)` is terminal. -/
def Sheaf.isTerminalOfBotCover (F : Sheaf J A) (X : C) (H : ⊥ ∈ J X) :
    IsTerminal (F.1.obj (op X)) :=
  by
  apply (config := { instances := false }) is_terminal.of_unique
  intro Y
  choose t h using F.2 Y _ H (by tidy) (by tidy)
  exact ⟨⟨t⟩, fun a => h.2 a (by tidy)⟩
#align category_theory.Sheaf.is_terminal_of_bot_cover CategoryTheory.Sheaf.isTerminalOfBotCover

section Preadditive

open Preadditive

variable [Preadditive A] {P Q : Sheaf J A}

instance sheafHomHasZsmul : SMul ℤ (P ⟶ Q)
    where smul n f :=
    Sheaf.Hom.mk
      { app := fun U => n • f.1.app U
        naturality' := fun U V i =>
          by
          induction' n using Int.induction_on with n ih n ih
          · simp only [zero_smul, comp_zero, zero_comp]
          ·
            simpa only [add_zsmul, one_zsmul, comp_add, nat_trans.naturality, add_comp,
              add_left_inj]
          ·
            simpa only [sub_smul, one_zsmul, comp_sub, nat_trans.naturality, sub_comp,
              sub_left_inj] using ih }
#align category_theory.Sheaf_hom_has_zsmul CategoryTheory.sheafHomHasZsmul

instance : Sub (P ⟶ Q) where sub f g := Sheaf.Hom.mk <| f.1 - g.1

instance : Neg (P ⟶ Q) where neg f := Sheaf.Hom.mk <| -f.1

instance sheafHomHasNsmul : SMul ℕ (P ⟶ Q)
    where smul n f :=
    Sheaf.Hom.mk
      { app := fun U => n • f.1.app U
        naturality' := fun U V i => by
          induction' n with n ih
          · simp only [zero_smul, comp_zero, zero_comp]
          ·
            simp only [Nat.succ_eq_add_one, add_smul, ih, one_nsmul, comp_add, nat_trans.naturality,
              add_comp] }
#align category_theory.Sheaf_hom_has_nsmul CategoryTheory.sheafHomHasNsmul

instance : Zero (P ⟶ Q) where zero := Sheaf.Hom.mk 0

instance : Add (P ⟶ Q) where add f g := Sheaf.Hom.mk <| f.1 + g.1

@[simp]
theorem Sheaf.Hom.add_app (f g : P ⟶ Q) (U) : (f + g).1.app U = f.1.app U + g.1.app U :=
  rfl
#align category_theory.Sheaf.hom.add_app CategoryTheory.Sheaf.Hom.add_app

instance : AddCommGroup (P ⟶ Q) :=
  Function.Injective.addCommGroup (fun f : Sheaf.Hom P Q => f.1) (fun _ _ h => Sheaf.Hom.ext _ _ h)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => by
      dsimp at *
      ext
      simpa [*] )
    fun _ _ => by
    dsimp at *
    ext
    simpa [*]

instance : Preadditive (Sheaf J A)
    where
  homGroup P Q := inferInstance
  add_comp P Q R f f' g := by
    ext
    simp
  comp_add P Q R f g g' := by
    ext
    simp

end Preadditive

end CategoryTheory

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presheaf

-- Under here is the equalizer story, which is equivalent if A has products (and doesn't
-- make sense otherwise). It's described in https://stacks.math.columbia.edu/tag/00VL,
-- between 00VQ and 00VR.
variable {C : Type u₁} [Category.{v₁} C]

variable {A : Type u₂} [Category.{max v₁ u₁} A]

variable (J : GrothendieckTopology C)

variable {U : C} (R : Presieve U)

variable (P : Cᵒᵖ ⥤ A)

section MultiequalizerConditions

/-- When `P` is a sheaf and `S` is a cover, the associated multifork is a limit. -/
def isLimitOfIsSheaf {X : C} (S : J.cover X) (hP : IsSheaf J P) : IsLimit (S.Multifork P)
    where
  lift := fun E : Multifork _ => hP.amalgamate S (fun I => E.ι _) fun I => E.condition _
  fac := by
    rintro (E : multifork _) (a | b)
    · apply hP.amalgamate_map
    · rw [← E.w (walking_multicospan.hom.fst b), ←
        (S.multifork P).w (walking_multicospan.hom.fst b), ← assoc]
      congr 1
      apply hP.amalgamate_map
  uniq := by
    rintro (E : multifork _) m hm
    apply hP.hom_ext S
    intro I
    erw [hm (walking_multicospan.left I)]
    symm
    apply hP.amalgamate_map
#align category_theory.presheaf.is_limit_of_is_sheaf CategoryTheory.Presheaf.isLimitOfIsSheaf

theorem isSheaf_iff_multifork :
    IsSheaf J P ↔ ∀ (X : C) (S : J.cover X), Nonempty (IsLimit (S.Multifork P)) :=
  by
  refine' ⟨fun hP X S => ⟨is_limit_of_is_sheaf _ _ _ hP⟩, _⟩
  intro h E X S hS x hx
  let T : J.cover X := ⟨S, hS⟩
  obtain ⟨hh⟩ := h _ T
  let K : multifork (T.index P) := multifork.of_ι _ E (fun I => x I.f I.hf) fun I => hx _ _ _ _ I.w
  use hh.lift K
  dsimp; constructor
  · intro Y f hf
    apply hh.fac K (walking_multicospan.left ⟨Y, f, hf⟩)
  · intro e he
    apply hh.uniq K
    rintro (a | b)
    · apply he
    · rw [← K.w (walking_multicospan.hom.fst b), ←
        (T.multifork P).w (walking_multicospan.hom.fst b), ← assoc]
      congr 1
      apply he
#align category_theory.presheaf.is_sheaf_iff_multifork CategoryTheory.Presheaf.isSheaf_iff_multifork

theorem isSheaf_iff_multiequalizer [∀ (X : C) (S : J.cover X), HasMultiequalizer (S.index P)] :
    IsSheaf J P ↔ ∀ (X : C) (S : J.cover X), IsIso (S.toMultiequalizer P) :=
  by
  rw [is_sheaf_iff_multifork]
  refine' forall₂_congr fun X S => ⟨_, _⟩
  · rintro ⟨h⟩
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.cone_point_unique_up_to_iso (limit.is_limit _)
    exact (inferInstance : is_iso e.hom)
  · intro h
    refine' ⟨is_limit.of_iso_limit (limit.is_limit _) (cones.ext _ _)⟩
    · apply (@as_iso _ _ _ _ _ h).symm
    · intro a
      symm
      erw [is_iso.inv_comp_eq]
      change _ = limit.lift _ _ ≫ _
      simp
#align category_theory.presheaf.is_sheaf_iff_multiequalizer CategoryTheory.Presheaf.isSheaf_iff_multiequalizer

end MultiequalizerConditions

section

variable [HasProducts.{max u₁ v₁} A]

/--
The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of <https://stacks.math.columbia.edu/tag/00VM>.
-/
def firstObj : A :=
  ∏ fun f : ΣV, { f : V ⟶ U // R f } => P.obj (op f.1)
#align category_theory.presheaf.first_obj CategoryTheory.Presheaf.firstObj

/--
The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork diagram
of <https://stacks.math.columbia.edu/tag/00VM>.
-/
def forkMap : P.obj (op U) ⟶ firstObj R P :=
  Pi.lift fun f => P.map f.2.1.op
#align category_theory.presheaf.fork_map CategoryTheory.Presheaf.forkMap

variable [HasPullbacks C]

/-- The rightmost object of the fork diagram of https://stacks.math.columbia.edu/tag/00VM, which
contains the data used to check a family of elements for a presieve is compatible.
-/
def secondObj : A :=
  ∏ fun fg : (ΣV, { f : V ⟶ U // R f }) × ΣW, { g : W ⟶ U // R g } =>
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))
#align category_theory.presheaf.second_obj CategoryTheory.Presheaf.secondObj

/-- The map `pr₀*` of <https://stacks.math.columbia.edu/tag/00VM>. -/
def firstMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun fg => Pi.π _ _ ≫ P.map pullback.fst.op
#align category_theory.presheaf.first_map CategoryTheory.Presheaf.firstMap

/-- The map `pr₁*` of <https://stacks.math.columbia.edu/tag/00VM>. -/
def secondMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun fg => Pi.π _ _ ≫ P.map pullback.snd.op
#align category_theory.presheaf.second_map CategoryTheory.Presheaf.secondMap

theorem w : forkMap R P ≫ firstMap R P = forkMap R P ≫ secondMap R P :=
  by
  apply limit.hom_ext
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩
  simp only [first_map, second_map, fork_map, limit.lift_π, limit.lift_π_assoc, assoc, fan.mk_π_app,
    Subtype.coe_mk, Subtype.val_eq_coe]
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp
#align category_theory.presheaf.w CategoryTheory.Presheaf.w

/-- An alternative definition of the sheaf condition in terms of equalizers. This is shown to be
equivalent in `category_theory.presheaf.is_sheaf_iff_is_sheaf'`.
-/
def IsSheaf' (P : Cᵒᵖ ⥤ A) : Prop :=
  ∀ (U : C) (R : Presieve U) (hR : generate R ∈ J U), Nonempty (IsLimit (Fork.ofι _ (w R P)))
#align category_theory.presheaf.is_sheaf' CategoryTheory.Presheaf.IsSheaf'

/-- (Implementation). An auxiliary lemma to convert between sheaf conditions. -/
def isSheafForIsSheafFor' (P : Cᵒᵖ ⥤ A) (s : A ⥤ Type max v₁ u₁)
    [∀ J, PreservesLimitsOfShape (Discrete.{max v₁ u₁} J) s] (U : C) (R : Presieve U) :
    IsLimit (s.mapCone (Fork.ofι _ (w R P))) ≃
      IsLimit (Fork.ofι _ (Equalizer.Presieve.w (P ⋙ s) R)) :=
  by
  apply Equiv.trans (is_limit_map_cone_fork_equiv _ _) _
  apply (is_limit.postcompose_hom_equiv _ _).symm.trans (is_limit.equiv_iso_limit _)
  · apply nat_iso.of_components _ _
    · rintro (_ | _)
      · apply preserves_product.iso s
      · apply preserves_product.iso s
    · rintro _ _ (_ | _)
      · ext : 1
        dsimp [equalizer.presieve.first_map, first_map]
        simp only [limit.lift_π, map_lift_pi_comparison, assoc, fan.mk_π_app, functor.map_comp]
        erw [pi_comparison_comp_π_assoc]
      · ext : 1
        dsimp [equalizer.presieve.second_map, second_map]
        simp only [limit.lift_π, map_lift_pi_comparison, assoc, fan.mk_π_app, functor.map_comp]
        erw [pi_comparison_comp_π_assoc]
      · dsimp
        simp
  · refine' fork.ext (iso.refl _) _
    dsimp [equalizer.fork_map, fork_map]
    simp [fork.ι]
#align category_theory.presheaf.is_sheaf_for_is_sheaf_for' CategoryTheory.Presheaf.isSheafForIsSheafFor'

/-- The equalizer definition of a sheaf given by `is_sheaf'` is equivalent to `is_sheaf`. -/
theorem isSheaf_iff_isSheaf' : IsSheaf J P ↔ IsSheaf' J P :=
  by
  constructor
  · intro h U R hR
    refine' ⟨_⟩
    apply coyoneda_jointly_reflects_limits
    intro X
    have q : presieve.is_sheaf_for (P ⋙ coyoneda.obj X) _ := h X.unop _ hR
    rw [← presieve.is_sheaf_for_iff_generate] at q
    rw [equalizer.presieve.sheaf_condition] at q
    replace q := Classical.choice q
    apply (is_sheaf_for_is_sheaf_for' _ _ _ _).symm q
  · intro h U X S hS
    rw [equalizer.presieve.sheaf_condition]
    refine' ⟨_⟩
    refine' is_sheaf_for_is_sheaf_for' _ _ _ _ _
    letI := preserves_smallest_limits_of_preserves_limits (coyoneda.obj (op U))
    apply is_limit_of_preserves
    apply Classical.choice (h _ S _)
    simpa
#align category_theory.presheaf.is_sheaf_iff_is_sheaf' CategoryTheory.Presheaf.isSheaf_iff_isSheaf'

end

section Concrete

variable [HasPullbacks C]

/--
For a concrete category `(A, s)` where the forgetful functor `s : A ⥤ Type v` preserves limits and
reflects isomorphisms, and `A` has limits, an `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is a sheaf iff its
underlying `Type`-valued presheaf `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf.

Note this lemma applies for "algebraic" categories, eg groups, abelian groups and rings, but not
for the category of topological spaces, topological rings, etc since reflecting isomorphisms doesn't
hold.
-/
theorem isSheaf_iff_isSheaf_forget (s : A ⥤ Type max v₁ u₁) [HasLimits A] [PreservesLimits s]
    [ReflectsIsomorphisms s] : IsSheaf J P ↔ IsSheaf J (P ⋙ s) :=
  by
  rw [is_sheaf_iff_is_sheaf', is_sheaf_iff_is_sheaf']
  apply forall_congr' fun U => _
  apply ball_congr fun R hR => _
  letI : reflects_limits s := reflects_limits_of_reflects_isomorphisms
  have : is_limit (s.map_cone (fork.of_ι _ (w R P))) ≃ is_limit (fork.of_ι _ (w R (P ⋙ s))) :=
    is_sheaf_for_is_sheaf_for' P s U R
  rw [← Equiv.nonempty_congr this]
  constructor
  · haveI := preserves_smallest_limits_of_preserves_limits s
    exact Nonempty.map fun t => is_limit_of_preserves s t
  · haveI := reflects_smallest_limits_of_reflects_limits s
    exact Nonempty.map fun t => is_limit_of_reflects s t
#align category_theory.presheaf.is_sheaf_iff_is_sheaf_forget CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget

end Concrete

end Presheaf

end CategoryTheory

