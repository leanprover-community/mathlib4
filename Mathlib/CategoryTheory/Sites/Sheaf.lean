/-
Copyright (c) 2020 Kevin Buzzard, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

#align_import category_theory.sites.sheaf from "leanprover-community/mathlib"@"2efd2423f8d25fa57cf7a179f5d8652ab4d0df44"

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
  are all sheaves of sets, see `CategoryTheory.Presheaf.IsSheaf`.
* When `A = Type`, this recovers the basic definition of sheaves of sets, see
  `CategoryTheory.isSheaf_iff_isSheaf_of_type`.
* A alternate definition in terms of limits, unconditionally equivalent to the original one:
  see `CategoryTheory.Presheaf.isSheaf_iff_isLimit`.
* An alternate definition when `C` is small, has pullbacks and `A` has products is given by an
  equalizer condition `CategoryTheory.Presheaf.IsSheaf'`. This is equivalent to the earlier
  definition, shown in `CategoryTheory.Presheaf.isSheaf_iff_isSheaf'`.
* When `A = Type`, this is *definitionally* equal to the equalizer condition for presieves in
  `CategoryTheory.Sites.SheafOfTypes`.
* When `A` has limits and there is a functor `s : A ⥤ Type` which is faithful, reflects isomorphisms
  and preserves limits, then `P : Cᵒᵖ ⥤ A` is a sheaf iff the underlying presheaf of types
  `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf (`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget`).
  Cf https://stacks.math.columbia.edu/tag/0073, which is a weaker version of this statement (it's
  only over spaces, not sites) and https://stacks.math.columbia.edu/tag/00YR (a), which
  additionally assumes filtered colimits.

## Implementation notes

Occasionally we need to take a limit in `A` of a collection of morphisms of `C` indexed
by a collection of objects in `C`. This turns out to force the morphisms of `A` to be
in a sufficiently large universe. Rather than use `UnivLE` we prove some results for
a category `A'` instead, whose morphism universe of `A'` is defined to be `max u₁ v₁`, where
`u₁, v₁` are the universes for `C`. Perhaps after we get better at handling universe
inequalities this can be changed.

-/


universe w v₁ v₂ v₃ u₁ u₂ u₃

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
      { x : FamilyOfElements (P ⋙ coyoneda.obj E) (S : Presieve X) // x.SieveCompatible } where
  toFun π :=
    ⟨fun Y f h => π.app (op ⟨Over.mk f, h⟩), fun X Y f g hf => by
      apply (id_comp _).symm.trans
      dsimp
      exact π.naturality (Quiver.Hom.op (Over.homMk _ (by rfl)))⟩
  invFun x :=
    { app := fun f => x.1 f.unop.1.hom f.unop.2
      naturality := fun f f' g => by
        refine Eq.trans ?_ (x.2 f.unop.1.hom g.unop.left f.unop.2)
        dsimp
        rw [id_comp]
        convert rfl
        rw [Over.w] }
  left_inv π := rfl
  right_inv x := rfl
#align category_theory.presheaf.cones_equiv_sieve_compatible_family CategoryTheory.Presheaf.conesEquivSieveCompatibleFamily

-- These lemmas have always been bad (#7657), but leanprover/lean4#2644 made `simp` start noticing
attribute [nolint simpNF] CategoryTheory.Presheaf.conesEquivSieveCompatibleFamily_apply_coe
  CategoryTheory.Presheaf.conesEquivSieveCompatibleFamily_symm_apply_app

variable {P S E} {x : FamilyOfElements (P ⋙ coyoneda.obj E) S.arrows} (hx : SieveCompatible x)

/-- The cone corresponding to a sieve_compatible family of elements, dot notation enabled. -/
@[simp]
def _root_.CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone :
    Cone (S.arrows.diagram.op ⋙ P) where
  pt := E.unop
  π := (conesEquivSieveCompatibleFamily P S E).invFun ⟨x, hx⟩
#align category_theory.presieve.family_of_elements.sieve_compatible.cone CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone

/-- Cone morphisms from the cone corresponding to a sieve_compatible family to the natural
    cone associated to a sieve `S` and a presheaf `P` are in 1-1 correspondence with amalgamations
    of the family. -/
def homEquivAmalgamation :
    (hx.cone ⟶ P.mapCone S.arrows.cocone.op) ≃ { t // x.IsAmalgamation t } where
  toFun l := ⟨l.hom, fun _ f hf => l.w (op ⟨Over.mk f, hf⟩)⟩
  invFun t := ⟨t.1, fun f => t.2 f.unop.1.hom f.unop.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
#align category_theory.presheaf.hom_equiv_amalgamation CategoryTheory.Presheaf.homEquivAmalgamation

variable (P S)

/-- Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone is a limit cone
    iff `Hom (E, P -)` is a sheaf of types for the sieve `S` and all `E : A`. -/
theorem isLimit_iff_isSheafFor :
    Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) S.arrows := by
  dsimp [IsSheafFor]; simp_rw [compatible_iff_sieveCompatible]
  rw [((Cone.isLimitEquivIsTerminal _).trans (isTerminalEquivUnique _ _)).nonempty_congr]
  rw [Classical.nonempty_pi]; constructor
  · intro hu E x hx
    specialize hu hx.cone
    erw [(homEquivAmalgamation hx).uniqueCongr.nonempty_congr] at hu
    exact (unique_subtype_iff_exists_unique _).1 hu
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    rw [← eqv.left_inv π]
    erw [(homEquivAmalgamation (eqv π).2).uniqueCongr.nonempty_congr]
    rw [unique_subtype_iff_exists_unique]
    exact h _ _ (eqv π).2
#align category_theory.presheaf.is_limit_iff_is_sheaf_for CategoryTheory.Presheaf.isLimit_iff_isSheafFor

/-- Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone admits at most one
    morphism from every cone in the same category (i.e. over the same diagram),
    iff `Hom (E, P -)`is separated for the sieve `S` and all `E : A`. -/
theorem subsingleton_iff_isSeparatedFor :
    (∀ c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSeparatedFor (P ⋙ coyoneda.obj E) S.arrows := by
  constructor
  · intro hs E x t₁ t₂ h₁ h₂
    have hx := is_compatible_of_exists_amalgamation x ⟨t₁, h₁⟩
    rw [compatible_iff_sieveCompatible] at hx
    specialize hs hx.cone
    rcases hs with ⟨hs⟩
    simpa only [Subtype.mk.injEq] using (show Subtype.mk t₁ h₁ = ⟨t₂, h₂⟩ from
      (homEquivAmalgamation hx).symm.injective (hs _ _))
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    constructor
    rw [← eqv.left_inv π]
    intro f₁ f₂
    let eqv' := homEquivAmalgamation (eqv π).2
    apply eqv'.injective
    ext
    apply h _ (eqv π).1 <;> exact (eqv' _).2
#align category_theory.presheaf.subsingleton_iff_is_separated_for CategoryTheory.Presheaf.subsingleton_iff_isSeparatedFor

/-- A presheaf `P` is a sheaf for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` is a limit cone. -/
theorem isSheaf_iff_isLimit :
    IsSheaf J P ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) :=
  ⟨fun h _ S hS => (isLimit_iff_isSheafFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (isLimit_iff_isSheafFor P S).1 (h S hS) (op E)⟩
#align category_theory.presheaf.is_sheaf_iff_is_limit CategoryTheory.Presheaf.isSheaf_iff_isLimit

/-- A presheaf `P` is separated for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` admits at most one morphism from every
    cone in the same category. -/
theorem isSeparated_iff_subsingleton :
    (∀ E : A, IsSeparated J (P ⋙ coyoneda.obj (op E))) ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → ∀ c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op) :=
  ⟨fun h _ S hS => (subsingleton_iff_isSeparatedFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (subsingleton_iff_isSeparatedFor P S).1 (h S hS) (op E)⟩
#align category_theory.presheaf.is_separated_iff_subsingleton CategoryTheory.Presheaf.isSeparated_iff_subsingleton

/-- Given presieve `R` and presheaf `P : Cᵒᵖ ⥤ A`, the natural cone associated to `P` and
    the sieve `Sieve.generate R` generated by `R` is a limit cone iff `Hom (E, P -)` is a
    sheaf of types for the presieve `R` and all `E : A`. -/
theorem isLimit_iff_isSheafFor_presieve :
    Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) R :=
  (isLimit_iff_isSheafFor P _).trans (forall_congr' fun _ => (isSheafFor_iff_generate _).symm)
#align category_theory.presheaf.is_limit_iff_is_sheaf_for_presieve CategoryTheory.Presheaf.isLimit_iff_isSheafFor_presieve

/-- A presheaf `P` is a sheaf for the Grothendieck topology generated by a pretopology `K`
    iff for every covering presieve `R` of `K`, the natural cone associated to `P` and
    `Sieve.generate R` is a limit cone. -/
theorem isSheaf_iff_isLimit_pretopology [HasPullbacks C] (K : Pretopology C) :
    IsSheaf (K.toGrothendieck C) P ↔
      ∀ ⦃X : C⦄ (R : Presieve X),
        R ∈ K X → Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) := by
  dsimp [IsSheaf]
  simp_rw [isSheaf_pretopology]
  exact
    ⟨fun h X R hR => (isLimit_iff_isSheafFor_presieve P R).2 fun E => h E.unop R hR,
      fun h E X R hR => (isLimit_iff_isSheafFor_presieve P R).1 (h R hR) (op E)⟩
#align category_theory.presheaf.is_sheaf_iff_is_limit_pretopology CategoryTheory.Presheaf.isSheaf_iff_isLimit_pretopology

end LimitSheafCondition

variable {J}

/-- This is a wrapper around `Presieve.IsSheafFor.amalgamate` to be used below.
  If `P`s a sheaf, `S` is a cover of `X`, and `x` is a collection of morphisms from `E`
  to `P` evaluated at terms in the cover which are compatible, then we can amalgamate
  the `x`s to obtain a single morphism `E ⟶ P.obj (op X)`. -/
def IsSheaf.amalgamate {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ I : S.Relation, x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op) : E ⟶ P.obj (op X) :=
  (hP _ _ S.condition).amalgamate (fun Y f hf => x ⟨Y, f, hf⟩) fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w =>
    hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩
#align category_theory.presheaf.is_sheaf.amalgamate CategoryTheory.Presheaf.IsSheaf.amalgamate

@[reassoc (attr := simp)]
theorem IsSheaf.amalgamate_map {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ I : S.Relation, x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op) (I : S.Arrow) :
    hP.amalgamate S x hx ≫ P.map I.f.op = x _ := by
  rcases I with ⟨Y, f, hf⟩
  apply
    @Presieve.IsSheafFor.valid_glue _ _ _ _ _ _ (hP _ _ S.condition) (fun Y f hf => x ⟨Y, f, hf⟩)
      (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w => hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩) f hf
#align category_theory.presheaf.is_sheaf.amalgamate_map CategoryTheory.Presheaf.IsSheaf.amalgamate_map

theorem IsSheaf.hom_ext {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (e₁ e₂ : E ⟶ P.obj (op X))
    (h : ∀ I : S.Arrow, e₁ ≫ P.map I.f.op = e₂ ≫ P.map I.f.op) : e₁ = e₂ :=
  (hP _ _ S.condition).isSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩
#align category_theory.presheaf.is_sheaf.hom_ext CategoryTheory.Presheaf.IsSheaf.hom_ext

lemma IsSheaf.hom_ext_ofArrows
    {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {I : Type*} {S : C} {X : I → C}
    (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows _ f ∈ J S) {E : A}
    {x y : E ⟶ P.obj (op S)} (h : ∀ i, x ≫ P.map (f i).op = y ≫ P.map (f i).op) :
    x = y := by
  apply hP.hom_ext ⟨_, hf⟩
  rintro ⟨Z, _, _, g, _, ⟨i⟩, rfl⟩
  dsimp
  rw [P.map_comp, reassoc_of% (h i)]

section

variable {P : Cᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf J P) {I : Type*} {S : C} {X : I → C}
  (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows _ f ∈ J S) {E : A}
  (x : ∀ i, E ⟶ P.obj (op (X i)))
  (hx : ∀ ⦃W : C⦄ ⦃i j : I⦄ (a : W ⟶ X i) (b : W ⟶ X j),
    a ≫ f i = b ≫ f j → x i ≫ P.map a.op = x j ≫ P.map b.op)

lemma IsSheaf.exists_unique_amalgamation_ofArrows :
    ∃! (g : E ⟶ P.obj (op S)), ∀ (i : I), g ≫ P.map (f i).op = x i :=
  (Presieve.isSheafFor_arrows_iff _ _).1
    ((Presieve.isSheafFor_iff_generate _).2 (hP E _ hf)) x (fun _ _ _ _ _ w => hx _ _ w)

/-- If `P : Cᵒᵖ ⥤ A` is a sheaf and `f i : X i ⟶ S` is a covering family, then
a morphism `E ⟶ P.obj (op S)` can be constructed from a compatible family of
morphisms `x : E ⟶ P.obj (op (X i))`. -/
def IsSheaf.amalgamateOfArrows : E ⟶ P.obj (op S) :=
  (hP.exists_unique_amalgamation_ofArrows f hf x hx).choose

@[reassoc (attr := simp)]
lemma IsSheaf.amalgamateOfArrows_map (i : I) :
    hP.amalgamateOfArrows f hf x hx ≫ P.map (f i).op = x i :=
  (hP.exists_unique_amalgamation_ofArrows f hf x hx).choose_spec.1 i

end

theorem isSheaf_of_iso_iff {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P' :=
  forall_congr' fun _ =>
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
  /-- the underlying presheaf -/
  val : Cᵒᵖ ⥤ A
  /-- the condition that the presheaf is a sheaf -/
  cond : Presheaf.IsSheaf J val
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf CategoryTheory.Sheaf

namespace Sheaf

variable {J A}

/-- Morphisms between sheaves are just morphisms of presheaves. -/
@[ext]
structure Hom (X Y : Sheaf J A) where
  /-- a morphism between the underlying presheaves -/
  val : X.val ⟶ Y.val
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.hom CategoryTheory.Sheaf.Hom

@[simps id_val comp_val]
instance instCategorySheaf : Category (Sheaf J A) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩
  id_comp _ := Hom.ext _ _ <| id_comp _
  comp_id _ := Hom.ext _ _ <| comp_id _
  assoc _ _ _ := Hom.ext _ _ <| assoc _ _ _

-- Let's make the inhabited linter happy.../sips
instance (X : Sheaf J A) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩

-- Porting note: added because `Sheaf.Hom.ext` was not triggered automatically
@[ext]
lemma hom_ext {X Y : Sheaf J A} (x y : X ⟶ Y) (h : x.val = y.val) : x = y :=
  Sheaf.Hom.ext _ _ h

/-- The bijection `(X ⟶ Y) ≃ (X.val ⟶ Y.val)` when `X` and `Y` are sheaves. -/
@[simps]
def homEquiv {X Y : Sheaf J A} : (X ⟶ Y) ≃ (X.val ⟶ Y.val) where
  toFun f := f.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Sheaf

/-- The inclusion functor from sheaves to presheaves. -/
@[simps]
def sheafToPresheaf : Sheaf J A ⥤ Cᵒᵖ ⥤ A where
  obj := Sheaf.val
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_to_presheaf CategoryTheory.sheafToPresheaf

/-- The sections of a sheaf (i.e. evaluation as a presheaf on `C`). -/
abbrev sheafSections : Cᵒᵖ ⥤ Sheaf J A ⥤ A := (sheafToPresheaf J A).flip

instance : (sheafToPresheaf J A).Full where map_surjective f := ⟨⟨f⟩, rfl⟩

instance : (sheafToPresheaf J A).Faithful where

/-- This is stated as a lemma to prevent class search from forming a loop since a sheaf morphism is
monic if and only if it is monic as a presheaf morphism (under suitable assumption). -/
theorem Sheaf.Hom.mono_of_presheaf_mono {F G : Sheaf J A} (f : F ⟶ G) [h : Mono f.1] : Mono f :=
  (sheafToPresheaf J A).mono_of_mono_map h
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.hom.mono_of_presheaf_mono CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono

instance Sheaf.Hom.epi_of_presheaf_epi {F G : Sheaf J A} (f : F ⟶ G) [h : Epi f.1] : Epi f :=
  (sheafToPresheaf J A).epi_of_epi_map h
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.hom.epi_of_presheaf_epi CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi

/-- The sheaf of sections guaranteed by the sheaf condition. -/
@[simps]
def sheafOver {A : Type u₂} [Category.{v₂} A] {J : GrothendieckTopology C} (ℱ : Sheaf J A) (E : A) :
    SheafOfTypes J :=
  ⟨ℱ.val ⋙ coyoneda.obj (op E), ℱ.cond E⟩
#align category_theory.sheaf_over CategoryTheory.sheafOver

theorem isSheaf_iff_isSheaf_of_type (P : Cᵒᵖ ⥤ Type w) :
    Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P := by
  constructor
  · intro hP
    refine' Presieve.isSheaf_iso J _ (hP PUnit)
    exact isoWhiskerLeft _ Coyoneda.punitIso ≪≫ P.rightUnitor
  · intro hP X Y S hS z hz
    refine' ⟨fun x => (hP S hS).amalgamate (fun Z f hf => z f hf x) _, _, _⟩
    · intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      exact congr_fun (hz g₁ g₂ hf₁ hf₂ h) x
    · intro Z f hf
      funext x
      apply Presieve.IsSheafFor.valid_glue
    · intro y hy
      funext x
      apply (hP S hS).isSeparatedFor.ext
      intro Y' f hf
      rw [Presieve.IsSheafFor.valid_glue _ _ _ hf, ← hy _ hf]
      rfl
#align category_theory.is_sheaf_iff_is_sheaf_of_type CategoryTheory.isSheaf_iff_isSheaf_of_type

/-- The category of sheaves taking values in Type is the same as the category of set-valued sheaves.
-/
@[simps]
def sheafEquivSheafOfTypes : Sheaf J (Type w) ≌ SheafOfTypes J where
  functor :=
    { obj := fun S => ⟨S.val, (isSheaf_iff_isSheaf_of_type _ _).1 S.2⟩
      map := fun f => ⟨f.val⟩ }
  inverse :=
    { obj := fun S => ⟨S.val, (isSheaf_iff_isSheaf_of_type _ _).2 S.2⟩
      map := fun f => ⟨f.val⟩ }
  unitIso := NatIso.ofComponents fun X => Iso.refl _
  counitIso := NatIso.ofComponents fun X => Iso.refl _
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_equiv_SheafOfTypes CategoryTheory.sheafEquivSheafOfTypes

instance : Inhabited (Sheaf (⊥ : GrothendieckTopology C) (Type w)) :=
  ⟨(sheafEquivSheafOfTypes _).inverse.obj default⟩

variable {J} {A}

/-- If the empty sieve is a cover of `X`, then `F(X)` is terminal. -/
def Sheaf.isTerminalOfBotCover (F : Sheaf J A) (X : C) (H : ⊥ ∈ J X) :
    IsTerminal (F.1.obj (op X)) := by
  refine @IsTerminal.ofUnique _ _ _ ?_
  intro Y
  choose t h using F.2 Y _ H (by tauto) (by tauto)
  exact ⟨⟨t⟩, fun a => h.2 a (by tauto)⟩
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.is_terminal_of_bot_cover CategoryTheory.Sheaf.isTerminalOfBotCover

section Preadditive

open Preadditive

variable [Preadditive A] {P Q : Sheaf J A}

instance sheafHomHasZSMul : SMul ℤ (P ⟶ Q) where
  smul n f :=
    Sheaf.Hom.mk
      { app := fun U => n • f.1.app U
        naturality := fun U V i => by
          induction' n using Int.induction_on with n ih n ih
          · simp only [zero_smul, comp_zero, zero_comp]
          · simpa only [add_zsmul, one_zsmul, comp_add, NatTrans.naturality, add_comp,
              add_left_inj]
          · simpa only [sub_smul, one_zsmul, comp_sub, NatTrans.naturality, sub_comp,
              sub_left_inj] using ih }
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_hom_has_zsmul CategoryTheory.sheafHomHasZSMul

instance : Sub (P ⟶ Q) where sub f g := Sheaf.Hom.mk <| f.1 - g.1

instance : Neg (P ⟶ Q) where neg f := Sheaf.Hom.mk <| -f.1

instance sheafHomHasNSMul : SMul ℕ (P ⟶ Q) where
  smul n f :=
    Sheaf.Hom.mk
      { app := fun U => n • f.1.app U
        naturality := fun U V i => by
          induction' n with n ih
          · simp only [zero_smul, comp_zero, zero_comp, Nat.zero_eq]
          · simp only [Nat.succ_eq_add_one, add_smul, ih, one_nsmul, comp_add,
              NatTrans.naturality, add_comp] }
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf_hom_has_nsmul CategoryTheory.sheafHomHasNSMul

instance : Zero (P ⟶ Q) where zero := Sheaf.Hom.mk 0

instance : Add (P ⟶ Q) where add f g := Sheaf.Hom.mk <| f.1 + g.1

@[simp]
theorem Sheaf.Hom.add_app (f g : P ⟶ Q) (U) : (f + g).1.app U = f.1.app U + g.1.app U :=
  rfl
set_option linter.uppercaseLean3 false in
#align category_theory.Sheaf.hom.add_app CategoryTheory.Sheaf.Hom.add_app

instance Sheaf.Hom.addCommGroup : AddCommGroup (P ⟶ Q) :=
  Function.Injective.addCommGroup (fun f : Sheaf.Hom P Q => f.1)
    (fun _ _ h => Sheaf.Hom.ext _ _ h) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => by aesop_cat) (fun _ _ => by aesop_cat)

instance : Preadditive (Sheaf J A) where
  homGroup P Q := Sheaf.Hom.addCommGroup

end Preadditive

end CategoryTheory

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presheaf

-- Under here is the equalizer story, which is equivalent if A has products (and doesn't
-- make sense otherwise). It's described in https://stacks.math.columbia.edu/tag/00VL,
-- between 00VQ and 00VR.
variable {C : Type u₁} [Category.{v₁} C]

-- `A` is a general category; `A'` is a variant where the morphisms live in a large enough
-- universe to guarantee that we can take limits in A of things coming from C.
-- I would have liked to use something like `UnivLE.{max v₁ u₁, v₂}` as a hypothesis on
-- `A`'s morphism universe rather than introducing `A'` but I can't get it to work.
-- So, for now, results which need max v₁ u₁ ≤ v₂ are just stated for `A'` and `P' : Cᵒᵖ ⥤ A'`
-- instead.
variable {A : Type u₂} [Category.{v₂} A]
variable {A' : Type u₂} [Category.{max v₁ u₁} A']
variable {B : Type u₃} [Category.{v₃} B]
variable (J : GrothendieckTopology C)
variable {U : C} (R : Presieve U)
variable (P : Cᵒᵖ ⥤ A) (P' : Cᵒᵖ ⥤ A')

section MultiequalizerConditions

/-- When `P` is a sheaf and `S` is a cover, the associated multifork is a limit. -/
def isLimitOfIsSheaf {X : C} (S : J.Cover X) (hP : IsSheaf J P) : IsLimit (S.multifork P) where
  lift := fun E : Multifork _ => hP.amalgamate S (fun I => E.ι _) fun I => E.condition _
  fac := by
    rintro (E : Multifork _) (a | b)
    · apply hP.amalgamate_map
    · rw [← E.w (WalkingMulticospan.Hom.fst b),
        ← (S.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply hP.amalgamate_map
  uniq := by
    rintro (E : Multifork _) m hm
    apply hP.hom_ext S
    intro I
    erw [hm (WalkingMulticospan.left I)]
    symm
    apply hP.amalgamate_map
#align category_theory.presheaf.is_limit_of_is_sheaf CategoryTheory.Presheaf.isLimitOfIsSheaf

theorem isSheaf_iff_multifork :
    IsSheaf J P ↔ ∀ (X : C) (S : J.Cover X), Nonempty (IsLimit (S.multifork P)) := by
  refine' ⟨fun hP X S => ⟨isLimitOfIsSheaf _ _ _ hP⟩, _⟩
  intro h E X S hS x hx
  let T : J.Cover X := ⟨S, hS⟩
  obtain ⟨hh⟩ := h _ T
  let K : Multifork (T.index P) := Multifork.ofι _ E (fun I => x I.f I.hf) fun I => hx _ _ _ _ I.w
  use hh.lift K
  dsimp; constructor
  · intro Y f hf
    apply hh.fac K (WalkingMulticospan.left ⟨Y, f, hf⟩)
  · intro e he
    apply hh.uniq K
    rintro (a | b)
    · apply he
    · rw [← K.w (WalkingMulticospan.Hom.fst b), ←
        (T.multifork P).w (WalkingMulticospan.Hom.fst b), ← assoc]
      congr 1
      apply he
#align category_theory.presheaf.is_sheaf_iff_multifork CategoryTheory.Presheaf.isSheaf_iff_multifork

theorem isSheaf_iff_multiequalizer [∀ (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)] :
    IsSheaf J P ↔ ∀ (X : C) (S : J.Cover X), IsIso (S.toMultiequalizer P) := by
  rw [isSheaf_iff_multifork]
  refine' forall₂_congr fun X S => ⟨_, _⟩
  · rintro ⟨h⟩
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.conePointUniqueUpToIso (limit.isLimit _)
    exact (inferInstance : IsIso e.hom)
  · intro h
    refine' ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext _ _)⟩
    · apply (@asIso _ _ _ _ _ h).symm
    · intro a
      symm
      erw [IsIso.inv_comp_eq]
      dsimp
      simp
#align category_theory.presheaf.is_sheaf_iff_multiequalizer CategoryTheory.Presheaf.isSheaf_iff_multiequalizer

end MultiequalizerConditions

section

variable [HasProducts.{max u₁ v₁} A]
variable [HasProducts.{max u₁ v₁} A']

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
  Pi.lift fun _ => Pi.π _ _ ≫ P.map pullback.fst.op
#align category_theory.presheaf.first_map CategoryTheory.Presheaf.firstMap

/-- The map `pr₁*` of <https://stacks.math.columbia.edu/tag/00VM>. -/
def secondMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map pullback.snd.op
#align category_theory.presheaf.second_map CategoryTheory.Presheaf.secondMap

theorem w : forkMap R P ≫ firstMap R P = forkMap R P ≫ secondMap R P := by
  apply limit.hom_ext
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩
  simp only [firstMap, secondMap, forkMap, limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app,
    Subtype.coe_mk]
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp
#align category_theory.presheaf.w CategoryTheory.Presheaf.w

/-- An alternative definition of the sheaf condition in terms of equalizers. This is shown to be
equivalent in `CategoryTheory.Presheaf.isSheaf_iff_isSheaf'`.
-/
def IsSheaf' (P : Cᵒᵖ ⥤ A) : Prop :=
  ∀ (U : C) (R : Presieve U) (_ : generate R ∈ J U), Nonempty (IsLimit (Fork.ofι _ (w R P)))
#align category_theory.presheaf.is_sheaf' CategoryTheory.Presheaf.IsSheaf'

-- Again I wonder whether `UnivLE` can somehow be used to allow `s` to take
-- values in a more general universe.
/-- (Implementation). An auxiliary lemma to convert between sheaf conditions. -/
def isSheafForIsSheafFor' (P : Cᵒᵖ ⥤ A) (s : A ⥤ Type max v₁ u₁)
    [∀ J, PreservesLimitsOfShape (Discrete.{max v₁ u₁} J) s] (U : C) (R : Presieve U) :
    IsLimit (s.mapCone (Fork.ofι _ (w R P))) ≃
      IsLimit (Fork.ofι _ (Equalizer.Presieve.w (P ⋙ s) R)) := by
  apply Equiv.trans (isLimitMapConeForkEquiv _ _) _
  apply (IsLimit.postcomposeHomEquiv _ _).symm.trans (IsLimit.equivIsoLimit _)
  · apply NatIso.ofComponents _ _
    · rintro (_ | _)
      · apply PreservesProduct.iso s
      · apply PreservesProduct.iso s
    · rintro _ _ (_ | _)
      · refine' limit.hom_ext (fun j => _)
        dsimp [Equalizer.Presieve.firstMap, firstMap]
        simp only [limit.lift_π, map_lift_piComparison, assoc, Fan.mk_π_app, Functor.map_comp]
        rw [piComparison_comp_π_assoc]
      · refine' limit.hom_ext (fun j => _)
        dsimp [Equalizer.Presieve.secondMap, secondMap]
        simp only [limit.lift_π, map_lift_piComparison, assoc, Fan.mk_π_app, Functor.map_comp]
        rw [piComparison_comp_π_assoc]
      · dsimp
        simp
  · refine' Fork.ext (Iso.refl _) _
    dsimp [Equalizer.forkMap, forkMap]
    simp [Fork.ι]
#align category_theory.presheaf.is_sheaf_for_is_sheaf_for' CategoryTheory.Presheaf.isSheafForIsSheafFor'

-- Remark : this lemma uses `A'` not `A`; `A'` is `A` but with a universe
-- restriction. Can it be generalised?
/-- The equalizer definition of a sheaf given by `isSheaf'` is equivalent to `isSheaf`. -/
theorem isSheaf_iff_isSheaf' : IsSheaf J P' ↔ IsSheaf' J P' := by
  constructor
  · intro h U R hR
    refine ⟨?_⟩
    apply coyonedaJointlyReflectsLimits
    intro X
    have q : Presieve.IsSheafFor (P' ⋙ coyoneda.obj X) _ := h X.unop _ hR
    rw [← Presieve.isSheafFor_iff_generate] at q
    rw [Equalizer.Presieve.sheaf_condition] at q
    replace q := Classical.choice q
    apply (isSheafForIsSheafFor' _ _ _ _).symm q
  · intro h U X S hS
    rw [Equalizer.Presieve.sheaf_condition]
    refine ⟨?_⟩
    refine' isSheafForIsSheafFor' _ _ _ _ _
    letI := preservesSmallestLimitsOfPreservesLimits (coyoneda.obj (op U))
    apply isLimitOfPreserves
    apply Classical.choice (h _ S.arrows _)
    simpa
#align category_theory.presheaf.is_sheaf_iff_is_sheaf' CategoryTheory.Presheaf.isSheaf_iff_isSheaf'

end

section Concrete

theorem isSheaf_of_isSheaf_comp (s : A ⥤ B) [ReflectsLimitsOfSize.{v₁, max v₁ u₁} s]
    (h : IsSheaf J (P ⋙ s)) : IsSheaf J P := by
  rw [isSheaf_iff_isLimit] at h ⊢
  exact fun X S hS ↦ (h S hS).map fun t ↦ isLimitOfReflects s t

theorem isSheaf_comp_of_isSheaf (s : A ⥤ B) [PreservesLimitsOfSize.{v₁, max v₁ u₁} s]
    (h : IsSheaf J P) : IsSheaf J (P ⋙ s) := by
  rw [isSheaf_iff_isLimit] at h ⊢
  apply fun X S hS ↦ (h S hS).map fun t ↦ isLimitOfPreserves s t

theorem isSheaf_iff_isSheaf_comp (s : A ⥤ B) [HasLimitsOfSize.{v₁, max v₁ u₁} A]
    [PreservesLimitsOfSize.{v₁, max v₁ u₁} s] [s.ReflectsIsomorphisms] :
    IsSheaf J P ↔ IsSheaf J (P ⋙ s) := by
  letI : ReflectsLimitsOfSize s := reflectsLimitsOfReflectsIsomorphisms
  exact ⟨isSheaf_comp_of_isSheaf J P s, isSheaf_of_isSheaf_comp J P s⟩

/--
For a concrete category `(A, s)` where the forgetful functor `s : A ⥤ Type v` preserves limits and
reflects isomorphisms, and `A` has limits, an `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is a sheaf iff its
underlying `Type`-valued presheaf `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf.

Note this lemma applies for "algebraic" categories, eg groups, abelian groups and rings, but not
for the category of topological spaces, topological rings, etc since reflecting isomorphisms doesn't
hold.
-/
theorem isSheaf_iff_isSheaf_forget (s : A' ⥤ Type max v₁ u₁) [HasLimits A'] [PreservesLimits s]
    [s.ReflectsIsomorphisms] : IsSheaf J P' ↔ IsSheaf J (P' ⋙ s) := by
  have : HasLimitsOfSize.{v₁, max v₁ u₁} A' := hasLimitsOfSizeShrink.{_, _, u₁, 0} A'
  have : PreservesLimitsOfSize.{v₁, max v₁ u₁} s := preservesLimitsOfSizeShrink.{_, 0, _, u₁} s
  apply isSheaf_iff_isSheaf_comp
#align category_theory.presheaf.is_sheaf_iff_is_sheaf_forget CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget

end Concrete

end Presheaf

end CategoryTheory
