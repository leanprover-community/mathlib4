/-
Copyright (c) 2020 Kevin Buzzard, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

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
* An alternate definition in terms of limits, unconditionally equivalent to the original one:
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

@[expose] public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₂} [Category.{v₂} A]
variable (J : GrothendieckTopology C)

-- We follow https://stacks.math.columbia.edu/tag/00VL definition 00VR
/-- A sheaf of A is a presheaf `P : Cᵒᵖ ⥤ A` such that for every `E : A`, the
presheaf of types given by sending `U : C` to `Hom_{A}(E, P U)` is a sheaf of types. -/
@[stacks 00VR]
def IsSheaf (P : Cᵒᵖ ⥤ A) : Prop :=
  ∀ E : A, Presieve.IsSheaf J (P ⋙ coyoneda.obj (op E))

/-- Condition that a presheaf with values in a concrete category is separated for
a Grothendieck topology. -/
def IsSeparated (P : Cᵒᵖ ⥤ A) {FA : A → A → Type*} {CA : A → Type*}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] : Prop :=
  ∀ (X : C) (S : Sieve X) (_ : S ∈ J X) (x y : ToType (P.obj (op X))),
    (∀ (Y : C) (f : Y ⟶ X) (_ : S f), P.map f.op x = P.map f.op y) → x = y

section LimitSheafCondition

open Presieve Presieve.FamilyOfElements Limits

variable (P : Cᵒᵖ ⥤ A) {X : C} (S : Sieve X) (R : Presieve X) (E : Aᵒᵖ)

set_option backward.isDefEq.respectTransparency false in
/-- Given a sieve `S` on `X : C`, a presheaf `P : Cᵒᵖ ⥤ A`, and an object `E` of `A`,
    the cones over the natural diagram `S.arrows.diagram.op ⋙ P` associated to `S` and `P`
    with cone point `E` are in 1-1 correspondence with `SieveCompatible` family of elements
    for the sieve `S` and the presheaf of types `Hom (E, P -)`. -/
def conesEquivSieveCompatibleFamily :
    (S.arrows.diagram.op ⋙ P).cones.obj E ≃
      { x : FamilyOfElements (P ⋙ coyoneda.obj E) (S : Presieve X) // x.SieveCompatible } where
  toFun π :=
    ⟨fun _ f h => π.app (op ⟨Over.mk f, h⟩), fun X Y f g hf => by
      let φ : S.arrows.categoryMk (g ≫ f) (S.downward_closed hf g) ⟶
        S.arrows.categoryMk f hf := ObjectProperty.homMk (Over.homMk _ (by rfl))
      simpa using π.naturality φ.op⟩
  invFun x :=
    { app := fun f => x.1 f.unop.1.hom f.unop.2
      naturality := fun f f' g => by
        have := x.2 f.unop.1.hom g.unop.hom.left f.unop.2
        dsimp at this ⊢
        rw [id_comp, ← this]
        convert rfl
        simp only [Over.w] }

variable {P S E}
variable {x : FamilyOfElements (P ⋙ coyoneda.obj E) S.arrows} (hx : SieveCompatible x)

/-- The cone corresponding to a `SieveCompatible` family of elements, dot notation enabled. -/
@[simp]
def _root_.CategoryTheory.Presieve.FamilyOfElements.SieveCompatible.cone :
    Cone (S.arrows.diagram.op ⋙ P) where
  pt := E.unop
  π := (conesEquivSieveCompatibleFamily P S E).invFun ⟨x, hx⟩

/-- Cone morphisms from the cone corresponding to a `SieveCompatible` family to the natural
    cone associated to a sieve `S` and a presheaf `P` are in 1-1 correspondence with amalgamations
    of the family. -/
def homEquivAmalgamation :
    (hx.cone ⟶ P.mapCone S.arrows.cocone.op) ≃ { t // x.IsAmalgamation t } where
  toFun l := ⟨l.hom, fun _ f hf => l.w (op ⟨Over.mk f, hf⟩)⟩
  invFun t := ⟨t.1, fun f => t.2 f.unop.1.hom f.unop.2⟩

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
    rw [(homEquivAmalgamation hx).uniqueCongr.nonempty_congr] at hu
    exact (unique_subtype_iff_existsUnique _).1 hu
  · rintro h ⟨E, π⟩
    let eqv := conesEquivSieveCompatibleFamily P S (op E)
    rw [← eqv.left_inv π]
    erw [(homEquivAmalgamation (eqv π).2).uniqueCongr.nonempty_congr]
    rw [unique_subtype_iff_existsUnique]
    exact h _ _ (eqv π).2

/-- Given sieve `S` and presheaf `P : Cᵒᵖ ⥤ A`, their natural associated cone admits at most one
    morphism from every cone in the same category (i.e. over the same diagram),
    iff `Hom (E, P -)` is separated for the sieve `S` and all `E : A`. -/
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

/-- A presheaf `P` is a sheaf for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` is a limit cone. -/
theorem isSheaf_iff_isLimit :
    IsSheaf J P ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → Nonempty (IsLimit (P.mapCone S.arrows.cocone.op)) :=
  ⟨fun h _ S hS => (isLimit_iff_isSheafFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (isLimit_iff_isSheafFor P S).1 (h S hS) (op E)⟩

/-- A presheaf `P` is separated for the Grothendieck topology `J` iff for every covering sieve
    `S` of `J`, the natural cone associated to `P` and `S` admits at most one morphism from every
    cone in the same category. -/
theorem isSeparated_iff_subsingleton :
    (∀ E : A, Presieve.IsSeparated J (P ⋙ coyoneda.obj (op E))) ↔
      ∀ ⦃X : C⦄ (S : Sieve X), S ∈ J X → ∀ c, Subsingleton (c ⟶ P.mapCone S.arrows.cocone.op) :=
  ⟨fun h _ S hS => (subsingleton_iff_isSeparatedFor P S).2 fun E => h E.unop S hS, fun h E _ S hS =>
    (subsingleton_iff_isSeparatedFor P S).1 (h S hS) (op E)⟩

/-- Given presieve `R` and presheaf `P : Cᵒᵖ ⥤ A`, the natural cone associated to `P` and
    the sieve `Sieve.generate R` generated by `R` is a limit cone iff `Hom (E, P -)` is a
    sheaf of types for the presieve `R` and all `E : A`. -/
theorem isLimit_iff_isSheafFor_presieve :
    Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) ↔
      ∀ E : Aᵒᵖ, IsSheafFor (P ⋙ coyoneda.obj E) R :=
  (isLimit_iff_isSheafFor P _).trans (forall_congr' fun _ => (isSheafFor_iff_generate _).symm)

/-- A presheaf `P` is a sheaf for the Grothendieck topology generated by a pretopology `K`
    iff for every covering presieve `R` of `K`, the natural cone associated to `P` and
    `Sieve.generate R` is a limit cone. -/
theorem isSheaf_iff_isLimit_pretopology [HasPullbacks C] (K : Pretopology C) :
    IsSheaf K.toGrothendieck P ↔
      ∀ ⦃X : C⦄ (R : Presieve X),
        R ∈ K X → Nonempty (IsLimit (P.mapCone (generate R).arrows.cocone.op)) := by
  dsimp [IsSheaf]
  simp_rw [isSheaf_pretopology]
  exact
    ⟨fun h X R hR => (isLimit_iff_isSheafFor_presieve P R).2 fun E => h E.unop R hR,
      fun h E X R hR => (isLimit_iff_isSheafFor_presieve P R).1 (h R hR) (op E)⟩

end LimitSheafCondition

variable {J}

/-- This is a wrapper around `Presieve.IsSheafFor.amalgamate` to be used below.
  If `P` is a sheaf, `S` is a cover of `X`, and `x` is a collection of morphisms from `E`
  to `P` evaluated at terms in the cover which are compatible, then we can amalgamate
  the `x`s to obtain a single morphism `E ⟶ P.obj (op X)`. -/
def IsSheaf.amalgamate {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
       x I₁ ≫ P.map r.g₁.op = x I₂ ≫ P.map r.g₂.op) : E ⟶ P.obj (op X) :=
  (hP _ _ S.condition).amalgamate (fun Y f hf => x ⟨Y, f, hf⟩) fun _ _ _ _ _ _ _ h₁ h₂ w =>
    @hx { hf := h₁, .. } { hf := h₂, .. } { w := w, .. }

@[reassoc (attr := simp)]
theorem IsSheaf.amalgamate_map {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
       x I₁ ≫ P.map r.g₁.op = x I₂ ≫ P.map r.g₂.op)
    (I : S.Arrow) :
    hP.amalgamate S x hx ≫ P.map I.f.op = x _ := by
  apply (hP _ _ S.condition).valid_glue

theorem IsSheaf.hom_ext {A : Type u₂} [Category.{v₂} A] {E : A} {X : C} {P : Cᵒᵖ ⥤ A}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (e₁ e₂ : E ⟶ P.obj (op X))
    (h : ∀ I : S.Arrow, e₁ ≫ P.map I.f.op = e₂ ≫ P.map I.f.op) : e₁ = e₂ :=
  (hP _ _ S.condition).isSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩

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
include hP hf hx

lemma IsSheaf.existsUnique_amalgamation_ofArrows :
    ∃! (g : E ⟶ P.obj (op S)), ∀ (i : I), g ≫ P.map (f i).op = x i :=
  (Presieve.isSheafFor_arrows_iff _ _).1
    ((Presieve.isSheafFor_iff_generate _).2 (hP E _ hf)) x (fun _ _ _ _ _ w => hx _ _ w)

/-- If `P : Cᵒᵖ ⥤ A` is a sheaf and `f i : X i ⟶ S` is a covering family, then
a morphism `E ⟶ P.obj (op S)` can be constructed from a compatible family of
morphisms `x : E ⟶ P.obj (op (X i))`. -/
def IsSheaf.amalgamateOfArrows : E ⟶ P.obj (op S) :=
  (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose

@[reassoc (attr := simp)]
lemma IsSheaf.amalgamateOfArrows_map (i : I) :
    hP.amalgamateOfArrows f hf x hx ≫ P.map (f i).op = x i :=
  (hP.existsUnique_amalgamation_ofArrows f hf x hx).choose_spec.1 i

end

theorem isSheaf_of_iso_iff {P P' : Cᵒᵖ ⥤ A} (e : P ≅ P') : IsSheaf J P ↔ IsSheaf J P' :=
  forall_congr' fun _ =>
    ⟨Presieve.isSheaf_iso J (Functor.isoWhiskerRight e _),
      Presieve.isSheaf_iso J (Functor.isoWhiskerRight e.symm _)⟩

variable (J)

theorem isSheaf_of_isTerminal {X : A} (hX : IsTerminal X) :
    Presheaf.IsSheaf J ((CategoryTheory.Functor.const _).obj X) := fun _ _ _ _ _ _ =>
  ⟨hX.from _, fun _ _ _ => hX.hom_ext _ _, fun _ _ => hX.hom_ext _ _⟩

end Presheaf

variable {C : Type u₁} [Category.{v₁} C]
variable (J : GrothendieckTopology C)
variable (A : Type u₂) [Category.{v₂} A]

/-- The category of sheaves taking values in `A` on a Grothendieck topology. -/
abbrev Sheaf := ObjectProperty.FullSubcategory (Presheaf.IsSheaf J (A := A))

section

variable {J A}

/-- The underlying presheaf of a sheaf. -/
@[deprecated "Use ObjectProperty.obj" (since := "2026-03-03")]
abbrev Sheaf.val (F : Sheaf J A) : Cᵒᵖ ⥤ A := F.obj

@[deprecated "Use ObjectProperty.FullSubcategory.property" (since := "2026-03-03")]
lemma Sheaf.cond (F : Sheaf J A) : Presheaf.IsSheaf J F.obj := F.property

@[deprecated (since := "2026-03-03")]
alias Sheaf.Hom.mk := ObjectProperty.homMk

lemma Sheaf.hom_ext_iff {F G : Sheaf J A} {f g : F ⟶ G} :
    f = g ↔ f.hom = g.hom := by
  cat_disch

lemma Sheaf.hom_ext {F G : Sheaf J A} {f g : F ⟶ G} (h : f.hom = g.hom) :
    f = g := by
  cat_disch

end

/-- The inclusion functor of the category of sheaves in the category of presheaves. -/
abbrev sheafToPresheaf : Sheaf J A ⥤ Cᵒᵖ ⥤ A := ObjectProperty.ι _

/-- The sections of a sheaf (i.e. evaluation as a presheaf on `C`). -/
abbrev sheafSections : Cᵒᵖ ⥤ Sheaf J A ⥤ A := (sheafToPresheaf J A).flip

/-- The sheaf sections functor on `X` is given by evaluation of presheaves on `X`. -/
@[simps!]
def sheafSectionsNatIsoEvaluation {X : C} :
    (sheafSections J A).obj (op X) ≅ sheafToPresheaf J A ⋙ (evaluation _ _).obj (op X) :=
  Iso.refl _

/-- The functor `Sheaf J A ⥤ Cᵒᵖ ⥤ A` is fully faithful. -/
abbrev fullyFaithfulSheafToPresheaf : (sheafToPresheaf J A).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

section

variable {J A}

/-- The bijection `(X ⟶ Y) ≃ (X.val ⟶ Y.val)` when `X` and `Y` are sheaves. -/
abbrev Sheaf.homEquiv {X Y : Sheaf J A} : (X ⟶ Y) ≃ (X.obj ⟶ Y.obj) :=
  (fullyFaithfulSheafToPresheaf J A).homEquiv

/-- `Sheaf.homEquiv` as a natural isomorphism. -/
@[simps!]
def sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf :
    sheafToPresheaf J A ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf J A).op ≅
      yoneda :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftYonedaIsoYoneda.symm.{max u₁ v₂} _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftYonedaCompWhiskeringLeft ≪≫
    uliftYonedaIsoYoneda

lemma sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf_app_app {X Y : Sheaf J A} :
    (sheafToPresheafCompYonedaCompWhiskeringLeftSheafToPresheaf.app X).app (op Y) =
      Sheaf.homEquiv.symm.toIso :=
  rfl

/-- `Sheaf.homEquiv` as a natural isomorphism, using coyoneda. -/
@[simps!]
def sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf :
    (sheafToPresheaf J A).op ⋙ coyoneda ⋙
      (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf J A) ≅
      coyoneda :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight uliftCoyonedaIsoCoyoneda.symm.{max u₁ v₂} _) ≪≫
    (fullyFaithfulSheafToPresheaf J A).compUliftCoyonedaCompWhiskeringLeft ≪≫
    uliftCoyonedaIsoCoyoneda

lemma sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf_app_app {X Y : Sheaf J A} :
    (sheafToPresheafCompCoyonedaCompWhiskeringLeftSheafToPresheaf.app (op X)).app Y =
      Sheaf.homEquiv.symm.toIso :=
  rfl

end

/-- This is stated as a lemma to prevent class search from forming a loop since a sheaf morphism is
monic if and only if it is monic as a presheaf morphism (under suitable assumption). -/
theorem Sheaf.Hom.mono_of_presheaf_mono {F G : Sheaf J A} (f : F ⟶ G) [h : Mono f.1] : Mono f :=
  (sheafToPresheaf J A).mono_of_mono_map h

instance Sheaf.Hom.epi_of_presheaf_epi {F G : Sheaf J A} (f : F ⟶ G) [h : Epi f.1] : Epi f :=
  (sheafToPresheaf J A).epi_of_epi_map h

theorem isSheaf_iff_isSheaf_of_type (P : Cᵒᵖ ⥤ TypeCat.{w}) :
    Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P := by
  constructor
  · intro hP
    refine Presieve.isSheaf_iso J ?_ (hP (TypeCat.of PUnit))
    exact Functor.isoWhiskerLeft _ Coyoneda.punitIso ≪≫ P.rightUnitor
  · intro hP X Y S hS z hz
    refine ⟨TypeCat.ofHom ⟨fun x => (hP S hS).amalgamate (fun Z f hf ↦
      (ConcreteCategory.hom (z f hf)) x) ?_⟩, ?_, ?_⟩
    · intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ h
      exact (ConcreteCategory.congr_hom (hz g₁ g₂ hf₁ hf₂ h)) x
    · intro Z f hf
      apply ConcreteCategory.hom_ext
      intro x
      simp only [Functor.comp_obj, Functor.flip_obj_obj, yoneda_obj_obj, Functor.comp_map,
        Functor.flip_obj_map, yoneda_map_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.mk_apply,
        comp_apply]
      apply Presieve.IsSheafFor.valid_glue
    · intro y hy
      apply ConcreteCategory.hom_ext
      intro x
      apply (hP S hS).isSeparatedFor.ext
      intro Y' f hf
      simp [Presieve.IsSheafFor.valid_glue _ _ _ hf, ← hy _ hf]

/-- The sheaf of sections guaranteed by the sheaf condition. -/
@[simps]
def sheafOver {A : Type u₂} [Category.{v₂} A] {J : GrothendieckTopology C} (ℱ : Sheaf J A) (E : A) :
    Sheaf J (Type _) where
  obj := ℱ.obj ⋙ coyoneda.obj (op E)
  property := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact ℱ.property E

variable {J} in
lemma Presheaf.IsSheaf.isSheafFor {P : Cᵒᵖ ⥤ TypeCat.{w}} (hP : Presheaf.IsSheaf J P)
    {X : C} (S : Sieve X) (hS : S ∈ J X) : Presieve.IsSheafFor P S.arrows := by
  rw [isSheaf_iff_isSheaf_of_type] at hP
  exact hP S hS

variable {A} in
lemma Presheaf.isSheaf_bot (P : Cᵒᵖ ⥤ A) : IsSheaf ⊥ P := fun _ ↦ Presieve.isSheaf_bot

/--
The category of sheaves on the bottom (trivial) Grothendieck topology is
equivalent to the category of presheaves.
-/
@[simps]
def sheafBotEquivalence : Sheaf (⊥ : GrothendieckTopology C) A ≌ Cᵒᵖ ⥤ A where
  functor := sheafToPresheaf _ _
  inverse :=
    { obj := fun P => ⟨P, Presheaf.isSheaf_bot P⟩
      map := fun f => ⟨f⟩ }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

instance : Inhabited (Sheaf (⊥ : GrothendieckTopology C) (TypeCat.{w})) :=
  ⟨(sheafBotEquivalence _).inverse.obj ((Functor.const _).obj default)⟩

variable {J} {A}

/-- If the empty sieve is a cover of `X`, then `F(X)` is terminal. -/
def Sheaf.isTerminalOfBotCover (F : Sheaf J A) (X : C) (H : ⊥ ∈ J X) :
    IsTerminal (F.1.obj (op X)) := by
  refine @IsTerminal.ofUnique _ _ _ ?_
  intro Y
  choose t h using F.2 Y _ H (by tauto) (by tauto)
  exact ⟨⟨t⟩, fun a => h.2 a (by tauto)⟩

@[simp]
theorem Sheaf.Hom.add_app [Preadditive A] {P Q : Sheaf J A} (f g : P ⟶ Q) (U : Cᵒᵖ) :
    (f + g).1.app U = f.1.app U + g.1.app U :=
  rfl

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

set_option backward.isDefEq.respectTransparency false in
/-- When `P` is a sheaf and `S` is a cover, the associated multifork is a limit. -/
def isLimitOfIsSheaf {X : C} (S : J.Cover X) (hP : IsSheaf J P) : IsLimit (S.multifork P) where
  lift := fun E : Multifork _ => hP.amalgamate S (fun _ => E.ι _)
    (fun _ _ r => E.condition ⟨r⟩)
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

set_option backward.isDefEq.respectTransparency false in
theorem isSheaf_iff_multifork :
    IsSheaf J P ↔ ∀ (X : C) (S : J.Cover X), Nonempty (IsLimit (S.multifork P)) := by
  refine ⟨fun hP X S => ⟨isLimitOfIsSheaf _ _ _ hP⟩, ?_⟩
  intro h E X S hS x hx
  let T : J.Cover X := ⟨S, hS⟩
  obtain ⟨hh⟩ := h _ T
  let K : Multifork (T.index P) := Multifork.ofι _ E (fun I => x I.f I.hf)
    (fun I => hx _ _ _ _ I.r.w)
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

variable {J P} in
/-- If `F : Cᵒᵖ ⥤ A` is a sheaf for a Grothendieck topology `J` on `C`,
and `S` is a cover of `X : C`, then the multifork `S.multifork F` is limit. -/
def IsSheaf.isLimitMultifork
    (hP : Presheaf.IsSheaf J P) {X : C} (S : J.Cover X) : IsLimit (S.multifork P) := by
  rw [Presheaf.isSheaf_iff_multifork] at hP
  exact (hP X S).some

set_option backward.isDefEq.respectTransparency false in
theorem isSheaf_iff_multiequalizer [∀ (X : C) (S : J.Cover X), HasMultiequalizer (S.index P)] :
    IsSheaf J P ↔ ∀ (X : C) (S : J.Cover X), IsIso (S.toMultiequalizer P) := by
  rw [isSheaf_iff_multifork]
  refine forall₂_congr fun X S => ⟨?_, ?_⟩
  · rintro ⟨h⟩
    let e : P.obj (op X) ≅ multiequalizer (S.index P) :=
      h.conePointUniqueUpToIso (limit.isLimit _)
    exact (inferInstance : IsIso e.hom)
  · intro h
    refine ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cones.ext ?_ ?_)⟩
    · apply (@asIso _ _ _ _ _ h).symm
    · intro a
      symm
      simp

end MultiequalizerConditions

section

variable [HasProducts.{max u₁ v₁} A]
variable [HasProducts.{max u₁ v₁} A']

/-- The middle object of the fork diagram given in Equation (3) of [MM92], as well as the fork
diagram of the Stacks entry. -/
@[stacks 00VM "The middle object of the fork diagram there."]
def firstObj : A :=
  ∏ᶜ fun f : Σ V, { f : V ⟶ U // R f } => P.obj (op f.1)

/-- The left morphism of the fork diagram given in Equation (3) of [MM92], as well as the fork
diagram of the Stacks entry. -/
@[stacks 00VM "The left morphism the fork diagram there."]
def forkMap : P.obj (op U) ⟶ firstObj R P :=
  Pi.lift fun f => P.map f.2.1.op

variable [HasPullbacks C]

/-- The rightmost object of the fork diagram of the Stacks entry, which
contains the data used to check a family of elements for a presieve is compatible.
-/
@[stacks 00VM "The rightmost object of the fork diagram there."]
def secondObj : A :=
  ∏ᶜ fun fg : (Σ V, { f : V ⟶ U // R f }) × Σ W, { g : W ⟶ U // R g } =>
    P.obj (op (pullback fg.1.2.1 fg.2.2.1))

/-- The map `pr₀*` of the Stacks entry. -/
@[stacks 00VM "The map `pr₀*` there."]
def firstMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.fst _ _).op

/-- The map `pr₁*` of the Stacks entry. -/
@[stacks 00VM "The map `pr₁*` there."]
def secondMap : firstObj R P ⟶ secondObj R P :=
  Pi.lift fun _ => Pi.π _ _ ≫ P.map (pullback.snd _ _).op

set_option backward.isDefEq.respectTransparency false in
theorem w : forkMap R P ≫ firstMap R P = forkMap R P ≫ secondMap R P := by
  apply limit.hom_ext
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩
  simp only [firstMap, secondMap, forkMap, limit.lift_π, limit.lift_π_assoc, assoc, Fan.mk_π_app,
    Subtype.coe_mk]
  rw [← P.map_comp, ← op_comp, pullback.condition]
  simp

/-- An alternative definition of the sheaf condition in terms of equalizers. This is shown to be
equivalent in `CategoryTheory.Presheaf.isSheaf_iff_isSheaf'`.
-/
def IsSheaf' (P : Cᵒᵖ ⥤ A) : Prop :=
  ∀ (U : C) (R : Presieve U) (_ : generate R ∈ J U), Nonempty (IsLimit (Fork.ofι _ (w R P)))

set_option backward.isDefEq.respectTransparency false in
-- Again I wonder whether `UnivLE` can somehow be used to allow `s` to take
-- values in a more general universe.
/-- (Implementation). An auxiliary lemma to convert between sheaf conditions. -/
def isSheafForIsSheafFor' (P : Cᵒᵖ ⥤ A) (s : A ⥤ TypeCat.{max v₁ u₁})
    [∀ J, PreservesLimitsOfShape (Discrete.{max v₁ u₁} J) s] (U : C) (R : Presieve U) :
    IsLimit (s.mapCone (Fork.ofι _ (w R P))) ≃
      IsLimit (Fork.ofι _ (Equalizer.Presieve.w (P ⋙ s) R)) := by
  let e : parallelPair (s.map (firstMap R P)) (s.map (secondMap R P)) ≅
    parallelPair (Equalizer.Presieve.firstMap (P ⋙ s) R)
      (Equalizer.Presieve.secondMap (P ⋙ s) R) := by
    refine parallelPair.ext (PreservesProduct.iso s _) ((PreservesProduct.iso s _))
      (limit.hom_ext (fun j => ?_)) (limit.hom_ext (fun j => ?_))
    · dsimp [Equalizer.Presieve.firstMap, firstMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
    · dsimp [Equalizer.Presieve.secondMap, secondMap]
      simp only [map_lift_piComparison, Functor.map_comp, limit.lift_π, Fan.mk_pt,
        Fan.mk_π_app, assoc, piComparison_comp_π_assoc]
  refine Equiv.trans (isLimitMapConeForkEquiv _ _) ?_
  refine (IsLimit.postcomposeHomEquiv e _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) ?_))
  dsimp [Equalizer.forkMap, forkMap, e, Fork.ι]
  simp only [id_comp, map_lift_piComparison]

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
    refine isSheafForIsSheafFor' _ _ _ _ ?_
    letI := preservesSmallestLimits_of_preservesLimits (coyoneda.obj (op U))
    apply isLimitOfPreserves
    apply Classical.choice (h _ S.arrows _)
    simpa

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
  letI : ReflectsLimitsOfSize s := reflectsLimits_of_reflectsIsomorphisms
  exact ⟨isSheaf_comp_of_isSheaf J P s, isSheaf_of_isSheaf_comp J P s⟩

/--
For a concrete category `(A, s)` where the forgetful functor `s : A ⥤ Type v` preserves limits and
reflects isomorphisms, and `A` has limits, an `A`-valued presheaf `P : Cᵒᵖ ⥤ A` is a sheaf iff its
underlying `Type`-valued presheaf `P ⋙ s : Cᵒᵖ ⥤ Type` is a sheaf.

Note this lemma applies for "algebraic" categories, e.g. groups, abelian groups and rings, but not
for the category of topological spaces, topological rings, etc. since reflecting isomorphisms does
not hold.
-/
theorem isSheaf_iff_isSheaf_forget (s : A' ⥤ TypeCat.{max v₁ u₁}) [HasLimits A'] [PreservesLimits s]
    [s.ReflectsIsomorphisms] : IsSheaf J P' ↔ IsSheaf J (P' ⋙ s) := by
  have : HasLimitsOfSize.{v₁, max v₁ u₁} A' := hasLimitsOfSizeShrink.{_, _, u₁, 0} A'
  have : PreservesLimitsOfSize.{v₁, max v₁ u₁} s := preservesLimitsOfSize_shrink.{_, 0, _, u₁} s
  apply isSheaf_iff_isSheaf_comp

end Concrete

end Presheaf

end CategoryTheory
