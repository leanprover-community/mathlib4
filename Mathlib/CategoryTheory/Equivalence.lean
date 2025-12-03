/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.Data.Int.Notation
/-!
# Equivalence of categories

An equivalence of categories `C` and `D` is a pair of functors `F : C ⥤ D` and `G : D ⥤ C` such
that `η : 𝟭 C ≅ F ⋙ G` and `ε : G ⋙ F ≅ 𝟭 D`. In many situations, equivalences are a better
notion of "sameness" of categories than the stricter isomorphism of categories.

Recall that one way to express that two functors `F : C ⥤ D` and `G : D ⥤ C` are adjoint is using
two natural transformations `η : 𝟭 C ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 D`, called the unit and the
counit, such that the compositions `F ⟶ FGF ⟶ F` and `G ⟶ GFG ⟶ G` are the identity. Unfortunately,
it is not the case that the natural isomorphisms `η` and `ε` in the definition of an equivalence
automatically give an adjunction. However, it is true that
* if one of the two compositions is the identity, then so is the other, and
* given an equivalence of categories, it is always possible to refine `η` in such a way that the
  identities are satisfied.

For this reason, in mathlib we define an equivalence to be a "half-adjoint equivalence", which is
a tuple `(F, G, η, ε)` as in the first paragraph such that the composite `F ⟶ FGF ⟶ F` is the
identity. By the remark above, this already implies that the tuple is an "adjoint equivalence",
i.e., that the composite `G ⟶ GFG ⟶ G` is also the identity.

We also define essentially surjective functors and show that a functor is an equivalence if and only
if it is full, faithful and essentially surjective.

## Main definitions

* `Equivalence`: bundled (half-)adjoint equivalences of categories
* `Functor.EssSurj`: type class on a functor `F` containing the data of the preimages
  and the isomorphisms `F.obj (preimage d) ≅ d`.
* `Functor.IsEquivalence`: type class on a functor `F` which is full, faithful and
  essentially surjective.

## Main results

* `Equivalence.mk`: upgrade an equivalence to a (half-)adjoint equivalence
* `isEquivalence_iff_of_iso`: when `F` and `G` are isomorphic functors,
  `F` is an equivalence iff `G` is.
* `Functor.asEquivalenceFunctor`: construction of an equivalence of categories from
  a functor `F` which satisfies the property `F.IsEquivalence` (i.e. `F` is full, faithful
  and essentially surjective).

## Notation

We write `C ≌ D` (`\backcong`, not to be confused with `≅`/`\cong`) for a bundled equivalence.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

/-- An equivalence of categories.

We define an equivalence between `C` and `D`, with notation `C ≌ D`, as a half-adjoint equivalence:
a pair of functors `F : C ⥤ D` and `G : D ⥤ C` with a unit `η : 𝟭 C ≅ F ⋙ G` and counit
`ε : G ⋙ F ≅ 𝟭 D`, such that the natural isomorphisms `η` and `ε` satisfy the triangle law for
`F`: namely, `Fη ≫ εF = 𝟙 F`. Or, in other words, the composite `F` ⟶ `F ⋙ G ⋙ F` ⟶ `F` is the
identity.

In `unit_inverse_comp`, we show that this is sufficient to establish a full adjoint
equivalence. I.e., the composite `G` ⟶ `G ⋙ F ⋙ G` ⟶ `G` is also the identity.

The triangle equation `functor_unitIso_comp` is written as a family of equalities between
morphisms. It is more complicated if we write it as an equality of natural transformations, because
then we would either have to insert natural transformations like `F ⟶ F𝟭` or abuse defeq. -/
@[ext, stacks 001J]
structure Equivalence (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] where mk' ::
  /-- The forwards direction of an equivalence. -/
  functor : C ⥤ D
  /-- The backwards direction of an equivalence. -/
  inverse : D ⥤ C
  /-- The composition `functor ⋙ inverse` is isomorphic to the identity. -/
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  /-- The composition `inverse ⋙ functor` is isomorphic to the identity. -/
  counitIso : inverse ⋙ functor ≅ 𝟭 D
  /-- The triangle law for the forwards direction of an equivalence: the unit and counit compose
  to the identity when whiskered along the forwards direction.

  We state this as a family of equalities among morphisms instead of an equality of natural
  transformations to avoid abusing defeq or inserting natural transformations like `F ⟶ F𝟭`. -/
  functor_unitIso_comp :
    ∀ X : C, functor.map (unitIso.hom.app X) ≫ counitIso.hom.app (functor.obj X) =
      𝟙 (functor.obj X) := by cat_disch

@[inherit_doc Equivalence]
infixr:10 " ≌ " => Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Equivalence

/-- The unit of an equivalence of categories. -/
abbrev unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse :=
  e.unitIso.hom

/-- The counit of an equivalence of categories. -/
abbrev counit (e : C ≌ D) : e.inverse ⋙ e.functor ⟶ 𝟭 D :=
  e.counitIso.hom

/-- The inverse of the unit of an equivalence of categories. -/
abbrev unitInv (e : C ≌ D) : e.functor ⋙ e.inverse ⟶ 𝟭 C :=
  e.unitIso.inv

/-- The inverse of the counit of an equivalence of categories. -/
abbrev counitInv (e : C ≌ D) : 𝟭 D ⟶ e.inverse ⋙ e.functor :=
  e.counitIso.inv

section CategoryStructure

instance : Category (C ≌ D) where
  Hom e f := e.functor ⟶ f.functor
  id e := 𝟙 e.functor
  comp {a b c} f g := (f ≫ g : a.functor ⟶ _)

/-- Promote a natural transformation `e.functor ⟶ f.functor` to a morphism in `C ≌ D`. -/
def mkHom {e f : C ≌ D} (η : e.functor ⟶ f.functor) : e ⟶ f := η

/-- Recover a natural transformation between `e.functor` and `f.functor` from the data of
a morphism `e ⟶ f`. -/
def asNatTrans {e f : C ≌ D} (η : e ⟶ f) : e.functor ⟶ f.functor := η

@[ext]
lemma hom_ext {e f : C ≌ D} {α β : e ⟶ f} (h : asNatTrans α = asNatTrans β) : α = β := h

@[simp]
lemma mkHom_asNatTrans {e f : C ≌ D} (η : e.functor ⟶ f.functor) :
    mkHom (asNatTrans η) = η :=
  rfl

@[simp]
lemma asNatTrans_mkHom {e f : C ≌ D} (η : e ⟶ f) :
    asNatTrans (mkHom η) = η :=
  rfl

@[simp]
lemma id_asNatTrans {e : C ≌ D} : asNatTrans (𝟙 e) = 𝟙 _ := rfl

@[simp, reassoc]
lemma comp_asNatTrans {e f g : C ≌ D} (α : e ⟶ f) (β : f ⟶ g) :
    asNatTrans (α ≫ β) = asNatTrans α ≫ asNatTrans β :=
  rfl

@[simp]
lemma mkHom_id_functor {e : C ≌ D} : mkHom (𝟙 e.functor) = 𝟙 e := rfl

@[simp, reassoc]
lemma mkHom_comp {e f g : C ≌ D} (α : e.functor ⟶ f.functor) (β : f.functor ⟶ g.functor) :
    mkHom (α ≫ β) = mkHom α ≫ mkHom β :=
  rfl

/-- Construct an isomorphism in `C ≌ D` from a natural isomorphism between the functors
of the equivalences. -/
@[simps]
def mkIso {e f : C ≌ D} (η : e.functor ≅ f.functor) : e ≅ f where
  hom := mkHom η.hom
  inv := mkHom η.inv

variable (C D) in
/-- The `functor` functor that sends an equivalence of categories to its functor. -/
@[simps!]
def functorFunctor : (C ≌ D) ⥤ C ⥤ D where
  obj f := f.functor
  map α := asNatTrans α

end CategoryStructure

/- While these abbreviations are convenient, they also cause some trouble,
preventing structure projections from unfolding. -/
@[simp]
theorem Equivalence_mk'_unit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unit = unit_iso.hom :=
  rfl

@[simp]
theorem Equivalence_mk'_counit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit = counit_iso.hom :=
  rfl

@[simp]
theorem Equivalence_mk'_unitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unitInv = unit_iso.inv :=
  rfl

@[simp]
theorem Equivalence_mk'_counitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counitInv = counit_iso.inv :=
  rfl

@[reassoc]
theorem counit_naturality (e : C ≌ D) {X Y : D} (f : X ⟶ Y) :
    e.functor.map (e.inverse.map f) ≫ e.counit.app Y = e.counit.app X ≫ f :=
  e.counit.naturality f

@[reassoc]
theorem unit_naturality (e : C ≌ D) {X Y : C} (f : X ⟶ Y) :
    e.unit.app X ≫ e.inverse.map (e.functor.map f) = f ≫ e.unit.app Y :=
  (e.unit.naturality f).symm

@[reassoc]
theorem counitInv_naturality (e : C ≌ D) {X Y : D} (f : X ⟶ Y) :
    e.counitInv.app X ≫ e.functor.map (e.inverse.map f) = f ≫ e.counitInv.app Y :=
  (e.counitInv.naturality f).symm

@[reassoc]
theorem unitInv_naturality (e : C ≌ D) {X Y : C} (f : X ⟶ Y) :
    e.inverse.map (e.functor.map f) ≫ e.unitInv.app Y = e.unitInv.app X ≫ f :=
  e.unitInv.naturality f

@[reassoc (attr := simp)]
theorem functor_unit_comp (e : C ≌ D) (X : C) :
    e.functor.map (e.unit.app X) ≫ e.counit.app (e.functor.obj X) = 𝟙 (e.functor.obj X) :=
  e.functor_unitIso_comp X

@[reassoc (attr := simp)]
theorem counitInv_functor_comp (e : C ≌ D) (X : C) :
    e.counitInv.app (e.functor.obj X) ≫ e.functor.map (e.unitInv.app X) = 𝟙 (e.functor.obj X) := by
  simpa using Iso.inv_eq_inv
    (e.functor.mapIso (e.unitIso.app X) ≪≫ e.counitIso.app (e.functor.obj X)) (Iso.refl _)

theorem counitInv_app_functor (e : C ≌ D) (X : C) :
    e.counitInv.app (e.functor.obj X) = e.functor.map (e.unit.app X) := by
  symm
  simp only [id_obj, comp_obj, counitInv]
  rw [← Iso.app_inv, ← Iso.comp_hom_eq_id (e.counitIso.app _), Iso.app_hom, functor_unit_comp]
  rfl

theorem counit_app_functor (e : C ≌ D) (X : C) :
    e.counit.app (e.functor.obj X) = e.functor.map (e.unitInv.app X) := by
  simpa using Iso.hom_comp_eq_id (e.functor.mapIso (e.unitIso.app X)) (f := e.counit.app _)

/-- The other triangle equality. The proof follows the following proof in Globular:
  http://globular.science/1905.001 -/
@[reassoc (attr := simp)]
theorem unit_inverse_comp (e : C ≌ D) (Y : D) :
    e.unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app Y) = 𝟙 (e.inverse.obj Y) := by
  rw [← id_comp (e.inverse.map _), ← map_id e.inverse, ← counitInv_functor_comp, map_comp]
  dsimp
  rw [← Iso.hom_inv_id_assoc (e.unitIso.app _) (e.inverse.map (e.functor.map _)), Iso.app_hom,
    Iso.app_inv]
  slice_lhs 2 3 => rw [← e.unit_naturality]
  slice_lhs 1 2 => rw [← e.unit_naturality]
  slice_lhs 4 4 =>
    rw [← Iso.hom_inv_id_assoc (e.inverse.mapIso (e.counitIso.app _)) (e.unitInv.app _)]
  slice_lhs 3 4 =>
    dsimp only [Functor.mapIso_hom, Iso.app_hom]
    rw [← map_comp e.inverse, e.counit_naturality, e.counitIso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    rw [map_id]
  dsimp only [comp_obj, id_obj]
  rw [id_comp]
  slice_lhs 2 3 =>
    dsimp only [Functor.mapIso_inv, Iso.app_inv]
    rw [← map_comp e.inverse, ← e.counitInv_naturality, map_comp]
  slice_lhs 3 4 => rw [e.unitInv_naturality]
  slice_lhs 4 5 =>
    rw [← map_comp e.inverse, ← map_comp e.functor, e.unitIso.hom_inv_id_app]
    dsimp only [Functor.id_obj]
    rw [map_id, map_id]
  dsimp only [comp_obj, id_obj]
  rw [id_comp]
  slice_lhs 3 4 => rw [← e.unitInv_naturality]
  slice_lhs 2 3 =>
    rw [← map_comp e.inverse, e.counitInv_naturality, e.counitIso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  simp

@[reassoc (attr := simp)]
theorem inverse_counitInv_comp (e : C ≌ D) (Y : D) :
    e.inverse.map (e.counitInv.app Y) ≫ e.unitInv.app (e.inverse.obj Y) = 𝟙 (e.inverse.obj Y) := by
  simpa using Iso.inv_eq_inv
    (e.unitIso.app (e.inverse.obj Y) ≪≫ e.inverse.mapIso (e.counitIso.app Y)) (Iso.refl _)

theorem unit_app_inverse (e : C ≌ D) (Y : D) :
    e.unit.app (e.inverse.obj Y) = e.inverse.map (e.counitInv.app Y) := by
  simpa using Iso.comp_hom_eq_id (e.inverse.mapIso (e.counitIso.app Y)) (f := e.unit.app _)

theorem unitInv_app_inverse (e : C ≌ D) (Y : D) :
    e.unitInv.app (e.inverse.obj Y) = e.inverse.map (e.counit.app Y) := by
  rw [← Iso.app_inv, ← Iso.app_hom, ← mapIso_hom, Eq.comm, ← Iso.hom_eq_inv]
  simpa using unit_app_inverse e Y

@[reassoc, simp]
theorem fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) :
    e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitInv.app Y :=
  (NatIso.naturality_2 e.counitIso f).symm

@[reassoc, simp]
theorem inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) :
    e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.app Y :=
  (NatIso.naturality_1 e.unitIso f).symm

section

-- In this section we convert an arbitrary equivalence to a half-adjoint equivalence.
variable {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)

/-- If `η : 𝟭 C ≅ F ⋙ G` is part of a (not necessarily half-adjoint) equivalence, we can upgrade it
to a refined natural isomorphism `adjointifyη η : 𝟭 C ≅ F ⋙ G` which exhibits the properties
required for a half-adjoint equivalence. See `Equivalence.mk`. -/
def adjointifyη : 𝟭 C ≅ F ⋙ G := by
  calc
    𝟭 C ≅ F ⋙ G := η
    _ ≅ F ⋙ 𝟭 D ⋙ G := isoWhiskerLeft F (leftUnitor G).symm
    _ ≅ F ⋙ (G ⋙ F) ⋙ G := isoWhiskerLeft F (isoWhiskerRight ε.symm G)
    _ ≅ F ⋙ G ⋙ F ⋙ G := isoWhiskerLeft F (associator G F G)
    _ ≅ (F ⋙ G) ⋙ F ⋙ G := (associator F G (F ⋙ G)).symm
    _ ≅ 𝟭 C ⋙ F ⋙ G := isoWhiskerRight η.symm (F ⋙ G)
    _ ≅ F ⋙ G := leftUnitor (F ⋙ G)

@[reassoc]
theorem adjointify_η_ε (X : C) :
    F.map ((adjointifyη η ε).hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) := by
  dsimp [adjointifyη, Trans.trans]
  simp only [comp_id, assoc, map_comp]
  have := ε.hom.naturality (F.map (η.inv.app X)); dsimp at this; rw [this]; clear this
  rw [← assoc _ _ (F.map _)]
  have := ε.hom.naturality (ε.inv.app <| F.obj X); dsimp at this; rw [this]; clear this
  have := (ε.app <| F.obj X).hom_inv_id; dsimp at this; rw [this]; clear this
  rw [id_comp]; have := (F.mapIso <| η.app X).hom_inv_id; dsimp at this; rw [this]

end

/-- Every equivalence of categories consisting of functors `F` and `G` such that `F ⋙ G` and
    `G ⋙ F` are naturally isomorphic to identity functors can be transformed into a half-adjoint
    equivalence without changing `F` or `G`. -/
protected def mk (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
  ⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩

/-- Equivalence of categories is reflexive. -/
@[refl, simps]
def refl : C ≌ C :=
  ⟨𝟭 C, 𝟭 C, Iso.refl _, Iso.refl _, fun _ => Category.id_comp _⟩

instance : Inhabited (C ≌ C) :=
  ⟨refl⟩

/-- Equivalence of categories is symmetric. -/
@[symm, simps]
def symm (e : C ≌ D) : D ≌ C :=
  ⟨e.inverse, e.functor, e.counitIso.symm, e.unitIso.symm, e.inverse_counitInv_comp⟩

@[simp]
lemma mkHom_id_inverse {e : C ≌ D} : mkHom (𝟙 e.inverse) = 𝟙 e.symm := rfl

variable {E : Type u₃} [Category.{v₃} E]

/-- Equivalence of categories is transitive. -/
@[trans, simps]
def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight (e.functor.rightUnitor.symm ≪≫
    isoWhiskerLeft _ f.unitIso ≪≫ (Functor.associator _ _ _ ).symm) _ ≪≫ Functor.associator _ _ _
  counitIso := (Functor.associator _ _ _ ).symm ≪≫ isoWhiskerRight ((Functor.associator _ _ _ ) ≪≫
      isoWhiskerLeft _ e.counitIso ≪≫ f.inverse.rightUnitor) _ ≪≫ f.counitIso
  -- We wouldn't have needed to give this proof if we'd used `Equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp`
  -- lemmas.
  functor_unitIso_comp X := by
    dsimp
    simp only [comp_id, id_comp, map_comp, fun_inv_map, comp_obj, id_obj, counitInv,
      functor_unit_comp_assoc, assoc]
    slice_lhs 2 3 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
    simp

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
def funInvIdAssoc (e : C ≌ D) (F : C ⥤ E) : e.functor ⋙ e.inverse ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor

@[simp]
theorem funInvIdAssoc_hom_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).hom.app X = F.map (e.unitInv.app X) := by
  dsimp [funInvIdAssoc]
  simp

@[simp]
theorem funInvIdAssoc_inv_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).inv.app X = F.map (e.unit.app X) := by
  dsimp [funInvIdAssoc]
  simp

/-- Composing a functor with both functors of an equivalence yields a naturally isomorphic
functor. -/
def invFunIdAssoc (e : C ≌ D) (F : D ⥤ E) : e.inverse ⋙ e.functor ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso F ≪≫ F.leftUnitor

@[simp]
theorem invFunIdAssoc_hom_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).hom.app X = F.map (e.counit.app X) := by
  dsimp [invFunIdAssoc]
  simp

@[simp]
theorem invFunIdAssoc_inv_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).inv.app X = F.map (e.counitInv.app X) := by
  dsimp [invFunIdAssoc]
  simp

/-- If `C` is equivalent to `D`, then `C ⥤ E` is equivalent to `D ⥤ E`. -/
@[simps! functor inverse unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
def congrLeft (e : C ≌ D) : C ⥤ E ≌ D ⥤ E where
  functor := (whiskeringLeft _ _ _).obj e.inverse
  inverse := (whiskeringLeft _ _ _).obj e.functor
  unitIso := (NatIso.ofComponents fun F => (e.funInvIdAssoc F).symm)
  counitIso := (NatIso.ofComponents fun F => e.invFunIdAssoc F)
  functor_unitIso_comp F := by
    ext X
    dsimp
    simp only [funInvIdAssoc_inv_app, id_obj, comp_obj, invFunIdAssoc_hom_app,
      Functor.comp_map, ← F.map_comp, unit_inverse_comp, map_id]

/-- If `C` is equivalent to `D`, then `E ⥤ C` is equivalent to `E ⥤ D`. -/
@[simps! functor inverse unitIso_hom_app unitIso_inv_app counitIso_hom_app counitIso_inv_app]
def congrRight (e : C ≌ D) : E ⥤ C ≌ E ⥤ D where
  functor := (whiskeringRight _ _ _).obj e.functor
  inverse := (whiskeringRight _ _ _).obj e.inverse
  unitIso := NatIso.ofComponents
      fun F => F.rightUnitor.symm ≪≫ isoWhiskerLeft F e.unitIso ≪≫ Functor.associator _ _ _
  counitIso := NatIso.ofComponents
      fun F => Functor.associator _ _ _ ≪≫ isoWhiskerLeft F e.counitIso ≪≫ F.rightUnitor

variable (E) in
/-- Promoting `Equivalence.congrRight` to a functor. -/
@[simps]
def congrRightFunctor : (C ≌ D) ⥤ ((E ⥤ C) ≌ (E ⥤ D)) where
  obj e := e.congrRight
  map {e f} α := mkHom <| (whiskeringRight _ _ _).map <| asNatTrans α

section CancellationLemmas

variable (e : C ≌ D)

/- We need special forms of `cancel_natIso_hom_right(_assoc)` and
`cancel_natIso_inv_right(_assoc)` for units and counits, because neither `simp` or `rw` will apply
those lemmas in this setting without providing `e.unitIso` (or similar) as an explicit argument.
We also provide the lemmas for length four compositions, since they're occasionally useful.
(e.g. in proving that equivalences take monos to monos) -/
@[simp]
theorem cancel_unit_right {X Y : C} (f f' : X ⟶ Y) :
    f ≫ e.unit.app Y = f' ≫ e.unit.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp]
theorem cancel_unitInv_right {X Y : C} (f f' : X ⟶ e.inverse.obj (e.functor.obj Y)) :
    f ≫ e.unitInv.app Y = f' ≫ e.unitInv.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp]
theorem cancel_counit_right {X Y : D} (f f' : X ⟶ e.functor.obj (e.inverse.obj Y)) :
    f ≫ e.counit.app Y = f' ≫ e.counit.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp]
theorem cancel_counitInv_right {X Y : D} (f f' : X ⟶ Y) :
    f ≫ e.counitInv.app Y = f' ≫ e.counitInv.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp]
theorem cancel_unit_right_assoc {W X X' Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
    f ≫ g ≫ e.unit.app Y = f' ≫ g' ≫ e.unit.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp]
theorem cancel_counitInv_right_assoc {W X X' Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) : f ≫ g ≫ e.counitInv.app Y = f' ≫ g' ≫ e.counitInv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp]
theorem cancel_unit_right_assoc' {W X X' Y Y' Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.unit.app Z = f' ≫ g' ≫ h' ≫ e.unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' := by
  simp only [← Category.assoc, cancel_mono]

@[simp]
theorem cancel_counitInv_right_assoc' {W X X' Y Y' Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.counitInv.app Z = f' ≫ g' ≫ h' ≫ e.counitInv.app Z ↔
    f ≫ g ≫ h = f' ≫ g' ≫ h' := by simp only [← Category.assoc, cancel_mono]

end CancellationLemmas

section

-- There's of course a monoid structure on `C ≌ C`,
-- but let's not encourage using it.
-- The power structure is nevertheless useful.
/-- Natural number powers of an auto-equivalence.  Use `(^)` instead. -/
def powNat (e : C ≌ C) : ℕ → (C ≌ C)
  | 0 => Equivalence.refl
  | 1 => e
  | n + 2 => e.trans (powNat e (n + 1))

/-- Powers of an auto-equivalence.  Use `(^)` instead. -/
def pow (e : C ≌ C) : ℤ → (C ≌ C)
  | Int.ofNat n => e.powNat n
  | Int.negSucc n => e.symm.powNat (n + 1)

instance : Pow (C ≌ C) ℤ :=
  ⟨pow⟩

@[simp]
theorem pow_zero (e : C ≌ C) : e ^ (0 : ℤ) = Equivalence.refl :=
  rfl

@[simp]
theorem pow_one (e : C ≌ C) : e ^ (1 : ℤ) = e :=
  rfl

@[simp]
theorem pow_neg_one (e : C ≌ C) : e ^ (-1 : ℤ) = e.symm :=
  rfl

-- TODO as necessary, add the natural isomorphisms `(e^a).trans e^b ≅ e^(a+b)`.
-- At this point, we haven't even defined the category of equivalences.
-- Note: the better formulation of this would involve `HasShift`.
end

/-- The functor of an equivalence of categories is essentially surjective. -/
@[stacks 02C3]
instance essSurj_functor (e : C ≌ E) : e.functor.EssSurj :=
  ⟨fun Y => ⟨e.inverse.obj Y, ⟨e.counitIso.app Y⟩⟩⟩

instance essSurj_inverse (e : C ≌ E) : e.inverse.EssSurj :=
  e.symm.essSurj_functor

/-- The functor of an equivalence of categories is fully faithful. -/
def fullyFaithfulFunctor (e : C ≌ E) : e.functor.FullyFaithful where
  preimage {X Y} f := e.unitIso.hom.app X ≫ e.inverse.map f ≫ e.unitIso.inv.app Y

/-- The inverse of an equivalence of categories is fully faithful. -/
def fullyFaithfulInverse (e : C ≌ E) : e.inverse.FullyFaithful where
  preimage {X Y} f := e.counitIso.inv.app X ≫ e.functor.map f ≫ e.counitIso.hom.app Y

/-- The functor of an equivalence of categories is faithful. -/
@[stacks 02C3]
instance faithful_functor (e : C ≌ E) : e.functor.Faithful :=
  e.fullyFaithfulFunctor.faithful

instance faithful_inverse (e : C ≌ E) : e.inverse.Faithful :=
  e.fullyFaithfulInverse.faithful

/-- The functor of an equivalence of categories is full. -/
@[stacks 02C3]
instance full_functor (e : C ≌ E) : e.functor.Full :=
  e.fullyFaithfulFunctor.full

instance full_inverse (e : C ≌ E) : e.inverse.Full :=
  e.fullyFaithfulInverse.full

/-- If `e : C ≌ D` is an equivalence of categories, and `iso : e.functor ≅ G` is
an isomorphism, then there is an equivalence of categories whose functor is `G`. -/
@[simps!]
def changeFunctor (e : C ≌ D) {G : C ⥤ D} (iso : e.functor ≅ G) : C ≌ D where
  functor := G
  inverse := e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight iso _
  counitIso := isoWhiskerLeft _ iso.symm ≪≫ e.counitIso

/-- Compatibility of `changeFunctor` with identity isomorphisms of functors -/
theorem changeFunctor_refl (e : C ≌ D) : e.changeFunctor (Iso.refl _) = e := by cat_disch

/-- Compatibility of `changeFunctor` with the composition of isomorphisms of functors -/
theorem changeFunctor_trans (e : C ≌ D) {G G' : C ⥤ D} (iso₁ : e.functor ≅ G) (iso₂ : G ≅ G') :
    (e.changeFunctor iso₁).changeFunctor iso₂ = e.changeFunctor (iso₁ ≪≫ iso₂) := by cat_disch

/-- If `e : C ≌ D` is an equivalence of categories, and `iso : e.functor ≅ G` is
an isomorphism, then there is an equivalence of categories whose inverse is `G`. -/
@[simps!]
def changeInverse (e : C ≌ D) {G : D ⥤ C} (iso : e.inverse ≅ G) : C ≌ D where
  functor := e.functor
  inverse := G
  unitIso := e.unitIso ≪≫ isoWhiskerLeft _ iso
  counitIso := isoWhiskerRight iso.symm _ ≪≫ e.counitIso
  functor_unitIso_comp X := by
    dsimp
    rw [← map_comp_assoc, assoc, iso.hom_inv_id_app, comp_id, functor_unit_comp]

end Equivalence

/-- A functor is an equivalence of categories if it is faithful, full and
essentially surjective. -/
class Functor.IsEquivalence (F : C ⥤ D) : Prop where
  faithful : F.Faithful := by infer_instance
  full : F.Full := by infer_instance
  essSurj : F.EssSurj := by infer_instance

instance Equivalence.isEquivalence_functor (F : C ≌ D) : IsEquivalence F.functor where

instance Equivalence.isEquivalence_inverse (F : C ≌ D) : IsEquivalence F.inverse :=
  F.symm.isEquivalence_functor

namespace Functor

namespace IsEquivalence

attribute [instance] faithful full essSurj

/-- To see that a functor is an equivalence, it suffices to provide an inverse functor `G` such that
    `F ⋙ G` and `G ⋙ F` are naturally isomorphic to identity functors. -/
protected lemma mk' {F : C ⥤ D} (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) :
    IsEquivalence F :=
  inferInstanceAs (IsEquivalence (Equivalence.mk F G η ε).functor)

end IsEquivalence

/-- A quasi-inverse `D ⥤ C` to a functor that `F : C ⥤ D` that is an equivalence,
i.e. faithful, full, and essentially surjective. -/
noncomputable def inv (F : C ⥤ D) [F.IsEquivalence] : D ⥤ C where
  obj X := F.objPreimage X
  map {X Y} f := F.preimage ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
  map_id X := by apply F.map_injective; simp
  map_comp {X Y Z} f g := by apply F.map_injective; simp

/-- Interpret a functor that is an equivalence as an equivalence. -/
@[simps functor, stacks 02C3]
noncomputable def asEquivalence (F : C ⥤ D) [F.IsEquivalence] : C ≌ D where
  functor := F
  inverse := F.inv
  unitIso := NatIso.ofComponents
    (fun X => (F.preimageIso <| F.objObjPreimageIso <| F.obj X).symm)
      (fun f => F.map_injective (by simp [inv]))
  counitIso := NatIso.ofComponents F.objObjPreimageIso (by simp [inv])

instance isEquivalence_refl : IsEquivalence (𝟭 C) :=
  Equivalence.refl.isEquivalence_functor

instance isEquivalence_inv (F : C ⥤ D) [IsEquivalence F] : IsEquivalence F.inv :=
  F.asEquivalence.symm.isEquivalence_functor

variable {E : Type u₃} [Category.{v₃} E]

instance isEquivalence_trans (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence F] [IsEquivalence G] :
    IsEquivalence (F ⋙ G) where

instance (F : C ⥤ D) [IsEquivalence F] : IsEquivalence ((whiskeringLeft C D E).obj F) :=
  (inferInstance : IsEquivalence (Equivalence.congrLeft F.asEquivalence).inverse)

instance (F : C ⥤ D) [IsEquivalence F] : IsEquivalence ((whiskeringRight E C D).obj F) :=
  (inferInstance : IsEquivalence (Equivalence.congrRight F.asEquivalence).functor)

end Functor

namespace Functor


@[simp]
theorem fun_inv_map (F : C ⥤ D) [IsEquivalence F] (X Y : D) (f : X ⟶ Y) :
    F.map (F.inv.map f) = F.asEquivalence.counit.app X ≫ f ≫ F.asEquivalence.counitInv.app Y := by
  simpa using (NatIso.naturality_2 (α := F.asEquivalence.counitIso) (f := f)).symm

@[simp]
theorem inv_fun_map (F : C ⥤ D) [IsEquivalence F] (X Y : C) (f : X ⟶ Y) :
    F.inv.map (F.map f) = F.asEquivalence.unitInv.app X ≫ f ≫ F.asEquivalence.unit.app Y := by
  simpa using (NatIso.naturality_1 (α := F.asEquivalence.unitIso) (f := f)).symm

lemma isEquivalence_of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsEquivalence] : G.IsEquivalence :=
  ((asEquivalence F).changeFunctor e).isEquivalence_functor

lemma isEquivalence_iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsEquivalence ↔ G.IsEquivalence :=
  ⟨fun _ => isEquivalence_of_iso e, fun _ => isEquivalence_of_iso e.symm⟩

/-- If `G` and `F ⋙ G` are equivalence of categories, then `F` is also an equivalence. -/
lemma isEquivalence_of_comp_right {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    [IsEquivalence G] [IsEquivalence (F ⋙ G)] : IsEquivalence F := by
  rw [isEquivalence_iff_of_iso (F.rightUnitor.symm ≪≫ isoWhiskerLeft F (G.asEquivalence.unitIso))]
  exact ((F ⋙ G).asEquivalence.trans G.asEquivalence.symm).isEquivalence_functor

/-- If `F` and `F ⋙ G` are equivalence of categories, then `G` is also an equivalence. -/
lemma isEquivalence_of_comp_left {E : Type*} [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    [IsEquivalence F] [IsEquivalence (F ⋙ G)] : IsEquivalence G := by
  rw [isEquivalence_iff_of_iso (G.leftUnitor.symm ≪≫
    isoWhiskerRight F.asEquivalence.counitIso.symm G)]
  exact (F.asEquivalence.symm.trans (F ⋙ G).asEquivalence).isEquivalence_functor

end Functor

namespace Equivalence

instance essSurjInducedFunctor {C' : Type*} (e : C' ≃ D) : (inducedFunctor e).EssSurj where
  mem_essImage Y := ⟨e.symm Y, by simpa using ⟨default⟩⟩

noncomputable instance inducedFunctorOfEquiv {C' : Type*} (e : C' ≃ D) :
    IsEquivalence (inducedFunctor e) where

noncomputable instance fullyFaithfulToEssImage (F : C ⥤ D) [F.Full] [F.Faithful] :
    IsEquivalence F.toEssImage where

end Equivalence

/-- An equality of properties of objects of a category `C` induces an equivalence of the
respective induced full subcategories of `C`. -/
@[simps]
def ObjectProperty.fullSubcategoryCongr {P P' : ObjectProperty C} (h : P = P') :
    P.FullSubcategory ≌ P'.FullSubcategory where
  functor := ObjectProperty.ιOfLE h.le
  inverse := ObjectProperty.ιOfLE h.symm.le
  unitIso := Iso.refl _
  counitIso := Iso.refl _

namespace Iso

variable {E : Type u₃} [Category.{v₃} E] {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E}

/-- Construct an isomorphism `F ⋙ H.inverse ≅ G` from an isomorphism `F ≅ G ⋙ H.functor`. -/
@[simps!]
def compInverseIso {H : D ≌ E} (i : F ≅ G ⋙ H.functor) : F ⋙ H.inverse ≅ G :=
  isoWhiskerRight i H.inverse ≪≫
    associator G _ H.inverse ≪≫ isoWhiskerLeft G H.unitIso.symm ≪≫ G.rightUnitor

/-- Construct an isomorphism `G ≅ F ⋙ H.inverse` from an isomorphism `G ⋙ H.functor ≅ F`. -/
@[simps!]
def isoCompInverse {H : D ≌ E} (i : G ⋙ H.functor ≅ F) : G ≅ F ⋙ H.inverse :=
  G.rightUnitor.symm ≪≫ isoWhiskerLeft G H.unitIso ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight i H.inverse

/-- Construct an isomorphism `G.inverse ⋙ F ≅ H` from an isomorphism `F ≅ G.functor ⋙ H`. -/
@[simps!]
def inverseCompIso {G : C ≌ D} (i : F ≅ G.functor ⋙ H) : G.inverse ⋙ F ≅ H :=
  isoWhiskerLeft G.inverse i ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight G.counitIso H ≪≫ H.leftUnitor

/-- Construct an isomorphism `H ≅ G.inverse ⋙ F` from an isomorphism `G.functor ⋙ H ≅ F`. -/
@[simps!]
def isoInverseComp {G : C ≌ D} (i : G.functor ⋙ H ≅ F) : H ≅ G.inverse ⋙ F :=
  H.leftUnitor.symm ≪≫ isoWhiskerRight G.counitIso.symm H ≪≫ associator _ _ _
    ≪≫ isoWhiskerLeft G.inverse i

/-- As a special case, given two equivalences `G` and `G'` between the same categories,
construct an isomorphism `G.inverse ≅ G.inverse` from an isomorphism `G.functor ≅ G.functor`. -/
@[simps!]
def isoInverseOfIsoFunctor {G G' : C ≌ D} (i : G.functor ≅ G'.functor) : G.inverse ≅ G'.inverse :=
  isoCompInverse ((isoWhiskerLeft G.inverse i).symm ≪≫ G.counitIso) ≪≫ leftUnitor G'.inverse

/-- As a special case, given two equivalences `G` and `G'` between the same categories,
construct an isomorphism `G.functor ≅ G.functor` from an isomorphism `G.inverse ≅ G.inverse`. -/
@[simps!]
def isoFunctorOfIsoInverse {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse) : G.functor ≅ G'.functor :=
  isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

/-- Sanity check: `isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i)` is just `i`. -/
@[simp]
lemma isoFunctorOfIsoInverse_isoInverseOfIsoFunctor {G G' : C ≌ D} (i : G.functor ≅ G'.functor) :
    isoFunctorOfIsoInverse (isoInverseOfIsoFunctor i) = i := by
  ext X
  simp [← NatTrans.naturality]

@[simp]
lemma isoInverseOfIsoFunctor_isoFunctorOfIsoInverse {G G' : C ≌ D} (i : G.inverse ≅ G'.inverse) :
    isoInverseOfIsoFunctor (isoFunctorOfIsoInverse i) = i :=
  isoFunctorOfIsoInverse_isoInverseOfIsoFunctor (G := G.symm) (G' := G'.symm) i

end Iso

end CategoryTheory
