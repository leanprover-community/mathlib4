/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Adjunction.Triple
public import Mathlib.CategoryTheory.Limits.Elements
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Local sites
A site (C,J) is called local if it has a terminal object whose only covering sieve is trivial -
this makes it possible to define coconstant sheaves on it, giving its sheaf topos the structure
of a local topos. This makes them an important stepping stone to cohesive sites.

See https://ncatlab.org/nlab/show/local+site.

## Main definitions / results
* `J.IsLocalSite`: typeclass stating that (C,J) is a local site.
* `IsLocalSite.point J`: the canonical point of any local site, whose fibre functor is given by
  the coyoneda embedding of the terminal object and extends to the global sections functors on
  presheaves and sheaves.
* `coconstantSheaf J A`: the coconstant sheaf functor `A ⥤ Sheaf J A` for any local site (C,J) and
  sufficiently nice target category `A`, defined as the skyscraper sheaf functor of the canonical
  point.
* `ΓCoconstantSheafAdj J A`: the adjunction between the global sections functor `Γ J A` and
  `coconstantSheaf J A`.
* `fullyFaithfulCoconstantSheaf`: `coconstantSheaf` is fully faithful.
* `fullyFaithfulConstantSheaf`: on local sites, the constant sheaf functor is fully faithful.

All together this shows that for local sites `Sheaf J (Type max u v w)` forms a local topos, but
since we don't yet have local topoi this can't be stated yet.
-/

universe w u v u' v'

@[expose] public section

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A local site is a site that has a terminal object with only a single covering sieve. -/
class GrothendieckTopology.IsLocalSite extends HasTerminal C where
  /-- The only covering sieve of the terminal object is the trivial sieve. -/
  eq_top_of_mem : ∀ S ∈ J (⊤_ C), S = ⊤

/-- On a local site, every covering sieve contains every morphism from the terminal object. -/
lemma IsLocalSite.from_terminal_mem_of_mem [J.IsLocalSite] {X : C} (f : ⊤_ C ⟶ X) {S : Sieve X}
    (hS : S ∈ J X) : S.arrows f :=
  (S.mem_iff_pullback_eq_top f).2 <| IsLocalSite.eq_top_of_mem _ <| J.pullback_stable f hS

/-- Every category with a terminal object becomes a local site with the trivial topology. -/
instance {C : Type u} [Category.{v} C] [HasTerminal C] : (trivial C).IsLocalSite where
  eq_top_of_mem _ := trivial_covering.1

/-- Every local site has a canonical point, given as a fibre functor by the coyoneda embedding of
the terminal object `⊤_ C`. -/
noncomputable def IsLocalSite.point [LocallySmall.{w} C] [J.IsLocalSite] : Point.{w} J where
  fiber := shrinkCoyoneda.obj (op (⊤_ C))
  jointly_surjective := fun R hR x ↦
    ⟨(⊤_ C), shrinkCoyonedaObjObjEquiv x,
      (IsLocalSite.from_terminal_mem_of_mem J (shrinkCoyonedaObjObjEquiv x) hR),
          shrinkCoyonedaObjObjEquiv.symm (𝟙 _), by
        rw [shrinkCoyoneda_obj_map_shrinkCoyonedaObjObjEquiv_symm]
        simp⟩

lemma shrinkCoyoneda_obj_map [LocallySmall.{w} C]
    {X : Cᵒᵖ} {Y Y' : C} (g : Y ⟶ Y') (f : (shrinkCoyoneda.obj X).obj Y) :
    (shrinkCoyoneda.obj _).map g f =
      shrinkCoyonedaObjObjEquiv.symm (shrinkCoyonedaObjObjEquiv f ≫ g) :=
  rfl

/-- The canonical initial object of `(shrinkCoyoneda.{w}.obj (op X)).Elements`, given
by `𝟙 X : X ⟶ X`. -/
noncomputable def shrinkCoyonedaElementsInitial [LocallySmall.{w} C] (X : C) :
  (shrinkCoyoneda.{w}.obj (op X)).Elements :=
    ⟨X, shrinkCoyonedaObjObjEquiv.symm (𝟙 X)⟩

set_option backward.isDefEq.respectTransparency false in
/-- `shrinkCoyonedaElementsInitial X` is indeed initial. -/
noncomputable def shrinkCoyonedaElementsInitialIsInitial [LocallySmall.{w} C] (X : C) :
    IsInitial (shrinkCoyonedaElementsInitial X) where
  desc s := ⟨shrinkCoyonedaObjObjEquiv s.pt.snd, by
    simp only [asEmptyCocone, shrinkCoyonedaElementsInitial]
    rw [← shrinkCoyonedaObjObjEquiv_symm_comp]
    simp⟩
  uniq := by
    intro s ⟨(f : X ⟶ _), hf⟩ _
    ext1
    simp only [shrinkCoyoneda_obj_map, asEmptyCocone, shrinkCoyonedaElementsInitial,
      Equiv.apply_symm_apply, Category.id_comp] at hf
    exact (Equiv.symm_apply_eq _).1 hf

set_option backward.isDefEq.respectTransparency false in
/-- The fibre of any presheaf `P : Cᵒᵖ ⥤ A` at `IsLocalSite.point J` is just `P` evaluated at
the terminal object. -/
noncomputable def IsLocalSite.pointPresheafFiberIso [LocallySmall.{w} C] [J.IsLocalSite]
    {A : Type u'} [Category.{v', u'} A] [Limits.HasColimitsOfSize.{w, w, v', u'} A] (P : Cᵒᵖ ⥤ A) :
    (IsLocalSite.point J).presheafFiber.obj P ≅ P.obj (op (⊤_ C)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (shrinkCoyonedaElementsInitialIsInitial (⊤_ C)).op _)

set_option backward.isDefEq.respectTransparency false in
lemma IsColimit.map_comp_coconePointUniqueUpToIso {J : Type*} [Category* J] {F G : J ⥤ C}
    {s : Cocone F} {t t' : Cocone G} (hs : IsColimit s) (ht : IsColimit t)
    (ht' : IsColimit t') (α : F ⟶ G) :
    hs.map t α ≫ (ht.coconePointUniqueUpToIso ht').hom = hs.map t' α :=
  hs.uniq (((Cocone.precompose α).obj t')) _ fun i ↦ by simp

set_option backward.isDefEq.respectTransparency false in
lemma IsColimit.coconePointUniqueUpToIso_comp_map {J : Type*} [Category* J] {F G : J ⥤ C}
    {s' s : Cocone F} (hs' : IsColimit s') (hs : IsColimit s) (t : Cocone G) (α : F ⟶ G) :
    (hs'.coconePointUniqueUpToIso hs).hom ≫ hs.map t α = hs'.map t α :=
  hs'.uniq (((Cocone.precompose α).obj t)) _ fun i ↦ by simp

lemma IsColimit.coconePointUniqueUpToIso_naturality {J : Type*} [Category* J] {F G : J ⥤ C}
    {s s' : Cocone F} {t t' : Cocone G} (hs : IsColimit s) (hs' : IsColimit s') (ht : IsColimit t)
    (ht' : IsColimit t') (α : F ⟶ G) :
    hs.map t α ≫ (ht.coconePointUniqueUpToIso ht').hom =
      (hs.coconePointUniqueUpToIso hs').hom ≫ hs'.map t' α := by
  rw [map_comp_coconePointUniqueUpToIso, coconePointUniqueUpToIso_comp_map]

set_option backward.isDefEq.respectTransparency false in
lemma IsLocalSite.pointPresheafFiberIso_naturality [LocallySmall.{w} C] [J.IsLocalSite]
    {A : Type u'} [Category.{v', u'} A] [Limits.HasColimitsOfSize.{w, w, v', u'} A]
    {P P' : Cᵒᵖ ⥤ A} (F : P ⟶ P') :
    (point J).presheafFiber.map F ≫ (pointPresheafFiberIso J P').hom =
      (pointPresheafFiberIso J P).hom ≫ F.app (op (⊤_ C)) := by
  refine (IsColimit.coconePointUniqueUpToIso_naturality _
    (colimitOfDiagramTerminal (shrinkCoyonedaElementsInitialIsInitial (⊤_ C)).op _) _ _
      (((CategoryOfElements.π (shrinkCoyoneda.{w}.obj (op (⊤_ C)))).op.whiskerLeft F))).trans ?_
  congr
  simp only [IsColimit.map, colimitOfDiagramTerminal, Cocone.precompose_obj_ι, NatTrans.comp_app,
    Functor.whiskerLeft_app, coconeOfDiagramTerminal_ι_app, IsTerminal.from_self, Functor.map_id]
  exact Category.comp_id _

/-- The presheaf fibre functor of `IsLocalSite.point J` is given by evaluation at the terminal
object. -/
noncomputable def IsLocalSite.pointPresheafFiberNatIso [LocallySmall.{w} C] [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [Limits.HasColimitsOfSize.{w, w, v', u'} A] :
    ((IsLocalSite.point J).presheafFiber : _ ⥤ A) ≅ (evaluation _ _).obj (op (⊤_ C)) :=
  NatIso.ofComponents (pointPresheafFiberIso J) fun F ↦ pointPresheafFiberIso_naturality J F

/-- The sheaf fibre functor of `IsLocalSite.point J` is the global sections functor. -/
noncomputable def IsLocalSite.pointSheafFiberIso [LocallySmall.{w} C] [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [Limits.HasColimitsOfSize.{w, w, v', u'} A]
    [HasWeakSheafify J A] : (IsLocalSite.point J).sheafFiber ≅ Γ J A :=
  ((sheafToPresheaf J A).isoWhiskerLeft (pointPresheafFiberNatIso J A)).trans
    (ΓNatIsoSheafSections J A terminalIsTerminal).symm

/-- The right adjoint to the global sections functor that exists over any local site. This is
implemented as the skyscraper functor associated to `IsLocalSite.point.{w} J`, but can be thought of
as taking any object `X : A` to the sheaf that sends each `Y : C` to the product over copies of `A`
indexed by the points `⊤_ C ⟶ Y` of `Y`. -/
noncomputable def IsLocalSite.coconstantSheaf [LocallySmall.{w} C] [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [Limits.HasColimitsOfSize.{w, w, v', u'} A]
    [HasProducts.{w} A] : A ⥤ Sheaf J A :=
  (point.{w} J).skyscraperSheafFunctor

noncomputable example [J.IsLocalSite] : Type max v w ⥤ Sheaf J (Type (max v w)) :=
  IsLocalSite.coconstantSheaf.{max v w} J (Type max v w)

variable [LocallySmall.{w} C] [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [Limits.HasColimitsOfSize.{w, w, v', u'} A]
    [HasProducts.{w} A] [HasWeakSheafify J A]

/-- On local sites, the global sections functor `Γ` is left-adjoint to the coconstant functor. -/
noncomputable def IsLocalSite.ΓCoconstantSheafAdj' : Γ J A ⊣ coconstantSheaf J A :=
  (point.{w} J).skyscraperSheafAdjunction.ofNatIsoLeft (pointSheafFiberIso J A)

instance : (Γ J A).IsLeftAdjoint :=
  ⟨IsLocalSite.coconstantSheaf.{w} J A, ⟨IsLocalSite.ΓCoconstantSheafAdj' J A⟩⟩

instance : (IsLocalSite.coconstantSheaf.{w} J A).IsRightAdjoint :=
  ⟨Γ J A, ⟨IsLocalSite.ΓCoconstantSheafAdj' J A⟩⟩

/-- The global sections of the coconstant sheaf on a type are naturally isomorphic to that type. -/
noncomputable def coconstantSheafΓNatIsoId' :
    IsLocalSite.coconstantSheaf J A ⋙ Γ J A ≅ 𝟭 A := by
  refine (Functor.isoWhiskerLeft _ (ΓNatIsoSheafSections J _ terminalIsTerminal)).trans ?_
  refine NatIso.ofComponents (fun X ↦ @productUniqueIso
    (((IsLocalSite.point J).fiber.obj (⊤_ C))) _ _ (equivShrink (⊤_ C ⟶ ⊤_ C)).symm.unique _) ?_
  intro X Y f
  simp only [IsLocalSite.coconstantSheaf, Point.skyscraperSheafFunctor,
    Point.skyscraperPresheafFunctor, Functor.comp, Functor.id_obj, Functor.flip_obj_map,
    ObjectProperty.ι_obj, ObjectProperty.ι_map, Functor.flip_map_app, piFunctor_map_app,
    productUniqueIso_hom, Functor.id_map]
  exact Pi.map_π _ _

/-- `coconstantSheaf` is fully faithful. -/
noncomputable def fullyFaithfulCoconstantSheaf :
    (IsLocalSite.coconstantSheaf.{w} J A).FullyFaithful :=
  (IsLocalSite.ΓCoconstantSheafAdj' J A).fullyFaithfulROfCompIsoId (coconstantSheafΓNatIsoId' J A)

instance : (IsLocalSite.coconstantSheaf.{w} J A).Full :=
  (fullyFaithfulCoconstantSheaf J A).full

instance : (IsLocalSite.coconstantSheaf.{w} J A).Faithful :=
  (fullyFaithfulCoconstantSheaf J A).faithful

/-- The adjoint triple `constantSheaf J A ⊣ Γ J A ⊣ coconstantSheaf J A` on any local site. -/
noncomputable abbrev IsLocalSite.constantΓCoconstantTriple :
    Adjunction.Triple (constantSheaf J A) (Γ J A) (coconstantSheaf.{w} J A) where
  adj₁ := constantSheafΓAdj J A
  adj₂ := ΓCoconstantSheafAdj' J A

/-- On local sites, the constant sheaf functor is fully faithful. -/
noncomputable def fullyFaithfulConstantSheaf : (constantSheaf J A).FullyFaithful :=
  (IsLocalSite.constantΓCoconstantTriple J A).fullyFaithfulEquiv.symm <|
    fullyFaithfulCoconstantSheaf.{w} J A

instance : (constantSheaf J A).Full :=
  (fullyFaithfulConstantSheaf.{w} J A).full

instance : (constantSheaf J A).Faithful :=
  (fullyFaithfulConstantSheaf.{w} J A).faithful

end CategoryTheory
