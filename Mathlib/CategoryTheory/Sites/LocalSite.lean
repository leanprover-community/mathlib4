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

Sheaves of types on any local site form a local topos (i.e. a topos whose global sections functor
has a fully faithful right adjoint), and a subcanonical site is local if and only if its topos of
sheaves of types is.

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

/-- The fibre of any presheaf `P : Cᵒᵖ ⥤ A` at `IsLocalSite.point J` is just `P` evaluated at
the terminal object. -/
noncomputable def IsLocalSite.pointPresheafFiberIso [LocallySmall.{w} C] [J.IsLocalSite]
    {A : Type u'} [Category.{v', u'} A] [HasColimitsOfSize.{w, w, v', u'} A] (P : Cᵒᵖ ⥤ A) :
    (IsLocalSite.point J).presheafFiber.obj P ≅ P.obj (op (⊤_ C)) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (colimitOfDiagramTerminal (Functor.Elements.isInitialOfCorepresentableBy
      <| shrinkCoyonedaCorepresentableBy <| op (⊤_ C)).op _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
lemma IsLocalSite.toPresheafFiber_pointPresheafFiberIso_hom [LocallySmall.{w} C] [J.IsLocalSite]
    {A : Type u'} [Category.{v', u'} A] [HasColimitsOfSize.{w, w, v', u'} A]
    {P : Cᵒᵖ ⥤ A} (X : C) (x : (point J).fiber.obj X) :
    (Point.toPresheafFiber (point J) _ x _) ≫ (pointPresheafFiberIso J P).hom =
      P.map (.op <| shrinkCoyonedaObjObjEquiv x) := by
  simp [Point.toPresheafFiber, pointPresheafFiberIso]
  rfl

@[reassoc (attr := simp)]
lemma IsLocalSite.pointPresheafFiberIso_naturality [LocallySmall.{w} C] [J.IsLocalSite]
    {A : Type u'} [Category.{v', u'} A] [HasColimitsOfSize.{w, w, v', u'} A]
    {P P' : Cᵒᵖ ⥤ A} (F : P ⟶ P') :
    (point J).presheafFiber.map F ≫ (pointPresheafFiberIso J P').hom =
      (pointPresheafFiberIso J P).hom ≫ F.app (op (⊤_ C)) := by
  cat_disch

/-- The presheaf fibre functor of `IsLocalSite.point J` is given by evaluation at the terminal
object. -/
noncomputable def IsLocalSite.pointPresheafFiberNatIso [LocallySmall.{w} C] [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [HasColimitsOfSize.{w, w, v', u'} A] :
    ((IsLocalSite.point J).presheafFiber : _ ⥤ A) ≅ (evaluation _ _).obj (op (⊤_ C)) :=
  NatIso.ofComponents (pointPresheafFiberIso J) fun F ↦ pointPresheafFiberIso_naturality J F

/-- The sheaf fibre functor of `IsLocalSite.point J` is the global sections functor. -/
noncomputable def IsLocalSite.pointSheafFiberIso [LocallySmall.{w} C] [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [HasColimitsOfSize.{w, w, v', u'} A]
    [HasWeakSheafify J A] : (IsLocalSite.point J).sheafFiber ≅ Γ J A :=
  ((sheafToPresheaf J A).isoWhiskerLeft (pointPresheafFiberNatIso J A)).trans
    (ΓNatIsoSheafSections J A terminalIsTerminal).symm

/-- The right adjoint to the global sections functor that exists over any local site. This is
implemented as the skyscraper functor associated to `IsLocalSite.point.{w} J`, but can be thought of
as taking any object `X : A` to the sheaf that sends each `Y : C` to the product over copies of `A`
indexed by the points `⊤_ C ⟶ Y` of `Y`.

Note this takes in an extra universe parameter `w` that does not appear in the output type
`A ⥤ Sheaf J A` but is required for the construction; it should always be given explicitly when
referring to this functor, as in e.g. `coconstantSheaf.{w} J A`. -/
noncomputable def IsLocalSite.coconstantSheaf [LocallySmall.{w} C] [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [HasProducts.{w} A] : A ⥤ Sheaf J A :=
  (point.{w} J).skyscraperSheafFunctor

/-- In particular, this construction works for sheaves of types. -/
noncomputable example [J.IsLocalSite] : Type max v w ⥤ Sheaf J (Type (max v w)) :=
  IsLocalSite.coconstantSheaf.{max v w} J (Type max v w)

variable [LocallySmall.{w} C] [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [HasColimitsOfSize.{w, w, v', u'} A]
    [HasProducts.{w} A] [HasWeakSheafify J A]

/-- On local sites, the global sections functor `Γ` is left-adjoint to the coconstant functor. -/
noncomputable def IsLocalSite.ΓCoconstantSheafAdj : Γ J A ⊣ coconstantSheaf.{w} J A :=
  (point.{w} J).skyscraperSheafAdjunction.ofNatIsoLeft (pointSheafFiberIso J A)

/-- On any locally `w`-small local site, the global sections functor to any category with colimits
and products of size `w` is a left adulljoint. A variant of this without the universe parameter `w`
is registered as an instance. -/
lemma IsLocalSite.Γ_isLeftAdjoint : (Γ J A).IsLeftAdjoint :=
  ⟨IsLocalSite.coconstantSheaf.{w} J A, ⟨IsLocalSite.ΓCoconstantSheafAdj J A⟩⟩

/-- On any local site with morphism types in `Type v`, the global sections functor to any category
with colimits and products of size `v` is a left adjoint. See `IsLocalSite.ΓIsLeftAdjoint` for a
version for `w`-locally small sites that can't be registered as an instance because of the extra
universe parameter `w`. -/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [HasColimitsOfSize.{v, v, v', u'} A]
    [HasProducts.{v} A] [HasWeakSheafify J A] : (Γ J A).IsLeftAdjoint :=
  IsLocalSite.Γ_isLeftAdjoint.{v} J A

instance : (IsLocalSite.coconstantSheaf.{w} J A).IsRightAdjoint :=
  ⟨Γ J A, ⟨IsLocalSite.ΓCoconstantSheafAdj J A⟩⟩

/-- The global sections of the coconstant sheaf on a type are naturally isomorphic to that type. -/
noncomputable def coconstantSheafΓNatIsoId :
    IsLocalSite.coconstantSheaf.{w} J A ⋙ Γ J A ≅ 𝟭 A := by
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
  (IsLocalSite.ΓCoconstantSheafAdj J A).fullyFaithfulROfCompIsoId (coconstantSheafΓNatIsoId J A)

instance : (IsLocalSite.coconstantSheaf.{w} J A).Full :=
  (fullyFaithfulCoconstantSheaf J A).full

instance : (IsLocalSite.coconstantSheaf.{w} J A).Faithful :=
  (fullyFaithfulCoconstantSheaf J A).faithful

/-- The adjoint triple `constantSheaf J A ⊣ Γ J A ⊣ coconstantSheaf J A` on any local site. -/
noncomputable abbrev IsLocalSite.constantΓCoconstantTriple :
    Adjunction.Triple (constantSheaf J A) (Γ J A) (coconstantSheaf.{w} J A) where
  adj₁ := constantSheafΓAdj J A
  adj₂ := ΓCoconstantSheafAdj J A

/-- On local sites, the constant sheaf functor is fully faithful. -/
noncomputable def fullyFaithfulConstantSheaf : (constantSheaf J A).FullyFaithful :=
  (IsLocalSite.constantΓCoconstantTriple J A).fullyFaithfulEquiv.symm <|
    fullyFaithfulCoconstantSheaf.{w} J A

/-- On any locally `w`-small local site, the constant sheaf functor from any category with colimits
and products of size `w` is full. A variant of this without the universe parameter `w`
is registered as an instance. -/
lemma IsLocalSite.constantSheaf_full : (constantSheaf J A).Full :=
  (fullyFaithfulConstantSheaf.{w} J A).full

/-- On any locally `w`-small local site, the constant sheaf functor from any category with colimits
and products of size `w` is faithful. A variant of this without the universe parameter `w`
is registered as an instance. -/
lemma IsLocalSite.constantSheaf_faithful : (constantSheaf J A).Faithful :=
  (fullyFaithfulConstantSheaf.{w} J A).faithful

/-- On any local site with morphism types in `Type v`, the constant sheaf functor from any category
with colimits and products of size `v` is full. See `IsLocalSite.constantSheaf_full` for a
version for `w`-locally small sites that can't be registered as an instance because of the extra
universe parameter `w`. -/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [HasColimitsOfSize.{v, v, v', u'} A]
    [HasProducts.{v} A] [HasWeakSheafify J A] : (constantSheaf J A).Full :=
  IsLocalSite.constantSheaf_full.{v} J A

/-- On any local site with morphism types in `Type v`, the constant sheaf functor from any category
with colimits and products of size `v` is faithful. See `IsLocalSite.constantSheaf_faithful` for a
version for `w`-locally small sites that can't be registered as an instance because of the extra
universe parameter `w`. -/
instance {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.IsLocalSite]
    (A : Type u') [Category.{v', u'} A] [HasColimitsOfSize.{v, v, v', u'} A]
    [HasProducts.{v} A] [HasWeakSheafify J A] : (constantSheaf J A).Faithful :=
  IsLocalSite.constantSheaf_faithful.{v} J A

end CategoryTheory
