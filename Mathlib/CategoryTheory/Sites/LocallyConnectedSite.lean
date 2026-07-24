/-
Copyright (c) 2025 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.CategoryTheory.Limits.Sifted
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Locally connected sites

A site is called locally connected if all covering sieves in it are connected as subcategories
of the corresponding slice category. This notion is useful because it guarantees the existence of a
further left adjoint `π₀` of the constant sheaf functor, making sheaf topoi on locally connected
sites locally connected.

See https://ncatlab.org/nlab/show/locally+connected+site.

## Main definitions and results

* `J.IsLocallyConnectedSite`: typeclass stating that a site is locally connected.
* Every trivial site is locally connected.
* `isSheaf_const_obj`: on locally connected sites, every constant presheaf is a sheaf.
* `π₀ J`: the connected components functor on locally connected sites, sending each sheaf
  to the colimit of its underlying presheaf.
* `π₀ConstantSheafAdj`: the adjunction between `π₀ J` and the constant sheaf functor. This shows
  that sheaf topoi on locally connected sites are locally connected.
* `uniqueπ₀ObjOfIsRepresentable`: `π₀` sends representable sheaves to singleton types, i.e.
  all representable sheaves are connected.
* On connected locally connected sites `constantSheaf` is fully faithful and `π₀` preserves the
  terminal object, i.e. the terminal sheaf is connected.
  This means that the sheaf topos is connected.
* On cosifted locally connected sites, `π₀` preserves all finite products, i.e. the sheaf topos
  is strongly connected.

## TODO

* Define the site of connected open subsets of a topological space, prove that it is
  locally connected and prove that it is a dense sub-site of the site of opens if and only if the
  space is locally connected.
-/

universe w u v u' v'

@[expose] public section

open CategoryTheory Limits Sheaf Opposite GrothendieckTopology

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A locally connected site is a site with the property that every covering sieve is connected
as a full subcategory of the corresponding slice category. In particular, every covering sieve
is nonempty. -/
class GrothendieckTopology.IsLocallyConnectedSite where
  /-- Every covering sieve `S ∈ J X` is connected when interpreted as a full subcategory of the
  slice category `Over X`. -/
  isConnected_of_mem : ∀ {X}, ∀ S ∈ J X, IsConnected S.arrows.category

namespace GrothendieckTopology.IsLocallyConnectedSite

/-- Every category becomes a locally connected site with the trivial topology. -/
instance : (trivial C).IsLocallyConnectedSite where
  isConnected_of_mem _ hS := @isConnected_of_hasTerminal _ _ <|
    @hasLimitsOfShape_of_closedUnderLimits _ _ _ _ _
      ⟨fun _ _ ↦ trivial_covering.1 hS ▸ _root_.trivial⟩ _

variable [J.IsLocallyConnectedSite] {A : Type*} [Category* A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On locally connected sites, every constant presheaf is a sheaf. -/
lemma isSheaf_const_obj {X : A} : Presheaf.IsSheaf J ((Functor.const _).obj X) := by
  intro W Y S hS x hx
  let ⟨f, hf⟩ := (IsLocallyConnectedSite.isConnected_of_mem S hS).is_nonempty
  refine ⟨@x f.left f.hom hf, ?_, ?_⟩
  · intro Z g hg
    have := IsLocallyConnectedSite.isConnected_of_mem S hS
    simpa using constant_of_preserves_morphisms (J := S.arrows.category) (α := W ⟶ X)
      (fun f ↦ @x f.obj.left f.obj.hom f.property) (fun f g h ↦ by
        simpa [Functor.const] using hx (𝟙 _) h.hom.left f.property g.property) ⟨f, hf⟩ ⟨.mk g, hg⟩
  · intro x hx
    simp [← hx f.hom hf]

/-- For constant presheaves on locally connected sites, `toSheafify` is an isomorphism. -/
instance [HasWeakSheafify J A] {X : A} :
    IsIso (CategoryTheory.toSheafify J ((Functor.const _).obj X)) :=
  CategoryTheory.isIso_toSheafify J (isSheaf_const_obj J)

variable (A)

/-- The constant sheaf functor composed with the forgetful functor to presheaves is just the
constant presheaf functor. -/
noncomputable def constantSheafToPresheafIsoConst [HasWeakSheafify J A] :
    constantSheaf J A ⋙ sheafToPresheaf J A ≅ Functor.const _ :=
  .symm <| NatIso.ofComponents
    (fun X ↦ (asIso <| CategoryTheory.toSheafify J ((Functor.const _).obj X):))
      fun _ ↦ CategoryTheory.toSheafify_naturality _ _

instance [IsConnected C] [HasWeakSheafify J A] : (constantSheaf J A).Full :=
  .of_comp_faithful_iso (constantSheafToPresheafIsoConst J A)

instance [IsConnected C] [HasWeakSheafify J A] : (constantSheaf J A).Faithful :=
  .of_comp_iso (constantSheafToPresheafIsoConst J A)

/-- The connected components functor on sheaves of types on any local site, defined as taking
colimits of the underlying presheaves. -/
noncomputable def π₀ [HasColimitsOfShape Cᵒᵖ A] : Sheaf J A ⥤ A :=
  sheafToPresheaf J _ ⋙ colim

/-- The connected components functor on local sites is left adjoint to the constant sheaf
functor. -/
noncomputable def π₀ConstantSheafAdj [HasColimitsOfShape Cᵒᵖ A]
    [HasWeakSheafify J A] : π₀ J A ⊣ constantSheaf J A := by
  refine colimConstAdj.restrictFullyFaithful (fullyFaithfulSheafToPresheaf J _) (.id _) ?_ ?_
  · exact (Functor.rightUnitor _).symm
  · refine ((Functor.leftUnitor _).trans ((Functor.rightUnitor _).symm.trans ?_)).trans
      (Functor.associator _ _ _).symm
    refine @asIso _ _ _ _ (Functor.whiskerLeft _ (CategoryTheory.toSheafification _ _)) ?_
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun X ↦ CategoryTheory.isIso_toSheafify J <| isSheaf_const_obj J

instance [HasColimitsOfShape Cᵒᵖ A] [HasWeakSheafify J A] : (constantSheaf J A).IsRightAdjoint :=
  (π₀ConstantSheafAdj J A).isRightAdjoint

instance [HasColimitsOfShape Cᵒᵖ A] [HasWeakSheafify J A] : (π₀ J A).IsLeftAdjoint :=
  (π₀ConstantSheafAdj J A).isLeftAdjoint

/-- `π₀` sends representable sheaves to singleton types. In other words, every representable
sheaf is connected. -/
@[implicit_reducible]
noncomputable def uniqueπ₀ObjOfIsRepresentable (X : Sheaf J (Type max u v w))
    [X.obj.IsRepresentable] : Unique ((π₀ J _).obj X) :=
  Types.uniqueColimitOfIsRepresentable X.obj

/-- On connected locally connected sites, `Sheaf.π₀` preserves the terminal object. -/
instance [IsConnected C] [HasColimitsOfShape Cᵒᵖ A] [HasTerminal A] [HasWeakSheafify J A] :
    PreservesLimit (Functor.empty.{0} _) (π₀ J A) := by
  refine preservesTerminal_of_iso _ ?_
  refine ((π₀ J A).mapIso (asIso (terminalComparison (constantSheaf J A))).symm).trans ?_
  exact (asIso ((π₀ConstantSheafAdj J A).counit.app (⊤_ _)):)

/-- Sheaf topoi on cosifted locally connected sites are strongly connected, in the sense that
`π₀` preserves all finite products. -/
instance [IsSifted Cᵒᵖ] : PreservesFiniteProducts (π₀ J (Type max u v w)) :=
  comp_preservesFiniteProducts _ _

end GrothendieckTopology.IsLocallyConnectedSite

end CategoryTheory
