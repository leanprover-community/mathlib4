/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Quasicoherent sheaves

A sheaf of modules is quasi-coherent if it admits locally a presentation as the
cokernel of a morphism between coproducts of copies of the sheaf of rings.
When these coproducts are finite, we say that the sheaf is of finite presentation.

## References

* https://stacks.math.columbia.edu/tag/01BD

-/

@[expose] public section

universe w u v₁ v₂ u₁ u₂

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

namespace SheafOfModules

section

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- A global presentation of a sheaf of modules `M` consists of a family `generators.s`
of sections `s` which generate `M`, and a family of sections which generate
the kernel of the morphism `generators.π : free (generators.I) ⟶ M`. -/
structure Presentation (M : SheafOfModules.{u} R) where
  /-- generators -/
  generators : M.GeneratingSections
  /-- relations -/
  relations : (kernel generators.π).GeneratingSections

/-- A global presentation of a sheaf of module if finite if the type
of generators and relations are finite. -/
class Presentation.IsFinite {M : SheafOfModules.{u} R} (p : M.Presentation) : Prop where
  isFiniteType_generators : p.generators.IsFiniteType := by infer_instance
  finite_relations : Finite p.relations.I := by infer_instance

attribute [instance] Presentation.IsFinite.isFiniteType_generators
  Presentation.IsFinite.finite_relations

end

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] {ι σ : Type u}

/-- Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain
generators of `Presentation M`. -/
@[simps! I s]
def generatorsOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) : M.GeneratingSections where
  I := σ
  s := M.freeHomEquiv g
  epi := by simpa using epi_of_isColimit_cofork H'

@[simp]
theorem generatorsOfIsCokernelFree_π {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (generatorsOfIsCokernelFree f g H H').π = g := M.freeHomEquiv.symm_apply_apply g

set_option backward.isDefEq.respectTransparency false in
/-- Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain
relations of `Presentation M`. -/
@[simps! I s]
def relationsOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (kernel (generatorsOfIsCokernelFree f g H H').π).GeneratingSections where
  I := ι
  s := (kernel (generatorsOfIsCokernelFree f g H H').π).freeHomEquiv <| kernel.lift
    (generatorsOfIsCokernelFree f g H H').π f (by simp [H])
  epi := by
    let h : cokernel f ≅ M := (H'.coconePointUniqueUpToIso (colimit.isColimit _)).symm
    let h' : Abelian.image f ≅ kernel (generatorsOfIsCokernelFree f g H H').π :=
      kernel.mapIso (cokernel.π f) (generatorsOfIsCokernelFree f g H H').π
        (Iso.refl _) h (by simp [h])
    have comp_aux : Abelian.factorThruImage f ≫ h'.hom =
      (kernel.lift (generatorsOfIsCokernelFree f g H H').π f (by simp [H])) :=
        equalizer.hom_ext <| by simp [h']
    rw [← comp_aux, Equiv.symm_apply_apply]
    infer_instance

/-- Given two morphisms of sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, we obtain a
`Presentation M`. -/
@[simps]
def presentationOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) : Presentation M where
  generators := generatorsOfIsCokernelFree f g H H'
  relations := relationsOfIsCokernelFree f g H H'

/-- Given a sheaf of `R`-modules `M` and a `Presentation M`, there is two morphism of
sheaves of `R`-modules `f : free ι ⟶ free σ` and `g : free σ ⟶ M` satisfying `H : f ≫ g = 0`
and `IsColimit (CokernelCofork.ofπ g H)`. -/
def Presentation.isColimit {M : SheafOfModules.{u} R} (P : Presentation M) :
    IsColimit (CokernelCofork.ofπ (f := (freeHomEquiv _).symm P.relations.s ≫ (kernel.ι _))
      P.generators.π (by simp)) :=
  isCokernelEpiComp (c := CokernelCofork.ofπ _ (kernel.condition P.generators.π))
      (Abelian.epiIsCokernelOfKernel _ <| limit.isLimit _) _ rfl

/-- Mapping a presentation under an isomorphism. -/
@[simps]
noncomputable def Presentation.of_isIso {M N : SheafOfModules.{u} R} (f : M ⟶ N) [IsIso f]
    (σ : M.Presentation) : N.Presentation where
  generators := σ.generators.ofEpi f
  relations := σ.relations.ofEpi ((kernelCompMono _ f).symm.trans <| eqToIso (by simp)).hom

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable {M : SheafOfModules.{u} R} (P : Presentation M)
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
  (η : F.obj (unit R) ≅ unit S)

-- `preservesColimitsOfSize_shrink` is not a global instance because it loops indefinitely.
-- But here it is fine as an instance since the universe `u` is inferrable from the type of `F`.
local instance : PreservesColimitsOfSize.{0, 0} F := preservesColimitsOfSize_shrink _

/-- Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` preserves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we will obtain
relations of `Presentation (F.obj M)`. -/
def Presentation.mapRelations : free P.relations.I (R := S) ⟶ free P.generators.I :=
  (mapFree F η P.relations.I).inv ≫ F.map ((freeHomEquiv _).symm P.relations.s) ≫
    F.map (kernel.ι _) ≫ (mapFree F η P.generators.I).hom

/-- Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` preserves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we will obtain
generators of `Presentation (F.obj M)`. -/
def Presentation.mapGenerators : free P.generators.I ⟶ F.obj M :=
  (mapFree F η P.generators.I).inv ≫ F.map (P.generators.π)

@[reassoc (attr := simp)]
theorem Presentation.mapRelations_mapGenerators :
    P.mapRelations F η ≫ P.mapGenerators F η = 0 := by
  simp only [mapRelations, mapGenerators, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]

/-- Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` preserves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we will get a
`Presentation (F.obj M)`. -/
@[simps! generators_I relations_I]
def Presentation.map : Presentation (F.obj M) :=
  presentationOfIsCokernelFree (P.mapRelations F η) (P.mapGenerators F η)
    (P.mapRelations_mapGenerators F η) <| by
    refine IsColimit.equivOfNatIsoOfIso (parallelPairIsoMk (mapFree F η _) (mapFree F η _)
      (by simp [Presentation.mapRelations]) (by simp)) _ _ ?_ (isColimitOfPreserves F P.isColimit)
    exact (Cocone.ext (Iso.refl _) <| by rintro (_ | _)
      <;> simp [Presentation.mapRelations, Presentation.mapGenerators, ← Functor.map_comp])

theorem Presentation.map_π_eq :
    (P.map F η).generators.π = (mapFree F η _).inv ≫ F.map (P.generators.π) :=
  (F.obj M).freeHomEquiv.symm_apply_eq.mpr rfl

end

section

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- This structure contains the data of a family of objects `X i` which cover
the terminal object, and of a presentation of `M.over (X i)` for all `i`. -/
structure QuasicoherentData (M : SheafOfModules.{u} R) where
  /-- the index type of the covering -/
  I : Type w
  /-- a family of objects which cover the terminal object -/
  X : I → C
  coversTop : J.CoversTop X
  /-- a presentation of the sheaf of modules `M.over (X i)` for any `i : I` -/
  presentation (i : I) : (M.over (X i)).Presentation

namespace QuasicoherentData

/-- Shrink the indexing type of `QuasicoherentData` into the universe of the site. -/
noncomputable
def shrink {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    QuasicoherentData.{u₁} M where
  I := Set.range q.X
  X i := q.X i.2.choose
  coversTop X := by
    refine J.superset_covering (fun Y hY H ↦ ?_) (q.coversTop X)
    obtain ⟨i, ⟨hi⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp H
    exact ⟨⟨_, i, rfl⟩, ⟨hi ≫ eqToHom (by grind)⟩⟩
  presentation i := q.presentation i.2.choose

/-- If `M` is quasicoherent, it is locally generated by sections. -/
@[simps]
def localGeneratorsData {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    M.LocalGeneratorsData where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i := (q.presentation i).generators

/-- A (local) presentation of a sheaf of module `M` is a finite presentation
if each given presentation of `M.over (X i)` is a finite presentation. -/
class IsFinitePresentation {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) : Prop where
  isFinite_presentation (i : q.I) : (q.presentation i).IsFinite := by infer_instance

attribute [instance] IsFinitePresentation.isFinite_presentation

set_option backward.isDefEq.respectTransparency false in
instance {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) [q.IsFinitePresentation] :
    q.localGeneratorsData.IsFiniteType where
  isFiniteType := by dsimp; infer_instance

end QuasicoherentData

/-- A sheaf of modules is quasi-coherent if it is locally the cokernel of a
morphism between coproducts of copies of the sheaf of rings. -/
class IsQuasicoherent (M : SheafOfModules.{u} R) : Prop where
  nonempty_quasicoherentData : Nonempty (QuasicoherentData.{u₁} M) := by infer_instance

lemma QuasicoherentData.isQuasicoherent {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) :
    M.IsQuasicoherent := ⟨⟨q.shrink⟩⟩

variable (R) in
@[inherit_doc IsQuasicoherent]
abbrev isQuasicoherent : ObjectProperty (SheafOfModules.{u} R) :=
  IsQuasicoherent

/-- A sheaf of modules is finitely presented if it is locally the cokernel of a
morphism between coproducts of finitely many copies of the sheaf of rings. -/
class IsFinitePresentation (M : SheafOfModules.{u} R) : Prop where
  exists_quasicoherentData (M) :
    ∃ (σ : QuasicoherentData.{u₁} M), σ.IsFinitePresentation

variable (R) in
@[inherit_doc IsFinitePresentation]
abbrev isFinitePresentation : ObjectProperty (SheafOfModules.{u} R) :=
  IsFinitePresentation

instance (M : SheafOfModules.{u} R) [M.IsFinitePresentation] :
    M.IsQuasicoherent where
  nonempty_quasicoherentData :=
    ⟨(IsFinitePresentation.exists_quasicoherentData M).choose⟩

instance (M : SheafOfModules.{u} R) [M.IsFinitePresentation] :
    M.IsFiniteType where
  exists_localGeneratorsData := by
    obtain ⟨σ, _⟩ := IsFinitePresentation.exists_quasicoherentData M
    exact ⟨σ.localGeneratorsData, inferInstance⟩

/-- A choice of local presentations when `M` is a sheaf of modules of finite presentation. -/
@[deprecated "Use the lemma `IsFinitePresentation.exists_quasicoherentData` instead."
  (since := "2025-10-28")]
noncomputable def quasicoherentDataOfIsFinitePresentation
    (M : SheafOfModules.{u} R) [M.IsFinitePresentation] : M.QuasicoherentData :=
  (IsFinitePresentation.exists_quasicoherentData M).choose

section map

set_option backward.isDefEq.respectTransparency false

variable {J : GrothendieckTopology C}
  {R : Sheaf J RingCat} [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] {C' : Type u₂} [Category.{v₂, u₂} C']
  {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}} [HasSheafify J' AddCommGrpCat.{u}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J'.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  {M : SheafOfModules.{u} R}
  (P : M.Presentation) (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
  [PreservesColimitsOfSize.{u, u} F]
  (η : F.obj (unit R) ≅ unit S)
  [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat]
  [∀ (X : C'), (J'.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ (X : C'), HasSheafify (J'.over X) AddCommGrpCat]
  [∀ (X : C'), (J'.over X).WEqualsLocallyBijective AddCommGrpCat]

noncomputable
def QuasicoherentData.pushforward
    (G : C' ⥤ C) [G.IsContinuous J' J] [G.IsCocontinuous J' J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J' J).obj R)
    [∀ (X : C') (Y : C) (f : G.obj X ⟶ Y),
      (Over.post G ⋙ Over.map f).IsContinuous (J'.over X) (J.over Y)]
    (h : ∀ (X : C') (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (J'.over X) J').map φ))
    (η : (pushforward φ).obj (unit R) ≅ unit S)
    {M : SheafOfModules.{u} R} (P : M.QuasicoherentData) :
    QuasicoherentData ((pushforward φ).obj M) where
  I := Σ (X : C') (i : P.I), G.obj X ⟶ P.X i
  X i := i.1
  coversTop := by
    intro Y
    refine J'.superset_covering ?_ <| G.cover_lift J' _ (P.coversTop (G.obj Y))
    intro Z g ⟨i, ⟨v⟩⟩
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
  presentation i := by
    letI overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
      SheafOfModules.pushforward (𝟙 _)
    letI G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
    letI ψ : S.over i.1 ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (J'.over i.1) (J.over (P.X i.2.1))).obj
          (R.over (P.X i.2.1)) :=
      ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (J'.over i.1) J').map φ
    letI e : (SheafOfModules.pushforward ψ).obj (unit (R.over (P.X i.snd.fst))) ≅
      unit (S.over i.fst) := overS.mapIso η
    haveI : PreservesColimitsOfSize.{u, u, _} (SheafOfModules.pushforward ψ) := h _ _ _
    exact (P.presentation i.2.1).map (SheafOfModules.pushforward ψ) e

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective
AddCommGrpCat] [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat] in
lemma isQuasicoherent_pushforward
    (G : C' ⥤ C) [G.IsContinuous J' J] [G.IsCocontinuous J' J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J' J).obj R)
    [∀ (X : C') (Y : C) (f : G.obj X ⟶ Y),
      (Over.post G ⋙ Over.map f).IsContinuous (J'.over X) (J.over Y)]
    (h : ∀ (X : C') (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (J'.over X) J').map φ))
    (η : (pushforward φ).obj (unit R) ≅ unit S)
    {M : SheafOfModules.{u} R} [IsQuasicoherent M] :
    IsQuasicoherent ((pushforward φ).obj M) :=
  IsQuasicoherent.nonempty_quasicoherentData.some.pushforward G φ h η |>.isQuasicoherent

@[simp]
lemma _root_.CategoryTheory.PreOneHypercover.map_toPreZeroHypercover
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X : C} (E : PreOneHypercover X) :
    (E.map F).toPreZeroHypercover = E.toPreZeroHypercover.map F :=
  rfl

lemma _root_.CategoryTheory.PreZeroHypercover.sieve₀_map
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {S : C}
    (E : PreZeroHypercover.{w} S) :
    (E.map F).sieve₀ = Sieve.functorPushforward _ E.sieve₀ := by
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← PreZeroHypercover.presieve₀,
    PreZeroHypercover.presieve₀_map, Sieve.generate_map_eq_functorPushforward]

lemma _root_.CategoryTheory.PreOneHypercover.sieve₀_map
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {S : C}
    (E : PreOneHypercover.{w} S) :
    (E.map F).sieve₀ = Sieve.functorPushforward _ E.sieve₀ := by
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← PreZeroHypercover.presieve₀,
    PreOneHypercover.map_toPreZeroHypercover, PreZeroHypercover.presieve₀_map,
    Sieve.generate_map_eq_functorPushforward]

instance {C : Type*} [Category* C] (X : C) (J : GrothendieckTopology C) :
    Functor.PreservesOneHypercovers.{w} (Over.forget X) (J.over X) J := by
  intro U E
  refine ⟨?_, ?_⟩
  · simpa [CategoryTheory.PreZeroHypercover.sieve₀_map] using E.mem₀
  · intro i₁ i₂ W p₁ p₂ h
    let W' : Over X := Over.mk (p₁ ≫ (E.X i₁).hom)
    let p₁' : W' ⟶ E.X i₁ := Over.homMk p₁ rfl
    let p₂' : W' ⟶ E.X i₂ := Over.homMk p₂ <| by
      dsimp at h
      simp only [Over.forget_obj, Over.mk_left, Functor.const_obj_obj, Over.mk_hom, W']
      rw [← Over.w (E.f i₂), ← reassoc_of% h]
      simp
    have := E.mem₁ _ _ p₁' p₂' (by ext; exact h)
    rw [J.mem_over_iff] at this
    refine J.superset_covering ?_ this
    intro U g hg
    rw [Sieve.overEquiv_iff] at hg
    obtain ⟨j, u, h₁, h₂⟩ := hg
    exact ⟨j, u.left, congr($(h₁).left), congr($(h₂).left)⟩

instance {C : Type*} [Category* C] {A : Type*} [Category* A]
    (J : GrothendieckTopology C) {F G : Sheaf J A} (f : F ⟶ G) [IsIso f] :
    IsIso f.hom := by
  refine ⟨(inv f).hom, ?_, ?_⟩
  · simp [← ObjectProperty.FullSubcategory.comp_hom, IsIso.hom_inv_id]
  · simp [← ObjectProperty.FullSubcategory.comp_hom, IsIso.inv_hom_id]

@[simp]
lemma _root_.CategoryTheory.Sheaf.inv_hom {C : Type*} [Category* C]
    {A : Type*} [Category* A]
    (J : GrothendieckTopology C) {F G : Sheaf J A} (f : F ⟶ G) [IsIso f] :
    (inv f).hom = inv f.hom := by
  apply IsIso.eq_inv_of_inv_hom_id
  simp [← ObjectProperty.FullSubcategory.comp_hom]

lemma isLeftAdjoint_pushforward_of_isIso (G : C' ⥤ C) [G.IsContinuous J' J] [G.IsCocontinuous J' J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J' J).obj R) [IsIso φ]
    [G.IsLeftAdjoint] :
    (pushforward.{u} φ).IsLeftAdjoint := by
  let adj := Adjunction.ofIsLeftAdjoint G
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u}) J' J
  let ψ : R ⟶ (G.rightAdjoint.sheafPushforwardContinuous RingCat.{u} J J').obj S :=
     shAdj.unit.app R ≫ (G.rightAdjoint.sheafPushforwardContinuous _ _ _).map (inv φ)
  let adj := by
    refine SheafOfModules.pushforwardPushforwardAdj adj φ ψ ?_ ?_
    · ext U : 2
      simp [ψ, shAdj]
    · ext U : 2
      have := (inv φ).hom.naturality
      simp only [Functor.sheafPushforwardContinuous_obj_obj_obj,
        Functor.sheafPushforwardContinuous_obj_obj_map, Sheaf.inv_hom, NatIso.isIso_inv_app,
        IsIso.eq_inv_comp] at this
      simp [ψ, shAdj, ← this, ← Functor.map_comp_assoc, ← op_comp]
  exact adj.isLeftAdjoint

set_option backward.isDefEq.respectTransparency false in
omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [HasSheafify J' AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat] in
lemma isQuasicoherent_pushforward_of_adjunction (G : C' ⥤ C) (F : C ⥤ C') (adj : G ⊣ F)
    [G.IsContinuous J' J] [F.IsContinuous J J'] [G.IsCocontinuous J' J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} J' J).obj R)
    (ψ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J J').obj S)
    (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj = ψ.hom ≫ F.op.whiskerLeft φ.hom)
    (H₂ : φ.hom ≫ G.op.whiskerLeft ψ.hom ≫ Functor.whiskerRight (NatTrans.op adj.unit) S.obj =
      𝟙 S.obj)
    [∀ X, Functor.IsContinuous.{u} (Over.post (X := X) F) (J.over _) (J'.over _)]
    [∀ X, Functor.IsContinuous.{u} (Over.post (X := X) G) (J'.over _) (J.over _)]
    [HasPullbacks C] [HasPullbacks C']
    (η : (pushforward φ).obj (unit R) ≅ unit S)
    {M : SheafOfModules.{u} R} [IsQuasicoherent M] :
    IsQuasicoherent ((pushforward φ).obj M) := by
  convert isQuasicoherent_pushforward G φ _ _
  · intro X Y f
    apply Functor.isContinuous_comp _ _ _ (J.over _) _
  · intro X Y f
    dsimp
    let G' := Over.post (X := X) G ⋙ Over.map f
    let F' : Over Y ⥤ Over X :=
      Over.pullback f ⋙ Over.post F ⋙ Over.pullback (adj.unit.app _)
    let GFadj : G' ⊣ F' :=
      .comp (Over.postAdjunctionLeft _) (Over.mapPullbackAdj f)
    have : G'.IsContinuous (J'.over X) (J.over Y) := by
      apply Functor.isContinuous_comp _ _ _ (J.over _) _
    have : F'.IsContinuous (J.over Y) (J'.over X) := by
      convert Functor.isContinuous_comp _ _ _ (J.over _) _
      · infer_instance
      · exact Functor.isContinuous_comp _ _ _ (J'.over _) _
    let a : S.over X ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (J'.over X) (J.over Y)).obj
          (R.over Y) :=
      ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (J'.over X) J').map φ
    let e :
        ((Over.forget Y).sheafPushforwardContinuous RingCat (J.over Y) J).obj
        ((F.sheafPushforwardContinuous RingCat J J').obj S) ⟶
          (F'.sheafPushforwardContinuous RingCat (J.over Y) (J'.over X)).obj (S.over X) :=
      { hom.app U := S.obj.map (Quiver.Hom.op <| pullback.fst _ _ ≫ F.map (pullback.fst _ _))
        hom.naturality U V g := by simp [← Functor.map_comp, ← op_comp, F'] }
    let b : R.over Y ⟶
        (F'.sheafPushforwardContinuous RingCat.{u} (J.over Y) (J'.over X)).obj (S.over X) :=
      ((Over.forget Y).sheafPushforwardContinuous RingCat.{u} _ _).map ψ ≫ e
    let adj : pushforward.{u} a ⊣ pushforward.{u} b := by
      refine SheafOfModules.pushforwardPushforwardAdj.{u, _, _, _, _, u} GFadj _ _ ?_ ?_
      · ext U : 2
        dsimp [F', G', GFadj, b, e, a]
        have := congr($(H₁).app (.op U.unop.left))
        dsimp at this
        simp [← op_comp, Category.assoc, ← reassoc_of% this, ← Functor.map_comp]
        simp [Functor.map_comp, Category.assoc, Adjunction.counit_naturality, Functor.comp_obj,
          Functor.id_obj, CategoryTheory.Adjunction.homEquiv]
      · ext U : 2
        have := congr($(H₂).app (.op U.unop.left))
        dsimp at this
        simp [G', a, F', b, e, GFadj, ← this,
          ← Functor.map_comp, ← op_comp, Adjunction.equivHomsetLeftOfNatIso]
    change PreservesColimitsOfSize (pushforward a)
    exact adj.leftAdjoint_preservesColimits
  · exact η
  · infer_instance

end map

end

noncomputable section

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]

/-- Given a sheaf of `R`-modules `M` and a `Presentation M`, we may construct the quasi-coherent
data on the trivial cover. -/
@[simps]
def Presentation.quasicoherentData {M : SheafOfModules.{u} R} (P : Presentation M) :
    QuasicoherentData M where
  I := C
  X := id
  coversTop x := GrothendieckTopology.covering_of_eq_top J <| by
    rw [Sieve.ext_iff]
    intro _ f
    simpa [Sieve.top_apply, iff_true] using ⟨x, Nonempty.intro f⟩
  presentation x := P.map (pushforward (𝟙 (R.over x))) (by rfl)

/-- If a sheaf of `R`-modules `M` has a presentation, then `M` is quasi-coherent. -/
theorem Presentation.isQuasicoherent {M : SheafOfModules.{u} R} (P : Presentation M) :
    IsQuasicoherent M where
  nonempty_quasicoherentData := Nonempty.intro (Presentation.quasicoherentData P)

end
section bind

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

#adaptation_note /-- After nightly-2026-02-23 we need this to avoid timeouts. -/
/-- Given an cover `X` and a quasicoherent data for `M` restricted onto each `Mᵢ`, we may glue them
into a quasicoherent data of `M` itself. -/
noncomputable def QuasicoherentData.bind {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) (D : Π i, QuasicoherentData (M.over (X i))) :
    M.QuasicoherentData where
  I := Σ i, (D i).I
  X ij := ((D ij.1).X ij.2).left
  coversTop Y := J.transitive (hX Y) _ fun Z f ⟨i, ⟨g⟩⟩ ↦
      J.superset_covering ((Sieve.functorPushforward_ofObjects_le _ _ _).trans
      (Sieve.ofObjects_mono fun i' ↦ by aesop)) ((D i).coversTop (.mk g))
  presentation i :=
    letI e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
      (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
    (((D i.1).presentation i.2).map e.inverse (.refl _)).of_isIso
      (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over (X i.1)).over ((D i.1).X i.2)))).hom

lemma IsQuasicoherent.of_coversTop {R : Sheaf J RingCat.{u}}
    (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X) [∀ i, IsQuasicoherent (M.over (X i))] :
    IsQuasicoherent M :=
  (QuasicoherentData.bind M X hX fun _ ↦
    IsQuasicoherent.nonempty_quasicoherentData.some).isQuasicoherent

set_option backward.isDefEq.respectTransparency false

instance [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    Functor.IsContinuous.{w} (Over.pullback f) (J.over Y) (J.over X) := by
  apply Functor.isContinuous_of_coverPreserving
  · apply compatiblePreserving_overPullback
  · apply coverPreserving_overPullback

noncomputable
def pushforwardOverPullback [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    R.over Y ⟶
      ((Over.pullback f).sheafPushforwardContinuous _ _ _).obj (R.over X) where
  hom.app U := R.obj.map (pullback.fst _ _).op
  hom.naturality U V g := by simp [← Functor.map_comp, ← op_comp]

/-- Transport an adjunction along a natural isomorphism on the left. -/
def _root_.CategoryTheory.Adjunction.ofNatIsoLeft' {C : Type*} [Category* C] {D : Type*}
    [Category* D] {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) : G ⊣ H where
  unit := adj.unit ≫ Functor.whiskerRight iso.hom _
  counit := Functor.whiskerLeft _ iso.inv ≫ adj.counit
  left_triangle_components X := by
    simp only [Functor.id_obj, Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.map_comp, Functor.whiskerLeft_app, Category.assoc, NatTrans.naturality_assoc]
    simp [← Functor.comp_map]

set_option backward.isDefEq.respectTransparency false in
-- set_option pp.universes true in
lemma isQuasicoherent_over [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [HasPullbacks C]
    (M : SheafOfModules.{u} R) (X : C) [IsQuasicoherent M] :
    IsQuasicoherent (M.over X) := by
  have (Z : Over X) (Y : C) (f : (Over.forget X).obj Z ⟶ Y) :
      (Over.post (Over.forget X) ⋙ Over.map f).IsContinuous
        ((J.over X).over Z) (J.over Y) := by
    convert Functor.isContinuous_comp _ _ _ (J.over _) _
    · convert Functor.isContinuous_of_iso (Z.iteratedSliceForwardIsoPost _).symm _ _
      dsimp
      infer_instance
    · infer_instance
  refine isQuasicoherent_pushforward _ _ ?_ (.refl _)
  intro Z Y f
  let G := Over.post (Over.forget X) ⋙ Over.map f
  let iso : Over.post (Over.forget X) ⋙ Over.map f ≅
      Z.iteratedSliceForward ⋙ Over.map f :=
    Functor.isoWhiskerRight (Z.iteratedSliceForwardIsoPost _) _
  let a3 :=
    Adjunction.ofNatIsoLeft' Z.iteratedSliceEquiv.toAdjunction
      (Z.iteratedSliceForwardIsoPost _).symm
  let adj : G ⊣ _ := a3.comp (Over.mapPullbackAdj f)
  let φ : (R.over X).over Z ⟶
      (G.sheafPushforwardContinuous RingCat.{u} _ _).obj (R.over _) :=
    𝟙 _
  have : Functor.IsContinuous.{u} (Over.pullback f ⋙ Z.iteratedSliceEquiv.inverse)
      (J.over Y) ((J.over X).over Z) := by
    convert Functor.isContinuous_comp.{u} _ _ _ (J.over _) _
    · infer_instance
    · dsimp
      infer_instance
  let adj' : pushforward.{u} φ ⊣ _ := by
    refine SheafOfModules.pushforwardPushforwardAdj.{u, _, _, _, _, u} adj φ ?_ ?_ ?_
    · exact pushforwardOverPullback _
    · ext U : 2
      simp [pushforwardOverPullback, adj, a3, φ, G, Adjunction.ofNatIsoLeft',
        Over.iteratedSliceEquiv]
    · ext U : 2
      simp [φ, adj, a3, Adjunction.ofNatIsoLeft', Over.iteratedSliceEquiv, G,
        pushforwardOverPullback, ← op_comp, ← Functor.map_comp]
  refine Adjunction.leftAdjoint_preservesColimits adj'

end bind

end SheafOfModules
