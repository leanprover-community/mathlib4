/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.FiberedCategory.HomLift

/-!
# Quasicoherent sheaves

A sheaf of modules is quasi-coherent if it admits locally a presentation as the
cokernel of a morphism between coproducts of copies of the sheaf of rings.
When these coproducts are finite, we say that the sheaf is of finite presentation.

## References

* https://stacks.math.columbia.edu/tag/01BD

-/

@[expose] public section

universe u v' u'

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
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

variable {C C' : Type (u')} [SmallCategory C] [SmallCategory C'] {J : GrothendieckTopology C}
  {J' : GrothendieckTopology C'} {R : Sheaf J RingCat} {S : Sheaf J' RingCat}
  [HasSheafify J AddCommGrpCat] [HasSheafify J' AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] [J'.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
  [J'.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] {ι σ : Type u}

/-- Given two morphism of sheaf of `R`-module `f : free ι ⟶ free σ` and `g : free σ ⟶ M`
satisfying `H : f ≫ g = 0` and `IsColimit (CokernelCofork.ofπ g H)`, then this sequence defines
a `Presentation M`. -/
def presentationOfIsCokernelFree {M : SheafOfModules.{u} R}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) : Presentation M :=
  letI gen : M.GeneratingSections :=
    { I := σ
      s := M.freeHomEquiv g
      epi := by simpa using epi_of_isColimit_cofork H'}
  haveI eq_aux : gen.π = g := Equiv.symm_apply_apply M.freeHomEquiv g
  haveI comp_zero : f ≫ gen.π = 0 := eq_aux ▸ H
  { generators := gen
    relations :=
      { I := ι
        s := (kernel gen.π).freeHomEquiv <| kernel.lift gen.π f comp_zero
        epi := by
          let h : cokernel f ≅ M := (H'.coconePointUniqueUpToIso (colimit.isColimit _)).symm
          let h' : Abelian.image f ≅ kernel gen.π :=
            kernel.mapIso (cokernel.π f) gen.π (Iso.refl _) h (by simp [h, eq_aux])
          have comp_aux : Abelian.factorThruImage f ≫ h'.hom =
            (kernel.lift gen.π f comp_zero) := equalizer.hom_ext <| by simp [h']
          rw [← comp_aux, Equiv.symm_apply_apply]
          infer_instance }}

/-- Given a sheaf of `R`-module `M` and a `Presentation M`, there is two morphism of
sheaf of `R`-module `f : free ι ⟶ free σ` and `g : free σ ⟶ M`  satisfying `H : f ≫ g = 0`
and `IsColimit (CokernelCofork.ofπ g H)`. -/
def Presentation.cokernelCofork {M : SheafOfModules.{u} R} (P : Presentation M) :
    Σ' (ι σ : Type u) (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0),
    IsColimit (CokernelCofork.ofπ g H) := by
  use P.relations.I, P.generators.I, (freeHomEquiv _).symm P.relations.s ≫ (kernel.ι _),
    P.generators.π, by simp
  exact isCokernelEpiComp (c := CokernelCofork.ofπ _ (kernel.condition P.generators.π))
      (Abelian.epiIsCokernelOfKernel _ <| limit.isLimit _) _ rfl

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Let `F` be a functor from sheaf of `R`-module to sheaf of `S`-module, if `F` preserves
colimits and `F.obj (unit R) ≅ unit S`, given a `P : Presentation M`, then we will get a
`Presentation (F.obj M)`. -/
def Presentation.map
    (F : SheafOfModules.{u'} R ⥤ SheafOfModules.{u'} S) [PreservesColimits F]
    (hf' : F.obj (unit R) ≅ unit S) {M : SheafOfModules.{u'} R} (P : Presentation M) :
    Presentation (F.obj M) := by
  obtain ⟨ι, σ, f, g, H, h⟩ := Presentation.cokernelCofork P
  let f_new := (Sigma.mapIso fun b ↦ hf').inv ≫ (PreservesCoproduct.iso F _).inv ≫ F.map f ≫
    (PreservesCoproduct.iso F _).hom ≫ (Sigma.mapIso fun b ↦ hf').hom
  let g_new := (Sigma.mapIso fun b ↦ hf').inv ≫ (PreservesCoproduct.iso F _).inv ≫ F.map g
  have H' : f_new ≫ g_new = 0 := by
    simp_rw [f_new, g_new, Category.assoc, Iso.hom_inv_id_assoc,
      Preadditive.IsIso.comp_left_eq_zero, IsHomLift.eq_of_isHomLift F (F.map f ≫ F.map g) (f ≫ g),
      H, Functor.map_zero]
  let h' : IsColimit (CokernelCofork.ofπ g_new H') := by
    refine IsColimit.ofIsoColimit ((IsColimit.precomposeHomEquiv
      (parallelPair.ext ?_ ?_ ?_ ?_) _).symm (isColimitCoforkMapOfIsColimit' F _ h))
      (Cocones.ext ?_ ?_) <;> dsimp
    · exact (Sigma.mapIso fun b ↦ hf').symm ≪≫ ((PreservesCoproduct.iso F _)).symm
    · exact (Sigma.mapIso fun b ↦ hf').symm ≪≫ ((PreservesCoproduct.iso F _)).symm
    · simp_rw [f_new, Category.assoc]
      erw [Iso.hom_inv_id_assoc, Iso.hom_inv_id]
      simp only [Functor.mapIso_inv, colim_map, PreservesCoproduct.inv_hom, Category.comp_id,
        Iso.trans_hom, Iso.symm_hom, Category.assoc]
    · simp
    · exact Iso.refl _
    · intro j
      have : (F.map f ≫ F.map g) = 0 := by
        simp_rw [IsHomLift.eq_of_isHomLift F (F.map f ≫ F.map g) (f ≫ g)]
        aesop
      cases j <;> dsimp
      · aesop
      · aesop
  exact presentationOfIsCokernelFree f_new g_new H' h'

end

variable [∀ X, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- This structure contains the data of a family of objects `X i` which cover
the terminal object, and of a presentation of `M.over (X i)` for all `i`. -/
structure QuasicoherentData (M : SheafOfModules.{u} R) where
  /-- the index type of the covering -/
  I : Type u'
  /-- a family of objects which cover the terminal object -/
  X : I → C
  coversTop : J.CoversTop X
  /-- a presentation of the sheaf of modules `M.over (X i)` for any `i : I` -/
  presentation (i : I) : (M.over (X i)).Presentation

namespace QuasicoherentData

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

instance {M : SheafOfModules.{u} R} (q : M.QuasicoherentData) [q.IsFinitePresentation] :
    q.localGeneratorsData.IsFiniteType where
  isFiniteType := by dsimp; infer_instance

end QuasicoherentData

/-- A sheaf of modules is quasi-coherent if it is locally the cokernel of a
morphism between coproducts of copies of the sheaf of rings. -/
class IsQuasicoherent (M : SheafOfModules.{u} R) : Prop where
  nonempty_quasicoherentData : Nonempty M.QuasicoherentData := by infer_instance

variable (R) in
@[inherit_doc IsQuasicoherent]
abbrev isQuasicoherent : ObjectProperty (SheafOfModules.{u} R) :=
  IsQuasicoherent

/-- A sheaf of modules is finitely presented if it is locally the cokernel of a
morphism between coproducts of finitely many copies of the sheaf of rings. -/
class IsFinitePresentation (M : SheafOfModules.{u} R) : Prop where
  exists_quasicoherentData (M) :
    ∃ (σ : M.QuasicoherentData), σ.IsFinitePresentation

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

end SheafOfModules
