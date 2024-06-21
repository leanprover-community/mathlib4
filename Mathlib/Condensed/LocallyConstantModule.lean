import Mathlib.CategoryTheory.Sites.Discrete
import Mathlib.Condensed.LocallyConstant
import Mathlib.Condensed.Module
import Mathlib.Condensed.Light.Module
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.CategoryTheory.Monad.EquivMon

universe w u

open CategoryTheory LocallyConstant CompHausLike Functor Category Functor Opposite

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    (i : L ⋙ R ≅ 𝟭 C)

lemma isIso_unit_of_abstract_iso' : IsIso adj.unit := by
  let T := adj.toMonad
  let M := T.toMon
  letI := endofunctorMonoidalCategory C
  have : M.one = adj.unit := rfl
  let M' : Mon_ (C ⥤ C) := {
    X := 𝟭 C
    one := 𝟙 _
    mul := by-- i.inv ≫ whiskerRight M.one (L ⋙ R) ≫ M.mul ≫ i.hom
      refine (i.inv ◫ adj.unit) ≫ M.mul ≫ i.hom
    one_mul := by sorry
      -- erw [MonoidalCategory.whiskerRight_id, assoc]
      -- change 𝟙 _ ≫ _ ≫ _ = _
      -- simp only [assoc, id_comp]
      -- change 𝟙 _ ≫ _ = _
      -- simp
      -- change _ = 𝟙 _
      -- slice_lhs 2 3 =>
      --   erw [M.one_mul]
      -- change _ ≫ 𝟙 _ ≫ _ = _
      -- simp
    mul_one := by sorry
      -- erw [MonoidalCategory.id_whiskerLeft, assoc]
      -- change 𝟙 _ ≫ _ ≫ _ = _
      -- simp only [assoc, id_comp]
      -- change 𝟙 _ ≫ _ = _
      -- simp
      -- change _ = 𝟙 _
      -- slice_lhs 2 3 =>
      --   erw [M.one_mul]
      -- change _ ≫ 𝟙 _ ≫ _ = _
      -- simp
    mul_assoc := sorry
  }
  suffices IsIso (adj.unit ≫ i.hom) from IsIso.of_isIso_comp_right adj.unit i.hom
  sorry
  -- refine ⟨i.hom ≫ (i.inv ◫ adj.unit) ≫ M.mul ≫ i.hom, ?_, ?_⟩
  -- · sorry
  -- · sorry

def transferIso : L ⊣ R := Adjunction.mkOfUnitCounit {
  unit := i.inv
  counit := adj.counit
  left_triangle := sorry
  right_triangle := sorry }

lemma isIso_unit_of_abstract_iso : IsIso ((adj.transferIso i).unit) :=
  inferInstanceAs (IsIso i.inv)

noncomputable def fullyFaithfulLOfLRIsoId : L.FullyFaithful :=
  have := adj.isIso_unit_of_abstract_iso i
  (adj.transferIso i).fullyFaithfulLOfIsIsoUnit

end CategoryTheory.Adjunction

#exit

attribute [local instance] ConcreteCategory.instFunLike

variable {P : TopCat.{u} → Prop}

namespace Condensed.LocallyConstantModule

variable (R : Type (max u w)) [Ring R]

/--
The functor from the category of `R`-modules to presheaves on `CompHaus` given by locally constant
maps.
-/
@[simps]
def functorToPresheaves : ModuleCat.{max u w} R ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ ModuleCat R) where
  obj X := {
    obj := fun ⟨S⟩ ↦ ModuleCat.of R (LocallyConstant S X)
    map := fun f ↦ comapₗ R f.unop }
  map f := { app := fun S ↦ mapₗ R f }

variable [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks.{u} P]
  (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/-- `Condensed.LocallyConstantModule.functorToPresheaves` lands in condensed modules. -/
@[simps]
def functor :
    have := CompHausLike.preregular hs
    ModuleCat R ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (ModuleCat R) where
  obj X := {
    val := (functorToPresheaves.{w, u} R).obj X
    cond := by
      have := CompHausLike.preregular hs
      apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp (s :=
        CategoryTheory.forget (ModuleCat R))
      exact ((Condensed.LocallyConstant.functor P hs).obj _).cond }
  map f := ⟨(functorToPresheaves.{w, u} R).map f⟩

end Condensed.LocallyConstantModule

namespace CondensedMod

variable (R : Type (u+1)) [Ring R]

abbrev LocallyConstant.functorToPresheaves : ModuleCat.{u+1} R ⥤ (CompHaus.{u}ᵒᵖ ⥤ ModuleCat R) :=
  Condensed.LocallyConstantModule.functorToPresheaves.{u+1, u} R

abbrev LocallyConstant.functor : ModuleCat R ⥤ CondensedMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u+1, u} R
    (fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

noncomputable def LocallyConstant.functorIsoDiscreteOne' (M : ModuleCat.{u+1} R) :
    M ≅ (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M)) where
  hom := constₗ R
  inv := evalₗ R PUnit.unit

def aux_map {M N : ModuleCat.{u+1} R} (f : M ⟶ N) :
  ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M) ⟶
    ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) N) := mapₗ R f

lemma LocallyConstant.functorIsoDiscreteOne'_w {M N : ModuleCat.{u+1} R} (f : M ⟶ N) :
    (functorIsoDiscreteOne' R M).inv ≫ f = aux_map R f ≫ (functorIsoDiscreteOne' R N).inv :=
  rfl

lemma LocallyConstant.functorIsoDiscreteOne'_w' {M N : ModuleCat.{u+1} R} (f : M ⟶ N) :
    f ≫ (functorIsoDiscreteOne' R N).hom = (functorIsoDiscreteOne' R M).hom ≫ aux_map R f :=
  rfl

def aux_map_of {M N : ModuleCat.{u+1} R} (f :
    ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M) ⟶
      ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) N)) :
  M ⟶ N where
    toFun x := (f (constₗ R x)).toFun PUnit.unit
    map_add' := by aesop
    map_smul' := by aesop

lemma LocallyConstant.functorIsoDiscreteOne'_w_of {M N : ModuleCat.{u+1} R} (f :
    ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M) ⟶
      ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) N)) :
    (functorIsoDiscreteOne' R M).hom ≫ f = aux_map_of R f ≫ (functorIsoDiscreteOne' R N).hom :=
  rfl

lemma LocallyConstant.functorIsoDiscreteOne'_w'_of {M N : ModuleCat.{u+1} R} (f :
    ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M) ⟶
      ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) N)) :
    f ≫ (functorIsoDiscreteOne' R N).inv = (functorIsoDiscreteOne' R M).inv ≫ aux_map_of R f :=
  rfl

noncomputable def LocallyConstant.functorIsoDiscreteOne (M : ModuleCat R) :
    (Condensed.discrete _).obj M ≅ (Condensed.discrete _).obj
      (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u+1}) M)) :=
  (Condensed.discrete _).mapIso (functorIsoDiscreteOne' R M)

instance (M : ModuleCat R) : IsIso ((Condensed.forget R).map
    ((Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.app
      ((CondensedMod.LocallyConstant.functor R).obj M))) := by
  erw [Sheaf.constantCommuteComposeApp_counit_comp]
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  change Sheaf.IsDiscrete _ _ _
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Faithful :=
    inferInstanceAs (Condensed.discrete _).Faithful
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Full :=
    inferInstanceAs (Condensed.discrete _).Full
  rw [Sheaf.isDiscrete_iff_mem_essImage]
  change _ ∈ (Condensed.discrete _).essImage
  rw [essImage_eq_of_natIso CondensedSet.LocallyConstant.iso.symm]
  exact obj_mem_essImage CondensedSet.LocallyConstant.functor M

noncomputable def LocallyConstant.functorIsoDiscrete_components (M : ModuleCat R) :
    (Condensed.discrete _).obj M ≅ (functor R).obj M := by
  have : (Condensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  refine (functorIsoDiscreteOne R M) ≪≫ (@asIso _ _ _ _ ?_ ?_)
  · exact (Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)
  · apply this.reflects

open Condensed.LocallyConstantModule in
noncomputable def LocallyConstant.functorIsoDiscrete : functor R ≅ Condensed.discrete _ := by
  refine NatIso.ofComponents (fun M ↦ (functorIsoDiscrete_components R M).symm) ?_
  intro M N f
  dsimp
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  dsimp [functorIsoDiscrete_components]
  rw [Category.assoc, ← Iso.eq_inv_comp]
  erw [← (Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.naturality]
  change _ ≫ ((Condensed.discreteUnderlyingAdj (ModuleCat R)).counit.app (((functor R).obj N))) = _
  simp only [← assoc]
  congr 1
  rw [← Iso.comp_inv_eq]
  apply Sheaf.hom_ext
  simp only [comp_obj, Condensed.underlying_obj, functor_obj_val, functorToPresheaves_obj_obj,
    coe_of, Condensed.discrete_obj, Functor.comp_map, Condensed.underlying_map,
    functorToPresheaves_map_app, Condensed.discrete_map, functorIsoDiscreteOne, mapIso_inv,
    ← Functor.map_comp]
  rfl

noncomputable def LocallyConstant.compIsoId :
    (functor R) ⋙ (Condensed.underlying (ModuleCat R)) ≅ 𝟭 _ :=
  NatIso.ofComponents fun M ↦ (functorIsoDiscreteOne' R _).symm

noncomputable def LocallyConstant.adjunction : functor R ⊣ Condensed.underlying (ModuleCat R) :=
  Adjunction.ofNatIsoLeft (Condensed.discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

noncomputable def LocallyConstant.fullyFaithfulFunctor :
    (functor R).FullyFaithful := (adjunction R).fullyFaithfulLOfLRIsoId (compIsoId R)

instance : (LocallyConstant.functor R).Faithful :=
  Functor.Faithful.of_comp_iso (LocallyConstant.compIsoId R)

open Condensed.LocallyConstantModule in
noncomputable def LocallyConstant.fullyFaithfulFunctorToPresheaves :
    (functorToPresheaves R).FullyFaithful where
  preimage f := (functorIsoDiscreteOne' R _).hom ≫ (f.app ⟨CompHaus.of PUnit.{u+1}⟩) ≫
    (functorIsoDiscreteOne' R _).inv
  map_preimage {M N} f := by
    simp only [coe_of, functorToPresheaves_obj_obj, Functor.map_comp]
    let LC := functorToPresheaves R
    set iM := (functorIsoDiscreteOne' R M)
    set iN := (functorIsoDiscreteOne' R N)
    let pt : CompHausᵒᵖ := ⟨CompHaus.of PUnit.{u+1}⟩
    change LC.map _ ≫ LC.map (f.app pt) ≫ LC.map _ = _
    ext S (g : LocallyConstant _ _)
    simp only [functorToPresheaves_obj_obj, coe_of, NatTrans.comp_app, ModuleCat.coe_comp,
      Function.comp_apply]
    apply LocallyConstant.ext
    sorry
    -- intro x
    -- have :
    --   (((LC.map iN.inv).app S) (((LC.map (f.app pt)).app S) (((LC.map iM.hom).app S) g))).toFun x = iN.inv ((f.app pt) (iM.hom (g x))) := rfl
    -- simp only [coe_of, functorToPresheaves_obj_obj, toFun_eq_coe] at this
    -- rw [this]
    -- let s : unop S ⟶ unop pt := (CompHaus.isTerminalPUnit.from (unop S))
    -- have hh : (LC.obj M).map s.op ≫ f.app S = f.app pt ≫ (LC.obj N).map s.op  :=
    --   f.naturality s.op
    -- have hM : (LC.obj M).map s.op = iM.inv ≫ (constₗ R) := rfl
    -- have hN : (LC.obj N).map s.op = iN.inv ≫ (constₗ R) := rfl
    -- rw [hM, hN] at hh

    -- have := LinearMap.congr_fun hh (iM.hom (g x))
    -- simp only [functorToPresheaves_obj_obj, op_unop, coe_of, functorIsoDiscreteOne', assoc, iM,
    --   iN] at this
    -- erw [LocallyConstant.coe_mk, LocallyConstant.coe_mk]
    -- erw [this]
    -- ext S : 2 -- (g : LocallyConstant _ _)
    -- simp only [functorToPresheaves_obj_obj, coe_of, NatTrans.comp_app]

    -- let gg : (LC.obj ((LC.obj M).obj S)).obj pt ⟶ (LC.obj ((LC.obj N).obj S)).obj pt :=
    --   (LC.map (f.app S)).app pt
    -- have : (LC.obj ((LC.obj _).obj _)).map _ ≫ (LC.map (f.app S)).app S =
    --     (LC.map (f.app S)).app pt ≫ (LC.obj ((LC.obj _).obj _)).map _ :=
    --   (LC.map (f.app S)).naturality s.op
    -- have h : (LC.obj ((LC.obj M).obj pt)).map s.op ≫ (LC.map (f.app pt)).app S =
    --     (LC.map (f.app pt)).app pt ≫ (LC.obj ((LC.obj N).obj pt)).map s.op :=
    --   (LC.map (f.app pt)).naturality s.op
    -- replace this : CommSq _ _ _ _ := ⟨this⟩
    -- replace h : CommSq _ _ _ _ := ⟨h⟩
    -- replace hh : CommSq _ _ _ _ := ⟨hh⟩
    -- replace hh := (LC.map_commSq hh)
    -- replace hh := NatTrans.congr_app hh.w S
    -- simp only [functorToPresheaves_obj_obj, op_unop, NatTrans.comp_app, coe_of] at hh
    -- replace hh : CommSq _ _ _ _ := ⟨hh⟩
    -- have hhhh := (h.horiz_comp hh).w

  preimage_map _ := rfl

noncomputable def LocallyConstant.fullyFaithfulFunctor' :
    (functor R).FullyFaithful :=
  haveI : (sheafToPresheaf (coherentTopology CompHaus) (ModuleCat R)).Faithful :=
    (fullyFaithfulSheafToPresheaf _ _).faithful
  FullyFaithful.ofCompFaithful (G := sheafToPresheaf (coherentTopology CompHaus) (ModuleCat R))
    (fullyFaithfulFunctorToPresheaves R)

end CondensedMod

namespace LightCondMod

variable (R : Type u) [Ring R]

abbrev LocallyConstant.functor : ModuleCat R ⥤ LightCondMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

def LocallyConstant.functorIsoDiscrete : functor R ≅ LightCondensed.discrete _ := sorry

end LightCondMod
