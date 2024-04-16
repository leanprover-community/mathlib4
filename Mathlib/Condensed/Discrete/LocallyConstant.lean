/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.TopComparison
import Mathlib.Condensed.Discrete.ConstantSheaf
/-!

# The presheaf of locally constant maps as a condensed set

This file defines the functor `Condensed.LocallyConstant.functor : Type (u+1) ⥤ CondensedSet.{u}`,
which sends a set `X` to the sheaf of locally constant maps into `X`.

We prove that this functor is left adjoint to `Condensed.underlying`, and hence isomorphic to
`Condensed.discrete`. The unit of this adjunction is an isomorphism, which yields a proof that
`Condensed.discrete` is fully faithful.
-/

universe u

open CategoryTheory Limits Condensed LocallyConstant Opposite

namespace Condensed

section SigmaComparison

open CompHaus

variable (X : CondensedSet.{u}) {α : Type u} [Finite α] (σ : α → Type u)
  [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)]

/--
The comparison map from the value of a condensed set on a finite coproduct to the product of the
values on the components.
-/
def sigmaComparison : X.val.obj ⟨(of ((a : α) × σ a))⟩ ⟶ ((a : α) → X.val.obj ⟨of (σ a)⟩) :=
  fun x a ↦ X.val.map ⟨Sigma.mk a, continuous_sigmaMk⟩ x

noncomputable instance : PreservesLimitsOfShape (Discrete α) X.val :=
  let α' := (Countable.toSmall α).equiv_small.choose
  let e : α ≃ α' := (Countable.toSmall α).equiv_small.choose_spec.some
  have : Fintype α := Fintype.ofFinite _
  have : Fintype α' := Fintype.ofEquiv α e
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) X.val

theorem sigmaComparison_eq_comp_isos : sigmaComparison X σ =
    (X.val.mapIso (opCoproductIsoProduct' (finiteCoproduct.isColimit.{u, u} fun a ↦ of (σ a))
      (productIsProduct fun x ↦ Opposite.op (of (σ x))))).hom ≫
    (PreservesProduct.iso X.val fun a ↦ ⟨of (σ a)⟩).hom ≫
    (Types.productIso.{u, u + 1} fun a ↦ X.val.obj ⟨of (σ a)⟩).hom := by
  ext x a
  simp only [finiteCoproduct.cocone_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, types_comp_apply, Types.productIso_hom_comp_eval_apply]
  have := congrFun (piComparison_comp_π X.val (fun a ↦ ⟨of (σ a)⟩) a)
  simp only [types_comp_apply] at this
  rw [this, ← FunctorToTypes.map_comp_apply]
  simp only [sigmaComparison]
  apply congrFun
  congr 2
  erw [← opCoproductIsoProduct_inv_comp_ι]
  simp only [coe_of, Opposite.unop_op, unop_comp, Quiver.Hom.unop_op, Category.assoc]
  change finiteCoproduct.ι.{u, u} (fun a ↦ of (σ a)) _ = _
  rw [← Sigma.ι_comp_toFiniteCoproduct]
  congr
  simp only [opCoproductIsoProduct, ← unop_comp, coproductIsoCoproduct,
    opCoproductIsoProduct'_comp_self]
  rfl

instance : IsIso <| sigmaComparison X σ := by
  rw [sigmaComparison_eq_comp_isos]
  infer_instance

end SigmaComparison

namespace LocallyConstant

/--
The functor from the category of sets to presheaves on `CompHaus` given by locally constant maps.
-/
@[simps]
def functorToPresheaves : Type* ⥤ (CompHaus.{u}ᵒᵖ ⥤ Type _) where
  obj X := {
    obj := fun ⟨S⟩ ↦ LocallyConstant S X
    map := fun f g ↦ g.comap f.unop }
  map f := { app := fun S t ↦ t.map f }

/--
Locally constant maps are the same as continuous maps when the target is equipped with the discrete
topology
-/
@[simps]
def locallyConstantIsoContinuousMap (Y X : Type*) [TopologicalSpace Y] :
    LocallyConstant Y X ≅ C(Y, TopCat.discrete.obj X) :=
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  { hom := fun f ↦ (f : C(Y, X))
    inv := fun f ↦ ⟨f, (IsLocallyConstant.iff_continuous f).mpr f.2⟩ }

/-- `locallyConstantIsoContinuousMap` is a natural isomorphism. -/
noncomputable def functorToPresheavesIsoTopCatToCondensed (X : Type (u+1)) :
    functorToPresheaves.obj X ≅ (topCatToCondensed.obj (TopCat.discrete.obj X)).val :=
  NatIso.ofComponents (fun S ↦ locallyConstantIsoContinuousMap _ _)

/-- `Condensed.LocallyConstant.functorToPresheaves` lands in condensed sets. -/
@[simps]
def functor : Type (u+1) ⥤ CondensedSet.{u} where
  obj X := {
    val := functorToPresheaves.obj X
    cond := by
      rw [Presheaf.isSheaf_of_iso_iff (functorToPresheavesIsoTopCatToCondensed X)]
      exact (topCatToCondensed.obj _).cond
  }
  map f := ⟨functorToPresheaves.map f⟩

/--
`Condensed.LocallyConstant.functor` is naturally isomorphic to the restriction of
`topCatToCondensed` to discrete topological spaces.
-/
noncomputable def functorIsoTopCatToCondensed : functor ≅ TopCat.discrete ⋙ topCatToCondensed :=
  NatIso.ofComponents (fun X ↦ {
    hom := ⟨(functorToPresheavesIsoTopCatToCondensed X).hom⟩
    inv := ⟨(functorToPresheavesIsoTopCatToCondensed X).inv⟩
    hom_inv_id := Sheaf.hom_ext _ _ (functorToPresheavesIsoTopCatToCondensed X).hom_inv_id
    inv_hom_id := Sheaf.hom_ext _ _ (functorToPresheavesIsoTopCatToCondensed X).inv_hom_id})

section

variable {S T : CompHaus.{u}} {Y : Type (u+1)} (f : S → Y) (f' : LocallyConstant S Y) (g : T ⟶ S)

section Index
/-!

# Locally constant maps and partitions

A locally constant map out of a compact Hausdorff space corresponds to a finite partition of the
space whose components are the fibers of the map. Each component is itself a compact Hausdorff
space.

In this section we define the indexing set for this partition and prove some API lemmas.
-/

/-- The indexing set of the partition. -/
def α : Type u := Set.range (fun (x : Set.range f) ↦ f ⁻¹' {x.val})

/--
The map from `α f`. When `f` is locally constant, `S` is the coproduct of `σ f` in `CompHaus`.
-/
def σ : α f → Type u := fun x ↦ x.val

instance (x : α f') : CompactSpace x.val := by
  obtain ⟨y, hy⟩ := x.prop
  erw [← isCompact_iff_compactSpace, ← hy]
  exact (f'.2.isClosed_fiber _).isCompact

instance (x : α f) : TopologicalSpace (σ f x) := (inferInstance : TopologicalSpace <| x.val)

instance (x : α f) : T2Space (σ f x) := (inferInstance : T2Space <| x.val)

instance (x : α f') : CompactSpace (σ f' x) := (inferInstance : CompactSpace x.val)

/--
Any `a : α f` is of the form `f ⁻¹' {x}` for some `x` in the image of `f`. We define `a.image` 
as `x`.
-/
noncomputable def α.image (a : α f) : Y := a.2.choose.1

lemma α.eq_fiber_image (a : α f) : a.1 = f ⁻¹' {a.image} := a.2.choose_spec.symm

/--
Given `s : S`, `α.mk f s` is the fiber of `f` that `s` belongs to, as an element of `α f`.
-/
def α.mk (s : S) : α f := ⟨f ⁻¹' {f s}, by simp⟩

/-- `s : S` as a term of the type `α.mk f s` -/
def α.mkSelf (s : S) : (mk f s).val := ⟨s, rfl⟩

lemma α.map_eq_image (a : α f) (x : a.1) : f x = a.image := by
  have := a.2.choose_spec
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage]
  convert x.prop

lemma α.mk_image (s : S) : (α.mk f s).image = f s :=
  (map_eq_image (x := mkSelf f s)).symm

lemma α.mem_iff_eq_image (s : S) (a : α f) : s ∈ a.val ↔ f s = a.image := by
  constructor
  · intro h
    exact a.map_eq_image _ ⟨s, h⟩
  · intro h
    rw [a.eq_fiber_image]
    exact h

/-- An arbitrary element of `a : α f`. -/
noncomputable def α.preimage (a : α f) : S := a.2.choose.2.choose

lemma α.map_preimage_eq_image (a : α f) : f a.preimage = a.image := a.2.choose.2.choose_spec

instance : Finite (α f') :=
  have : Finite (Set.range f') := range_finite f'
  Finite.Set.finite_range _

lemma α.map_preimage_eq_image_map {X : Type (u+1)} (g : Y → X) (a : α (g ∘ f)) :
    g (f a.preimage) = a.image := by rw [← map_preimage_eq_image]; rfl

lemma α.map_eq_image_comap (a : α (f'.comap g)) (x : a.1) : f' (g x.val) = a.image := by
  rw [← map_eq_image (f'.comap g) a x]; rfl

lemma α.map_preimage_eq_image_comap (a : α (f'.comap g)) : f' (g a.preimage) = a.image := by
  rw [← map_preimage_eq_image]; rfl

lemma α.image_eq_image_mk (a : α (f'.comap g)) : a.image = (α.mk f' (g (a.preimage _))).image := by
  rw [← map_preimage_eq_image_comap, mk_image]

end Index

/-- The canonical map from the coproduct induced by `f` to `S`. -/
@[simps apply]
def sigmaIsoHom : C((x : α f) × x.val, S) where
  toFun := fun ⟨a, x⟩ ↦ x.val

lemma sigmaIsoHom_inj : Function.Injective (sigmaIsoHom f) := by
  rintro ⟨⟨_, _, rfl⟩, ⟨_, hx⟩⟩ ⟨⟨_, _, rfl⟩, ⟨_, hy⟩⟩ h
  refine Sigma.subtype_ext ?_ h
  simp only [sigmaIsoHom_apply] at h
  rw [Set.mem_preimage, Set.mem_singleton_iff] at hx hy
  simp [← hx, ← hy, h]

lemma sigmaIsoHom_surj : Function.Surjective (sigmaIsoHom f) :=
  fun _ ↦ ⟨⟨⟨_, ⟨⟨_, Set.mem_range_self _⟩, rfl⟩⟩, ⟨_, rfl⟩⟩, rfl⟩

/-- The canonical map from the coproduct induced by `f` to `S` as an isomorphism in `CompHaus`. -/
noncomputable def sigmaIso : (CompHaus.of <| (x : α f') × x.val) ≅ S :=
  CompHaus.isoOfBijective (sigmaIsoHom f') ⟨sigmaIsoHom_inj f', sigmaIsoHom_surj f'⟩

/-- The inclusion map from a component of the coproduct induced by `f` into `S`. -/
def sigmaIncl (a : α f') : CompHaus.of a.val ⟶ S where
  toFun := fun x ↦ x.val

/--
This is an auxiliary definition, the details do not matter. What's important is that this map exists
so that the lemma `sigmaIncl_comp_sigmaIncl` works.
-/
def sigmaInclIncl {X : Type (u+1)} (g : Y → X) (a : α (f'.map g))
    (b : α (f'.comap (sigmaIncl (map g f') a))) :
    CompHaus.of b.val ⟶ CompHaus.of (α.mk f' (b.preimage).val).val where
  toFun x := ⟨x.val.val, by
    rw [α.mem_iff_eq_image, α.mk_image]
    simp only [map_apply, CompHaus.coe_of, sigmaIncl, coe_comap,
      ContinuousMap.coe_mk]
    have := x.prop
    rw [α.mem_iff_eq_image] at this
    simp only [map_apply, CompHaus.coe_of, sigmaIncl, coe_comap,
      ContinuousMap.coe_mk, Function.comp_apply] at this
    rw [this]
    exact (α.map_preimage_eq_image _ _).symm⟩
  continuous_toFun := Continuous.subtype_mk (continuous_induced_dom.comp continuous_induced_dom) _

lemma sigmaIncl_comp_sigmaIncl {X : Type (u+1)} (g : Y → X) (a : α (f'.map g))
    (b : α (f'.comap (sigmaIncl (f'.map g) a))) :
    sigmaIncl (f'.comap (sigmaIncl (f'.map g) a)) b ≫ sigmaIncl (f'.map g) a =
      (sigmaInclIncl _ _ a b) ≫ sigmaIncl f' (α.mk f' (b.preimage).val) := rfl

end

section Adjunction
/-!

# The condensed set of locally constant maps is left adjoint to the forgetful functor

The hard part of this adjunction is to define the counit. See `counitAppApp` for an explanation. 
-/

variable {S T : CompHaus.{u}} (g : T ⟶ S) {Y : CondensedSet.{u}}
  (f : LocallyConstant S (Y.val.obj (op (⊤_ _))))

lemma sigmaComparison_comp_sigmaIso' (X : CondensedSet.{u}) (a : α f):
    (X.val.mapIso (sigmaIso f).op).hom ≫ sigmaComparison X (σ f) ≫ (fun g ↦ g a) =
      X.val.map (sigmaIncl f a).op := by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, types_comp_apply, sigmaComparison,
    CompHaus.coe_of, ← FunctorToTypes.map_comp_apply]
  congr

lemma sigmaComparison_comp_sigmaIso (a : α f):
    (Y.val.mapIso (sigmaIso f).op).hom ≫ sigmaComparison Y (σ f) ≫ (fun g ↦ g a) =
      Y.val.map (sigmaIncl f a).op := sigmaComparison_comp_sigmaIso' f Y a

/-- The projection of the counit. -/
noncomputable def counitAppAppImage : (a : α f) → Y.val.obj ⟨CompHaus.of <| a.val⟩ :=
  fun a ↦ Y.val.map (terminal.from _).op a.image

/--
The counit is defined as follows: given a locally constant map `f : S → Y(*)`, let
`S = S₁ ⊔ ⋯ ⊔ Sₙ` be the corresponding decomposition of `S` into the fibers. We need to provide an
element of `Y(S)`. It suffices to provide an element of `Y(Sᵢ)` for all `i`. Let `yᵢ ∈ Y(*)` denote
the value of `f` on `Sᵢ`. Our desired element is the image of `yᵢ` under the canonical map
`Y(*) → Y(Sᵢ)`.
-/
noncomputable def counitAppApp (S : CompHaus.{u}) (Y : CondensedSet.{u}) :
    LocallyConstant S (Y.val.obj (op (⊤_ _))) ⟶ Y.val.obj ⟨S⟩ :=
  fun f ↦ ((inv (sigmaComparison Y (σ f))) ≫ (Y.val.mapIso (sigmaIso f).op).inv)
    (counitAppAppImage f)

-- This is the key lemma to prove naturality of the counit: to check equality of two elements of
-- `X(S)`, it suffices to check equality after composing with each `X(S) → X(Sᵢ)`.
lemma locallyConstantCondensed_ext (X : CondensedSet.{u}) (x y : X.val.obj ⟨S⟩)
    (h : ∀ (a : α f), X.val.map (sigmaIncl f a).op x = X.val.map (sigmaIncl f a).op y) : x = y := by
  apply_fun (X.val.mapIso (sigmaIso f).op).hom using injective_of_mono _
  apply_fun sigmaComparison X (σ f) using injective_of_mono _
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso'] at h
  exact h

lemma incl_of_counitAppApp (a : α f) :
    Y.val.map (sigmaIncl f a).op (counitAppApp S Y f) = counitAppAppImage f a := by
  simp only [← sigmaComparison_comp_sigmaIso, Functor.mapIso_hom, Iso.op_hom, types_comp_apply]
  simp only [counitAppApp, Functor.mapIso_inv, ← Iso.op_hom, types_comp_apply,
    ← FunctorToTypes.map_comp_apply, Iso.inv_hom_id, FunctorToTypes.map_id_apply]
  exact congrFun (inv_hom_id_apply (asIso (sigmaComparison Y (σ f))) (counitAppAppImage f)) _

/--
This is an auxiliary definition, the details do not matter. What's important is that this map exists
so that the lemma `incl_comap` works.
-/
def component_hom (a : α (f.comap g)) :
    CompHaus.of a.val ⟶ CompHaus.of (α.mk f (g a.preimage)).val where
  toFun x := ⟨g x.val, by
    simp only [α.mk, Set.mem_preimage, Set.mem_singleton_iff]
    rw [α.map_eq_image_comap, α.map_preimage_eq_image_comap]
    ⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.comp g.continuous continuous_subtype_val) _

lemma incl_comap {S T : CompHausᵒᵖ} (f : LocallyConstant S.unop (Y.val.obj (op (⊤_ _))))
    (g : S ⟶ T) (a : α (f.comap g.unop)) : g ≫ (sigmaIncl (f.comap g.unop) a).op =
    (sigmaIncl f _).op ≫ (component_hom g.unop f a).op := by
  rfl

/-- The counit is natural in the compact Hausdorff space `S` -/
@[simps!]
noncomputable def counitApp (Y : CondensedSet.{u}) : functor.obj (Y.val.obj (op (⊤_ _))) ⟶ Y where
  val := {
    app := fun ⟨S⟩ ↦ counitAppApp S Y
    naturality := by
      intro S T g
      simp only [functor, functorToPresheaves]
      ext f
      apply locallyConstantCondensed_ext (f.comap g.unop)
      intro a
      simp only [op_unop, types_comp_apply]
      rw [incl_of_counitAppApp, ← FunctorToTypes.map_comp_apply, incl_comap]
      simp only [op_unop, FunctorToTypes.map_comp_apply]
      rw [incl_of_counitAppApp]
      simp only [counitAppAppImage, ← FunctorToTypes.map_comp_apply, ← op_comp,
        terminal.comp_from, α.image_eq_image_mk]
  }

theorem hom_apply_counitAppApp {X : CondensedSet.{u}} (g : Y ⟶ X)
    (a : α (f.map (g.val.app (op (⊤_ CompHaus))))) :
    X.val.map (sigmaIncl (map (g.val.app (op (⊤_ CompHaus))) f) a).op
      (g.val.app ⟨S⟩ (counitAppApp S Y f)) =
        counitAppAppImage (map (g.val.app (op (⊤_ CompHaus))) f) a := by
  apply locallyConstantCondensed_ext (f.comap (sigmaIncl _ _))
  intro b
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  simp only [counitAppAppImage]
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  simp only [CompHaus.coe_of, map_apply, terminal.comp_from]
  rw [← α.map_preimage_eq_image_map]
  change (_ ≫ X.val.map _) _ = (_ ≫ X.val.map _) _
  simp only [← g.val.naturality]
  rw [sigmaIncl_comp_sigmaIncl]
  simp only [coe_comap, map_apply, CompHaus.coe_of, op_comp, Functor.map_comp, types_comp_apply]
  rw [incl_of_counitAppApp]
  simp only [counitAppAppImage, ← FunctorToTypes.map_comp_apply, ← op_comp,
    terminal.comp_from]
  erw [α.mk_image]
  change (Y.val.map _ ≫ _) _ = (Y.val.map _ ≫ _) _
  simp only [g.val.naturality]
  simp only [types_comp_apply]
  have := α.map_preimage_eq_image (f := g.val.app _ ∘ f) (a := a)
  simp only [Function.comp_apply] at this
  rw [this]
  apply congrArg
  erw [← α.mem_iff_eq_image (f := g.val.app _ ∘ f)]
  exact (b.preimage).prop

/-- The counit is natural in both the compact Hausdorff space `S` and the condensed set `Y` -/
@[simps]
noncomputable def counit : underlying (Type (u+1)) ⋙ functor ⟶ 𝟭 _ where
  app := counitApp
  naturality X Y g := by
    apply Sheaf.hom_ext
    simp only [underlying, functor, id_eq, eq_mpr_eq_cast, Functor.comp_obj, Functor.flip_obj_obj,
      sheafToPresheaf_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      sheafToPresheaf_map, Functor.id_map]
    rw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_comp_val]
    ext S (f : LocallyConstant _ _)
    simp only [FunctorToTypes.comp, counitApp_val_app]
    apply locallyConstantCondensed_ext (f.map (g.val.app (op (⊤_ _))))
    intro a
    simp only [map_apply, op_unop]
    erw [incl_of_counitAppApp]
    exact (hom_apply_counitAppApp _ _ _).symm

/--
The unit of the adjunciton is given by mapping each element to the corresponding constant map.
-/
@[simps]
def unit : 𝟭 _ ⟶ functor ⋙ underlying _ where
  app X x := LocallyConstant.const _ x

theorem locallyConstantAdjunction_left_triangle (X : Type (u + 1)) :
    functorToPresheaves.map (unit.app X) ≫ (counit.app (functor.obj X)).val = 𝟙 (functorToPresheaves.obj X) := by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, Functor.comp_obj, underlying_obj, FunctorToTypes.comp, NatTrans.id_app,
    functorToPresheaves_obj_obj, types_id_apply]
  simp only [counit, counitApp_val_app]
  apply locallyConstantCondensed_ext (X := functor.obj X) (Y := functor.obj X) (f.map (unit.app X))
  intro a
  erw [incl_of_counitAppApp]
  simp only [functor_obj_val, functorToPresheaves_obj_obj, unop_op, Functor.id_obj, map_apply, CompHaus.coe_of,
    counitAppAppImage, functorToPresheaves_obj_map, Quiver.Hom.unop_op]
  ext x
  erw [← α.map_eq_image _ a x]
  rfl

/-- The unit of the adjunction is an iso. -/
noncomputable def unitIso : 𝟭 (Type (u+1)) ≅ functor ⋙ underlying _ where
  hom := unit
  inv := { app := fun X f ↦ f.toFun (CompHaus.terminalIsoPUnit.inv PUnit.unit) }
  inv_hom_id := by
    ext
    simp only [Functor.comp_obj, underlying_obj, functor_obj_val, functorToPresheaves_obj_obj,
      FunctorToTypes.comp, toFun_eq_coe, unit_app, const, NatTrans.id_app, types_id_apply]
    apply DFunLike.ext
    intro _
    simp only [coe_mk, Function.const_apply]
    congr
    apply_fun CompHaus.terminalIsoPUnit.hom
    · rfl
    · intro _ _ h
      convert congrArg CompHaus.terminalIsoPUnit.inv h
      all_goals simp

/--
`Condensed.LocallyConstant.functor` is left adjoint to the forgetful functor.
-/
@[simps! unit_app_apply counit_app_val_app]
noncomputable def adjunction : functor ⊣ underlying _ :=
  Adjunction.mkOfUnitCounit {
    unit := unit
    counit := counit
    left_triangle := by
      ext X
      simp only [id_eq, eq_mpr_eq_cast, Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
        underlying_obj, functorToPresheaves_obj_obj, whiskerRight_app, Functor.associator_hom_app,
        whiskerLeft_app, Category.id_comp, NatTrans.id_app']
      apply Sheaf.hom_ext
      rw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_id_val]
      exact locallyConstantAdjunction_left_triangle X
    right_triangle := by
      ext X (x : X.val.obj _)
      simp only [Functor.comp_obj, Functor.id_obj, underlying_obj, counit, FunctorToTypes.comp,
        whiskerLeft_app, Functor.associator_inv_app, functor_obj_val, functorToPresheaves_obj_obj,
        types_id_apply, whiskerRight_app, underlying_map, counitApp_val_app, NatTrans.id_app']
      apply locallyConstantCondensed_ext (unit.app _ x)
      intro a
      erw [incl_of_counitAppApp]
      simp only [unit, Functor.id_obj, coe_const, counitAppAppImage]
      let y : ⊤_ CompHaus := CompHaus.terminalIsoPUnit.inv PUnit.unit
      have := α.map_eq_image _ a ⟨y, by simp [α.mem_iff_eq_image, ← α.map_preimage_eq_image, unit]⟩
      erw [← this]
      simp only [unit, Functor.id_obj, coe_const, Function.const_apply]
      have hh : sigmaIncl (const _ x) a = terminal.from _ := Unique.uniq _ _
      rw [hh] }

instance : IsIso adjunction.unit := (inferInstance : IsIso unitIso.hom)

end Adjunction

/--
`Condensed.LocallyConstant.functor` is isomorphic to `Condensed.discrete` (by uniqueness of
adjoints).
-/
noncomputable def iso : functor ≅ discrete _ :=
  adjunction.leftAdjointUniq (discrete_underlying_adj _)

instance : functor.Faithful := L_faithful_of_unit_isIso adjunction

noncomputable instance : functor.Full := lFullOfUnitIsIso adjunction

instance : (discrete (Type _)).Faithful := Functor.Faithful.of_iso iso

noncomputable instance : (discrete (Type _)).Full := Functor.Full.ofIso iso

end Condensed.LocallyConstant
