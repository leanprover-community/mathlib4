/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Data.Countable.Small
import Mathlib.Topology.Category.CompHausLike.EffectiveEpi
import Mathlib.Topology.LocallyConstant.Basic
/-!

# The sheaf of locally constant maps on `CompHausLike`
-/

universe u w

open CategoryTheory Limits LocallyConstant Opposite CompHausLike

namespace CompHausLike.Aux

section

-- variable {S T : CompHaus.{u}} {Y : Type w} (f : S → Y) (f' : LocallyConstant S Y) (g : T ⟶ S)

variable {S T Y : Type*}
  [TopologicalSpace S] [CompactSpace S] [TopologicalSpace T] [CompactSpace T]
  (f : S → Y) (f' : LocallyConstant S Y) (g : C(T, S))

section Index
/-!

# Locally constant maps and partitions

A locally constant map out of a compact Hausdorff space corresponds to a finite partition of the
space whose components are the fibers of the map. Each component is itself a compact Hausdorff
space.

In this section we define the indexing set for this partition and prove some API lemmas.
-/

/-- The indexing set of the partition. -/
def α : Type _ := Set.range (fun (x : Set.range f) ↦ f ⁻¹' {x.val})

/--
The map from `α f`. When `f` is locally constant, `S` is the coproduct of `σ f` in `CompHaus`.
-/
def σ : α f → Type _ := fun x ↦ x.val

instance (x : α f') : CompactSpace x.val := by
  obtain ⟨y, hy⟩ := x.prop
  erw [← isCompact_iff_compactSpace, ← hy]
  exact (f'.2.isClosed_fiber _).isCompact

instance (x : α f) : TopologicalSpace (σ f x) := (inferInstance : TopologicalSpace <| x.val)

instance (x : α f) [T2Space S] : T2Space (σ f x) := (inferInstance : T2Space <| x.val)

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

lemma α.map_preimage_eq_image_map {X : Type w} (g : Y → X) (a : α (g ∘ f)) :
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

/-- The inclusion map from a component of the coproduct induced by `f` into `S`. -/
def sigmaIncl (a : α f) : C(a.val, S) where
  toFun := fun x ↦ x.val

/--
This is an auxiliary definition, the details do not matter. What's important is that this map exists
so that the lemma `sigmaIncl_comp_sigmaIncl` works.
-/
def sigmaInclIncl {X : Type w} (g : Y → X) (a : α (f'.map g))
    (b : α (f'.comap (sigmaIncl (map g f') a))) :
    C(b.val, (α.mk f' (b.preimage).val).val) where
  toFun x := ⟨x.val.val, by
    rw [α.mem_iff_eq_image, α.mk_image]
    simp only [map_apply, sigmaIncl, coe_comap, ContinuousMap.coe_mk]
    have := x.prop
    rw [α.mem_iff_eq_image] at this
    simp only [map_apply, sigmaIncl, coe_comap,
      ContinuousMap.coe_mk, Function.comp_apply] at this
    rw [this]
    exact (α.map_preimage_eq_image _ _).symm⟩
  continuous_toFun := Continuous.subtype_mk (continuous_induced_dom.comp continuous_induced_dom) _

lemma sigmaIncl_comp_sigmaIncl {X : Type w} (g : Y → X) (a : α (f'.map g))
    (b : α (f'.comap (sigmaIncl (f'.map g) a))) :
    (sigmaIncl (f'.map g) a).comp (sigmaIncl (f'.comap (sigmaIncl (f'.map g) a)) b) =
      (sigmaIncl f' (α.mk f' (b.preimage).val)).comp (sigmaInclIncl f' g a b) := rfl

end

end Aux

variable {P : TopCat.{u} → Prop}

section SigmaComparison

variable
  (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w) [PreservesFiniteProducts X]
  {α : Type u} [Finite α] (σ : α → Type u)
  [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)]
  (h : ∀ a, P (TopCat.of (σ a))) (hP : P (TopCat.of (Σ (a : α), (TopCat.of (σ a)))))
  [HasFiniteCoproducts (CompHausLike P)]

/--
The comparison map from the value of a condensed set on a finite coproduct to the product of the
values on the components.
-/
def sigmaComparison : X.obj ⟨(of P ((a : α) × σ a) hP)⟩ ⟶ ((a : α) → X.obj ⟨of P (σ a) (h a)⟩) :=
  fun x a ↦ X.map ⟨Sigma.mk a, continuous_sigmaMk⟩ x

noncomputable instance : PreservesLimitsOfShape (Discrete α) X :=
  let α' := (Countable.toSmall α).equiv_small.choose
  let e : α ≃ α' := (Countable.toSmall α).equiv_small.choose_spec.some
  have : Fintype α := Fintype.ofFinite _
  have : Fintype α' := Fintype.ofEquiv α e
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) X

theorem sigmaComparison_eq_comp_isos : sigmaComparison X σ h hP =
    (X.mapIso (opCoproductIsoProduct'
      (finiteCoproduct.isColimit.{u, u} (fun a ↦ of P (σ a) (h a)) hP)
      (productIsProduct fun x ↦ Opposite.op (of P (σ x) (h x))))).hom ≫
    (PreservesProduct.iso X fun a ↦ ⟨of P (σ a) (h a)⟩).hom ≫
    (Types.productIso.{u, max u w} fun a ↦ X.obj ⟨of P (σ a) (h a)⟩).hom := by
  ext x a
  simp only [Cofan.mk_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, types_comp_apply, Types.productIso_hom_comp_eval_apply]
  have := congrFun (piComparison_comp_π X (fun a ↦ ⟨of P (σ a) (h a)⟩) a)
  simp only [types_comp_apply] at this
  rw [this, ← FunctorToTypes.map_comp_apply]
  simp only [sigmaComparison]
  apply congrFun
  congr 2
  erw [← opCoproductIsoProduct_inv_comp_ι]
  simp only [coe_of, Opposite.unop_op, unop_comp, Quiver.Hom.unop_op, Category.assoc]
  change finiteCoproduct.ι.{u, u} (fun a ↦ of P (σ a) (h a)) hP _ = _
  simp only [opCoproductIsoProduct, ← unop_comp, opCoproductIsoProduct'_comp_self]
  erw [IsColimit.fac]
  rfl

instance isIsoSigmaComparison : IsIso <| sigmaComparison X σ h hP := by
  rw [sigmaComparison_eq_comp_isos]
  infer_instance

end SigmaComparison

namespace LocallyConstant

/--
The functor from the category of sets to presheaves on `CompHaus` given by locally constant maps.
-/
@[simps]
def functorToPresheaves : Type (max u w) ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w) where
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

-- /-- `locallyConstantIsoContinuousMap` is a natural isomorphism. -/
-- noncomputable def functorToPresheavesIsoTopCatToCondensed (X : Type max u w) :
--     functorToPresheaves.{u, w}.obj X ≅ (topCatToCondensed.obj (TopCat.discrete.obj X)).val :=
--   NatIso.ofComponents (fun S ↦ locallyConstantIsoContinuousMap _ _)

-- /-- `Condensed.LocallyConstant.functorToPresheaves` lands in condensed sets. -/
-- @[simps]
-- def functor : Type (max u w) ⥤ Condensed.{u} (Type max u w) where
--   obj X := {
--     val := functorToPresheaves.{u, w}.obj X
--     cond := by
--       rw [Presheaf.isSheaf_of_iso_iff (functorToPresheavesIsoTopCatToCondensed.{u, w} X)]
--       exact (topCatToCondensed.obj _).cond
--   }
--   map f := ⟨functorToPresheaves.map f⟩

-- /--
-- `Condensed.LocallyConstant.functor` is naturally isomorphic to the restriction of
-- `topCatToCondensed` to discrete topological spaces.
-- -/
-- noncomputable def functorIsoTopCatToCondensed :
--     functor.{u, w} ≅ TopCat.discrete.{max w u} ⋙ topCatToCondensed.{w, u} :=
--   @natIsoOfCompFullyFaithful _ _ _ _ _ _ _ _ (sheafToPresheaf _ _)
--     (instFullSheafFunctorOppositeSheafToPresheaf _ _)
--     (instFaithfulSheafFunctorOppositeSheafToPresheaf _ _)
--     (NatIso.ofComponents (fun X ↦ functorToPresheavesIsoTopCatToCondensed.{u, w} X))
--   -- why aren't these `Full` and `Faithful` instances found automatically??

section Adjunction
/-!

# The condensed set of locally constant maps is left adjoint to the forgetful functor

The hard part of this adjunction is to define the counit. See `counitAppApp` for an explanation. 
-/

variable {S T : CompHausLike.{u} P} (g : T ⟶ S) {Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w}
    [PreservesFiniteProducts Y] (hu : P (TopCat.of PUnit.{u+1}))
    (f : LocallyConstant S (Y.obj (op (CompHausLike.of P PUnit.{u+1} hu))))

variable (hP : ∀ {α : Type} [Finite α] (X : α → CompHausLike P),
      P (TopCat.of (Σ (a : α), (X a).toTop)))
-- (h : ∀ a, P (TopCat.of (σ a))) (hP : P (TopCat.of (Σ (a : α), (TopCat.of (σ a)))))
--   [HasFiniteCoproducts (CompHausLike P)]
  --{Y : CondensedSet.{u}}
  --(f : LocallyConstant S (Y.val.obj (op (⊤_ _))))

open Aux

#exit

/-- The inclusion map from a component of the coproduct induced by `f` into `S`. -/
def sigmaIncl (a : α f) : CompHausLike.of P a.val ⟶ S := Condensed.sigmaIncl _ a

/-- The canonical map from the coproduct induced by `f` to `S` as an isomorphism in `CompHaus`. -/
noncomputable def sigmaIso : (CompHaus.of <| (x : α f) × x.val) ≅ S :=
  CompHaus.isoOfBijective (sigmaIsoHom f) ⟨sigmaIsoHom_inj f, sigmaIsoHom_surj f⟩

lemma _root_.CompHaus.comp {X Y Z : CompHaus} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (g : C(_, _)).comp f := rfl

-- /--
-- This is an auxiliary definition, the details do not matter. What's important is that this map exists
-- so that the lemma `sigmaIncl_comp_sigmaIncl` works.
-- -/
-- def sigmaInclIncl {X : Type w}
--     (g : (Y.obj (op (CompHaus.of PUnit.{u+1}))) → X) (a : α (f.map g))
--     (b : α (f.comap (sigmaIncl (f.map g) a))) :
--     CompHaus.of b.val ⟶ CompHaus.of (α.mk f (b.preimage).val).val where
--   toFun x := ⟨x.val.val, by
--     rw [α.mem_iff_eq_image, α.mk_image]
--     simp only [map_apply, CompHaus.coe_of, sigmaIncl, coe_comap,
--       ContinuousMap.coe_mk]
--     have := x.prop
--     rw [α.mem_iff_eq_image] at this
--     simp only [map_apply, CompHaus.coe_of, sigmaIncl, coe_comap,
--       ContinuousMap.coe_mk, Function.comp_apply] at this
--     rw [this]
--     exact (α.map_preimage_eq_image _ _).symm⟩
--   continuous_toFun := Continuous.subtype_mk (continuous_induced_dom.comp continuous_induced_dom)

-- lemma sigmaIncl_comp_sigmaIncl {X : Type w}
--     (g : (Y.obj (op (CompHaus.of PUnit.{u+1}))) → X) (a : α (f.map g))
--     (b : α (f.comap (sigmaIncl (f.map g) a))) :
--     sigmaIncl (f.comap (sigmaIncl (f.map g) a)) b ≫ sigmaIncl (f.map g) a =
--       (sigmaInclIncl _ _ a b) ≫ sigmaIncl f (α.mk f (b.preimage).val) := rfl

lemma sigmaComparison_comp_sigmaIso' (X : CompHaus.{u}ᵒᵖ ⥤ Type max u w) (a : α f):
    (X.mapIso (sigmaIso f).op).hom ≫ sigmaComparison X (σ f) ≫ (fun g ↦ g a) =
      X.map (sigmaIncl f a).op := by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, types_comp_apply, sigmaComparison,
    CompHaus.coe_of, ← FunctorToTypes.map_comp_apply]
  congr

lemma sigmaComparison_comp_sigmaIso (a : α f):
    (Y.mapIso (sigmaIso f).op).hom ≫ sigmaComparison Y (σ f) ≫ (fun g ↦ g a) =
      Y.map (sigmaIncl f a).op := sigmaComparison_comp_sigmaIso' f Y a

/-- The projection of the counit. -/
noncomputable def counitAppAppImage : (a : α f) → Y.obj ⟨CompHaus.of <| a.val⟩ :=
  fun a ↦ Y.map (CompHaus.isTerminalPUnit.from _).op a.image

/--
The counit is defined as follows: given a locally constant map `f : S → Y(*)`, let
`S = S₁ ⊔ ⋯ ⊔ Sₙ` be the corresponding decomposition of `S` into the fibers. We need to provide an
element of `Y(S)`. It suffices to provide an element of `Y(Sᵢ)` for all `i`. Let `yᵢ ∈ Y(*)` denote
the value of `f` on `Sᵢ`. Our desired element is the image of `yᵢ` under the canonical map
`Y(*) → Y(Sᵢ)`.
-/
noncomputable def counitAppApp (S : CompHaus.{u}) (Y : CompHaus.{u}ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts Y] :
    LocallyConstant S (Y.obj (op (CompHaus.of PUnit.{u+1}))) ⟶ Y.obj ⟨S⟩ :=
  fun f ↦ ((inv (sigmaComparison Y (σ f))) ≫ (Y.mapIso (sigmaIso f).op).inv)
    (counitAppAppImage f)

-- This is the key lemma to prove naturality of the counit: to check equality of two elements of
-- `X(S)`, it suffices to check equality after composing with each `X(S) → X(Sᵢ)`.
lemma locallyConstantCondensed_ext (X : CompHaus.{u}ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts X] (x y : X.obj ⟨S⟩)
    (h : ∀ (a : α f), X.map (sigmaIncl f a).op x = X.map (sigmaIncl f a).op y) : x = y := by
  apply_fun (X.mapIso (sigmaIso f).op).hom using injective_of_mono _
  apply_fun sigmaComparison X (σ f) using injective_of_mono _
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso'] at h
  exact h

lemma incl_of_counitAppApp (a : α f) :
    Y.map (sigmaIncl f a).op (counitAppApp S Y f) = counitAppAppImage f a := by
  rw [← sigmaComparison_comp_sigmaIso, Functor.mapIso_hom, Iso.op_hom, types_comp_apply]
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
    erw [α.map_eq_image_comap, α.map_preimage_eq_image_comap]
    ⟩
  continuous_toFun := Continuous.subtype_mk (Continuous.comp g.continuous continuous_subtype_val) _

lemma incl_comap {S T : CompHausᵒᵖ}
    (f : LocallyConstant S.unop (Y.obj (op (CompHaus.of PUnit.{u+1}))))
    (g : S ⟶ T) (a : α (f.comap g.unop)) : g ≫ (sigmaIncl (f.comap g.unop) a).op =
    (sigmaIncl f _).op ≫ (component_hom g.unop f a).op := by
  rfl

/-- The counit is natural in the compact Hausdorff space `S` -/
@[simps!]
noncomputable def counitApp (Y : CompHaus.{u}ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts Y] :
    (functorToPresheaves.obj (Y.obj (op (CompHaus.of PUnit.{u+1})))) ⟶ Y where
  app := fun ⟨S⟩ ↦ counitAppApp S Y
  naturality := by
    intro S T g
    simp only [functorToPresheaves]
    ext f
    apply locallyConstantCondensed_ext (f.comap g.unop)
    intro a
    simp only [op_unop, types_comp_apply]
    rw [incl_of_counitAppApp, ← FunctorToTypes.map_comp_apply, incl_comap]
    simp only [op_unop, FunctorToTypes.map_comp_apply]
    rw [incl_of_counitAppApp]
    simp only [counitAppAppImage, ← FunctorToTypes.map_comp_apply, ← op_comp,
      terminal.comp_from, α.image_eq_image_mk]
    rfl

theorem hom_apply_counitAppApp (X : CompHaus.{u}ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts X] (g : Y ⟶ X)
    (a : α (f.map (g.app (op (CompHaus.of PUnit.{u+1}))))) :
    X.map (sigmaIncl (map (g.app (op (CompHaus.of PUnit.{u+1}))) f) a).op
      (g.app ⟨S⟩ (counitAppApp S Y f)) =
        counitAppAppImage (map (g.app (op (CompHaus.of PUnit.{u+1}))) f) a := by
  apply locallyConstantCondensed_ext (f.comap (sigmaIncl _ _))
  intro b
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  simp only [counitAppAppImage]
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
  simp only [CompHaus.coe_of, map_apply, IsTerminal.comp_from]
  rw [← α.map_preimage_eq_image_map f (g.app (op (CompHaus.of PUnit.{u+1})))]
  change (_ ≫ X.map _) _ = (_ ≫ X.map _) _
  simp only [← g.naturality]
  sorry
  -- rw [CompHaus.comp, sigmaIncl_comp_sigmaIncl]
  -- simp only [coe_comap, map_apply, CompHaus.coe_of, op_comp, Functor.map_comp, types_comp_apply]
  -- rw [incl_of_counitAppApp]
  -- simp only [counitAppAppImage, ← FunctorToTypes.map_comp_apply, ← op_comp,
  --   terminal.comp_from]
  -- erw [α.mk_image]
  -- change (Y.map _ ≫ _) _ = (Y.map _ ≫ _) _
  -- simp only [g.naturality]
  -- simp only [types_comp_apply]
  -- have := α.map_preimage_eq_image (f := g.app _ ∘ f) (a := a)
  -- simp only [Function.comp_apply] at this
  -- rw [this]
  -- apply congrArg
  -- erw [← α.mem_iff_eq_image (f := g.app _ ∘ f)]
  -- exact (b.preimage).prop

/-- The counit is natural in both the compact Hausdorff space `S` and the condensed set `Y` -/
@[simps]
noncomputable def counit : underlying (Type max u w) ⋙ functor.{u, w} ⟶ 𝟭 (Condensed.{u} (Type max u w)) where
  app X := ⟨counitApp.{u, w} X.val⟩
  naturality X Y g := by
    apply Sheaf.hom_ext
    simp only [underlying, functor, id_eq, eq_mpr_eq_cast, Functor.comp_obj, Functor.flip_obj_obj,
      sheafToPresheaf_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      sheafToPresheaf_map, Functor.id_map]
    rw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_comp_val]
    ext S (f : LocallyConstant _ _)
    simp only [FunctorToTypes.comp, counitApp_app]
    apply locallyConstantCondensed_ext.{u, w} (f.map (g.val.app (op (CompHaus.of PUnit.{u+1}))))
    intro a
    simp only [map_apply, op_unop]
    erw [incl_of_counitAppApp]
    rw [← hom_apply_counitAppApp]

/--
The unit of the adjunciton is given by mapping each element to the corresponding constant map.
-/
@[simps]
def unit : 𝟭 _ ⟶ functor ⋙ underlying _ where
  app X x := LocallyConstant.const _ x

theorem locallyConstantAdjunction_left_triangle (X : Type max u w) :
    functorToPresheaves.{u, w}.map (unit.app X) ≫ (counit.app (functor.obj X)).val =
    𝟙 (functorToPresheaves.obj X) := by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, Functor.comp_obj, underlying_obj, FunctorToTypes.comp, NatTrans.id_app,
    functorToPresheaves_obj_obj, types_id_apply]
  simp only [counit, counitApp_app]
  apply locallyConstantCondensed_ext
    (X := (functor.obj X).val) (Y := (functor.{u, w}.obj X).val) (f.map (unit.app X))
  intro a
  erw [incl_of_counitAppApp]
  simp only [functor_obj_val, functorToPresheaves_obj_obj, unop_op, Functor.id_obj, map_apply,
    CompHaus.coe_of, counitAppAppImage, functorToPresheaves_obj_map, Quiver.Hom.unop_op]
  ext x
  erw [← α.map_eq_image _ a x]
  rfl

/-- The unit of the adjunction is an iso. -/
noncomputable def unitIso : 𝟭 (Type max u w) ≅ functor.{u, w} ⋙ underlying _ where
  hom := unit
  inv := { app := fun X f ↦ f.toFun PUnit.unit }

/--
`Condensed.LocallyConstant.functor` is left adjoint to the forgetful functor.
-/
@[simps! unit_app_apply counit_app_val_app]
noncomputable def adjunction : functor.{u, w} ⊣ underlying _ :=
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
        types_id_apply, whiskerRight_app, underlying_map, counitApp_app, NatTrans.id_app']
      apply locallyConstantCondensed_ext (unit.app _ x)
      intro a
      erw [incl_of_counitAppApp]
      simp only [CompHaus.coe_of, unit, Functor.id_obj, coe_const, counitAppAppImage]
      have := α.map_eq_image _ a ⟨PUnit.unit, by
        simp [α.mem_iff_eq_image (a := a), ← α.map_preimage_eq_image]⟩
      erw [← this]
      simp only [unit, Functor.id_obj, coe_const, Function.const_apply]
      congr }

instance : IsIso adjunction.unit := (inferInstance : IsIso unitIso.hom)

end Adjunction

/--
`Condensed.LocallyConstant.functor` is isomorphic to `Condensed.discrete` (by uniqueness of
adjoints).
-/
noncomputable def iso : functor.{u, u+1} ≅ discrete _ :=
  adjunction.leftAdjointUniq (discrete_underlying_adj _)

instance : functor.{u, w}.Faithful := adjunction.L_faithful_of_unit_isIso

noncomputable instance : functor.{u, w}.Full := adjunction.L_full_of_unit_isIso

instance : (discrete (Type _)).Faithful := Functor.Faithful.of_iso iso

noncomputable instance : (discrete (Type _)).Full := Functor.Full.of_iso iso

end Condensed.LocallyConstant
