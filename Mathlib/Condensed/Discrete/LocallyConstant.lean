/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Condensed.Discrete.Basic
import Mathlib.Condensed.TopComparison
/-!

# The sheaf of locally constant maps on `CompHausLike P`

This file proves that under suitable conditions, the functor from types to sheaves for the coherent
topology on `CompHausLike P`, given by mapping a set to the sheaf of locally constant maps to it,
is left adjoint to the "underlying set" functor (evaluation at the point).

We apply this to prove that the constant sheaf functor into (light) condensed sets is isomorphic to
the functor of sheaves of locally constant maps described above.
-/

universe u w u'

open CategoryTheory Limits LocallyConstant Opposite CompHausLike

attribute [local instance] ConcreteCategory.instFunLike

variable {P : TopCat.{u} → Prop}

namespace CompHausLike.Aux

section

variable {S : Type u} {T : Type u'} {Y : Type*}
  [TopologicalSpace S] [CompactSpace S] [TopologicalSpace T] [CompactSpace T]
  (f : S → Y) (f' : LocallyConstant S Y) (g : C(T, S))

section Index
/-!

# Locally constant maps and partitions

A locally constant map out of a compact space corresponds to a finite partition of the
space whose components are the fibers of the map. If the space is also Hausdorff, then each
component is itself a compact Hausdorff space.

In this section we define the indexing set for this partition and prove some API lemmas.
-/

/-- The indexing set of the partition. -/
def α : Type u := Set.range (fun (x : Set.range f) ↦ f ⁻¹' {x.val})

/--
The map from `α f`. When `f` is locally constant, `S` is the coproduct of `σ f` in `CompHausLike P`.
-/
def σ : α f → Type u := fun x ↦ x.val

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

lemma α.mem_iff_eq_image (s : S) (a : α f) : s ∈ a.val ↔ f s = a.image :=
  ⟨fun h ↦ a.map_eq_image _ ⟨s, h⟩, fun h ↦ by rw [a.eq_fiber_image]; exact h⟩

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

lemma sigmaIncl_comp_sigmaIncl {X : Type w} (g : Y → X) (a : α (f'.map g))
    (b : α (f'.comap (sigmaIncl (f'.map g) a))) :
    (sigmaIncl (f'.map g) a).comp (sigmaIncl (f'.comap (sigmaIncl (f'.map g) a)) b) =
      (sigmaIncl f' (α.mk f' (b.preimage).val)).comp (sigmaInclIncl f' g a b) := rfl

end

end Aux

variable [HasExplicitFiniteCoproducts.{u} P]

section SigmaComparison
/-!

# The sigma-comparison map

In this section we define the map `sigmaComparison` associated to a presheaf `X` on
`CompHausLike P`, and a finite family `S₁,...,Sₙ` of spaces in `CompHausLike P`, where `P` is
stable under taking finite disjoint unions.

The map `sigmaComparison` is the canonical map `X(S₁ ⊔ ... ⊔ Sₙ) ⟶ X(S₁) × ... × X(Sₙ)` induced by
the inclusion maps `Sᵢ ⟶ S₁ ⊔ ... ⊔ Sₙ`, and it is an isomorphism when `X` preserves finite
products.
-/

variable
  (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w) [PreservesFiniteProducts X]
  {α : Type u} [Finite α] (σ : α → Type u)
  [∀ a, TopologicalSpace (σ a)] [∀ a, CompactSpace (σ a)] [∀ a, T2Space (σ a)]
  [∀ a, HasProp P (σ a)]

instance : HasProp P (Σ (a : α), (σ a)) :=
  HasExplicitFiniteCoproducts.hasProp (fun a ↦ of P (σ a))

/--
The comparison map from the value of a condensed set on a finite coproduct to the product of the
values on the components.
-/
def sigmaComparison : X.obj ⟨(of P ((a : α) × σ a))⟩ ⟶ ((a : α) → X.obj ⟨of P (σ a)⟩) :=
  fun x a ↦ X.map ⟨Sigma.mk a, continuous_sigmaMk⟩ x

noncomputable instance : PreservesLimitsOfShape (Discrete α) X :=
  let α' := (Countable.toSmall α).equiv_small.choose
  let e : α ≃ α' := (Countable.toSmall α).equiv_small.choose_spec.some
  letI : Fintype α := Fintype.ofFinite _
  letI : Fintype α' := Fintype.ofEquiv α e
  preservesLimitsOfShapeOfEquiv (Discrete.equivalence e.symm) X

theorem sigmaComparison_eq_comp_isos : sigmaComparison X σ =
    (X.mapIso (opCoproductIsoProduct'
      (finiteCoproduct.isColimit.{u, u} (fun a ↦ of P (σ a)))
      (productIsProduct fun x ↦ Opposite.op (of P (σ x))))).hom ≫
    (PreservesProduct.iso X fun a ↦ ⟨of P (σ a)⟩).hom ≫
    (Types.productIso.{u, max u w} fun a ↦ X.obj ⟨of P (σ a)⟩).hom := by
  ext x a
  simp only [Cofan.mk_pt, Fan.mk_pt, Functor.mapIso_hom,
    PreservesProduct.iso_hom, types_comp_apply, Types.productIso_hom_comp_eval_apply]
  have := congrFun (piComparison_comp_π X (fun a ↦ ⟨of P (σ a)⟩) a)
  simp only [types_comp_apply] at this
  rw [this, ← FunctorToTypes.map_comp_apply]
  simp only [sigmaComparison]
  apply congrFun
  congr 2
  erw [← opCoproductIsoProduct_inv_comp_ι]
  simp only [coe_of, Opposite.unop_op, unop_comp, Quiver.Hom.unop_op, Category.assoc]
  change finiteCoproduct.ι.{u, u} (fun a ↦ of P (σ a)) _ = _
  simp only [opCoproductIsoProduct, ← unop_comp, opCoproductIsoProduct'_comp_self]
  erw [IsColimit.fac]
  rfl

instance isIsoSigmaComparison : IsIso <| sigmaComparison X σ := by
  rw [sigmaComparison_eq_comp_isos]
  infer_instance

end SigmaComparison

namespace LocallyConstant

/--
The functor from the category of sets to presheaves on `CompHausLike P` given by locally constant
maps.
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

section Adjunction
/-!

# The functor of sheaves of locally constant maps is left adjoint to the forgetful functor

The hard part of this adjunction is to define the counit. See `counitAppApp` for an explanation. 
-/

variable {S T : CompHausLike.{u} P} (g : T ⟶ S) {Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w}
    [PreservesFiniteProducts Y] [HasProp P PUnit.{u+1}]
    (f : LocallyConstant S (Y.obj (op (CompHausLike.of P PUnit.{u+1}))))

open Aux

variable [∀ (S : CompHausLike.{u} P) (p : S → Prop), HasProp P (Subtype p)]

/-- A fiber of a locally constant map as a `CompHausLike P`. -/
def part {Q : CompHausLike.{u} P} {Z : Type max u w} (r : LocallyConstant Q Z) (a : α r) :
    CompHausLike.{u} P :=
  CompHausLike.of P a.val

instance {Q : CompHausLike.{u} P} {Z : Type max u w} (r : LocallyConstant Q Z) (a : α r) :
    HasProp P (part r a) := by
  change HasProp P (Subtype _)
  infer_instance

/-- The inclusion map from a component of the coproduct induced by `f` into `S`. -/
def sigmaIncl {Q : CompHausLike.{u} P} {Z : Type max u w} (r : LocallyConstant Q Z) (a : α r) :
    part r a ⟶ Q :=
  CompHausLike.Aux.sigmaIncl _ a

/-- The canonical map from the coproduct induced by `f` to `S` as an isomorphism in
`CompHausLike P`. -/
noncomputable def sigmaIso {Q : CompHausLike.{u} P} {Z : Type max u w} (r : LocallyConstant Q Z) :
    (CompHausLike.finiteCoproduct (part r)) ≅ Q :=
  CompHausLike.isoOfBijective (sigmaIsoHom r) ⟨sigmaIsoHom_inj r, sigmaIsoHom_surj r⟩

/--
This is an auxiliary definition, the details do not matter. What's important is that this map exists
so that the lemma `sigmaIncl_comp_sigmaIncl` works.
-/
def sigmaInclIncl {Q : CompHausLike.{u} P} {Z : Type (max u w)} (r : LocallyConstant Q Z)
    {X : Type (max u w)}  (g : Z → X) (a : α (r.map g))
      (b : α (r.comap ((sigmaIncl (r.map g) a)))) :
        part _ b ⟶ part _ (α.mk r (b.preimage).val) :=
  Aux.sigmaInclIncl _ _ _ _

lemma sigmaIncl_comp_sigmaIncl {Q : CompHausLike.{u} P} {Z : Type (max u w)}
    (r : LocallyConstant Q Z) {X : Type (max u w)}  (g : Z → X) (a : α (r.map g))
      (b : α (r.comap ((sigmaIncl (r.map g) a)))) :
    sigmaIncl (r.comap (sigmaIncl (r.map g) a)) b ≫ sigmaIncl (r.map g) a =
      (sigmaInclIncl r g a b) ≫ sigmaIncl r (α.mk r (b.preimage).val) := rfl

lemma sigmaComparison_comp_sigmaIso {Q : CompHausLike.{u} P} {Z : Type (max u w)}
    (r : LocallyConstant Q Z)
    (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w) (a : α r) :
    (X.mapIso (sigmaIso r).op).hom ≫ sigmaComparison X (fun a ↦ (part r a).1) ≫
      (fun g ↦ g a) = X.map (sigmaIncl r a).op := by
  ext
  simp only [Functor.mapIso_hom, Iso.op_hom, types_comp_apply, sigmaComparison,
    CompHausLike.coe_of, ← FunctorToTypes.map_comp_apply]
  congr

/-- The projection of the counit. -/
noncomputable def counitAppAppImage : (a : α f) → Y.obj ⟨part f a⟩ :=
  fun a ↦ Y.map (CompHausLike.isTerminalPUnit.from _).op a.image

/--
The counit is defined as follows: given a locally constant map `f : S → Y(*)`, let
`S = S₁ ⊔ ⋯ ⊔ Sₙ` be the corresponding decomposition of `S` into the fibers. We need to provide an
element of `Y(S)`. It suffices to provide an element of `Y(Sᵢ)` for all `i`. Let `yᵢ ∈ Y(*)` denote
the value of `f` on `Sᵢ`. Our desired element is the image of `yᵢ` under the canonical map
`Y(*) → Y(Sᵢ)`.
-/
noncomputable def counitAppApp (S : CompHausLike.{u} P) (Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts Y] :
    LocallyConstant S (Y.obj (op (CompHausLike.of P PUnit.{u+1}))) ⟶ Y.obj ⟨S⟩ := by
  intro r
  refine ((inv (sigmaComparison Y (fun a ↦ (part r a).1))) ≫
    (Y.mapIso (sigmaIso r).op).inv) (counitAppAppImage r)

-- This is the key lemma to prove naturality of the counit: to check equality of two elements of
-- `X(S)`, it suffices to check equality after composing with each `X(S) → X(Sᵢ)`.
lemma locallyConstantCondensed_ext (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts X] (x y : X.obj ⟨S⟩)
    (h : ∀ (a : α f), X.map (sigmaIncl f a).op x = X.map (sigmaIncl f a).op y) : x = y := by
  apply injective_of_mono (X.mapIso (sigmaIso f).op).hom
  apply injective_of_mono (sigmaComparison X (fun a ↦ (part f a).1))
  ext a
  specialize h a
  rw [← sigmaComparison_comp_sigmaIso] at h
  exact h

lemma incl_of_counitAppApp (a : α f) :
    Y.map (sigmaIncl f a).op (counitAppApp S Y f) = counitAppAppImage f a := by
  rw [← sigmaComparison_comp_sigmaIso, Functor.mapIso_hom, Iso.op_hom, types_comp_apply]
  simp only [counitAppApp, Functor.mapIso_inv, ← Iso.op_hom, types_comp_apply,
    ← FunctorToTypes.map_comp_apply, Iso.inv_hom_id, FunctorToTypes.map_id_apply]
  exact congrFun (inv_hom_id_apply (asIso (sigmaComparison Y (fun a ↦ (part f a).1)))
    (counitAppAppImage f)) _

/--
This is an auxiliary definition, the details do not matter. What's important is that this map exists
so that the lemma `incl_comap` works.
-/
def component_hom (a : α (f.comap g)) :
    part _ a ⟶ part _ (α.mk f (g a.preimage)) where
  toFun x := ⟨g x.val, by
    simp only [α.mk, Set.mem_preimage, Set.mem_singleton_iff]
    erw [α.map_eq_image_comap, α.map_preimage_eq_image_comap]⟩
  continuous_toFun := by
    exact Continuous.subtype_mk (Continuous.comp g.continuous continuous_subtype_val) _
    -- term mode gives "unknown free variable" error.

lemma incl_comap {S T : (CompHausLike P)ᵒᵖ}
    (f : LocallyConstant S.unop (Y.obj (op (CompHausLike.of P PUnit.{u+1}))))
      (g : S ⟶ T) (a : α (f.comap g.unop)) :
        g ≫ (sigmaIncl (f.comap g.unop) a).op =
          (sigmaIncl f _).op ≫ (component_hom g.unop f a).op := by
  rfl

/-- The counit is natural in the compact Hausdorff space `S` -/
@[simps!]
noncomputable def counitApp (Y : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts Y] :
    (functorToPresheaves.obj (Y.obj (op (CompHausLike.of P PUnit.{u+1})))) ⟶ Y where
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

theorem hom_apply_counitAppApp (X : (CompHausLike.{u} P)ᵒᵖ ⥤ Type max u w)
    [PreservesFiniteProducts X] (g : Y ⟶ X)
    (a : α (f.map (g.app (op (CompHausLike.of P PUnit.{u+1}))))) :
      X.map (sigmaIncl (map (g.app (op (CompHausLike.of P PUnit.{u+1}))) f) a).op
        (g.app ⟨S⟩ (counitAppApp S Y f)) =
          counitAppAppImage (map (g.app (op (CompHausLike.of P PUnit.{u+1}))) f) a := by
  apply locallyConstantCondensed_ext (f.comap (sigmaIncl _ _))
  intro b
  simp only [counitAppAppImage, ← FunctorToTypes.map_comp_apply, ← op_comp,
    CompHausLike.coe_of, map_apply, IsTerminal.comp_from,
    ← α.map_preimage_eq_image_map f (g.app (op (CompHausLike.of P PUnit.{u+1})))]
  change (_ ≫ X.map _) _ = (_ ≫ X.map _) _
  simp only [← g.naturality, sigmaIncl_comp_sigmaIncl]
  simp only [op_comp, Functor.map_comp, types_comp_apply, incl_of_counitAppApp]
  simp only [counitAppAppImage, ← FunctorToTypes.map_comp_apply, ← op_comp, terminal.comp_from]
  erw [α.mk_image]
  change (Y.map _ ≫ _) _ = (Y.map _ ≫ _) _
  simp only [g.naturality]
  simp only [types_comp_apply]
  have := α.map_preimage_eq_image (f := g.app _ ∘ f) (a := a)
  simp only [Function.comp_apply] at this
  rw [this]
  apply congrArg
  erw [← α.mem_iff_eq_image (f := g.app _ ∘ f)]
  exact (b.preimage).prop

end Adjunction

end CompHausLike.LocallyConstant

open CategoryTheory CompHausLike CompHausLike.LocallyConstant Condensed Limits Opposite

namespace Condensed.LocallyConstant

variable (P : TopCat.{u} → Prop) (X : TopCat.{max u w})
    [CompHausLike.HasExplicitFiniteCoproducts.{0} P] [CompHausLike.HasExplicitPullbacks.{u} P]
    (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/-- `locallyConstantIsoContinuousMap` is a natural isomorphism. -/
noncomputable def functorToPresheavesIsoTopCatToCondensed (X : Type (max u w)) :
    functorToPresheaves.{u, w}.obj X ≅
      ((topCatToSheafCompHausLike P hs).obj (TopCat.discrete.obj X)).val :=
  NatIso.ofComponents (fun S ↦ locallyConstantIsoContinuousMap _ _)

/-- `Condensed.LocallyConstant.functorToPresheaves` lands in condensed sets. -/
@[simps]
def functor :
    have := CompHausLike.preregular hs
    Type (max u w) ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w)) where
  obj X := {
    val := functorToPresheaves.{u, w}.obj X
    cond := by
      rw [Presheaf.isSheaf_of_iso_iff
        (functorToPresheavesIsoTopCatToCondensed P hs X)]
      exact ((topCatToSheafCompHausLike P hs).obj (TopCat.discrete.obj X)).cond
  }
  map f := ⟨functorToPresheaves.{u, w}.map f⟩

/--
`Condensed.LocallyConstant.functor` is naturally isomorphic to the restriction of
`topCatToCondensed` to discrete topological spaces.
-/
noncomputable def functorIsoTopCatToCondensed :
    functor.{u, w} P hs ≅ TopCat.discrete.{max w u} ⋙ topCatToSheafCompHausLike P hs :=
  NatIso.ofComponents (fun X ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (functorToPresheavesIsoTopCatToCondensed P hs X))

variable [CompHausLike.HasProp P PUnit.{u+1}] (J : GrothendieckTopology (CompHausLike.{u} P))
  (A : Type*) [Category A]


variable [∀ (S : CompHausLike.{u} P) (p : S → Prop), HasProp P (Subtype p)]
variable [HasExplicitFiniteCoproducts.{u} P]
variable  [HasExplicitPullbacks P]

noncomputable instance {C A : Type*} [Category C] [Category A] [Preregular C] [FinitaryExtensive C]
    (F : Sheaf (coherentTopology C) A)
    [HasPullbacks C] : PreservesFiniteProducts F.val :=
  Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition F.val |>.mp F.cond |>.1.some

/-- The counit is natural in both the compact Hausdorff space `S` and the condensed set `Y` -/
@[simps]
noncomputable def counit :
    have := CompHausLike.preregular hs
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ ⋙ functor.{u, w} P hs ⟶
        𝟭 (Sheaf (coherentTopology (CompHausLike.{u} P)) (Type (max u w))) where
  app X :=
    have := CompHausLike.preregular hs
    ⟨counitApp.{u, w} X.val⟩
  naturality X Y g := by
    have := CompHausLike.preregular hs
    apply Sheaf.hom_ext
    simp only [functor, id_eq, eq_mpr_eq_cast, Functor.comp_obj, Functor.flip_obj_obj,
      sheafToPresheaf_obj, Functor.id_obj, Functor.comp_map, Functor.flip_obj_map,
      sheafToPresheaf_map, Sheaf.instCategorySheaf_comp_val, Functor.id_map]
    ext S (f : LocallyConstant _ _)
    simp only [FunctorToTypes.comp, counitApp_app]
    apply locallyConstantCondensed_ext.{u, w} (f.map (g.val.app (op
      (CompHausLike.of P PUnit.{u+1}))))
    intro a
    simp only [op_unop, functorToPresheaves_map_app]
    erw [incl_of_counitAppApp]
    rw [← hom_apply_counitAppApp]

/--
The unit of the adjunciton is given by mapping each element to the corresponding constant map.
-/
@[simps]
def unit : 𝟭 _ ⟶ functor P hs ⋙ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ where
  app X x := LocallyConstant.const _ x

theorem locallyConstantAdjunction_left_triangle (X : Type max u w) :
    functorToPresheaves.{u, w}.map ((unit P hs).app X) ≫
      ((counit P hs).app ((functor P hs).obj X)).val =
    𝟙 (functorToPresheaves.obj X) := by
  ext ⟨S⟩ (f : LocallyConstant _ X)
  simp only [Functor.id_obj, Functor.comp_obj, FunctorToTypes.comp, NatTrans.id_app,
    functorToPresheaves_obj_obj, types_id_apply]
  simp only [counit, counitApp_app]
  have := CompHausLike.preregular hs
  apply locallyConstantCondensed_ext
    (X := ((functor P hs).obj X).val) (Y := ((functor.{u, w} P hs).obj X).val)
      (f.map ((unit P hs).app X))
  intro a
  erw [incl_of_counitAppApp]
  simp only [functor_obj_val, functorToPresheaves_obj_obj, coe_of, Functor.id_obj,
    counitAppAppImage, LocallyConstant.map_apply, functorToPresheaves_obj_map, Quiver.Hom.unop_op]
  ext x
  erw [← Aux.α.map_eq_image _ a x]
  rfl

/-- The unit of the adjunction is an iso. -/
noncomputable def unitIso : 𝟭 (Type max u w) ≅ functor.{u, w} P hs ⋙
    (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ where
  hom := unit P hs
  inv := { app := fun X f ↦ f.toFun PUnit.unit }

/--
`Condensed.LocallyConstant.functor` is left adjoint to the forgetful functor.
-/
-- Note: adding `@[simps]` makes the linter complain.
noncomputable def adjunction :
    functor.{u, w} P hs ⊣ (sheafSections _ _).obj ⟨CompHausLike.of P PUnit.{u+1}⟩ :=
  Adjunction.mkOfUnitCounit {
    unit := unit P hs
    counit := counit P hs
    left_triangle := by
      ext X : 2
      simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.flip_obj_obj,
        sheafToPresheaf_obj, functor_obj_val, functorToPresheaves_obj_obj, coe_of, whiskerRight_app,
        Functor.associator_hom_app, whiskerLeft_app, Category.id_comp, NatTrans.id_app']
      apply Sheaf.hom_ext
      rw [Sheaf.instCategorySheaf_comp_val, Sheaf.instCategorySheaf_id_val]
      exact locallyConstantAdjunction_left_triangle P hs X
    right_triangle := by
      ext X (x : X.val.obj _)
      simp only [Functor.comp_obj, Functor.id_obj, Functor.flip_obj_obj, sheafToPresheaf_obj,
        FunctorToTypes.comp, whiskerLeft_app, unit_app, coe_of, Functor.associator_inv_app,
        functor_obj_val, functorToPresheaves_obj_obj, types_id_apply, whiskerRight_app,
        Functor.flip_obj_map, sheafToPresheaf_map, counit_app_val, counitApp_app, NatTrans.id_app']
      have := CompHausLike.preregular hs
      let _ : PreservesFiniteProducts
          ((sheafToPresheaf (coherentTopology (CompHausLike P)) (Type (max u w))).obj X) :=
        (inferInstance : PreservesFiniteProducts (Sheaf.val _))
      apply locallyConstantCondensed_ext ((unit P hs).app _ x)
      intro a
      erw [incl_of_counitAppApp]
      simp only [sheafToPresheaf_obj, unit_app, coe_of, counitAppAppImage,
        LocallyConstant.coe_const]
      have := Aux.α.map_eq_image _ a ⟨PUnit.unit, by
        simp [Aux.α.mem_iff_eq_image (a := a), ← Aux.α.map_preimage_eq_image]⟩
      erw [← this]
      simp only [coe_of, unit_app, LocallyConstant.coe_const, Function.const_apply]
      congr }

instance : IsIso (adjunction P hs).unit := (inferInstance : IsIso (unitIso P hs).hom)

end Condensed.LocallyConstant

open Condensed.LocallyConstant

/-- The functor from sets to condensed sets given by locally constant maps into the set. -/
abbrev CondensedSet.LocallyConstant.functor : Type (u+1) ⥤ CondensedSet.{u} :=
  Condensed.LocallyConstant.functor.{u, u+1} (P := fun _ ↦ True)
    (hs := fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

/--
`CondensedSet.LocallyConstant.functor` is isomorphic to `Condensed.discrete`
(by uniqueness of adjoints).
-/
noncomputable def CondensedSet.LocallyConstant.iso :
    CondensedSet.LocallyConstant.functor ≅ discrete (Type (u+1)) :=
  (adjunction _ _).leftAdjointUniq (discreteUnderlyingAdj _)

/-- `CondensedSet.LocallyConstant.functor` is fully faithful. -/
noncomputable def fullyFaithfulCondensedSetLocallyConstantFunctor :
    CondensedSet.LocallyConstant.functor.FullyFaithful :=
  (adjunction.{u, u+1} _ _).fullyFaithfulLOfIsIsoUnit

noncomputable instance : CondensedSet.LocallyConstant.functor.Faithful :=
  fullyFaithfulCondensedSetLocallyConstantFunctor.faithful

noncomputable instance : CondensedSet.LocallyConstant.functor.Full :=
  fullyFaithfulCondensedSetLocallyConstantFunctor.full

instance : (discrete (Type _)).Faithful := Functor.Faithful.of_iso
  CondensedSet.LocallyConstant.iso

noncomputable instance : (discrete (Type _)).Full := Functor.Full.of_iso
  CondensedSet.LocallyConstant.iso

/-- The functor from sets to light condensed sets given by locally constant maps into the set. -/
abbrev LightCondSet.LocallyConstant.functor : Type u ⥤ LightCondSet.{u} :=
  Condensed.LocallyConstant.functor.{u, u}
    (P := fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X)
    (hs := fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

instance (S : LightProfinite.{u}) (p : S → Prop) :
    HasProp (fun X ↦ TotallyDisconnectedSpace X ∧ SecondCountableTopology X) (Subtype p) :=
  ⟨⟨(inferInstance : TotallyDisconnectedSpace (Subtype p)),
    (inferInstance : SecondCountableTopology {s | p s})⟩⟩

/--
`LightCondSet.LocallyConstant.functor` is isomorphic to `LightCondensed.discrete`
(by uniqueness of adjoints).
-/
noncomputable def LightCondSet.LocallyConstant.iso :
    LightCondSet.LocallyConstant.functor ≅ LightCondensed.discrete (Type u) :=
  (adjunction _ _).leftAdjointUniq (LightCondensed.discreteUnderlyingAdj _)

/-- `LightCondSet.LocallyConstant.functor` is fully faithful. -/
noncomputable def fullyFaithfulLightCondSetLocallyConstantFunctor :
    LightCondSet.LocallyConstant.functor.{u}.FullyFaithful :=
  (adjunction _ _).fullyFaithfulLOfIsIsoUnit

instance : LightCondSet.LocallyConstant.functor.{u}.Faithful :=
  fullyFaithfulLightCondSetLocallyConstantFunctor.faithful

instance : LightCondSet.LocallyConstant.functor.Full :=
  fullyFaithfulLightCondSetLocallyConstantFunctor.full

instance : (LightCondensed.discrete (Type u)).Faithful := Functor.Faithful.of_iso
  LightCondSet.LocallyConstant.iso.{u}

instance : (LightCondensed.discrete (Type u)).Full := Functor.Full.of_iso
  LightCondSet.LocallyConstant.iso.{u}
