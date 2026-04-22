/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Full
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!

# Essential surjectivity of fiber functors

Let `F : C ⥤ FintypeCat` be a fiber functor of a Galois category `C` and denote by
`H` the induced functor `C ⥤ Action FintypeCat (Aut F)`.

In this file we show that the essential image of `H` consists of the finite `Aut F`-sets where
the `Aut F` action is continuous.

## Main results

- `exists_lift_of_quotient_openSubgroup`: If `U` is an open subgroup of `Aut F`, then
  there exists an object `X` such that `F.obj X` is isomorphic to `Aut F ⧸ U` as
  `Aut F`-sets.
- `exists_lift_of_continuous`: If `X` is a finite, discrete `Aut F`-set with continuous
  `Aut F`-action, then
  there exists an object `A` such that `F.obj A` is isomorphic to `X` as
  `Aut F`-sets.

## Strategy

We first show that every finite, discrete `Aut F`-set `Y` with continuous `Aut F`-action has a
decomposition into connected components and each connected component is of the form `Aut F ⧸ U`
for an open subgroup `U`.
Since `H` preserves finite coproducts, it hence suffices to treat the case `Y = Aut F ⧸ U`.
For the case `Y = Aut F ⧸ U` we closely follow the second part of Stacks Project Tag 0BN4.

-/

@[expose] public section

noncomputable section

universe u₁ u₂

namespace CategoryTheory

namespace PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {F : C ⥤ FintypeCat.{u₁}}

open Limits Functor

variable [GaloisCategory C] [FiberFunctor F]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

set_option backward.privateInPublic true in
private local instance fintypeQuotient (H : OpenSubgroup (G)) :
    Fintype (G ⧸ (H : Subgroup (G))) :=
  have : Finite (G ⧸ H.toSubgroup) := H.toSubgroup.quotient_finite_of_isOpen H.isOpen'
  Fintype.ofFinite _

set_option backward.privateInPublic true in
private local instance fintypeQuotientStabilizer {X : Type*} [MulAction G X]
    [TopologicalSpace X] [ContinuousSMul G X] [DiscreteTopology X] (x : X) :
    Fintype (G ⧸ (MulAction.stabilizer (G) x)) :=
  fintypeQuotient ⟨MulAction.stabilizer (G) x, stabilizer_isOpen (G) x⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `X` is a finite discrete `G`-set with continuous `G`-action, it can be written as the
finite disjoint union of quotients of the form `G ⧸ Uᵢ` for open subgroups `(Uᵢ)`. Note that this
is simply the decomposition into orbits. -/
lemma has_decomp_quotients (X : Action FintypeCat G)
    [TopologicalSpace X.V] [DiscreteTopology X.V] [ContinuousSMul G X.V] :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → OpenSubgroup (G)),
      Nonempty ((∐ fun i ↦ G ⧸ₐ (f i).toSubgroup) ≅ X) := by
  obtain ⟨ι, hf, f, u, hc⟩ := has_decomp_connected_components' X
  letI (i : ι) : TopologicalSpace (f i).V := ⊥
  haveI (i : ι) : DiscreteTopology (f i).V := ⟨rfl⟩
  have (i : ι) : ContinuousSMul G (f i).V := ContinuousSMul.mk <| by
    let r : f i ⟶ X := Sigma.ι f i ≫ u.hom
    let r'' (p : G × (f i).V) : G × X.V := (p.1, r.hom p.2)
    let q (p : G × X.V) : X.V := (X.ρ p.1).hom p.2
    let q' (p : G × (f i).V) : (f i).V := ((f i).ρ p.1).hom p.2
    have heq : q ∘ r'' = r.hom ∘ q' := by
      ext (p : G × (f i).V)
      exact (ConcreteCategory.congr_hom (r.comm p.1) p.2).symm
    have hrinj : Function.Injective r.hom :=
      (ConcreteCategory.mono_iff_injective_of_preservesPullback r).mp <| mono_comp _ _
    let t₁ : TopologicalSpace (G × (f i).V) := inferInstance
    change @Continuous _ _ _ ⊥ q'
    have : TopologicalSpace.induced r.hom inferInstance = ⊥ := by
      rw [← le_bot_iff]
      exact fun s _ ↦ ⟨r.hom '' s, ⟨isOpen_discrete (r.hom '' s), Set.preimage_image_eq s hrinj⟩⟩
    rw [← this, continuous_induced_rng, ← heq]
    exact Continuous.comp continuous_smul (by fun_prop)
  have (i : ι) : ∃ (U : OpenSubgroup (G)), (Nonempty ((f i) ≅ G ⧸ₐ U.toSubgroup)) := by
    obtain ⟨(x : (f i).V)⟩ := nonempty_fiber_of_isConnected (forget₂ _ _) (f i)
    let U : OpenSubgroup (G) := ⟨MulAction.stabilizer (G) x, stabilizer_isOpen (G) x⟩
    exact ⟨U, ⟨FintypeCat.isoQuotientStabilizerOfIsConnected (f i) x⟩⟩
  choose g ui using this
  exact ⟨ι, hf, g, ⟨(Sigma.mapIso (fun i ↦ (ui i).some)).symm ≪≫ u⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `X` is connected and `x` is in the fiber of `X`, `F.obj X` is isomorphic
to the quotient of `Aut F` by the stabilizer of `x` as `Aut F`-sets. -/
def fiberIsoQuotientStabilizer (X : C) [IsConnected X] (x : F.obj X) :
    (functorToAction F).obj X ≅ Aut F ⧸ₐ MulAction.stabilizer (Aut F) x :=
  haveI : IsConnected ((functorToAction F).obj X) := PreservesIsConnected.preserves
  letI : Fintype (Aut F ⧸ MulAction.stabilizer (Aut F) x) := fintypeQuotientStabilizer x
  FintypeCat.isoQuotientStabilizerOfIsConnected ((functorToAction F).obj X) x

section

open Action.FintypeCat

variable (V : OpenSubgroup (Aut F)) {U : OpenSubgroup (Aut F)}
  (h : Subgroup.Normal U.toSubgroup) {A : C} (u : (functorToAction F).obj A ≅ Aut F ⧸ₐ U.toSubgroup)

/-

### Strategy outline

Let `A` be an object of `C` with fiber `Aut F`-isomorphic to `Aut F ⧸ U` for an open normal
subgroup `U`. Then for any open subgroup `V` of `Aut F`, `V ⧸ (U ⊓ V)` acts on `A`. This
induces the diagram `quotientDiag`. Now assume `U ≤ V`. Then we can also postcompose
the diagram `quotientDiag` with `F`. The goal of this section is to compute that the colimit
of this composed diagram is `Aut F ⧸ V`. Finally, we obtain `F.obj (A ⧸ V) ≅ Aut F ⧸ V` as
`Aut F`-sets.
-/

private def quotientToEndObjectHom :
    V.toSubgroup ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →* End A :=
  let ff : (functorToAction F).FullyFaithful := FullyFaithful.ofFullyFaithful (functorToAction F)
  let e : End A ≃* End (Aut F ⧸ₐ U.toSubgroup) := (ff.mulEquivEnd A).trans (Iso.conj u)
  e.symm.toMonoidHom.comp (quotientToEndHom V.toSubgroup U.toSubgroup)

private lemma functorToAction_map_quotientToEndObjectHom
    (m : SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup) ⟶
      SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup)) :
    (functorToAction F).map (quotientToEndObjectHom V h u m) =
      u.hom ≫ quotientToEndHom V.toSubgroup U.toSubgroup m ≫ u.inv := by
  simp [← cancel_epi u.inv, ← cancel_mono u.hom, ← Iso.conj_apply, quotientToEndObjectHom]

@[simps!]
private def quotientDiag : SingleObj (V.toSubgroup ⧸ Subgroup.subgroupOf U V) ⥤ C :=
  SingleObj.functor (quotientToEndObjectHom V h u)

variable {V} (hUinV : U ≤ V)

set_option backward.isDefEq.respectTransparency false in
@[simps]
private def coconeQuotientDiag :
    Cocone (quotientDiag V h u ⋙ functorToAction F) where
  pt := Aut F ⧸ₐ V.toSubgroup
  ι := SingleObj.natTrans (u.hom ≫ quotientToQuotientOfLE V.toSubgroup U.toSubgroup hUinV) <| by
    intro (m : V ⧸ Subgroup.subgroupOf U V)
    simp only [const_obj_obj, Functor.comp_map, const_obj_map, Category.comp_id]
    rw [← cancel_epi (u.inv), Iso.inv_hom_id_assoc]
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    induction m, x using Quotient.inductionOn₂ with | _ σ μ
    suffices h : ⟦μ * σ⁻¹⟧ = ⟦μ⟧ by
      simp only [quotientToQuotientOfLE_hom_mk, quotientDiag_map,
        functorToAction_map_quotientToEndObjectHom V _ u]
      simpa
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply).mpr
    simp

set_option backward.isDefEq.respectTransparency false in
@[simps]
private def coconeQuotientDiagDesc
    (s : Cocone (quotientDiag V h u ⋙ functorToAction F)) :
      (coconeQuotientDiag h u hUinV).pt ⟶ s.pt where
  hom := FintypeCat.homMk
    (Quotient.lift (fun σ ↦ (u.inv ≫ s.ι.app (SingleObj.star _)).hom ⟦σ⟧) <| fun σ τ hst ↦ by
      let J' := quotientDiag V h u ⋙ functorToAction F
      let m : End (SingleObj.star (V.toSubgroup ⧸ Subgroup.subgroupOf U V)) :=
        ⟦⟨σ⁻¹ * τ, (QuotientGroup.leftRel_apply).mp hst⟩⟧
      have h1 : J'.map m ≫ s.ι.app (SingleObj.star _) = s.ι.app (SingleObj.star _) :=
        s.ι.naturality m
      conv_rhs => rw [← h1]
      have h2 : (J'.map m).hom (u.inv.hom ⟦τ⟧) = u.inv.hom ⟦σ⟧ := by
        simp only [comp_obj, quotientDiag_obj, Functor.comp_map, quotientDiag_map, J',
          functorToAction_map_quotientToEndObjectHom V h u m]
        change (u.inv ≫ u.hom ≫ _ ≫ u.inv).hom ⟦τ⟧ = u.inv.hom ⟦σ⟧
        simp [m]
      simp [← h2, J'])
  comm g := by
    ext (x : Aut F ⧸ V.toSubgroup)
    induction x using Quotient.inductionOn with | _ σ
    simp only [const_obj_obj]
    change (((Aut F ⧸ₐ U.toSubgroup).ρ g ≫ u.inv.hom) ≫ (s.ι.app (SingleObj.star _)).hom) ⟦σ⟧ =
      ((s.ι.app (SingleObj.star _)).hom ≫ s.pt.ρ g) (u.inv.hom ⟦σ⟧)
    have : ((functorToAction F).obj A).ρ g ≫ (s.ι.app (SingleObj.star _)).hom =
        (s.ι.app (SingleObj.star _)).hom ≫ s.pt.ρ g :=
      (s.ι.app (SingleObj.star _)).comm g
    rw [← this, u.inv.comm g]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The constructed cocone `coconeQuotientDiag` on the diagram `quotientDiag` is colimiting. -/
private def coconeQuotientDiagIsColimit :
    IsColimit (coconeQuotientDiag h u hUinV) where
  desc := coconeQuotientDiagDesc h u hUinV
  fac s j := by
    apply (cancel_epi u.inv).mp
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    induction x using Quotient.inductionOn
    simp
    rfl
  uniq s f hf := by
    apply Action.hom_ext
    ext (x : Aut F ⧸ V.toSubgroup)
    induction x using Quotient.inductionOn with | _ σ
    simp [← hf (SingleObj.star _), ← ConcreteCategory.comp_apply]

end

set_option backward.isDefEq.respectTransparency false in
/-- For every open subgroup `V` of `Aut F`, there exists an `X : C` such that
`F.obj X ≅ Aut F ⧸ V` as `Aut F`-sets. -/
lemma exists_lift_of_quotient_openSubgroup (V : OpenSubgroup (Aut F)) :
    ∃ (X : C), Nonempty ((functorToAction F).obj X ≅ Aut F ⧸ₐ V.toSubgroup) := by
  obtain ⟨I, hf, hc, hi⟩ := exists_set_ker_evaluation_subset_of_isOpen F (one_mem V) V.isOpen'
  haveI (X : I) : IsConnected X.val := hc X X.property
  haveI (X : I) : Nonempty (F.obj X.val) := nonempty_fiber_of_isConnected F X
  have hn : Nonempty (F.obj <| (∏ᶜ fun X : I => X)) := nonempty_fiber_pi_of_nonempty_of_finite F _
  obtain ⟨A, f, hgal⟩ := exists_hom_from_galois_of_fiber_nonempty F (∏ᶜ fun X : I => X) hn
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  let U : OpenSubgroup (Aut F) := ⟨MulAction.stabilizer (Aut F) a, stabilizer_isOpen (Aut F) a⟩
  let u := fiberIsoQuotientStabilizer A a
  have hUnormal : U.toSubgroup.Normal := stabilizer_normal_of_isGalois F A a
  have h1 (σ : Aut F) (σinU : σ ∈ U) : σ.hom.app A = 𝟙 (F.obj A) := by
    have hi : (Aut F ⧸ₐ MulAction.stabilizer (Aut F) a).ρ σ = 𝟙 _ := by
      refine FintypeCat.hom_ext _ _ (fun x ↦ ?_)
      induction x using Quotient.inductionOn with | _ τ
      change ⟦σ * τ⟧ = ⟦τ⟧
      apply Quotient.sound
      apply (QuotientGroup.leftRel_apply).mpr
      simp only [mul_inv_rev]
      exact Subgroup.Normal.conj_mem hUnormal _ (Subgroup.inv_mem U.toSubgroup σinU) _
    simp [← cancel_mono u.hom.hom, show σ.hom.app A ≫ u.hom.hom = _ from u.hom.comm σ, hi]
  have h2 (σ : Aut F) (σinU : σ ∈ U) : ∀ X : I, σ.hom.app X = 𝟙 (F.obj X) := by
    intro ⟨X, hX⟩
    ext (x : F.obj X)
    let p : A ⟶ X := f ≫ Pi.π (fun Z : I => (Z : C)) ⟨X, hX⟩
    have : IsConnected X := hc X hX
    obtain ⟨a, rfl⟩ := surjective_of_nonempty_fiber_of_isConnected F p x
    simp only [FintypeCat.id_apply, FunctorToFintypeCat.naturality, h1 σ σinU]
  have hUinV : (U : Set (Aut F)) ≤ V := fun u uinU ↦ hi u (h2 u uinU)
  have := V.quotient_finite_of_isOpen' (U.subgroupOf V) V.isOpen (V.subgroupOf_isOpen U U.isOpen)
  exact ⟨colimit (quotientDiag V hUnormal u),
    ⟨preservesColimitIso (functorToAction F) (quotientDiag V hUnormal u) ≪≫
    colimit.isoColimitCocone ⟨coconeQuotientDiag hUnormal u hUinV,
    coconeQuotientDiagIsColimit hUnormal u hUinV⟩⟩⟩

/--
If `X` is a finite, discrete `Aut F`-set with continuous `Aut F`-action, then
there exists `A : C` such that `F.obj A ≅ X` as `Aut F`-sets.
-/
@[stacks 0BN4 "Essential surjectivity part"]
theorem exists_lift_of_continuous (X : Action FintypeCat (Aut F))
    [TopologicalSpace X.V] [DiscreteTopology X.V] [ContinuousSMul (Aut F) X.V] :
    ∃ A, Nonempty ((functorToAction F).obj A ≅ X) := by
  obtain ⟨ι, hfin, f, ⟨u⟩⟩ := has_decomp_quotients X
  choose g gu using (fun i ↦ exists_lift_of_quotient_openSubgroup (f i))
  exact ⟨∐ g, ⟨PreservesCoproduct.iso (functorToAction F) g ≪≫
    Sigma.mapIso (fun i ↦ (gu i).some) ≪≫ u⟩⟩

end PreGaloisCategory

end CategoryTheory
