/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.Topology.Algebra.OpenSubgroup

/-!

# Essential surjectivity of fiber functors

Let `F : C ⥤ FintypeCat` be a fiber functor of a Galois category `C` and denote by
`H` the induced functor `C ⥤ Action (Aut F) FintypeCat`.

In this file we show that the essential image of `H` are the finite `Aut F`-sets where
the `Aut F` action is continuous.

## Main results

- `exists_lift_of_quotient_openSubgroup`: If `U` is an open subgroup of `Aut F`, then
  there exists an object `X` such that `F.obj X` is isomorphic to `Aut F ⧸ U` as
  `Aut F`-sets.

## Strategy

We use the fact that the category of
finite `Aut F`-sets with continuous action is a Galois category (TODO). In particular, every
continuous, finite `Aut F`-set `Y` has a decomposition into connected components and each connected
component is of the form `Aut F ⧸ U` for an open subgroup `U` (TODO). Since `H` preserves
finite coproducts, it hence suffices to treat the case `Y = Aut F ⧸ U`.
For the case `Y = Aut F ⧸ U` we closely follow the second part of Stacks Project Tag 0BN4.

-/

universe u

namespace CategoryTheory

namespace PreGaloisCategory

variable {C : Type u} [Category.{u} C] (F : C ⥤ FintypeCat.{u})

open Limits Functor

variable [GaloisCategory C] [FiberFunctor F]

noncomputable local instance fintypeQuotient (H : OpenSubgroup (Aut F)) :
    Fintype (Aut F ⧸ (H : Subgroup (Aut F))) :=
  have : Finite (Aut F ⧸ H.toSubgroup) := H.toSubgroup.quotient_finite_of_isOpen H.isOpen'
  Fintype.ofFinite _

noncomputable local instance (X : C) (x : F.obj X) :
    Fintype (Aut F ⧸ (MulAction.stabilizer (Aut F) x)) :=
  fintypeQuotient F ⟨MulAction.stabilizer (Aut F) x, stabilizer_isOpen (Aut F) x⟩

/-- If `X` is connected and `x` is in the fiber of `X`, `F.obj X` is isomorphic
to the quotient of `Aut F` by the stabilizer of `x` as `Aut F`-sets. -/
noncomputable def fiberIsoQuotientStabilizer (X : C) [IsConnected X] (x : F.obj X) :
    (functorToAction F).obj X ≅ Aut F ⧸ₐ MulAction.stabilizer (Aut F) x :=
  let e : ((functorToAction F).obj X).V ≃ Aut F ⧸ MulAction.stabilizer (Aut F) x :=
    (Equiv.Set.univ (F.obj X)).symm.trans <|
      (Equiv.setCongr ((MulAction.orbit_eq_univ (Aut F) x).symm)).trans <|
      MulAction.orbitEquivQuotientStabilizer (Aut F) x
  Iso.symm <| Action.mkIso (FintypeCat.equivEquivIso e.symm) <| fun σ ↦ by
    ext (a : Aut F ⧸ MulAction.stabilizer (Aut F) x)
    obtain ⟨τ, rfl⟩ := Quotient.exists_rep a
    rfl

section

open Action.FintypeCat

variable {F} (V : OpenSubgroup (Aut F)) {U : OpenSubgroup (Aut F)}
  (h : Subgroup.Normal U.toSubgroup) {A : C} (u : (functorToAction F).obj A ≅ Aut F ⧸ₐ U.toSubgroup)

/-

### Strategy outline

Let `A` be object of `C` with fiber `Aut F`-isomorphic to `Aut F ⧸ U` for an open normal
subgroup `U`. Then for any open subgroup `V` of `Aut F`, `V ⧸ (U ⊓ V)` acts on `A`. This
induces the diagram `quotientDiag`. Now assume `U ≤ V`. Then we can also postcompose
the diagram `quotientDiag` with `F`. The goal of this section is to compute that the colimit
of this composed diagram is `Aut F ⧸ V`. Finally, we obtain `F.obj (A ⧸ V) ≅ Aut F ⧸ V` as
`Aut F`-sets.
-/

private noncomputable def quotientToEndObjectHom :
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
private noncomputable def quotientDiag : SingleObj (V.toSubgroup ⧸ Subgroup.subgroupOf U V) ⥤ C :=
  SingleObj.functor (quotientToEndObjectHom V h u)

variable {V} (hUinV : U ≤ V)

@[simps]
private noncomputable def coconeQuotientDiag :
    Cocone (quotientDiag V h u ⋙ functorToAction F) where
  pt := Aut F ⧸ₐ V.toSubgroup
  ι := SingleObj.natTrans (u.hom ≫ quotientToQuotientOfLE V.toSubgroup U.toSubgroup hUinV) <| by
    intro (m : V ⧸ Subgroup.subgroupOf U V)
    simp only [const_obj_obj, Functor.comp_map, const_obj_map, Category.comp_id]
    rw [← cancel_epi (u.inv), Iso.inv_hom_id_assoc]
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    induction' m, x using Quotient.inductionOn₂ with σ μ
    suffices h : ⟦μ * σ⁻¹⟧ = ⟦μ⟧ by
      simp only [quotientToQuotientOfLE_hom_mk, quotientDiag_map,
        functorToAction_map_quotientToEndObjectHom V _ u]
      simpa
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply).mpr
    simp

@[simps]
private noncomputable def coconeQuotientDiagDesc
    (s : Cocone (quotientDiag V h u ⋙ functorToAction F)) :
      (coconeQuotientDiag h u hUinV).pt ⟶ s.pt where
  hom := Quotient.lift (fun σ ↦ (u.inv ≫ s.ι.app (SingleObj.star _)).hom ⟦σ⟧) <| fun σ τ hst ↦ by
    let J' := quotientDiag V h u ⋙ functorToAction F
    let m : End (SingleObj.star (V.toSubgroup ⧸ Subgroup.subgroupOf U V)) :=
      ⟦⟨σ⁻¹ * τ, (QuotientGroup.leftRel_apply).mp hst⟩⟧
    have h1 : J'.map m ≫ s.ι.app (SingleObj.star _) = s.ι.app (SingleObj.star _) := s.ι.naturality m
    conv_rhs => rw [← h1]
    have h2 : (J'.map m).hom (u.inv.hom ⟦τ⟧) = u.inv.hom ⟦σ⟧ := by
      simp only [comp_obj, quotientDiag_obj, Functor.comp_map, quotientDiag_map, J',
        functorToAction_map_quotientToEndObjectHom V h u m]
      show (u.inv ≫ u.hom ≫ _ ≫ u.inv).hom ⟦τ⟧ = u.inv.hom ⟦σ⟧
      simp [m]
    simp only [← h2, const_obj_obj, Action.comp_hom, FintypeCat.comp_apply]
  comm g := by
    ext (x : Aut F ⧸ V.toSubgroup)
    induction' x using Quotient.inductionOn with σ
    simp only [const_obj_obj]
    show (((Aut F ⧸ₐ U.toSubgroup).ρ g ≫ u.inv.hom) ≫ (s.ι.app (SingleObj.star _)).hom) ⟦σ⟧ =
      ((s.ι.app (SingleObj.star _)).hom ≫ s.pt.ρ g) (u.inv.hom ⟦σ⟧)
    have : ((functorToAction F).obj A).ρ g ≫ (s.ι.app (SingleObj.star _)).hom =
        (s.ι.app (SingleObj.star _)).hom ≫ s.pt.ρ g :=
      (s.ι.app (SingleObj.star _)).comm g
    rw [← this, u.inv.comm g]
    rfl

/-- The constructed cocone `coconeQuotientDiag` on the diagram `quotientDiag` is colimiting. -/
private noncomputable def coconeQuotientDiagIsColimit :
    IsColimit (coconeQuotientDiag h u hUinV) where
  desc := coconeQuotientDiagDesc h u hUinV
  fac s j := by
    apply (cancel_epi u.inv).mp
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    induction' x using Quotient.inductionOn with σ
    simp
    rfl
  uniq s f hf := by
    apply Action.hom_ext
    ext (x : Aut F ⧸ V.toSubgroup)
    induction' x using Quotient.inductionOn with σ
    simp [← hf (SingleObj.star _)]

end

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
  let u := fiberIsoQuotientStabilizer F A a
  have hUnormal : U.toSubgroup.Normal := stabilizer_normal_of_isGalois F A a
  have h1 (σ : Aut F) (σinU : σ ∈ U) : σ.hom.app A = 𝟙 (F.obj A) := by
    have hi : (Aut F ⧸ₐ MulAction.stabilizer (Aut F) a).ρ σ = 𝟙 _ := by
      refine FintypeCat.hom_ext _ _ (fun x ↦ ?_)
      induction' x using Quotient.inductionOn with τ
      show ⟦σ * τ⟧ = ⟦τ⟧
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
  have := V.quotient_finite_of_isOpen' U V.isOpen' U.isOpen'
  exact ⟨colimit (quotientDiag V hUnormal u),
    ⟨preservesColimitIso (functorToAction F) (quotientDiag V hUnormal u) ≪≫
    colimit.isoColimitCocone ⟨coconeQuotientDiag hUnormal u hUinV,
    coconeQuotientDiagIsColimit hUnormal u hUinV⟩⟩⟩

end PreGaloisCategory

end CategoryTheory
