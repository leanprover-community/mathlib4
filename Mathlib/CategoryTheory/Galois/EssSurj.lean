/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Full
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.CategoryTheory.Endomorphism

/-!

# Essential surjectivity of fiber functors

-/

universe u₁ u₂ w u v₁

section Profinite

variable {G : Type*} [Group G]

open Function Set

lemma QuotientGroup.preimage_mk_singleton_mk (H : Subgroup G) (g : G) :
    mk (s := H) ⁻¹' {mk g} = (g * ·) '' H := by
  ext g'
  simp only [mem_preimage, mem_singleton_iff, QuotientGroup.eq, image_mul_left, SetLike.mem_coe]
  rw [← H.inv_mem_iff]
  simp

variable [TopologicalSpace G] [TopologicalGroup G]

instance (X : Type*) [MulAction G X] [Fintype X] : MulAction G (FintypeCat.of X) :=
  inferInstanceAs <| MulAction G X

lemma closed_of_open (U : Subgroup G) (h : IsOpen (U : Set G)) : IsClosed (U : Set G) :=
  OpenSubgroup.isClosed ⟨U, h⟩

lemma Subgroup.discreteTopology (U : Subgroup G) (U_open : IsOpen (U : Set G)) :
    DiscreteTopology (G ⧸ U) := by
  apply singletons_open_iff_discrete.mp
  rintro ⟨g⟩
  erw [isOpen_mk, QuotientGroup.preimage_mk_singleton_mk]
  exact Homeomorph.mulLeft g |>.isOpen_image|>.mpr U_open

def finiteQuotientOfOpen [CompactSpace G] (U : Subgroup G) (h : IsOpen (U : Set G)) :
    Finite (G ⧸ U) :=
  have : CompactSpace (G ⧸ U) := Quotient.compactSpace
  have : DiscreteTopology (G ⧸ U) := U.discreteTopology h
  finite_of_compact_of_discrete

def finiteQuotientSubgroups [CompactSpace G] (U K : Subgroup G) (hUopen : IsOpen (U : Set G))
    (hKpoen : IsOpen (K : Set G)) : Finite (U ⧸ Subgroup.subgroupOf K U) := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp <| IsClosed.isCompact
    <| closed_of_open U hUopen
  apply finiteQuotientOfOpen (Subgroup.subgroupOf K U)
  show IsOpen (((Subgroup.subtype U) ⁻¹' K) : Set U)
  apply Continuous.isOpen_preimage
  continuity
  assumption

end Profinite

section

variable (G : Type*) [Group G] [TopologicalSpace G] {X : Type*} [MulAction G X]
  [TopologicalSpace X] [DiscreteTopology X] [ContinuousSMul G X]

lemma stabilizer_isOpen (x : X) : IsOpen (MulAction.stabilizer G x : Set G) :=
  IsOpen.preimage (f := fun g ↦ g • x) (by fun_prop) (isOpen_discrete {x})

end

namespace CategoryTheory

namespace PreGaloisCategory

variable {C : Type u} [Category.{u} C] (F : C ⥤ FintypeCat.{u})

open Limits Functor

variable [GaloisCategory C] [FiberFunctor F]

noncomputable instance (G : Type u) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (functorToAction F) :=
  Action.preservesColimitsOfShapeOfPreserves _ <|
    inferInstanceAs <| PreservesColimitsOfShape (SingleObj G) F

section

noncomputable instance fintypeQuotient (H : OpenSubgroup (Aut F)) :
    Fintype (Aut F ⧸ (H : Subgroup (Aut F))) :=
  have : Finite (Aut F ⧸ H.toSubgroup) := finiteQuotientOfOpen H.toSubgroup H.isOpen'
  Fintype.ofFinite _

end

notation:10 G:10 " ⧸ₐ " H:10 => Action.FintypeCat.ofMulAction G (FintypeCat.of <| G ⧸ H)

noncomputable instance (X : C) (x : F.obj X) : Fintype (Aut F ⧸ (MulAction.stabilizer (Aut F) x)) :=
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

variable {G : Type*} [Group G] (H N : Subgroup G) [Fintype (G ⧸ N)]

def quotientToEndHom [hn : N.Normal] : H ⧸ Subgroup.subgroupOf N H →* End (G ⧸ₐ N) :=
  let φ' : H →* End (G ⧸ₐ N) := {
    toFun := fun ⟨v, _⟩ ↦ {
      hom := Quotient.lift (fun σ ↦ ⟦σ * v⁻¹⟧) <| fun a b h ↦ Quotient.sound <| by
        apply (QuotientGroup.leftRel_apply).mpr
        simp only [mul_inv_rev, inv_inv]
        convert_to v * (a⁻¹ * b) * v⁻¹ ∈ N
        · group
        · exact Subgroup.Normal.conj_mem hn _ (QuotientGroup.leftRel_apply.mp h) _
      comm := fun (g : G) ↦ by
        ext (x : G ⧸ N)
        induction' x using Quotient.inductionOn with x
        simp only [FintypeCat.comp_apply, Action.FintypeCat.ofMulAction_apply, Quotient.lift_mk]
        letI : SMul G (G ⧸ N) := inferInstance
        show Quotient.lift (fun σ ↦ ⟦σ * v⁻¹⟧) _ (⟦g • x⟧) = _
        simp only [smul_eq_mul, Quotient.lift_mk]
        show _ = ⟦g * _⟧
        rw [mul_assoc]
    }
    map_one' := by
      apply Action.hom_ext
      ext (x : G ⧸ N)
      induction' x using Quotient.inductionOn with x
      simp
    map_mul' := fun σ τ ↦ by
      apply Action.hom_ext
      ext (x : G ⧸ N)
      induction' x using Quotient.inductionOn with x
      show ⟦x * (σ * τ)⁻¹⟧ = ⟦x * τ⁻¹ * σ⁻¹⟧
      rw [mul_inv_rev, mul_assoc, Subgroup.coe_mul]
  }
  QuotientGroup.lift (Subgroup.subgroupOf N H) φ' <| by
  intro u uinU'
  apply Action.hom_ext
  ext (x : G ⧸ N)
  induction' x using Quotient.inductionOn with μ
  apply Quotient.sound
  apply (QuotientGroup.leftRel_apply).mpr
  simpa

@[simp]
lemma quotientToEndHom_mk [N.Normal] (x : H) (g : G) :
    (quotientToEndHom H N ⟦x⟧).hom ⟦g⟧ = ⟦g * x⁻¹⟧ :=
  rfl

def quotientToQuotientOfLE [Fintype (G ⧸ H)] (h : N ≤ H) : (G ⧸ₐ N) ⟶ (G ⧸ₐ H) where
  hom := Quotient.lift _ <| fun a b hab ↦ Quotient.sound <|
    (QuotientGroup.leftRel_apply).mpr (h <| (QuotientGroup.leftRel_apply).mp hab)
  comm g := by
    ext (x : G ⧸ N)
    induction' x using Quotient.inductionOn with μ
    rfl

@[simp]
lemma quotientToQuotientOfLE_hom_mk [Fintype (G ⧸ H)] (h : N ≤ H) (x : G) :
    (quotientToQuotientOfLE H N h).hom ⟦x⟧ = ⟦x⟧ :=
  rfl

end

section

variable {F} (V : OpenSubgroup (Aut F)) {U : OpenSubgroup (Aut F)}
  (h : Subgroup.Normal U.toSubgroup) {A : C} (u : (functorToAction F).obj A ≅ Aut F ⧸ₐ U.toSubgroup)

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

/--
If `A` is an object of `C` with fiber `Aut F`-isomorphic to `Aut F ⧸ U` for an open normal
subgroup `U`, then for any open subgroup `V` of `Aut F`, `V ⧸ (U ⊓ V)` acts on `A`.
This is the diagram induced by the action.
-/
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
lemma ess_surj_of_quotient_by_open (V : OpenSubgroup (Aut F)) :
    ∃ (X : C), Nonempty ((functorToAction F).obj X ≅
      Action.FintypeCat.ofMulAction (Aut F) (FintypeCat.of <| Aut F ⧸ V.toSubgroup)) := by
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
  have := finiteQuotientSubgroups V U V.isOpen' U.isOpen'
  exact ⟨colimit (quotientDiag V hUnormal u),
    ⟨preservesColimitIso (functorToAction F) (quotientDiag V hUnormal u) ≪≫
    colimit.isoColimitCocone ⟨coconeQuotientDiag hUnormal u hUinV,
    coconeQuotientDiagIsColimit hUnormal u hUinV⟩⟩⟩

end PreGaloisCategory

end CategoryTheory
