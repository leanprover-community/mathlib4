import Mathlib.CategoryTheory.GaloisCategories.Topology
import Mathlib.CategoryTheory.GaloisCategories.Prorepresantability
import Mathlib.Data.Rel
import Mathlib.Topology.Algebra.OpenSubgroup
/-

We show that the fibre functor `F` has as essential image the subcategory
of continuous `Aut F` sets.

Possible strategy:

- F preserves decompositions in connected objects, so we only need to show this
  for connected `Aut F`-sets, aka. finite sets with continuous and transitive
  `Aut F` action.
- Each such object is of the form Aut F / H for some open subgroup H of Aut F
  (H is the stabilizer of the action which is closed, by continuity and of finite
  index since the set is finite, i.e. H is open)
- Show that each Aut F / H for H open subgroup is realized by explicit construction

-/


universe u v w

open CategoryTheory Limits Functor

namespace Galois

--lemma ProfiniteGroup.open_of_closed_of_finite_index {G : Type*} [Group G]
--    [TopologicalSpace G] [CompactSpace G] [TotallyDisconnectedSpace G]
--    [T2Space G] (H : Subgroup G) (h : IsClosed (H : Set G)) [Finite (G ⧸ H)] :
--    IsOpen (H : Set G) :=
--  sorry

variable {C : Type u} [Category.{u, u} C] (F : C ⥤ FintypeCat.{u})
  [PreGaloisCategory C] [FibreFunctor F]

lemma surject_to_connected_of_nonempty_fibre {A X : C} (h : Nonempty (F.obj A))
    [ConnectedObject X] (f : A ⟶ X) :
    Function.Surjective (F.map f) := by
  obtain ⟨a⟩ := h
  intro x
  obtain ⟨σ, hσ : (σ.hom.app X) (F.map f a) = x⟩ := MulAction.exists_smul_eq (Aut F) (F.map f a) x
  use (σ.hom.app A) a
  show (σ.hom.app A ≫ F.map f) a = x
  rw [←σ.hom.naturality, FintypeCat.comp_apply, hσ]

instance (X : C) : ContinuousSMul (Aut F) (F.obj X) := inferInstance

lemma stabilizer_open (X : C) (x : ((H F).obj X).V) :
    IsOpen (MulAction.stabilizer (Aut F) x : Set (Aut F)) := by
  let q (g : Aut F) : Aut F × F.obj X := (g, x)
  have : Continuous q := by
    continuity
  let h (p : Aut F × F.obj X) : F.obj X := p.1.hom.app X p.2
  have : Continuous h := continuous_smul
  let p (g : Aut F) : F.obj X := g.hom.app X x
  have : p ⁻¹' {x} = MulAction.stabilizer (Aut F) x := rfl
  rw [←this]
  apply IsOpen.preimage
  show Continuous (h ∘ q)
  apply Continuous.comp
  assumption
  assumption
  trivial

--instance : EssSurj (H F) := EssSurj.mk <| by
--  intro Y
--  admit

instance (G : Type u) [Group G] [Finite G] : PreservesColimitsOfShape (SingleObj G) (H F) := by
  apply Action.preservesColimitOfShapeOfPreserves
  show PreservesColimitsOfShape (SingleObj G) F
  infer_instance

section

noncomputable instance fintypeQuotient (H : OpenSubgroup (Aut F)) :
    Fintype (Aut F ⧸ (H : Subgroup (Aut F))) := by
  have : Finite (Aut F ⧸ H.toSubgroup) := finiteQuotientOfOpen H.toSubgroup H.isOpen'
  apply Fintype.ofFinite

instance (H : Subgroup (Aut F)) : MulAction (Aut F) (Aut F ⧸ H) := inferInstance

end

private lemma help0 (X : C) [GaloisObject F X] :
    ∃ (U : OpenSubgroup (Aut F))
      (_ : (H F).obj X ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)),
    Subgroup.Normal U.toSubgroup := by
  have : ConnectedObject X := GaloisObject.connected F
  have hc : ConnectedObject ((H F).obj X) := PreservesConnectedObjects.preserves
  have : Nonempty (F.obj X) := nonempty_fibre_of_connected X
  obtain ⟨x : ((H F).obj X).V⟩ := this
  have : MulAction (Aut F) (F.obj X) := by
    show MulAction (Aut F) ((H F).obj X).V
    infer_instance
  have : MulAction.IsPretransitive (Aut F) ((H F).obj X).V := by
    exact (Action.connected_iff_transitive ((H F).obj X)).mp hc
  have : MulAction.orbit (Aut F) x ≃ Aut F ⧸ MulAction.stabilizer (Aut F) x :=
    MulAction.orbitEquivQuotientStabilizer (Aut F) x
  have : MulAction.orbit (Aut F) x = Set.univ := MulAction.orbit_eq_univ (Aut F) x
  have : MulAction.orbit (Aut F) x ≃ Set.univ := Equiv.setCongr this
  let e : ((H F).obj X).V ≃ Aut F ⧸ MulAction.stabilizer (Aut F) x := by
    trans
    exact (Equiv.Set.univ ↑(F.obj X)).symm
    trans
    apply Equiv.setCongr
    exact (MulAction.orbit_eq_univ (Aut F) x).symm
    exact MulAction.orbitEquivQuotientStabilizer (Aut F) x
  let U : OpenSubgroup (Aut F) := ⟨MulAction.stabilizer (Aut F) x, stabilizer_open F X x⟩
  use U
  let inst : Fintype (Aut F ⧸ U.toSubgroup) := fintypeQuotient F U
  let u : Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup) ≅ (H F).obj X := by
    apply Action.mkIso
    swap
    exact (FintypeCat.equivEquivIso e.symm)
    intro (σ : Aut F)
    ext (a : Aut F ⧸ MulAction.stabilizer (Aut F) x)
    obtain ⟨τ, hτ⟩ := Quotient.exists_rep a
    rw [←hτ]
    rfl
  use u.symm
  constructor
  intro n ninstab g
  simp
  show g • n • (g⁻¹ • x) = x
  have : MulAction.IsPretransitive (Aut X) (F.obj X) := inferInstance
  let inst : SMul (Aut X) ((H F).obj X).V := autMulFibre F X
  have : MulAction.IsPretransitive (Aut X) ((H F).obj X).V := by
    exact autMulFibreTransitiveOfGalois F X
  have : ∃ (φ : Aut X), F.map φ.hom x = g⁻¹ • x := MulAction.IsPretransitive.exists_smul_eq x (g⁻¹ • x)
  obtain ⟨φ, h⟩ := this
  rw [←h]
  show g • n • (F.map φ.hom x) = x
  show g • (((H F).map φ.hom).hom ≫ ((H F).obj X).ρ n) x = x
  rw [←((H F).map φ.hom).comm]
  simp only [FintypeCat.comp_apply]
  show g • F.map φ.hom (n • x) = x
  rw [ninstab, h]
  show (g * g⁻¹) • x = x
  simp

private lemma help1 (H : Subgroup (Aut F)) (h : IsOpen (H : Set (Aut F)))
    : ∃ (I : Set C) (_ : Fintype I), (∀ X ∈ I, ConnectedObject X)
    ∧ ((σ : Aut F) → (∀ X : I, σ.hom.app X = 𝟙 (F.obj X)) → σ ∈ H) := by
  obtain ⟨U, hUopen, hU⟩ := isOpen_induced_iff.mp h
  have h1inU : 1 ∈ U := by
    show 1 ∈ autEmbedding F ⁻¹' U
    rw [hU]
    exact Subgroup.one_mem H
  obtain ⟨I, u, ho, ha⟩ := isOpen_pi_iff.mp hUopen 1 h1inU
  choose fι ff fc h4 h5 h6 using (fun X : I => hasDecompConnectedComponents F X)
  let J : Set C := ⋃ X, Set.range (ff X)
  use J
  use Fintype.ofFinite J
  constructor
  intro X ⟨A, ⟨Y, hY⟩, hA2⟩
  have : X ∈ Set.range (ff Y) := by simpa [hY]
  obtain ⟨i, hi⟩ := this
  rw [←hi]
  exact h4 Y i
  intro σ h
  have (X : I) : σ.hom.app X = 𝟙 (F.obj X) := by
    --have is : ∐ ff X ≅ X := h3 X
    let t : ColimitCocone (Discrete.functor (ff X)) := fc X
    let s : Cocone (Discrete.functor (ff X) ⋙ F) := F.mapCocone t.cocone
    have : Fintype (fι X) := Fintype.ofFinite _
    let hs : IsColimit s := isColimitOfPreserves F t.isColimit
    rw [h6]
    ext (x : F.obj t.cocone.pt)
    obtain ⟨⟨j⟩, a, ha : F.map (t.cocone.ι.app ⟨j⟩) a = x⟩ :=
      FintypeCat.jointly_surjective (Discrete.functor (ff X) ⋙ F) s hs x
    show σ.hom.app (fc X).cocone.pt x = x
    rw [←ha]
    show (F.map (t.cocone.ι.app ⟨j⟩) ≫ σ.hom.app (fc X).cocone.pt) a = F.map (t.cocone.ι.app ⟨j⟩) a
    erw [σ.hom.naturality]
    simp
    have : σ.hom.app ((ff X) j) = 𝟙 (F.obj ((ff X) j)) := by
      have : (ff X) j ∈ J := by aesop
      exact h ⟨(ff X) j, this⟩
    rw [this]
    rfl
  have (X : I) : autEmbedding F σ X = 1 := by
    apply Iso.ext
    exact this X
  have (X : I) : autEmbedding F σ X ∈ u X := by
    rw [this X]
    exact (ho X.val X.property).right
  have : autEmbedding F σ ∈ Set.pi I u := by
    intro X XinI
    exact this ⟨X, XinI⟩
  have : σ ∈ autEmbedding F ⁻¹' U := by
    apply ha
    exact this
  rw [hU] at this
  exact this

private lemma help2 (I : Set C) [Fintype I] (h : ∀ X ∈ I, ConnectedObject X) :
    Nonempty (F.obj (∏ fun X : I => X)) := by
  let P : FintypeCat := ∏ fun X : I => F.obj X
  have i1 : F.obj (∏ fun X : I => X) ≅ P := PreservesProduct.iso F _
  let f (X : I) : Type u := F.obj X
  have i2 : FintypeCat.incl.obj P ≅ ∏ f := PreservesProduct.iso FintypeCat.incl _
  have (X : I) : Nonempty (F.obj X) := by
    have : ConnectedObject (X : C) := h X.val X.property
    exact nonempty_fibre_of_connected (X : C)
  have : Nonempty (∀ X : I, F.obj X) := inferInstance
  obtain ⟨x⟩ := this
  have i3 : ∏ f ≅ Shrink.{u, u} (∀ X : I, f X) := Types.Small.productIso f
  let y : ∏ f := i3.inv ((equivShrink _) x)
  let y' : P := i2.inv y
  use i1.inv y'

private noncomputable def help3 (H N : OpenSubgroup (Aut F)) (hn : Subgroup.Normal N.toSubgroup) :
    H ⧸ Subgroup.subgroupOf N H →* End (Action.ofMulAction' (Aut F) (Aut F ⧸ N.toSubgroup)) := by
  let φ' : H →* End (Action.ofMulAction' (Aut F) (Aut F ⧸ N.toSubgroup)) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    intro ⟨v, _⟩
    show Action.ofMulAction' (Aut F) (Aut F ⧸ N.toSubgroup) ⟶ Action.ofMulAction' (Aut F) (Aut F ⧸ N.toSubgroup)
    let fh : (Action.ofMulAction' (Aut F) (Aut F ⧸ N.toSubgroup)).V
        ⟶ (Action.ofMulAction' (Aut F) (Aut F ⧸ N.toSubgroup)).V := by
      show Aut F ⧸ N.toSubgroup → Aut F ⧸ N.toSubgroup
      apply Quotient.lift
      swap
      intro σ
      exact ⟦σ * v⁻¹⟧
      intro σ τ hst
      apply Quotient.sound
      apply (QuotientGroup.leftRel_apply).mpr
      simp
      show v * (σ⁻¹ * τ) * v⁻¹ ∈ N
      apply Subgroup.Normal.conj_mem hn
      exact QuotientGroup.leftRel_apply.mp hst
    constructor
    swap
    exact fh
    intro (σ : Aut F)
    ext (x : Aut F ⧸ N.toSubgroup)
    obtain ⟨τ, hτ⟩ := Quotient.exists_rep x
    rw [←hτ]
    rfl
    apply Action.hom_ext
    ext (x : Aut F ⧸ N.toSubgroup)
    obtain ⟨τ, hτ⟩ := Quotient.exists_rep x
    rw [←hτ]
    rfl
    intro σ τ
    apply Action.hom_ext
    ext (x : Aut F ⧸ N.toSubgroup)
    obtain ⟨μ, hμ⟩ := Quotient.exists_rep x
    rw [←hμ]
    show ⟦μ * (σ * τ)⁻¹⟧ = ⟦μ * τ⁻¹ * σ⁻¹⟧
    group
    rfl
  apply QuotientGroup.lift (Subgroup.subgroupOf N.toSubgroup H.toSubgroup) φ'
  intro u uinU'
  show φ' u = 1
  apply Action.hom_ext
  ext (x : Aut F ⧸ N.toSubgroup)
  obtain ⟨μ, hμ⟩ := Quotient.exists_rep x
  rw [←hμ]
  show ⟦μ * u⁻¹⟧ = ⟦μ⟧
  apply Quotient.sound
  apply (QuotientGroup.leftRel_apply).mpr
  simpa

--private def help411 {G M : Type*} [Group G] [Group M]
--    (J : SingleObj M ⥤ Action FintypeCat (MonCat.of G)) :
--    Action FintypeCat (MonCat.of G) where
--  V := (J.obj (SingleObj.star M)).V ⧸ M

--private def help41 {G M : Type*} [Group G] [Group M]
--    (J : SingleObj M ⥤ Action FintypeCat (MonCat.of G)) :
--    Cocone J where
--  pt := J.obj (SingleObj.star M) ⧸ M
--  ι := {
--    app := fun _ => 𝟙 (J.obj _)
--    --naturality := 
--  }

--private def help42 {G M : Type*} [Group G] [Group M] (H N : Subgroup G) (h : Subgroup.Normal N)
--  (J : SingleObj M ⥤ Action FintypeCat (MonCat.of G))

--private lemma help4 {G M : Type*} [Group G] [Group M] [Finite M]
--    (J : SingleObj M ⥤ Action FintypeCat (MonCat.of G)) :
--  colimit J ≅ Action.ofMulAction' G (G ⧸ H) := sorry

def help43 {G : Type*} [Group G] (H N : Subgroup G) [Fintype (G ⧸ N)]
    [Fintype (G ⧸ H)] (h : N ≤ H) :
    Action.ofMulAction' G (G ⧸ N) ⟶ Action.ofMulAction' G (G ⧸ H) := by
  constructor
  swap
  apply Quotient.lift
  intro a b hab
  apply Quotient.sound
  apply (QuotientGroup.leftRel_apply).mpr
  apply h
  exact (QuotientGroup.leftRel_apply).mp hab
  intro (g : G)
  ext (x : G ⧸ N)
  obtain ⟨μ, hμ⟩ := Quotient.exists_rep x
  rw [←hμ]
  rfl

noncomputable def help44 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (u : (H F).obj A ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) :
    V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →* End A := by
  let φ : V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →*
      End (Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) :=
    help3 F V U h
  let e1 : End A ≃* End ((H F).obj A) := equivMulOfFullyFaithful (H F)
  let e2 : End ((H F).obj A) ≃* End (Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) := Iso.conj u
  let e : End A ≃* End (Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) := e1.trans e2
  exact MonoidHom.comp e.symm.toMonoidHom φ

lemma help441 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (u : (H F).obj A ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup))
    (m : SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup) ⟶ SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup)) :
    (H F).map (help44 F V U h A u m) = u.hom ≫ help3 F V U h m ≫ u.inv := by
  apply (cancel_epi (u.inv)).mp
  apply (cancel_mono (u.hom)).mp
  erw [equivMulOfFullyFaithful_symm_apply]
  simp [←Iso.conj_apply, MulEquiv.apply_symm_apply]

noncomputable def help45 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (u : (H F).obj A ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) :
    SingleObj (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup) ⥤ C :=
  SingleObj.functor (help44 F V U h A u)

noncomputable def help46 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (hUinV : U ≤ V)
    (u : (H F).obj A ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) :
    Cocone (help45 F V U h A u ⋙ H F) where
  pt := Action.ofMulAction' (Aut F) (Aut F ⧸ V.toSubgroup)
  ι := by
    apply SingleObj.natTrans
    swap
    show (H F).obj A ⟶ Action.ofMulAction' (Aut F) (Aut F ⧸ V.toSubgroup)
    exact (u.hom ≫ help43 V.toSubgroup U.toSubgroup hUinV)
    intro (m : V ⧸ Subgroup.subgroupOf U V)
    show (H F).map (help44 F V U h A u m) ≫ u.hom ≫ help43 V.toSubgroup U.toSubgroup hUinV = u.hom ≫ help43 V.toSubgroup U.toSubgroup hUinV
    apply (cancel_epi (u.inv)).mp
    rw [Iso.inv_hom_id_assoc]
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    obtain ⟨μ, hμ⟩ := Quotient.exists_rep x
    rw [←hμ]
    let φ : V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →* End (Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) :=
      help3 F V U h
    have : u.inv ≫ (H F).map (help44 F V U h A u m) ≫ u.hom = φ m := by
      erw [equivMulOfFullyFaithful_symm_apply]
      simp [←Iso.conj_apply, MulEquiv.apply_symm_apply]
    show Action.Hom.hom ((u.inv ≫ (H F).map (help44 F V U h A u m) ≫ u.hom) ≫ help43 V.toSubgroup U.toSubgroup hUinV) ⟦μ⟧
      = ⟦μ⟧
    rw [this]
    show ((φ m).hom ≫ (help43 V.toSubgroup U.toSubgroup hUinV).hom) ⟦μ⟧ = ⟦μ⟧
    obtain ⟨σ, hσ⟩ := Quotient.exists_rep m
    rw [←hσ]
    show ⟦μ * σ⁻¹⟧ = ⟦μ⟧
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply).mpr
    simp only [SubgroupClass.coe_inv, mul_inv_rev, _root_.inv_inv, inv_mul_cancel_right,
      SetLike.coe_mem]

noncomputable def help461 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (hUinV : U ≤ V)
    (u : (H F).obj A ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) :
    (s : Cocone (help45 F V U h A u ⋙ H F)) → (help46 F V U h A hUinV u).pt ⟶ s.pt := by
  let M := V ⧸ Subgroup.subgroupOf U V
  let J : SingleObj M ⥤ C := help45 F V U h A u
  let J' : SingleObj M ⥤ Action FintypeCat (MonCat.of (Aut F)) := J ⋙ H F
  let φ : M →* End (Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) :=
    help3 F V U h
  intro s
  constructor
  swap
  show Aut F ⧸ V.toSubgroup ⟶ s.pt.V
  apply Quotient.lift
  swap
  intro (σ : Aut F)
  let f : (H F).obj A ⟶ s.pt := s.ι.app (SingleObj.star M)
  exact (u.inv ≫ f).hom ⟦σ⟧
  intro σ τ hst
  have : σ⁻¹ * τ ∈ V := (QuotientGroup.leftRel_apply).mp hst
  let m : (SingleObj.star M ⟶ SingleObj.star M) := ⟦⟨σ⁻¹ * τ, this⟩⟧
  have h1 : J'.map m ≫ s.ι.app (SingleObj.star M) = s.ι.app (SingleObj.star M) :=
    s.ι.naturality m
  have h2 : (J'.map m).hom (u.inv.hom ⟦τ⟧) = u.inv.hom ⟦σ⟧ := by
    erw [(help441 F V U h A u m : J'.map m = u.hom ≫ φ m ≫ u.inv)]
    show Action.Hom.hom (u.inv ≫ u.hom ≫ φ m ≫ u.inv) ⟦τ⟧ = Action.Hom.hom u.inv ⟦σ⟧
    simp only [Iso.inv_hom_id_assoc, Action.comp_hom, FintypeCat.comp_apply]
    apply congrArg
    show ⟦τ * (σ⁻¹ * τ)⁻¹⟧ = ⟦σ⟧
    simp only [mul_inv_rev, _root_.inv_inv, mul_inv_cancel_left]
  have h3 : (u.inv ≫ s.ι.app (SingleObj.star M)).hom ⟦σ⟧
      = (u.inv ≫ J'.map m ≫ s.ι.app (SingleObj.star M)).hom ⟦τ⟧ := by
    show (u.inv ≫ s.ι.app (SingleObj.star M)).hom ⟦σ⟧
      = (s.ι.app (SingleObj.star M)).hom ((J'.map m).hom (u.inv.hom ⟦τ⟧))
    rw [h2]
    rfl
  rw [h1] at h3
  exact h3
  intro (g : Aut F)
  ext (x : Aut F ⧸ V.toSubgroup)
  obtain ⟨σ, hσ⟩ := Quotient.exists_rep x
  rw [←hσ]
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_trans_apply, id_eq, Action.comp_hom, FintypeCat.comp_apply,
    SubgroupClass.coe_inv, eq_mpr_eq_cast]
  have : ((H F).obj A).ρ g ≫ (s.ι.app (SingleObj.star M)).hom
    = (s.ι.app (SingleObj.star M)).hom ≫ s.pt.ρ g := (s.ι.app (SingleObj.star M)).comm g
  show (((Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)).ρ g ≫ u.inv.hom) ≫
      (s.ι.app (SingleObj.star M)).hom) ⟦σ⟧ =
    ((s.ι.app (SingleObj.star M)).hom ≫ s.pt.ρ g) (u.inv.hom ⟦σ⟧)
  rw [←this, u.inv.comm g]
  rfl

noncomputable def help47 (V U : OpenSubgroup (Aut F)) (h : Subgroup.Normal U.toSubgroup) (A : C)
    (hUinV : U ≤ V)
    (u : (H F).obj A ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)) :
    IsColimit (help46 F V U h A hUinV u) where
  desc := help461 F V U h A hUinV u
  fac s j := by
    apply (cancel_epi u.inv).mp
    apply Action.hom_ext
    ext (x : Aut F ⧸ U.toSubgroup)
    obtain ⟨σ, hσ⟩ := Quotient.exists_rep x
    rw [←hσ]
    show Action.Hom.hom (help461 F V U h A hUinV u s)
      (Action.Hom.hom (u.inv ≫ u.hom ≫ help43 V.toSubgroup U.toSubgroup hUinV) ⟦σ⟧) =
      Action.Hom.hom (s.ι.app j) (Action.Hom.hom u.inv ⟦σ⟧)
    simp only [Iso.inv_hom_id_assoc, comp_obj, const_obj_obj]
    rfl
  uniq s := by
    let M := V ⧸ Subgroup.subgroupOf U V
    intro f hf
    apply Action.hom_ext
    ext (x : Aut F ⧸ V.toSubgroup)
    obtain ⟨σ, hσ⟩ := Quotient.exists_rep x
    rw [←hσ]
    let y : F.obj A := u.inv.hom ⟦σ⟧
    have h1 : ⟦σ⟧ = ((help46 F V U h A hUinV u).ι.app (SingleObj.star M)).hom y := by
      show ⟦σ⟧ = (u.inv ≫ u.hom ≫ help43 V.toSubgroup U.toSubgroup hUinV).hom ⟦σ⟧
      simp only [Iso.inv_hom_id_assoc]
      rfl
    show Action.Hom.hom f ⟦σ⟧ = (s.ι.app (SingleObj.star M)).hom y
    rw [←hf (SingleObj.star M), h1]
    rfl

example (V : OpenSubgroup (Aut F))
    : ∃ (X : C), Nonempty ((H F).obj X ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ V.toSubgroup)) := by
  obtain ⟨I, hf, hc, hi⟩ := help1 F V.toSubgroup V.isOpen'
  have : Fintype I := inferInstance
  let Y : C := ∏ fun X : I => X
  have hn : Nonempty (F.obj Y) := help2 F I hc
  obtain ⟨A, f, hgal⟩ := exists_map_from_galois_of_fibre_nonempty F Y hn
  obtain ⟨U, u, hUnormal⟩ := help0 F A
  have h1 : ∀ σ ∈ U, σ.hom.app A = 𝟙 (F.obj A) := by
    intro σ σinU
    have hi : (Action.ofMulAction' (Aut F) (Aut F ⧸ U.toSubgroup)).ρ σ = 𝟙 (Aut F ⧸ U.toSubgroup) := by
      apply FintypeCat.hom_ext
      intro (x : Aut F ⧸ U.toSubgroup)
      obtain ⟨τ, hτ⟩ := Quotient.exists_rep x
      rw [←hτ]
      show ⟦σ * τ⟧ = ⟦τ⟧
      apply Quotient.sound
      apply (QuotientGroup.leftRel_apply).mpr
      simp only [mul_inv_rev]
      apply Subgroup.Normal.conj_mem hUnormal
      exact Subgroup.inv_mem U.toSubgroup σinU
    have : Mono u.hom.hom := by
      show Mono ((forget₂ _ FintypeCat).map u.hom)
      infer_instance
    apply (cancel_mono u.hom.hom).mp
    erw [u.hom.comm σ, hi]
    rfl
  have h2 : ∀ σ ∈ U, ∀ X : I, σ.hom.app X = 𝟙 (F.obj X) := by
    intro σ σinU ⟨X, hX⟩
    ext (x : F.obj X)
    have : ConnectedObject A := GaloisObject.connected F
    have hne : Nonempty (F.obj A) := nonempty_fibre_of_connected A
    let p : A ⟶ X := f ≫ Pi.π (fun Z : I => (Z : C)) ⟨X, hX⟩
    have : ConnectedObject X := hc X hX
    have : Function.Surjective (F.map p) := surject_to_connected_of_nonempty_fibre F hne p
    obtain ⟨a, ha⟩ := this x
    simp only [FintypeCat.id_apply, ←ha]
    show (F.map p ≫ σ.hom.app X) a = F.map p a
    rw [σ.hom.naturality, h1 σ σinU]
    rfl
  have hUinV : (U : Set (Aut F)) ≤ V := by
    intro u uinU
    exact hi u (h2 u uinU)
  let U' : Subgroup V := Subgroup.subgroupOf U.toSubgroup V
  have hU'normal : Subgroup.Normal U' := Subgroup.Normal.subgroupOf hUnormal V
  let M := V ⧸ U'
  have : Finite M := finiteQuotientSubgroups V U V.isOpen' U.isOpen'
  let J : SingleObj M ⥤ C := help45 F V U hUnormal A u
  let i1 : (H F).obj (colimit J) ≅ colimit (J ⋙ H F) := preservesColimitIso (H F) J
  let c : Cocone (J ⋙ H F) := help46 F V U hUnormal A hUinV u
  let ci : IsColimit c := help47 F V U hUnormal A hUinV u
  let i2 : colimit (J ⋙ H F) ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ V.toSubgroup) :=
    colimit.isoColimitCocone ⟨c, ci⟩
  let i3 : (H F).obj (colimit J) ≅ Action.ofMulAction' (Aut F) (Aut F ⧸ V.toSubgroup) := i1 ≪≫ i2
  let X : C := colimit J
  use X
  exact ⟨i3⟩
