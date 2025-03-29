import Mathlib


-- #check AlgebraicClosure

open CategoryTheory AlgebraicGeometry Limits

universe u

open Set.Notation
lemma IsPreirreducible.preimage_of_dense_isPreirreducible_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {V : Set Y} (hV : IsPreirreducible V)
    (f : X → Y) (hf' : IsOpenMap f) (hf'' : Dense (V ↓∩ { x | IsPreirreducible (f ⁻¹' {x}) })) :
    IsPreirreducible (f ⁻¹' V) := by
  rintro U₁ U₂ hU₁ hU₂ ⟨x, hxV, hxU₁⟩ ⟨y, hyV, hyU₂⟩
  obtain ⟨z, hzV, hz₁, hz₂⟩ :=
    hV _ _ (hf' _ hU₁) (hf' _ hU₂) ⟨f x, hxV, x, hxU₁, rfl⟩ ⟨f y, hyV, y, hyU₂, rfl⟩
  obtain ⟨z, ⟨⟨z₁, hz₁, e₁⟩, ⟨z₂, hz₂, e₂⟩⟩, hz⟩ :=
    hf''.inter_open_nonempty (V ↓∩ (f '' U₁ ∩ f '' U₂)) ⟨_, (hf' _ hU₁).inter (hf' _ hU₂), rfl⟩
      ⟨⟨z, hzV⟩, hz₁, hz₂⟩
  obtain ⟨z₃, hz₃, hz₃'⟩ := hz _ _ hU₁ hU₂ ⟨z₁, e₁, hz₁⟩ ⟨z₂, e₂, hz₂⟩
  refine ⟨z₃, show f z₃ ∈ _ from (show f z₃ = z from hz₃) ▸ z.2, hz₃'⟩

open Set.Notation
lemma IsPreirreducible.preimage_of_isPreirreducible_fiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {V : Set Y} (hV : IsPreirreducible V)
    (f : X → Y) (hf' : IsOpenMap f) (hf'' : ∀ x, IsPreirreducible (f ⁻¹' {x})) :
    IsPreirreducible (f ⁻¹' V) := by
  refine hV.preimage_of_dense_isPreirreducible_fiber f hf' ?_
  simp [hf'']

lemma image_mem_irreducibleComponents
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf₁ : Continuous f) (hf₂ : IsOpenMap f)
    (hf₃ : ∀ x, IsPreirreducible (f ⁻¹' {x}))
    (hf₄ : Function.Surjective f)
    {W : Set X} (hW : W ∈ irreducibleComponents X) : f '' W ∈ irreducibleComponents Y :=
    ⟨hW.1.image _ hf₁.continuousOn, fun Z hZ hWZ ↦ by
    have := hW.2 ⟨(by obtain ⟨x, hx⟩ := hW.1.1; exact ⟨x, hWZ ⟨x, hx, rfl⟩⟩),
      hZ.2.preimage_of_isPreirreducible_fiber f hf₂ hf₃⟩ (Set.image_subset_iff.mp hWZ)
    rw [← Set.image_preimage_eq Z hf₄]
    exact Set.image_mono this⟩

lemma preimage_mem_irreducibleComponents
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf₁ : Continuous f) (hf₂ : IsOpenMap f)
    (hf₃ : ∀ x, IsPreirreducible (f ⁻¹' {x}))
    (hf₄ : Function.Surjective f)
    {W : Set Y} (hW : W ∈ irreducibleComponents Y) : f ⁻¹' W ∈ irreducibleComponents X := by
  obtain ⟨Z, hZ, hWZ, H⟩ :=
    exists_preirreducible _ (hW.1.2.preimage_of_isPreirreducible_fiber f hf₂ hf₃)
  have hZ' : IsIrreducible Z := by
    obtain ⟨x, hx⟩ := hW.1.1
    obtain ⟨x, rfl⟩ := hf₄ x
    exact ⟨⟨_, hWZ hx⟩, hZ⟩
  have hWZ' : f ⁻¹' W = Z := by
    refine hWZ.antisymm (Set.image_subset_iff.mp ?_)
    exact hW.2 (IsIrreducible.image hZ' f hf₁.continuousOn)
      ((Set.image_preimage_eq W hf₄).symm.trans_le (Set.image_mono hWZ))
  rw [hWZ']
  exact ⟨hZ', fun s hs hs' ↦ (H s hs.2 hs').le⟩

lemma preimage_image_eq_of_mem_irreducibleComponents
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf₁ : Continuous f) (hf₂ : IsOpenMap f)
    (hf₃ : ∀ x, IsPreirreducible (f ⁻¹' {x}))
    {W : Set X} (hW : W ∈ irreducibleComponents X) : f ⁻¹' (f '' W) = W := by
  refine (Set.subset_preimage_image _ _).antisymm' (hW.2 ?_ (Set.subset_preimage_image _ _))
  refine ⟨?_, (hW.1.image _ hf₁.continuousOn).2.preimage_of_isPreirreducible_fiber _ hf₂ hf₃⟩
  obtain ⟨x, hx⟩ := hW.1.1
  exact ⟨_, x, hx, rfl⟩

def irreducibleComponentsEquivOfIsPreirreducibleFiber
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf₁ : Continuous f) (hf₂ : IsOpenMap f)
    (hf₃ : ∀ x, IsPreirreducible (f ⁻¹' {x}))
    (hf₄ : Function.Surjective f) :
    irreducibleComponents Y ≃o irreducibleComponents X where
  invFun W := ⟨f '' W.1, image_mem_irreducibleComponents f hf₁ hf₂ hf₃ hf₄ W.2⟩
  toFun W := ⟨f ⁻¹' W.1, preimage_mem_irreducibleComponents f hf₁ hf₂ hf₃ hf₄ W.2⟩
  right_inv W := Subtype.ext <|
    preimage_image_eq_of_mem_irreducibleComponents f hf₁ hf₂ hf₃ W.2
  left_inv _ := Subtype.ext <| Set.image_preimage_eq _ hf₄
  map_rel_iff' {W Z} := by
    refine ⟨fun H ↦ ?_, Set.preimage_mono⟩
    simpa only [Equiv.coe_fn_mk, Set.image_preimage_eq _ hf₄] using Set.image_mono (f := f) H

lemma IrreducibleSpace.of_surjective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (hf' : Function.Surjective f) [IrreducibleSpace X] :
    IrreducibleSpace Y := by
  rw [irreducibleSpace_def, Set.top_eq_univ, ← Set.image_univ_of_surjective hf']
  exact (isIrreducible_univ X).image _ hf.continuousOn

lemma irreducibleSpace_iff_isIrreducible {X : Type*} [TopologicalSpace X] {s : Set X} :
    IrreducibleSpace s ↔ IsIrreducible s :=
  ⟨fun H ↦ by simpa using
    ((irreducibleSpace_def s).mp H).image _ continuous_subtype_val.continuousOn,
    Subtype.irreducibleSpace⟩

lemma Subalgebra.FG.sup {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {S₁ S₂ : Subalgebra R S} (hS₁ : S₁.FG) (hS₂ : S₂.FG) : (S₁ ⊔ S₂).FG := by
  classical
  obtain ⟨s₁, rfl⟩ := hS₁
  obtain ⟨s₂, rfl⟩ := hS₂
  exact ⟨s₁ ∪ s₂, by simp [Algebra.adjoin_union]⟩

-- needs chevalley
open TensorProduct in
lemma isOpenMap_tensorProduct_of_flat
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra.HasGoingDown R T] [Algebra.FinitePresentation R T] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap S (S ⊗[R] T))) := by
  sorry

open TensorProduct in
lemma TensorProduct.exists_fg_mem_range_map_val_id
    {R S T : Type*} [Field R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S ⊗[R] T) :
    ∃ S' : Subalgebra R S, S'.FG ∧
      f ∈ (Algebra.TensorProduct.map S'.val (.id R T)).range := by
  induction f with
  | zero => exact ⟨⊥, Subalgebra.fg_bot, zero_mem _⟩
  | tmul x y => exact ⟨Algebra.adjoin R {x}, ⟨{x}, by simp⟩,
      ⟨x, Algebra.self_mem_adjoin_singleton _ _⟩ ⊗ₜ y, by simp⟩
  | add x y hx hy =>
    obtain ⟨S₁, hS₁, x, rfl⟩ := hx
    obtain ⟨S₂, hS₂, y, rfl⟩ := hy
    refine ⟨S₁ ⊔ S₂, hS₁.sup hS₂,
      Algebra.TensorProduct.map (S₁.inclusion le_sup_left) (.id R T) x +
      Algebra.TensorProduct.map (S₂.inclusion le_sup_right) (.id R T) y, ?_⟩
    simp only [RingHom.map_add, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      ← AlgHom.comp_apply]
    congr 2
    · ext <;> rfl
    · ext <;> rfl

open TensorProduct in
lemma TensorProduct.exists_fg_mem_range_map_id_val
    {R S T : Type*} [Field R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S ⊗[R] T) :
    ∃ T' : Subalgebra R T, T'.FG ∧
      f ∈ (Algebra.TensorProduct.map (.id R S) T'.val).range := by
  induction f with
  | zero => exact ⟨⊥, Subalgebra.fg_bot, zero_mem _⟩
  | tmul x y => exact ⟨Algebra.adjoin R {y}, ⟨{y}, by simp⟩,
      x ⊗ₜ ⟨y, Algebra.self_mem_adjoin_singleton _ _⟩, by simp⟩
  | add x y hx hy =>
    obtain ⟨T₁, hT₁, x, rfl⟩ := hx
    obtain ⟨T₂, hT₂, y, rfl⟩ := hy
    refine ⟨T₁ ⊔ T₂, hT₁.sup hT₂,
      Algebra.TensorProduct.map (.id R S) (T₁.inclusion le_sup_left)  x +
      Algebra.TensorProduct.map (.id R S) (T₂.inclusion le_sup_right) y, ?_⟩
    simp only [RingHom.map_add, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      ← AlgHom.comp_apply]
    congr 2
    · ext <;> rfl
    · ext <;> rfl

open TensorProduct in
lemma TensorProduct.exists_finiteType_mem_range_map_id_val
    {R S : Type*} {T : Type u} [Field R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S ⊗[R] T) :
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra R T') (_ : Algebra.FiniteType R T')
      (φ : T' →ₐ[R] T), Function.Injective φ ∧
      f ∈ (Algebra.TensorProduct.map (.id R S) φ).range := by
  obtain ⟨T', hT', hT''⟩ := TensorProduct.exists_fg_mem_range_map_id_val f
  exact ⟨T', _, _, T'.fg_iff_finiteType.mp hT', T'.val, Subtype.val_injective, hT''⟩


lemma IsNilpotent.map_algHom_iff {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    {f : S →ₐ[R] T} (hf : Function.Injective f) {x} : IsNilpotent (f x) ↔ IsNilpotent x :=
  IsNilpotent.map_iff hf

open TensorProduct in
lemma isOpenMap_tensorProduct_of_field
    {R S T : Type*} [Field R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap S (S ⊗[R] T))) := by
  refine PrimeSpectrum.isBasis_basic_opens.isOpenMap_iff.mpr ?_
  rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
  obtain ⟨T', _, _, _, ψ, hψ, f', hf'⟩ := TensorProduct.exists_finiteType_mem_range_map_id_val f
  have : (PrimeSpectrum.comap (algebraMap S (S ⊗[R] T)) '' PrimeSpectrum.basicOpen f) =
      (PrimeSpectrum.comap (algebraMap S (S ⊗[R] T')) '' PrimeSpectrum.basicOpen f') := by
    apply subset_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      refine ⟨PrimeSpectrum.comap (Algebra.TensorProduct.map (.id R S) ψ).toRingHom p, ?_, ?_⟩
      · simpa [← hf'] using hp
      · rw [← PrimeSpectrum.comap_comp_apply]
        congr 2
        ext
        simp
    · intro p hp
      rw [PrimeSpectrum.mem_image_comap_basicOpen] at hp ⊢
      contrapose! hp
      let φ : ((S ⊗[R] T') ⊗[S] p.asIdeal.ResidueField) →ₐ[S]
          ((S ⊗[R] T) ⊗[S] p.asIdeal.ResidueField) :=
        Algebra.TensorProduct.map (Algebra.TensorProduct.map (.id _ _) ψ) (.id _ _)
      have hφ : Function.Injective φ := by
        let φ' : ((S ⊗[R] T') ⊗[S] p.asIdeal.ResidueField) →ₗ[S]
            ((S ⊗[R] T) ⊗[S] p.asIdeal.ResidueField) := by
          refine (TensorProduct.comm _ _ _).toLinearMap ∘ₗ ?_ ∘ₗ
            (TensorProduct.comm _ _ _).toLinearMap
          refine (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S _ _).symm.toLinearMap ∘ₗ
            ?_ ∘ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S _ _).toLinearMap
          exact (ψ.toLinearMap.baseChange _).restrictScalars S
        have : φ.toLinearMap = φ' := by
          ext a b
          change ((1 : S) ⊗ₜ[R] ψ a) ⊗ₜ[S] b = ((1 : S) ⊗ₜ[R] ψ a) ⊗ₜ[S] ((1 : S) • b)
          rw [one_smul]
        show Function.Injective φ.toLinearMap
        rw [this]
        exact (TensorProduct.comm _ _ _).injective.comp
          (((TensorProduct.AlgebraTensorModule.cancelBaseChange R S S _ _).symm.injective.comp
          ((Module.Flat.lTensor_preserves_injective_linearMap ψ.toLinearMap hψ).comp
          (TensorProduct.AlgebraTensorModule.cancelBaseChange R S S _ _).injective)).comp
          (TensorProduct.comm _ _ _).injective)
      refine (IsNilpotent.map_algHom_iff (f := φ) hφ).mp ?_
      rwa [← hf'] at hp
  rw [this]
  have : Algebra.FinitePresentation R T' :=
    Algebra.FinitePresentation.of_finiteType.mp ‹_›
  exact isOpenMap_tensorProduct_of_flat R S T' _ (PrimeSpectrum.basicOpen f').2

namespace AlgebraicGeometry

def Geometrically (P : ObjectProperty Scheme.{u})
    {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) : Prop :=
  ∀ ⦃K : Type u⦄ [Field K] (φ : k →+* K), P (pullback f (Spec.map (CommRingCat.ofHom φ)))

lemma of_geometrically (P : ObjectProperty Scheme.{u})
    {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (H : Geometrically P f) [P.IsClosedUnderIsomorphisms] :
    P X := by
  have : IsIso (CommRingCat.ofHom (RingHom.id k)) := by -- add instance?
    simp only [CommRingCat.ofHom_id]; infer_instance
  exact P.prop_of_iso (asIso (pullback.fst f
    (Spec.map (CommRingCat.ofHom (RingHom.id k))))) (H (.id _))

@[stacks 038I]
lemma geometrically_irreducibleSpace_iff
    {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    {K : Type u} [Field K] [Algebra k K] [IsSepClosed K] :
    Geometrically (IrreducibleSpace ·) f ↔
      IrreducibleSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  sorry

open Lean PrettyPrinter.Delaborator SubExpr Qq in
@[app_delab TopCat.carrier]
partial def delabAdjoinNotation : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let pos ← getPos

  guard <| e.isAppOfArity ``TopCat.carrier 1
  let pos := pos.pushNaryArg 1 0
  let .some e := e.getAppArgs[0]? | failure

  guard <| e.isAppOfArity ``PresheafedSpace.carrier 3
  let pos := pos.pushNaryArg 3 2
  let .some e := e.getAppArgs[2]? | failure

  guard <| e.isAppOfArity ``SheafedSpace.toPresheafedSpace 3
  let pos := pos.pushNaryArg 3 2
  let .some e := e.getAppArgs[2]? | failure

  guard <| e.isAppOfArity ``LocallyRingedSpace.toSheafedSpace 1
  let pos := pos.pushNaryArg 1 0
  let .some e := e.getAppArgs[0]? | failure

  guard <| e.isAppOfArity ``Scheme.toLocallyRingedSpace 1
  let pos := pos.pushNaryArg 1 0
  let .some e := e.getAppArgs[0]? | failure

  let F ← withTheReader SubExpr (fun cfg => { cfg with expr := e, pos := pos }) delab
  `(↥$F)

lemma isIrreducible_snd_preimage_singleton_of_geometrically_irreducibleSpace
    {X Y : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (H : Geometrically (IrreducibleSpace ·) f)
    (y : Y) : IsIrreducible ((pullback.snd f g).base ⁻¹' {y}) := by
  let φ := Spec.preimage (Y.fromSpecResidueField y ≫ g)
  have := H φ.hom
  simp only [CommRingCat.ofHom_hom] at this
  let e : pullback f (Spec.map φ) ≅ (pullback.snd f g).fiber y :=
    pullback.congrHom rfl (by simp [φ]) ≪≫ (pullbackLeftPullbackSndIso ..).symm
  have := (e.hom.homeomorph.trans ((pullback.snd f g).fiberHomeo _))
  rw [← irreducibleSpace_iff_isIrreducible]
  have inst : IrreducibleSpace (pullback f (Spec.map φ)).toPresheafedSpace := ‹_›
  exact .of_surjective this.continuous this.surjective

lemma isIrreducible_preimage_singleton_of_geometrically_irreducibleSpace
    {X Y : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (H : Geometrically (IrreducibleSpace ·) f)
    (y : Y) : IsIrreducible ((pullback.snd f g).base ⁻¹' {y}) := by
  let φ := Spec.preimage (Y.fromSpecResidueField y ≫ g)
  have := H φ.hom
  simp only [CommRingCat.ofHom_hom] at this
  let e : pullback f (Spec.map φ) ≅ (pullback.snd f g).fiber y :=
    pullback.congrHom rfl (by simp [φ]) ≪≫ (pullbackLeftPullbackSndIso ..).symm
  have := (e.hom.homeomorph.trans ((pullback.snd f g).fiberHomeo _))
  rw [← irreducibleSpace_iff_isIrreducible]
  have inst : IrreducibleSpace (pullback f (Spec.map φ)).toPresheafedSpace := ‹_›
  exact .of_surjective this.continuous this.surjective

lemma isIrreducible_preimage_singleton_of_geometrically_eirreducibleSpace
    {X Y : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    {ZX ZY : Scheme.{u}} (iX : ZX ⟶ X) (iY : ZY ⟶ Y)
    (H : Geometrically (IrreducibleSpace ·) (iX ≫ f)) :
      IrreducibleSpace ↑(pullback (iX ≫ f) (iY ≫ g)) := by






  -- sorryh








end AlgebraicGeometry
