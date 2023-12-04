import Mathlib.CategoryTheory.GaloisCategories.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finite.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory

universe u v w v₁ u₁ u₂

open CategoryTheory Limits Functor

namespace Galois

variable {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory C]
  [FibreFunctor F]

theorem hasDecompConnectedComponents (X : C) : ∃ (ι : Type) (f : ι → C)
    (t : ColimitCocone (Discrete.functor f)),
    (∀ i, ConnectedObject (f i)) ∧ Finite ι ∧ X = t.cocone.pt := by
  revert X
  have hp : ∀ (n : ℕ) (X : C), n = Nat.card (F.obj X) →
    ∃ (ι : Type) (f : ι → C) (t : ColimitCocone (Discrete.functor f)),
    (∀ i, ConnectedObject (f i)) ∧ Finite ι ∧ X = t.cocone.pt
  intro n
  induction' n using Nat.strongRecOn with n hi
  intro X hn
  by_cases ConnectedObject X
  let ι : Type := PUnit
  let f : ι → C := fun _ ↦ X
  use ι
  use f
  let t : ColimitCocone (Discrete.functor f) := {
    cocone := constantCofan X
    isColimit := constantCofanIsColimit X
  }
  use t
  simp only [and_true, forall_const]
  constructor
  assumption
  constructor
  infer_instance
  rfl
  by_cases h : (IsInitial X → False)
  swap
  simp only [not_forall] at h
  obtain ⟨hin⟩ := h
  let ι : Type := PEmpty
  let f : ι → C := fun _ ↦ X
  use ι
  use f
  let t : ColimitCocone (empty C) := {
      cocone := asEmptyCocone X
      isColimit := hin
  }
  rw [←empty_ext' (empty C) (Discrete.functor f)]
  use t
  simp
  infer_instance
  have : ¬ (∀ (Y : C) (i : Y ⟶ X) [Mono i], (IsInitial Y → False) → IsIso i) := by
    by_contra a
    have : ConnectedObject X := ⟨h, a⟩
    contradiction
  simp at this
  choose Y hnotinitial v hvmono hvnoiso using this
  have hn0 : Nat.card (F.obj Y) ≠ 0 := by
    intro hzero
    have h : Nonempty (IsInitial Y) := by
      rw [(initialIffFibreEmpty Y : Nonempty (IsInitial Y) ↔ IsEmpty (F.obj Y))]
      exact Finite.card_eq_zero_iff.mp hzero
    exact Nonempty.elim h hnotinitial
  choose Z u x using PreGaloisCategory.monoInducesIsoOnDirectSummand v
  let c := Classical.choice x
  let t : ColimitCocone (pair Y Z) := { cocone := BinaryCofan.mk v u, isColimit := c }
  have hn1 : Nat.card (F.obj Y) < n := by
    rw [hn]
    exact ltCardFibre_of_mono_of_notIso v hvnoiso
  have i : X ≅ Y ⨿ Z := (colimit.isoColimitCocone t).symm
  have hnn : Nat.card (F.obj X) = Nat.card (F.obj Y) + Nat.card (F.obj Z) := by
    rw [cardFibre_eq_of_iso i]
    exact cardFibre_eq_sum_of_coprod Y Z
  have hn2 : Nat.card (F.obj Z) < n := by
    rw [hn, hnn]
    simp only [lt_add_iff_pos_left]
    have : Nat.card (F.obj Y) ≠ 0 := hn0
    exact Nat.pos_of_ne_zero hn0
  let ⟨ι₁, f₁, t₁, hc₁, hf₁, he₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
  let ⟨ι₂, f₂, t₂, hc₂, hf₂, he₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
  use ι₁ ⊕ ι₂
  use Sum.elim f₁ f₂
  let heq : pair Y Z ≅ pair t₁.cocone.pt t₂.cocone.pt := by
    apply Discrete.natIso
    intro ⟨i⟩
    match i with
    | WalkingPair.left =>
        show Y ≅ t₁.cocone.pt
        exact eqToIso he₁
    | WalkingPair.right =>
        show Z ≅ t₂.cocone.pt
        exact eqToIso he₂
  let t' : ColimitCocone (pair t₁.cocone.pt t₂.cocone.pt) := {
    cocone := (Cocones.precompose heq.inv).obj t.cocone
    isColimit := (IsColimit.precomposeInvEquiv heq t.cocone).invFun t.isColimit
  }
  use combCofanPairColimitCocone t'
  simp
  constructor
  constructor
  assumption
  assumption
  constructor
  infer_instance
  rfl
  intro X
  exact hp (Nat.card (F.obj X)) X rfl

lemma mono_coprod_inclusion {ι : Type} [Fintype ι] {f : ι → C}
    (t : ColimitCocone (Discrete.functor f)) (i : ι) :
    Mono (Cofan.inj t.cocone i) := by
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone t.cocone
  let s' : IsColimit s := isColimitOfPreserves F t.isColimit
  have h : s.ι.app ⟨i⟩ = F.map (Cofan.inj t.cocone i) := by
    simp only [Functor.mapCocone_ι_app]
    rfl
  have : Mono (s.ι.app ⟨i⟩) := FintypeCat.mono_of_cofanInj' (Discrete.functor f ⋙ F) ⟨s, s'⟩ i
  rw [h] at this
  exact mono_of_mono_map F this

lemma fibre_in_connected_component (X : C) (x : F.obj X) : ∃ (Y : C) (i : Y ⟶ X) (y : F.obj Y),
    F.map i y = x ∧ ConnectedObject Y ∧ Mono i := by
  obtain ⟨ι, f, t, hc, hf, he⟩ := hasDecompConnectedComponents F X
  have : Fintype ι := Fintype.ofFinite ι
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone t.cocone
  let s' : IsColimit s := isColimitOfPreserves F t.isColimit
  have : s.pt = F.obj X := by simp only [mapCocone_pt, he]
  let x' : s.pt := (eqToHom this.symm) x
  have : ∃ (j : Discrete ι) (z : (Discrete.functor f ⋙ F).obj j), s.ι.app j z = x' :=
    FintypeCat.jointly_surjective _ s s' x'
  obtain ⟨⟨j⟩, z, h⟩ := this
  let Y : C := f j
  let i : Y ⟶ t.cocone.pt := t.cocone.ι.app ⟨j⟩
  have : Mono i := mono_coprod_inclusion F t j
  use Y
  use (i ≫ eqToHom he.symm)
  use z
  refine ⟨?_, ?_, ?_⟩
  simp only [map_comp, FintypeCat.comp_apply, ←Functor.mapCocone_ι_app, h]
  aesop_subst he
  simp only [eqToHom_refl, mapCocone_pt, FintypeCat.id_apply, CategoryTheory.Functor.map_id]
  exact hc j
  exact mono_comp i (eqToHom he.symm)

lemma connected_component_unique {X A B : C} [ConnectedObject A] [ConnectedObject B]
    (a : F.obj A) (b : F.obj B) (i : A ⟶ X)
    (j : B ⟶ X) (h : F.map i a = F.map j b) [Mono i] [Mono j] : ∃ (f : A ≅ B), F.map f.hom a = b := by
  let Y : C := pullback i j
  let u : Y ⟶ A := pullback.fst
  let v : Y ⟶ B := pullback.snd
  let G := F ⋙ FintypeCat.incl
  let is : G.obj Y ≅ { p : G.obj A × G.obj B // G.map i p.1 = G.map j p.2 } :=
    (PreservesPullback.iso G i j) ≪≫ (Types.pullbackIsoPullback (G.map i) (G.map j))
  let y : F.obj Y := is.inv ⟨(a, b), h⟩
  have hn : IsInitial Y → False := notinitial_of_inhabited y
  have : IsIso u := ConnectedObject.noTrivialComponent Y u hn
  have : IsIso v := ConnectedObject.noTrivialComponent Y v hn
  have hu : F.map u y = a := by
    show G.map u y = a
    rw [←PreservesPullback.iso_hom_fst G]
    simp only [comp_obj, FintypeCat.incl_obj, Functor.comp_map, Iso.trans_inv, FintypeCat.incl_map,
      types_comp_apply, inv_hom_id_apply]
    show ((Types.pullbackIsoPullback (FintypeCat.incl.map (F.map i)) (FintypeCat.incl.map (F.map j))).inv
      ≫ pullback.fst) { val := (a, b), property := h } = a
    rw [Types.pullbackIsoPullback_inv_fst]
  have hv : F.map v y = b := by
    show G.map v y = b
    rw [←PreservesPullback.iso_hom_snd G]
    simp only [comp_obj, FintypeCat.incl_obj, Functor.comp_map, Iso.trans_inv, FintypeCat.incl_map,
      types_comp_apply, inv_hom_id_apply]
    show ((Types.pullbackIsoPullback (FintypeCat.incl.map (F.map i)) (FintypeCat.incl.map (F.map j))).inv
      ≫ pullback.snd) { val := (a, b), property := h } = b
    rw [Types.pullbackIsoPullback_inv_snd]
  let φ : A ≅ B := (asIso u).symm ≪≫ asIso v
  use φ
  rw [←hu, ←hv]
  have : CategoryTheory.inv (F.map u) (F.map u y) = y := by
    show (F.map u ≫ CategoryTheory.inv (F.map u)) y = y
    simp only [IsIso.hom_inv_id, FintypeCat.id_apply]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, map_comp, Functor.map_inv,
    FintypeCat.comp_apply]
  rw [this]

lemma exists_galois_representative (X : C) :
    ∃ (A : C) (a : F.obj A), GaloisObject F A ∧ Function.Bijective (evaluation A X a) := by
  let ι : FintypeCat.{w} := F.obj X
  let f : ι → C := fun _ => X
  let Y : C := ∏ f
  have : Fintype ι := inferInstance
  let g : ι → FintypeCat.{w} := fun x => F.obj (f x)
  let i : F.obj Y ≅ ∏ g := PreservesProduct.iso F f
  have : HasProduct g := inferInstance
  let z : (∏ g : FintypeCat.{w}) := FintypeCat.Pi.mk g id
  let y : F.obj Y := i.inv z
  obtain ⟨A, u, a, h1, h2, h3⟩ := fibre_in_connected_component F Y y
  use A
  use a
  let p (x : F.obj X) : A ⟶ X := u ≫ Pi.π f x
  have hp (x : F.obj X) : F.map (p x) a = x := by
    simp [h1]
    have : piComparison F f ≫ Pi.π g x = F.map (Pi.π f x) := piComparison_comp_π F f x
    rw [←congrFun this]
    simp
    rw [←PreservesProduct.iso_hom]
    simp [FintypeCat.Pi.π_mk]
  constructor
  constructor
  assumption
  constructor
  have lrr (a' : F.obj A) : ∃ (fiso : A ≅ A), F.map fiso.hom a' = a := by
    let y' : F.obj Y := F.map u a'
    let σ (t : F.obj X) : F.obj X := F.map (u ≫ Pi.π f t) a'
    have hsig (t : F.obj X) : σ t = F.map (Pi.π f t) y' := by simp only [map_comp, FintypeCat.comp_apply]
    have : Function.Bijective σ := by
      apply Finite.injective_iff_bijective.mp
      intro t s (hs : F.map (p t) a' = F.map (p s) a')
      have h : p t = p s := evaluationInjectiveOfConnected A X a' hs
      rw [←hp t, ←hp s, h]
    let τ : F.obj X ≃ F.obj X := Equiv.ofBijective σ this
    let φ : Y ⟶ Y := Pi.map' τ (fun _ => 𝟙 X)
    have hphi : φ = Pi.lift (fun a => Pi.π _ (τ a) ≫ 𝟙 X) := rfl
    let ψ : Y ⟶ Y := Pi.map' τ.invFun (fun _ => 𝟙 X)
    have : φ ≫ ψ = 𝟙 Y := by
      ext x
      rw [Category.assoc]
      show (Pi.map' τ (fun _ => 𝟙 X)) ≫ (Pi.map' τ.invFun (fun _ => 𝟙 X) ≫ Pi.π f x) = 𝟙 Y ≫ Pi.π f x
      rw [Pi.map'_comp_π, Category.comp_id, Pi.map'_comp_π, Category.comp_id, Category.id_comp]
      simp
    have : ψ ≫ φ = 𝟙 Y := by
      ext x
      rw [Category.assoc]
      show (Pi.map' τ.invFun (fun _ => 𝟙 X)) ≫ (Pi.map' τ (fun _ => 𝟙 X) ≫ Pi.π f x) = 𝟙 Y ≫ Pi.π f x
      rw [Pi.map'_comp_π, Category.comp_id, Pi.map'_comp_π, Category.comp_id, Category.id_comp]
      simp
    let is : Y ≅ Y := Iso.mk φ ψ
    let is1 : A ⟶ Y := u ≫ is.hom
    have : IsIso is.hom := IsIso.of_iso is
    have : Mono is.hom := IsIso.mono_of_iso is.hom
    have : Mono is1 := mono_comp _ _
    have : F.map is.hom y = y' := by
      rw [←FintypeCat.hom_inv_id_apply i y', ←FintypeCat.hom_inv_id_apply i (F.map φ y)]
      apply congrArg i.inv
      rw [PreservesProduct.iso_hom]
      have : PreservesLimit (Discrete.functor fun b ↦ F.obj (f b)) (FintypeCat.incl) := inferInstance
      apply @Concrete.limit_ext FintypeCat.{w} _ _ _ _ _
        _ _ (piComparison F f (F.map φ y)) (piComparison F f y')
      intro ⟨(t : F.obj X)⟩
      rw [hphi]
      show (F.map (Pi.lift fun a ↦ Pi.π f (τ a) ≫ 𝟙 X) ≫ piComparison F (fun _ ↦ X) ≫ Pi.π (fun _ ↦ F.obj X) t) y =
        (piComparison F (fun _ ↦ X) ≫ Pi.π (fun _ ↦ F.obj X) t) y'
      rw [←Category.assoc, map_lift_piComparison, Pi.lift_π, Category.comp_id, piComparison_comp_π]
      rw [←hsig, ←piComparison_comp_π, ←PreservesProduct.iso_hom, FintypeCat.comp_apply]
      show ((PreservesProduct.iso F f).inv ≫ (PreservesProduct.iso F f).hom ≫ Pi.π (fun b ↦ F.obj (f b)) (σ t))
        z = σ t
      rw [Iso.inv_hom_id_assoc]
      simp only [map_comp, FintypeCat.comp_apply, FintypeCat.Pi.π_mk, id_eq]
    have hl : F.map u a' = F.map is1 a := by
      show y' = F.map (u ≫ is.hom) a
      rw [map_comp, FintypeCat.comp_apply, h1, this]
    exact connected_component_unique F a' a u is1 hl
  intro x y
  obtain ⟨fi1, hfi1⟩ := lrr x
  obtain ⟨fi2, hfi2⟩ := lrr y
  use fi1 ≪≫ fi2.symm
  show F.map (fi1.hom ≫ fi2.inv) x = y
  simp only [map_comp, FintypeCat.comp_apply]
  rw [hfi1, ←hfi2]
  simp only [FintypeCat.FunctorToFintypeCat.map_inv_map_hom_apply]
  have h1' : Function.Surjective (evaluation A X a) := by
    intro x
    use u ≫ Pi.π f x
    exact hp x
  have h2 : Function.Injective (evaluation A X a) := evaluationInjectiveOfConnected A X a
  exact ⟨h2, h1'⟩

lemma exists_map_from_galois_of_fibre (X : C) (x : F.obj X) :
    ∃ (A : C) (f : A ⟶ X) (a : F.obj A), GaloisObject F A ∧ F.map f a = x := by
  obtain ⟨A, a, h1, h2⟩ := exists_galois_representative F X
  use A
  obtain ⟨f, hf⟩ := h2.surjective x
  use f
  use a
  exact ⟨h1, hf⟩

lemma exists_map_from_galois_of_fibre_nonempty (X : C) (h : Nonempty (F.obj X)) :
    ∃ (A : C) (_ : A ⟶ X), GaloisObject F A := by
  obtain ⟨x⟩ := h
  obtain ⟨A, a, h1, h2⟩ := exists_galois_representative F X
  use A
  obtain ⟨f, _⟩ := h2.surjective x
  use f

lemma exists_map_from_galois_of_connected (X : C) [ConnectedObject X] :
    ∃ (A : C) (_ : A ⟶ X), GaloisObject F A := by
  apply exists_map_from_galois_of_fibre_nonempty F X
  exact nonempty_fibre_of_connected X
