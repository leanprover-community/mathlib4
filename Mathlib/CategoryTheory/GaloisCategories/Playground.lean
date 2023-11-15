import Mathlib.CategoryTheory.GaloisCategories.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finite.Basic

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
  by_cases (IsInitial X → False)
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

lemma mono_of_discrete (ι : Type*) (F : Discrete ι ⥤ FintypeCat.{w}) (t : ColimitCocone F) (i : ι) :
    Mono (t.cocone.ι.app ⟨i⟩) :=
  sorry

lemma jointly_surjective_of_discrete {ι : Type*} {F : Discrete ι ⥤ FintypeCat.{w}}
    (t : ColimitCocone F) (x : t.cocone.pt) : ∃ (i : ι) (y : F.obj ⟨i⟩),
    t.cocone.ι.app ⟨i⟩ y = x :=
  sorry

lemma mono_of_cofan_inj (ι : Type*) (f : ι → Type w)
    (t : ColimitCocone (Discrete.functor f)) (i : ι) : Mono (Cofan.inj t.cocone i) :=
  sorry

lemma mono_coprod_inclusion {ι : Type} [Fintype ι] {f : ι → C}
    (t : ColimitCocone (Discrete.functor f)) (i : ι) :
    Mono (Cofan.inj t.cocone i) := by
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone t.cocone
  let s' : IsColimit s := isColimitOfPreserves F t.isColimit
  have h : s.ι.app ⟨i⟩ = F.map (Cofan.inj t.cocone i) := by
    show (F.mapCocone t.cocone).ι.app ⟨i⟩ = F.map (t.cocone.ι.app ⟨i⟩)
    simp only [Functor.mapCocone_ι_app]
  have : Mono (s.ι.app ⟨i⟩) := mono_of_discrete ι (Discrete.functor f ⋙ F) ⟨s, s'⟩ i
  rw [h] at this
  exact mono_of_mono_map F this

example (X : C) (x : F.obj X) : ∃ (Y : C) (i : Y ⟶ X) (y : F.obj Y),
    F.map i y = x ∧ ConnectedObject Y ∧ Mono i := by
  obtain ⟨ι, f, t, hc, hf, he⟩ := hasDecompConnectedComponents F X
  have : Fintype ι := Fintype.ofFinite ι
  let s : Cocone (Discrete.functor f ⋙ F) := F.mapCocone t.cocone
  let s' : IsColimit s := isColimitOfPreserves F t.isColimit
  have : s.pt = F.obj X := by simp only [mapCocone_pt, he]
  let x' : s.pt := (eqToHom this.symm) x
  have : ∃ (j : ι) (z : (Discrete.functor f ⋙ F).obj ⟨j⟩), s.ι.app ⟨j⟩ z = x' :=
    jointly_surjective_of_discrete ⟨s, s'⟩ x'
  obtain ⟨j, z, h⟩ := this
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
