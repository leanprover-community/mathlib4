import Mathlib.CategoryTheory.GaloisCategories.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finite.Basic

universe u v w v₁ u₁ u₂

open CategoryTheory Limits Functor

namespace Galois

variable {C : Type u} [Category.{v, u} C] (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory C]
  [FibreFunctor F]

example (X : C) : ∃ (ι : Type) (f : ι → C) (t : ColimitCocone (Discrete.functor f)),
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

noncomputable def blub2 (X : C) :
    (ι : Type) × (ι → C) := by
  revert X
  let hp : ∀ (n : ℕ) (X : C), n = Nat.card (F.obj X) → (ι : Type) × (ι → C)
  intro n
  induction' n using Nat.strongRecOn with n hi
  intro X hn
  by_cases ConnectedObject X
  let ι : Type := PUnit
  let f : ι → C := fun _ ↦ X
  exact ⟨ι, f⟩
  by_cases (IsInitial X → False)
  swap
  simp only [not_forall] at h
  let ι : Type := PEmpty
  let f : ι → C := fun _ ↦ X
  exact ⟨ι, f⟩
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
  let ⟨ι₁, f₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
  obtain ⟨ι₂, f₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
  let ι := Sum ι₁ ι₂
  let f : ι → C := Sum.elim f₁ f₂
  exact ⟨ι, f⟩
  intro X
  exact hp (Nat.card (F.obj X)) X rfl

noncomputable def components.index (X : C) : Type
  := (blub2 F X).1

noncomputable def components.map (X : C) : components.index F X → C
  := (blub2 F X).2

noncomputable instance (X : C) : Finite (components.index F X) := by
  admit

example (X : C) (i : components.index F X) : ConnectedObject (components.map F X i) := by
  admit

noncomputable def components.iso (X : C) : X ≅ ∐ components.map F X := by
  admit

noncomputable def components.isoObj (X : C) :
    F.obj X ≅ ∐ fun j ↦ F.obj (components.map F X j) := by
  admit

def blub (X : C) : (ι : Type) × (f : ι → C) × (ColimitCocone (Discrete.functor f)) := by
  revert X
  let : ∀ (n : ℕ) (X : C), n = Nat.card (F.obj X) → (ι : Type) × (f : ι → C) × (ColimitCocone (Discrete.functor f))
  intro n
  induction' n using Nat.strongRecOn with n hi
  intro X hn
  by_cases ConnectedObject X
  let ι : Type := PUnit
  let f : ι → C := fun _ ↦ X
  let t : ColimitCocone (Discrete.functor f) := colimitCoconeOfUnique f
  exact ⟨ι, f, t⟩
  by_cases (IsInitial X → False)
  swap
  simp only [not_forall] at h
  choose hin _ using h
  let ι : Type := PEmpty
  let f : ι → C := fun _ ↦ X
  let t : ColimitCocone (Discrete.functor f) := getColimitCocone (Discrete.functor f)
  exact ⟨ι, f, t⟩
  have : ¬ (∀ (Y : C) (i : Y ⟶ X) [Mono i], (IsInitial Y → False) → IsIso i) := sorry
  simp at this
  choose Y hnotinitial v hvmono hvnoiso using this
  have : Function.Injective (F.map v) := (monomorphismIffInducesInjective v).mp hvmono
  have : Nat.card (F.obj Y) ≠ 0 := sorry
  choose Z u x using PreGaloisCategory.monoInducesIsoOnDirectSummand v
  have hn1 : Nat.card (F.obj Y) < n := sorry
  have hn2 : Nat.card (F.obj Z) < n := sorry
  let ⟨ι₁, f₁, t₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
  obtain ⟨ι₂, f₂, t₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
  let ι := Sum ι₁ ι₂
  let f : ι → C := Sum.elim f₁ f₂
  let c : Cocone (Discrete.functor f) := {
    pt := X
    ι := by
      apply Discrete.natTrans
      rintro ⟨i⟩
      cases i with
      | inl j =>
          let bla := t₁.cocone.ι.app ⟨j⟩
          simp at bla
          exact t₁.cocone.ι.app ⟨j⟩
      | inr j => exact t₁.cocone.ι.app ⟨j⟩
  }
  --let t : ColimitCocone (Discrete.functor f) where
  --  cocone := c
  --  isColimit := sorry
  admit
  admit

example (X : C) [ConnectedObject X] : ∃ (ι : Type) (D : Discrete ι ⥤ C) (t : Cocone D) (_ : IsColimit t),
    Finite ι ∧ (∀ i, ConnectedObject (D.obj i)) ∧ t.pt = X := by
  use PUnit
  use fromPUnit X
  use {
    pt := X
    ι := { app := fun _ ↦ 𝟙 X }
  }
  use { desc := fun s ↦ s.ι.app ⟨PUnit.unit⟩ }
  simp only [const_obj_obj, forall_const, and_true]
  constructor
  exact Finite.of_fintype PUnit.{1}
  assumption

def bla1 (X : C) : Type := by
  revert X
  let : ∀ (n : ℕ) (X : C), n = Nat.card (F.obj X) → Type
  intro n
  induction' n using Nat.strongRecOn with n hi
  intro X hn
  by_cases ConnectedObject X
  exact PUnit

def bla2 (X : C) : bla1 X → C := sorry

instance (X : C) : Finite (bla1 X) := sorry

--example (X : C) : ∃ (ι : Type) (_ : Finite ι) (f : ι → C) (_ : X ≅ ∐ f), ∀ i, ConnectedObject (f i) := by
--  revert X
--  have : ∀ (n : ℕ) (X : C), n = Nat.card (F.obj X) → ∃ (ι : Type) (_ : Finite ι) (f : ι → C) (_ : X ≅ ∐ f),
--    ∀ i, ConnectedObject (f i)

--lemma sumOfConnectedComponents : (X : C) → ∃ (ι : Type) (D : Discrete ι ⥤ C) (t : Cocone D) (_ : IsColimit t),
--    Finite ι ∧ (∀ i, ConnectedObject (D.obj i)) ∧ t.pt = X := by
--  have : ∀ (n : ℕ) (X : C), n = Nat.card (F.obj X) → ∃ (ι : Type) (D : Discrete ι ⥤ C) (t : Cocone D) (_ : IsColimit t),
--    Finite ι ∧ (∀ i, ConnectedObject (D.obj i)) ∧ t.pt = X
--  intro n
--  induction' n using Nat.strong_induction_on with n hi
--  intro X hn
--  by_cases ConnectedObject X
--  use PUnit
--  use fromPUnit X
--  use {
--    pt := X
--    ι := { app := fun _ ↦ 𝟙 X }
--  }
--  use { desc := fun s ↦ s.ι.app ⟨PUnit.unit⟩ }
--  simp only [const_obj_obj, forall_const, and_true]
--  constructor
--  exact Finite.of_fintype PUnit.{1}
--  assumption
--  by_cases (IsInitial X → False)
--  . have : ¬ (∀ (Y : C) (i : Y ⟶ X) [Mono i], (IsInitial Y → False) → IsIso i) := sorry
--    simp at this
--    obtain ⟨Y, hnotinitial, v, hvmono, hvnoiso⟩ := this
--    have : Function.Injective (F.map v) := (monomorphismIffInducesInjective v).mp hvmono
--    have : Nat.card (F.obj Y) ≠ 0 := sorry
--    obtain ⟨Z, u, x, _⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand v
--    have hn1 : Nat.card (F.obj Y) < n := sorry
--    have hn2 : Nat.card (F.obj Z) < n := sorry
--    obtain ⟨ι₁, D₁, t₁, ht₁, hfin₁, hconn₁, h₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
--    obtain ⟨ι₂, D₂, t₂, ht₂, hfin₂, hconn₂, h₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
--    let ι := Sum ι₁ ι₂
--    use ι
--    let f : ι → C
--    | Sum.inl i => D₁.obj ⟨i⟩
--    | Sum.inr i => D₂.obj ⟨i⟩
--    use (Discrete.functor f)
--    let t : Cocone (Discrete.functor f) := {
--      pt := X
--      ι := by
--        apply Discrete.natTrans
--        intro ⟨i⟩
--        exact match i with
--        | Sum.inl i => by
--            let h := t₁.ι.app ⟨i⟩
--            rw [h₁] at h
--            exact h ≫ v
--        | Sum.inr i => by
--            let h := t₂.ι.app ⟨i⟩
--            rw [h₂] at h
--            exact h ≫ u
--    }
--    use t
--    have hco : IsColimit t := {
--      desc := by
--        intro s
--        show X ⟶ s.pt
--        let s₁ : Cocone D₁ := {
--          pt := s.pt
--          ι := by
--            apply Discrete.natTrans
--            intro ⟨i⟩
--            exact s.ι.app ⟨Sum.inl i⟩
--        }
--        let f₁ : Y ⟶ s.pt := by
--          rw [←h₁]
--          exact ht₁.desc s₁
--        let s₂ : Cocone D₂ := {
--          pt := s.pt
--          ι := by
--            apply Discrete.natTrans
--            intro ⟨i⟩
--            exact s.ι.app ⟨Sum.inr i⟩
--        }
--        let f₂ : Z ⟶ s.pt := by
--          rw [←h₂]
--          exact ht₂.desc s₂
--        let c : BinaryCofan Y Z := BinaryCofan.mk f₁ f₂
--        let g : X ⟶ s.pt := x c
--        exact g
--    }
--    use hco
--    simp
--    constructor
--    exact Finite.instFiniteSum
--    intro ⟨i⟩
--    match i with
--    | Sum.inl i => exact hconn₁ ⟨i⟩
--    | Sum.inr i => exact hconn₂ ⟨i⟩
--  . simp at h
--    obtain ⟨y, _⟩ := h
--    use PEmpty
--    use empty C
--    use asEmptyCocone X
--    use y
--    simp only [IsEmpty.forall_iff, asEmptyCocone_pt, and_self, and_true]
--    exact Finite.of_fintype PEmpty.{1}
--  intro X
--  exact this (Nat.card (F.obj X)) X rfl
