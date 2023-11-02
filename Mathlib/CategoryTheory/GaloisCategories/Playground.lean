import Mathlib.CategoryTheory.GaloisCategories.Basic

universe u v w v₁ u₁ u₂

open CategoryTheory Limits Functor

namespace Galois

variable {C : Type u} [Category.{v, u} C] {F : C ⥤ Type w} [PreGaloisCategory C] [FundamentalFunctor F]

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

lemma sumOfConnectedComponents : (X : C) → ∃ (ι : Type) (D : Discrete ι ⥤ C) (t : Cocone D) (_ : IsColimit t),
    Finite ι ∧ (∀ i, ConnectedObject (D.obj i)) ∧ t.pt = X := by
  have : ∀ (n : ℕ) (X : C), n = Nat.card (F.obj X) → ∃ (ι : Type) (D : Discrete ι ⥤ C) (t : Cocone D) (_ : IsColimit t),
    Finite ι ∧ (∀ i, ConnectedObject (D.obj i)) ∧ t.pt = X
  intro n
  induction' n using Nat.strong_induction_on with n hi
  intro X hn
  by_cases ConnectedObject X
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
  by_cases (IsInitial X → False)
  . have : ¬ (∀ (Y : C) (i : Y ⟶ X) [Mono i], (IsInitial Y → False) → IsIso i) := sorry
    simp at this
    obtain ⟨Y, hnotinitial, v, hvmono, hvnoiso⟩ := this
    have : Function.Injective (F.map v) := (monomorphismIffInducesInjective v).mp hvmono
    have : Nat.card (F.obj Y) ≠ 0 := sorry
    obtain ⟨Z, u, x, _⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand v
    have hn1 : Nat.card (F.obj Y) < n := sorry
    have hn2 : Nat.card (F.obj Z) < n := sorry
    obtain ⟨ι₁, D₁, t₁, ht₁, hfin₁, hconn₁, h₁⟩ := hi (Nat.card (F.obj Y)) hn1 Y rfl
    obtain ⟨ι₂, D₂, t₂, ht₂, hfin₂, hconn₂, h₂⟩ := hi (Nat.card (F.obj Z)) hn2 Z rfl
    let ι := Sum ι₁ ι₂
    use ι
    let f : ι → C
    | Sum.inl i => D₁.obj ⟨i⟩
    | Sum.inr i => D₂.obj ⟨i⟩
    use (Discrete.functor f)
    let t : Cocone (Discrete.functor f) := {
      pt := X
      ι := by
        apply Discrete.natTrans
        intro ⟨i⟩
        exact match i with
        | Sum.inl i => by
            let h := t₁.ι.app ⟨i⟩
            rw [h₁] at h
            exact h ≫ v
        | Sum.inr i => by
            let h := t₂.ι.app ⟨i⟩
            rw [h₂] at h
            exact h ≫ u
    }
    use t
    have hco : IsColimit t := {
      desc := by
        intro s
        show X ⟶ s.pt
        let s₁ : Cocone D₁ := {
          pt := s.pt
          ι := by
            apply Discrete.natTrans
            intro ⟨i⟩
            exact s.ι.app ⟨Sum.inl i⟩
        }
        let f₁ : Y ⟶ s.pt := by
          rw [←h₁]
          exact ht₁.desc s₁
        let s₂ : Cocone D₂ := {
          pt := s.pt
          ι := by
            apply Discrete.natTrans
            intro ⟨i⟩
            exact s.ι.app ⟨Sum.inr i⟩
        }
        let f₂ : Z ⟶ s.pt := by
          rw [←h₂]
          exact ht₂.desc s₂
        let c : BinaryCofan Y Z := BinaryCofan.mk f₁ f₂
        let g : X ⟶ s.pt := x.desc c
        exact g
    }
    use hco
    simp
    constructor
    exact Finite.instFiniteSum
    intro ⟨i⟩
    match i with
    | Sum.inl i => exact hconn₁ ⟨i⟩
    | Sum.inr i => exact hconn₂ ⟨i⟩
  . simp at h
    obtain ⟨y, _⟩ := h
    use PEmpty
    use empty C
    use asEmptyCocone X
    use y
    simp only [IsEmpty.forall_iff, asEmptyCocone_pt, and_self, and_true]
    exact Finite.of_fintype PEmpty.{1}
  intro X
  exact this (Nat.card (F.obj X)) X rfl
