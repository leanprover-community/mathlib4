/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.VecNotation
/-!

Marginis:

Relative computability and uniform continuity of relations
Arno M Pauly, Martin A. Ziegler

We formalize their n-fold version of the Henkin quantifier property
and prove it implies an "ordinary" quantifier property.
The converse fails once n is at least 2 and the domain has at least 2 elements.
In that case, we show that one of the four variables can be ignored and the converse still fails.

-/

/-- `Henkin R` is the statement (when `n=2`) that
  `∀ x₁ x₂ ∃ y₁ y₂ R (x₁, x₂) (y₁, y₂)`,
  and moreover `y₁` depends only on `x₁` and `y₂` depends only on `x₂`.
-/
def Henkin {n:ℕ} {U : Type} (R : (Fin n → U) → (Fin n → U) → Prop) :=
  ∃ Y : Fin n → U → U, ∀ x : Fin n → U, R x (fun k ↦ Y k (x k))

/-- The Henkin property is a kind of "uniform ∀ x, ∃ y". -/
lemma henkin_implies {n : ℕ} {U : Type} (R : (Fin n → U) → (Fin n → U) → Prop) :
  Henkin R → ∀ x, ∃ y, R x y := by
  intro h x
  obtain ⟨Y,hY⟩ := h
  use (fun k ↦ Y k (x k))
  tauto

/-- There is only one empty tuple so they "all" have the same properties. -/
lemma empty_tuples_agree {U : Type} (a x : Fin 0 → U) (R : (Fin 0 → U) → (Fin 0 → U) → Prop)
    (y : Fin 0 → U) (h : R a x) : R a y := ((List.ofFn_inj.mp rfl) : x = y) ▸ h

/-- How large a domain do we need in order to separate Henkin and ∀x ∃y? n=0 is not enough -/
lemma zero_not_enough : ¬ ∃ U, ∃ (R : (Fin 0 → U) → (Fin 0 → U) → Prop),
  (∀ x, ∃ y, R x y) ∧ ¬ Henkin R := by
    push_neg
    intro U R h
    use (fun k : Fin 0 ↦ False.elim (Nat.not_succ_le_zero k.1 k.2))
    intro x
    obtain ⟨y,hy⟩ := h x
    apply empty_tuples_agree x y R
    exact hy

/-- n=1 is not enough to separate Henkin and ∀x∃y, either.
  The proof uses Choice (and is basically equivalent to Choice). -/
lemma one_not_enough : ¬ ∃ U, ∃ (R : (Fin 1 → U) → (Fin 1 → U) → Prop),
  (∀ x, ∃ y, R x y) ∧ ¬ Henkin R := by
    push_neg
    intro U R h
    use (fun _ x ↦
      (@Classical.choice {y // R (fun _ ↦ x) y} (nonempty_subtype.mpr (h _))).1 0)
    intro x
    have h₁: (fun k ↦
      (Classical.choice (nonempty_subtype.mpr (h fun _ ↦ x k))).1 0) =
      (Classical.choice (nonempty_subtype.mpr (h fun _ ↦ x 0))).1 :=
      funext (fun x₁ => Fin.fin_one_eq_zero x₁ ▸ rfl)
    have h₀ : x = (fun _ ↦ x 0) := funext (fun x₁ => by rw [Fin.fin_one_eq_zero x₁])
    nth_rewrite 1 [h₀]
    rw [h₁]
    exact (Classical.choice (nonempty_subtype.mpr (h fun _ ↦ x 0))).2


/-- n=2 may be enough to separate Henkin and ∀x∃y, but not if U has only one element. -/
lemma unit_not_enough {n : ℕ} : ¬ ∃ (R : (Fin n → Unit) → (Fin n → Unit) → Prop),
  (∀ x, ∃ y, R x y) ∧ ¬ Henkin R := by
    intro hc
    obtain ⟨R,hR⟩ := hc
    revert hR
    contrapose
    intro
    push_neg
    intro h
    exists (fun _ ↦ by
      intro; exact ()
    )
    intro x
    simp
    obtain ⟨_,hy⟩ := h x
    tauto

/-- n=2 is enough with U having two elements.
  We can even ignore one of the variables (`y 1` below) completely. -/
lemma separate_henkin : ∃ (R : (Fin 2 → Bool) → (Fin 2 → Bool) → Prop),
  (∀ x, ∃ y, R x y) ∧ ¬ Henkin R := by
  use (fun x y ↦  y 0 = xor (x 0) (x 1))
  constructor
  · intro x
    use (fun _ ↦ xor (x 0) (x 1))
  unfold Henkin
  push_neg
  intro Y
  use ![false, ! Y 0 false]
  simp

/-- Definition of "there are infinitely many" using Henkin quantifiers. -/
def HenkinInfinite {A : Type} : Prop :=
  ∃ a : A,  Henkin (fun x y : Fin 2 → A => (x 0 = x 1 ↔ y 0 = y 1) ∧ y 0 ≠ a)

open Unit

/-- The ∀ x, ∃ y version of HenkinInfinite holds already in a 2-element type. -/
lemma classical_henkin : ∃ a : Unit ⊕ Unit, ∀ x : Fin 2 → Unit ⊕ Unit,
    ∃ y  : Fin 2 → Unit ⊕ Unit, (x 0 = x 1 ↔ y 0 = y 1) ∧ y 0 ≠ a := by
  use .inl unit
  intro x
  use ![.inr unit, ite (x 0 = x 1) (.inr unit) (.inl unit)]
  split_ifs with h <;> tauto

/-- A Henkin infinite type is in fact infinite. -/
theorem henkinInfinite_implies {A : Type} (H : @HenkinInfinite A) :
  ∃ f : A → A, Function.Injective f ∧ ¬ Function.Surjective f := by
  obtain ⟨a,ha⟩ := H
  obtain ⟨Y,hY⟩ := ha
  simp at hY
  have : Y 0 = Y 1 := by
    ext u
    let Q := (hY ![u,u]).1.mp (by simp)
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at Q
    exact Q
  use Y 0
  constructor
  · intro b c hbc
    rw [← this] at hY
    let Q := (hY ![b,c]).1.mpr hbc
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at Q
    exact Q
  · intro hc
    have : ∃ b, Y 0 b = a := by exact hc a
    obtain ⟨b,hb⟩ := this
    let Q := (hY ![b,b]).2
    simp at Q
    exact Q hb

/-- An infinite type is in fact Henkin infinite. -/
theorem implies_HenkinInfinite {A : Type}
    (f : A → A) (hi : Function.Injective f) (hs : ¬ Function.Surjective f) :
    @HenkinInfinite A := by
  unfold Function.Surjective at hs
  push_neg at hs
  obtain ⟨a,ha⟩ := hs
  use a, (fun _ => f)
  exact fun x => ⟨⟨congrArg f, @hi (x 0) (x 1)⟩, ha _⟩

/-- A result mentioned in Wikipedia at
  https://en.wikipedia.org/wiki/Branching_quantifier#Definition_and_properties -/
theorem henkinInfite_characterization {A : Type} :
    (∃ (f : A → A), Function.Injective f ∧ ¬ Function.Surjective f) ↔ @HenkinInfinite A :=
  ⟨fun ⟨f,hf⟩ => implies_HenkinInfinite (by tauto) (fun ⦃a₁⦄ ↦ fun x hx => hf.1 hx) hf.2,
    henkinInfinite_implies⟩
