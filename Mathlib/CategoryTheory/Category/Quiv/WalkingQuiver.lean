import Mathlib.CategoryTheory.Category.Quiv
import Mathlib.Data.Fintype.Basic
import Mathlib.CategoryTheory.ConcreteCategory.Basic

import Mathlib.Tactic.ApplyFun
-- import Mathlib.Tactic.finCases

open CategoryTheory

inductive WalkingQuiver where | zero | one deriving Inhabited

-- instance : Fintype WalkingQuiver := Fin.fintype 2

instance : OfNat WalkingQuiver 0 := ⟨WalkingQuiver.zero⟩
instance : OfNat WalkingQuiver 1 := ⟨WalkingQuiver.one⟩

-- set `0` and `1` as simp normal forms
@[simp]
lemma zero_eq : WalkingQuiver.zero = 0 := rfl
@[simp]
lemma one_eq : WalkingQuiver.one = 1 := rfl

-- instance : Zero WalkingQuiver := ⟨WalkingQuiver.zero⟩
-- instance : One WalkingQuiver := ⟨WalkingQuiver.one⟩

-- Delaborators to use `0` and `1` instead of `WalkingQuiver.zero` and `WalkingQuiver.one`

@[delab app.WalkingQuiver.zero]
def delabWalkingQuiverZero : Lean.PrettyPrinter.Delaborator.Delab := do
  return ← `(0)

@[delab app.WalkingQuiver.one]
def delabWalkingQuiverOne : Lean.PrettyPrinter.Delaborator.Delab := do
  return ← `(1)




inductive WalkingQuiver.Hom : WalkingQuiver → WalkingQuiver → Type
| id X : WalkingQuiver.Hom X X
| source : WalkingQuiver.Hom .one .zero
| target: WalkingQuiver.Hom .one .zero

def WalkingQuiver.forget : WalkingQuiver → Type
  | .zero => Bool
  | .one => Unit

instance (X Y : WalkingQuiver) :
    FunLike (WalkingQuiver.Hom X Y) (WalkingQuiver.forget X) (WalkingQuiver.forget Y) where
  coe
  | .id X => id
  | .source => fun _ => false
  | .target => fun _ => true
  coe_injective' X Y f := by
    cases X <;> cases Y <;> simp_all [funext_iff, WalkingQuiver.forget]

instance : Category WalkingQuiver where
  Hom := WalkingQuiver.Hom
  id := WalkingQuiver.Hom.id
  comp
    | WalkingQuiver.Hom.id _, g => g
    | f, WalkingQuiver.Hom.id _ => f
  id_comp f := by cases f <;> rfl
  comp_id f := by cases f <;> rfl
  assoc {W X Y Z} f g h := by
    cases Z; swap
    · cases h; cases g; cases f; rfl
    · cases Y; swap
      · cases g; cases f; cases h <;> rfl
      · cases h
        cases X; swap
        · cases f; cases g <;> rfl
        · cases g; cases f <;> rfl

#check instCategoryWalkingQuiver.match_1

instance : ConcreteCategory WalkingQuiver WalkingQuiver.Hom where
  hom := id
  ofHom := id
  comp_apply {X Y Z} f g X' := by
    simp [instCategoryWalkingQuiver]
    cases Y
    · cases X
      · cases f; simp; rfl
      · cases Z
        · cases g; cases f <;> {simp; rfl}
        · cases g
    · cases X
      · cases f
      · cases f; cases g <;> {simp; rfl}

namespace WalkingQuiver

/-- Convenience recursor for `WalkingQuiver` in terms of the notation `0` and `1`. -/
@[elab_as_elim, cases_eliminator]
def casesOn' {motive : WalkingQuiver → Sort*}
    (m : WalkingQuiver) (zero : motive 0) (one : motive 1) : motive m :=
  match m with | 0 => zero | 1 => one

@[simp]
lemma id_def (X : WalkingQuiver) : WalkingQuiver.Hom.id X = 𝟙 X := rfl

@[simp]
lemma hom₀₁_empty : IsEmpty ((0 : WalkingQuiver) ⟶ 1) := ⟨by rintro ⟨⟩⟩

/-- Any function out of `WalkingQuiver` can be represented as a pair of values for `0` and `1`. -/
def funByCases {α : WalkingQuiver → Sort*} : ((m : WalkingQuiver) → α m) ≃ (α 0 ×' α 1) :=
  { toFun := fun f => ⟨f 0, f 1⟩,
    invFun := fun ⟨f₀, f₁⟩ => fun | 0 => f₀ | 1 => f₁,
    left_inv := fun f => by ext x; cases x <;> rfl,
    right_inv := fun ⟨f₀, f₁⟩ => by simp }


@[elab_as_elim]
def casesOn_fun {α : WalkingQuiver → Sort*} {motive : ((m : WalkingQuiver) → α m) → Sort*}
    (f : (m : WalkingQuiver) → α m) (split : motive (fun | 0 => f 0 | 1 => f 1)) :
    motive f := by
  convert split with m; cases m <;> simp

lemma funByCases_eq {α : WalkingQuiver → Sort*} (f : (m : WalkingQuiver) → α m) :
    f = fun | 0 => f 0 | 1 => f 1 := by
  ext x; cases x <;> rfl

lemma forall_byCases {p : WalkingQuiver → Prop}  :
    (∀ m, p m) ↔ p 0 ∧ p 1 where
  mp h := by simp [h]
  mpr := fun ⟨h₀, h₁⟩ m ↦ by cases m <;> assumption

@[simp]
lemma forall₀₀ {p : ((0 : WalkingQuiver) ⟶ 0) → Prop} : (∀ f, p f) ↔ p (𝟙 0) where
  mp h := h _
  mpr h := fun f ↦ by cases f; exact h

@[simp]
lemma forall₁₁ {p : ((1 : WalkingQuiver) ⟶ 1) → Prop} : (∀ f, p f) ↔ p (𝟙 1) where
  mp h := h _
  mpr h := fun f ↦ by cases f; exact h

@[simp]
lemma forall₀₁ {p : ((0 : WalkingQuiver) ⟶ 1) → Prop} : (∀ f, p f) ↔ True where
  mp _ := trivial
  mpr _ := nofun

@[simp]
lemma forall₁₀ {p : ((1 : WalkingQuiver) ⟶ 0) → Prop} : (∀ f, p f) ↔ p .source ∧ p .target where
  mp h := by simp [h]
  mpr := fun ⟨h₀, h₁⟩ f ↦ by cases f <;> assumption

@[simp]
lemma forallHom_byCases {p : {m₁ m₂ : WalkingQuiver} → (m₁ ⟶ m₂) → Prop} :
    (∀ {m₁ m₂} (f : m₁ ⟶ m₂), p f) ↔ (∀ m, p (𝟙 m)) ∧ p .source ∧ p .target where
  mp h := by simp [h]
  mpr := fun ⟨h_id, h_src, h_tgt⟩ m₁ m₂ f ↦ by
    cases f with
    | id => cases m₁ <;> simp_all
    | _ => simp_all
