/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Satisfiability

/-!
# Equivalence of Formulas

## Main Definitions
- `FirstOrder.Language.Theory.Implies`: `φ ⟹[T] ψ` indicates that `φ` implies `ψ` in models of `T`.
- `FirstOrder.Language.Theory.SemanticallyEquivalent`: `φ ⇔[T] ψ` indicates that `φ` and `ψ` are
  equivalent formulas or sentences in models of `T`.
- `FirstOrder.Language.Theory.Formula`: `T.Formula α` is the quotient of `L.Formula α` by
  equivalence modulo a theory `T`.

## Main Results
- `T.Formula α` forms a boolean algebra, with `≤` corresponding to implication.

-/

universe u v w w'

open Cardinal CategoryTheory

open Cardinal FirstOrder

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w} {n : ℕ}
variable {M : Type*} [Nonempty M] [L.Structure M] [M ⊨ T]

namespace Theory

/-- `φ ⟹[T] ψ` indicates that `φ` implies `ψ` in models of `T`. -/
def Implies (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.imp ψ

@[inherit_doc FirstOrder.Language.Theory.Implies]
scoped[FirstOrder] notation:25 φ " ⟹[" T "] " ψ => Language.Theory.Implies T φ ψ

namespace Implies

@[refl]
protected theorem refl (φ : L.BoundedFormula α n) : φ ⟹[T] φ := fun _ _ _ => id

instance : IsRefl (L.BoundedFormula α n) T.Implies := ⟨Implies.refl⟩

@[trans]
protected theorem trans {φ ψ θ : L.BoundedFormula α n} (h1 : φ ⟹[T] ψ) (h2 : ψ ⟹[T] θ) :
    φ ⟹[T] θ := fun M v xs => (h2 M v xs) ∘ (h1 M v xs)

instance : IsTrans (L.BoundedFormula α n) T.Implies := ⟨fun _ _ _ => Implies.trans⟩

end Implies

section Implies

lemma bot_implies (φ : L.BoundedFormula α n) : ⊥ ⟹[T] φ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_bot, false_implies]

lemma implies_top (φ : L.BoundedFormula α n) : φ ⟹[T] ⊤ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true]

lemma implies_sup_left {φ ψ : L.BoundedFormula α n} : φ ⟹[T] φ ⊔ ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inl

lemma implies_sup_right {φ ψ : L.BoundedFormula α n} : ψ ⟹[T] φ ⊔ ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inr

lemma sup_implies {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] θ) (h₂ : ψ ⟹[T] θ) :
    φ ⊔ ψ ⟹[T] θ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact fun h => h.elim (h₁ M v xs) (h₂ M v xs)

lemma inf_implies_left {φ ψ : L.BoundedFormula α n} : φ ⊓ ψ ⟹[T] φ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.left

lemma inf_implies_right {φ ψ : L.BoundedFormula α n} : φ ⊓ ψ ⟹[T] ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.right

lemma implies_inf {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : φ ⟹[T] θ) :
    φ ⟹[T] ψ ⊓ θ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact fun h => ⟨h₁ M v xs h, h₂ M v xs h⟩

lemma inf_not_implies_bot (φ : L.BoundedFormula α n) :
    φ ⊓ ∼φ ⟹[T] ⊥ := fun M v xs => by simp only [BoundedFormula.realize_imp,
      BoundedFormula.realize_inf, BoundedFormula.realize_not, and_not_self,
      BoundedFormula.realize_bot, imp_self]

lemma top_implies_sup_not (φ : L.BoundedFormula α n) :
    ⊤ ⟹[T] φ ⊔ ∼φ := fun M v xs => by
    simp only [BoundedFormula.realize_imp,
      BoundedFormula.realize_top, BoundedFormula.realize_sup, BoundedFormula.realize_not,
      true_implies]
    exact or_not

end Implies

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
def SemanticallyEquivalent (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.iff ψ

@[inherit_doc FirstOrder.Language.Theory.SemanticallyEquivalent]
scoped[FirstOrder] notation:25 φ " ⇔[" T "] " ψ => Language.Theory.SemanticallyEquivalent T φ ψ

theorem semanticallyEquivalent_iff_implies_and_implies {φ ψ : L.BoundedFormula α n} :
    (φ ⇔[T] ψ) ↔ (φ ⟹[T] ψ) ∧ (ψ ⟹[T] φ) := by
  simp only [Implies, ModelsBoundedFormula, BoundedFormula.realize_imp, ← forall_and,
    SemanticallyEquivalent, BoundedFormula.realize_iff, iff_iff_implies_and_implies]

theorem implies_antisymm {φ ψ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : ψ ⟹[T] φ) :
    φ ⇔[T] ψ :=
  semanticallyEquivalent_iff_implies_and_implies.2 ⟨h₁, h₂⟩

namespace SemanticallyEquivalent

protected theorem mp {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    φ ⟹[T] ψ := (semanticallyEquivalent_iff_implies_and_implies.1 h).1

protected theorem mpr {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    ψ ⟹[T] φ := (semanticallyEquivalent_iff_implies_and_implies.1 h).2

@[refl]
protected theorem refl (φ : L.BoundedFormula α n) : φ ⇔[T] φ :=
  fun M v xs => by rw [BoundedFormula.realize_iff]

instance : IsRefl (L.BoundedFormula α n) T.SemanticallyEquivalent :=
  ⟨SemanticallyEquivalent.refl⟩

@[symm]
protected theorem symm {φ ψ : L.BoundedFormula α n}
    (h : φ ⇔[T] ψ) : ψ ⇔[T] φ := fun M v xs => by
  rw [BoundedFormula.realize_iff, Iff.comm, ← BoundedFormula.realize_iff]
  exact h M v xs

instance : IsSymm (L.BoundedFormula α n) T.SemanticallyEquivalent :=
  ⟨fun _ _ => SemanticallyEquivalent.symm⟩

@[trans]
protected theorem trans {φ ψ θ : L.BoundedFormula α n}
    (h1 : φ ⇔[T] ψ) (h2 : ψ ⇔[T] θ) :
    φ ⇔[T] θ := fun M v xs => by
  have h1' := h1 M v xs
  have h2' := h2 M v xs
  rw [BoundedFormula.realize_iff] at *
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩

instance : IsTrans (L.BoundedFormula α n) T.SemanticallyEquivalent :=
  ⟨fun _ _ _ => SemanticallyEquivalent.trans⟩

theorem realize_bd_iff {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ)
    {v : α → M} {xs : Fin n → M} : φ.Realize v xs ↔ ψ.Realize v xs :=
  BoundedFormula.realize_iff.1 (h.realize_boundedFormula M)

theorem realize_iff {φ ψ : L.Formula α} {M : Type*} [Nonempty M]
    [L.Structure M] [M ⊨ T] (h : φ ⇔[T] ψ) {v : α → M} :
    φ.Realize v ↔ ψ.Realize v :=
  h.realize_bd_iff

theorem models_sentence_iff {φ ψ : L.Sentence} {M : Type*} [Nonempty M]
    [L.Structure M] [M ⊨ T] (h : φ ⇔[T] ψ) :
    M ⊨ φ ↔ M ⊨ ψ :=
  h.realize_iff

protected theorem all {φ ψ : L.BoundedFormula α (n + 1)}
    (h : φ ⇔[T] ψ) : φ.all ⇔[T] ψ.all := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_all]
  exact fun M v xs => forall_congr' fun a => h.realize_bd_iff

protected theorem ex {φ ψ : L.BoundedFormula α (n + 1)} (h : φ ⇔[T] ψ) :
    φ.ex ⇔[T] ψ.ex := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex]
  exact fun M v xs => exists_congr fun a => h.realize_bd_iff

protected theorem not {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    φ.not ⇔[T] ψ.not := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_not]
  exact fun M v xs => not_congr h.realize_bd_iff

protected theorem imp {φ ψ φ' ψ' : L.BoundedFormula α n} (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') :
    (φ.imp φ') ⇔[T] (ψ.imp ψ') := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_imp]
  exact fun M v xs => imp_congr h.realize_bd_iff h'.realize_bd_iff

protected theorem sup {φ ψ φ' ψ' : L.BoundedFormula α n}
    (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') :
    (φ ⊔ φ') ⇔[T] (ψ ⊔ ψ') := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_sup]
  exact fun M v xs => or_congr h.realize_bd_iff h'.realize_bd_iff

protected theorem inf {φ ψ φ' ψ' : L.BoundedFormula α n}
    (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') :
    (φ ⊓ φ') ⇔[T] (ψ ⊓ ψ') := by
  simp_rw [SemanticallyEquivalent, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf]
  exact fun M v xs => and_congr h.realize_bd_iff h'.realize_bd_iff

end SemanticallyEquivalent

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def semanticallyEquivalentSetoid (T : L.Theory) : Setoid (L.BoundedFormula α n) where
  r := SemanticallyEquivalent T
  iseqv := ⟨fun _ => refl _, fun {_ _} h => h.symm, fun {_ _ _} h1 h2 => h1.trans h2⟩

end Theory

namespace BoundedFormula

variable (φ ψ : L.BoundedFormula α n)

theorem semanticallyEquivalent_not_not : φ ⇔[T] φ.not.not := fun M v xs => by
  simp

theorem imp_semanticallyEquivalent_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ) :=
  fun M v xs => by simp [imp_iff_not_or]

theorem sup_semanticallyEquivalent_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not :=
  fun M v xs => by simp [imp_iff_not_or]

theorem inf_semanticallyEquivalent_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not :=
  fun M v xs => by simp

theorem all_semanticallyEquivalent_not_ex_not (φ : L.BoundedFormula α (n + 1)) :
    φ.all ⇔[T] φ.not.ex.not := fun M v xs => by simp

theorem ex_semanticallyEquivalent_not_all_not (φ : L.BoundedFormula α (n + 1)) :
    φ.ex ⇔[T] φ.not.all.not := fun M v xs => by simp

theorem semanticallyEquivalent_all_liftAt : φ ⇔[T] (φ.liftAt 1 n).all :=
  fun M v xs => by
  rw [realize_iff, realize_all_liftAt_one_self]

end BoundedFormula

namespace Formula

variable (φ ψ : L.Formula α)

theorem semanticallyEquivalent_not_not : φ ⇔[T] φ.not.not :=
  BoundedFormula.semanticallyEquivalent_not_not φ

theorem imp_semanticallyEquivalent_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ) :=
  BoundedFormula.imp_semanticallyEquivalent_not_sup φ ψ

theorem sup_semanticallyEquivalent_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not :=
  BoundedFormula.sup_semanticallyEquivalent_not_inf_not φ ψ

theorem inf_semanticallyEquivalent_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not :=
  BoundedFormula.inf_semanticallyEquivalent_not_sup_not φ ψ

end Formula

namespace Theory

variable (T) (α)

/-- The type of formulas modulo a theory. -/
protected def Formula := Quot (T.SemanticallyEquivalent : L.Formula α → _)

variable {T} {α}

namespace Formula

instance : Coe (L.Formula α) (T.Formula α) := ⟨Quot.mk _⟩

@[simps]
instance : BooleanAlgebra (T.Formula α) where
  le := Quot.lift₂ T.Implies
    (fun _ _ _ h => iff_eq_eq.mp ⟨fun h' => h'.trans h.implies, fun h' => h'.trans h.symm.implies⟩)
    (fun _ _ _ h => iff_eq_eq.mp ⟨h.symm.implies.trans, h.implies.trans⟩)
  le_refl := Quot.ind Implies.refl
  le_trans := Quot.ind (fun _ => Quot.ind (fun _ => Quot.ind (fun _ => Implies.trans)))
  le_antisymm := Quot.ind (fun _ => Quot.ind (fun _ h₁ h₂ =>
    (T.semanticallyEquivalentSetoid.iseqv.quot_mk_eq_iff _ _).2 (implies_antisymm h₁ h₂)))
  sup := Quot.map₂ (· ⊔ ·) (fun _ _ _ => (SemanticallyEquivalent.refl _).sup)
     (fun _ _ _ h => h.sup (refl _))
  le_sup_left := Quot.ind (fun _ => Quot.ind (fun _ => implies_sup_left))
  le_sup_right := Quot.ind (fun _ => Quot.ind (fun _ => implies_sup_right))
  sup_le := Quot.ind (fun _ => Quot.ind (fun _ => (Quot.ind (fun _ => sup_implies))))
  inf := Quot.map₂ (· ⊓ ·) (fun _ _ _ => (SemanticallyEquivalent.refl _).inf)
     (fun _ _ _ h => h.inf (refl _))
  inf_le_left := Quot.ind (fun _ => Quot.ind (fun _ => inf_implies_left))
  inf_le_right := Quot.ind (fun _ => Quot.ind (fun _ => inf_implies_right))
  le_inf := Quot.ind (fun _ => Quot.ind (fun _ => (Quot.ind (fun _ => implies_inf))))
  le_sup_inf := Quot.ind (fun _ => Quot.ind fun _ => Quot.ind (fun _ M v xs h => by
    simp only [BoundedFormula.realize_inf, BoundedFormula.realize_sup] at *
    tauto))
  bot := Quot.mk _ ⊥
  bot_le := Quot.ind bot_implies
  top := Quot.mk _ ⊤
  le_top := Quot.ind implies_top
  compl := Quot.map Formula.not (fun _ _ h => h.not)
  inf_compl_le_bot := Quot.ind inf_not_implies_bot
  top_le_sup_compl := Quot.ind top_implies_sup_not

/-- Evaluates a formula modulo `T` as true or false in a nonempty model of `T`. -/
@[simp]
def Realize (φ : T.Formula α) {M : Type*} [L.Structure M] [M ⊨ T] [Nonempty M] (v : α → M) : Prop :=
  Quot.lift (fun (ψ : L.Formula α) => ψ.Realize v) (fun _ _ h => iff_eq_eq.mp h.realize_iff) φ

lemma Realize_coe (φ : L.Formula α) {M : Type*} [L.Structure M] [M ⊨ T] [Nonempty M] (v : α → M) :
    Formula.Realize (φ : T.Formula α) v ↔ φ.Realize v := by simp only [Realize]

end Formula

end Theory

end Language

end FirstOrder
