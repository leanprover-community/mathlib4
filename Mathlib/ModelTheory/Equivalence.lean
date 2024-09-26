/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.Satisfiability

/-!
# Equivalence of Formulas

## Main Definitions
- `FirstOrder.Language.Theory.Imp`: `φ ⟹[T] ψ` indicates that `φ` implies `ψ` in models of `T`.
- `FirstOrder.Language.Theory.Iff`: `φ ⇔[T] ψ` indicates that `φ` and `ψ` are equivalent formulas or
  sentences in models of `T`.
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
protected def Imp (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.imp ψ

@[inherit_doc FirstOrder.Language.Theory.Imp]
scoped[FirstOrder] notation:51 φ:50 " ⟹[" T "] " ψ:51 => Language.Theory.Imp T φ ψ

namespace Imp

@[refl]
protected theorem refl (φ : L.BoundedFormula α n) : φ ⟹[T] φ := fun _ _ _ => id

instance : IsRefl (L.BoundedFormula α n) T.Imp := ⟨Imp.refl⟩

@[trans]
protected theorem trans {φ ψ θ : L.BoundedFormula α n} (h1 : φ ⟹[T] ψ) (h2 : ψ ⟹[T] θ) :
    φ ⟹[T] θ := fun M v xs => (h2 M v xs) ∘ (h1 M v xs)

instance : IsTrans (L.BoundedFormula α n) T.Imp := ⟨fun _ _ _ => Imp.trans⟩

end Imp

section Imp

lemma bot_imp (φ : L.BoundedFormula α n) : ⊥ ⟹[T] φ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_bot, false_implies]

lemma imp_top (φ : L.BoundedFormula α n) : φ ⟹[T] ⊤ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_top, implies_true]

lemma imp_sup_left (φ ψ : L.BoundedFormula α n) : φ ⟹[T] φ ⊔ ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inl

lemma imp_sup_right (φ ψ : L.BoundedFormula α n) : ψ ⟹[T] φ ⊔ ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact Or.inr

lemma sup_imp {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] θ) (h₂ : ψ ⟹[T] θ) :
    φ ⊔ ψ ⟹[T] θ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_sup]
  exact fun h => h.elim (h₁ M v xs) (h₂ M v xs)

lemma sup_imp_iff {φ ψ θ : L.BoundedFormula α n} :
    (φ ⊔ ψ ⟹[T] θ) ↔ (φ ⟹[T] θ) ∧ (ψ ⟹[T] θ) :=
  ⟨fun h => ⟨(imp_sup_left _ _).trans h, (imp_sup_right _ _).trans h⟩,
    fun ⟨h₁, h₂⟩ => sup_imp h₁ h₂⟩

lemma inf_imp_left (φ ψ : L.BoundedFormula α n) : φ ⊓ ψ ⟹[T] φ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.left

lemma inf_imp_right (φ ψ : L.BoundedFormula α n) : φ ⊓ ψ ⟹[T] ψ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact And.right

lemma imp_inf {φ ψ θ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : φ ⟹[T] θ) :
    φ ⟹[T] ψ ⊓ θ := fun M v xs => by
  simp only [BoundedFormula.realize_imp, BoundedFormula.realize_inf]
  exact fun h => ⟨h₁ M v xs h, h₂ M v xs h⟩

lemma imp_inf_iff {φ ψ θ : L.BoundedFormula α n} :
    (φ ⟹[T] ψ ⊓ θ) ↔ (φ ⟹[T] ψ) ∧ (φ ⟹[T] θ) :=
  ⟨fun h => ⟨h.trans (inf_imp_left _ _), h.trans (inf_imp_right _ _)⟩,
    fun ⟨h₁, h₂⟩ => imp_inf h₁ h₂⟩

lemma inf_not_imp_bot (φ : L.BoundedFormula α n) :
    φ ⊓ ∼φ ⟹[T] ⊥ := fun M v xs => by simp only [BoundedFormula.realize_imp,
      BoundedFormula.realize_inf, BoundedFormula.realize_not, and_not_self,
      BoundedFormula.realize_bot, imp_self]

lemma top_imp_sup_not (φ : L.BoundedFormula α n) :
    ⊤ ⟹[T] φ ⊔ ∼φ := fun M v xs => by
    simp only [BoundedFormula.realize_imp,
      BoundedFormula.realize_top, BoundedFormula.realize_sup, BoundedFormula.realize_not,
      true_implies]
    exact or_not

end Imp

/-- Two (bounded) formulas are semantically equivalent over a theory `T` when they have the same
interpretation in every model of `T`. (This is also known as logical equivalence, which also has a
proof-theoretic definition.) -/
protected def Iff (T : L.Theory) (φ ψ : L.BoundedFormula α n) : Prop :=
  T ⊨ᵇ φ.iff ψ

@[inherit_doc FirstOrder.Language.Theory.Iff]
scoped[FirstOrder]
notation:51 φ:50 " ⇔[" T "] " ψ:51 => Language.Theory.Iff T φ ψ

theorem iff_iff_imp_and_imp {φ ψ : L.BoundedFormula α n} :
    (φ ⇔[T] ψ) ↔ (φ ⟹[T] ψ) ∧ (ψ ⟹[T] φ) := by
  simp only [Theory.Imp, ModelsBoundedFormula, BoundedFormula.realize_imp, ← forall_and,
    Theory.Iff, BoundedFormula.realize_iff, iff_iff_implies_and_implies]

theorem imp_antisymm {φ ψ : L.BoundedFormula α n} (h₁ : φ ⟹[T] ψ) (h₂ : ψ ⟹[T] φ) :
    φ ⇔[T] ψ :=
  iff_iff_imp_and_imp.2 ⟨h₁, h₂⟩

namespace Iff

protected theorem mp {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    φ ⟹[T] ψ := (iff_iff_imp_and_imp.1 h).1

protected theorem mpr {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    ψ ⟹[T] φ := (iff_iff_imp_and_imp.1 h).2

@[refl]
protected theorem refl (φ : L.BoundedFormula α n) : φ ⇔[T] φ :=
  fun M v xs => by rw [BoundedFormula.realize_iff]

instance : IsRefl (L.BoundedFormula α n) T.Iff :=
  ⟨Iff.refl⟩

@[symm]
protected theorem symm {φ ψ : L.BoundedFormula α n}
    (h : φ ⇔[T] ψ) : ψ ⇔[T] φ := fun M v xs => by
  rw [BoundedFormula.realize_iff, Iff.comm, ← BoundedFormula.realize_iff]
  exact h M v xs

instance : IsSymm (L.BoundedFormula α n) T.Iff :=
  ⟨fun _ _ => Iff.symm⟩

@[trans]
protected theorem trans {φ ψ θ : L.BoundedFormula α n}
    (h1 : φ ⇔[T] ψ) (h2 : ψ ⇔[T] θ) :
    φ ⇔[T] θ := fun M v xs => by
  have h1' := h1 M v xs
  have h2' := h2 M v xs
  rw [BoundedFormula.realize_iff] at *
  exact ⟨h2'.1 ∘ h1'.1, h1'.2 ∘ h2'.2⟩

instance : IsTrans (L.BoundedFormula α n) T.Iff :=
  ⟨fun _ _ _ => Iff.trans⟩

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
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_all]
  exact fun M v xs => forall_congr' fun a => h.realize_bd_iff

protected theorem ex {φ ψ : L.BoundedFormula α (n + 1)} (h : φ ⇔[T] ψ) :
    φ.ex ⇔[T] ψ.ex := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_ex]
  exact fun M v xs => exists_congr fun a => h.realize_bd_iff

protected theorem not {φ ψ : L.BoundedFormula α n} (h : φ ⇔[T] ψ) :
    φ.not ⇔[T] ψ.not := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_not]
  exact fun M v xs => not_congr h.realize_bd_iff

protected theorem imp {φ ψ φ' ψ' : L.BoundedFormula α n} (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') :
    (φ.imp φ') ⇔[T] (ψ.imp ψ') := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_imp]
  exact fun M v xs => imp_congr h.realize_bd_iff h'.realize_bd_iff

protected theorem sup {φ ψ φ' ψ' : L.BoundedFormula α n}
    (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') :
    (φ ⊔ φ') ⇔[T] (ψ ⊔ ψ') := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_sup]
  exact fun M v xs => or_congr h.realize_bd_iff h'.realize_bd_iff

protected theorem inf {φ ψ φ' ψ' : L.BoundedFormula α n}
    (h : φ ⇔[T] ψ) (h' : φ' ⇔[T] ψ') :
    (φ ⊓ φ') ⇔[T] (ψ ⊓ ψ') := by
  simp_rw [Theory.Iff, ModelsBoundedFormula, BoundedFormula.realize_iff,
    BoundedFormula.realize_inf]
  exact fun M v xs => and_congr h.realize_bd_iff h'.realize_bd_iff

end Iff

/-- Semantic equivalence forms an equivalence relation on formulas. -/
def iffSetoid (T : L.Theory) : Setoid (L.BoundedFormula α n) where
  r := T.Iff
  iseqv := ⟨fun _ => refl _, fun {_ _} h => h.symm, fun {_ _ _} h1 h2 => h1.trans h2⟩

end Theory

namespace BoundedFormula

variable (φ ψ : L.BoundedFormula α n)

theorem iff_not_not : φ ⇔[T] φ.not.not := fun M v xs => by
  simp

theorem imp_iff_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ) :=
  fun M v xs => by simp [imp_iff_not_or]

theorem sup_iff_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not :=
  fun M v xs => by simp [imp_iff_not_or]

theorem inf_iff_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not :=
  fun M v xs => by simp

theorem all_iff_not_ex_not (φ : L.BoundedFormula α (n + 1)) :
    φ.all ⇔[T] φ.not.ex.not := fun M v xs => by simp

theorem ex_iff_not_all_not (φ : L.BoundedFormula α (n + 1)) :
    φ.ex ⇔[T] φ.not.all.not := fun M v xs => by simp

theorem iff_all_liftAt : φ ⇔[T] (φ.liftAt 1 n).all :=
  fun M v xs => by
  rw [realize_iff, realize_all_liftAt_one_self]

end BoundedFormula

namespace Formula

variable (φ ψ : L.Formula α)

theorem iff_not_not : φ ⇔[T] φ.not.not :=
  BoundedFormula.iff_not_not φ

theorem imp_iff_not_sup : (φ.imp ψ) ⇔[T] (φ.not ⊔ ψ) :=
  BoundedFormula.imp_iff_not_sup φ ψ

theorem sup_iff_not_inf_not : (φ ⊔ ψ) ⇔[T] (φ.not ⊓ ψ.not).not :=
  BoundedFormula.sup_iff_not_inf_not φ ψ

theorem inf_iff_not_sup_not : (φ ⊓ ψ) ⇔[T] (φ.not ⊔ ψ.not).not :=
  BoundedFormula.inf_iff_not_sup_not φ ψ

end Formula

namespace Theory

variable (T) (α)

/-- The type of formulas modulo a theory. -/
protected def Formula := Quot (T.Iff : L.Formula α → _)

variable {T} {α}

namespace Formula

instance : Coe (L.Formula α) (T.Formula α) := ⟨Quot.mk _⟩

@[simps]
instance : BooleanAlgebra (T.Formula α) where
  le := Quot.lift₂ T.Imp
    (fun _ _ _ h => iff_eq_eq.mp ⟨fun h' => h'.trans h.mp, fun h' => h'.trans h.mpr⟩)
    (fun _ _ _ h => iff_eq_eq.mp ⟨h.mpr.trans, h.mp.trans⟩)
  le_refl := Quot.ind Imp.refl
  le_trans := Quot.ind (fun _ => Quot.ind (fun _ => Quot.ind (fun _ => Imp.trans)))
  le_antisymm := Quot.ind (fun _ => Quot.ind (fun _ h₁ h₂ =>
    (T.iffSetoid.iseqv.quot_mk_eq_iff _ _).2 (imp_antisymm h₁ h₂)))
  sup := Quot.map₂ (· ⊔ ·) (fun _ _ _ => (Iff.refl _).sup)
     (fun _ _ _ h => h.sup (refl _))
  le_sup_left := Quot.ind (fun _ => Quot.ind (fun _ => imp_sup_left _ _))
  le_sup_right := Quot.ind (fun _ => Quot.ind (fun _ => imp_sup_right _ _))
  sup_le := Quot.ind (fun _ => Quot.ind (fun _ => (Quot.ind (fun _ => sup_imp))))
  inf := Quot.map₂ (· ⊓ ·) (fun _ _ _ => (Iff.refl _).inf)
     (fun _ _ _ h => h.inf (refl _))
  inf_le_left := Quot.ind (fun _ => Quot.ind (fun _ => inf_imp_left _ _))
  inf_le_right := Quot.ind (fun _ => Quot.ind (fun _ => inf_imp_right _ _))
  le_inf := Quot.ind (fun _ => Quot.ind (fun _ => (Quot.ind (fun _ => imp_inf))))
  le_sup_inf := Quot.ind (fun _ => Quot.ind fun _ => Quot.ind (fun _ M v xs h => by
    simp only [BoundedFormula.realize_inf, BoundedFormula.realize_sup] at *
    tauto))
  bot := Quot.mk _ ⊥
  bot_le := Quot.ind bot_imp
  top := Quot.mk _ ⊤
  le_top := Quot.ind imp_top
  compl := Quot.map Formula.not (fun _ _ h => h.not)
  inf_compl_le_bot := Quot.ind inf_not_imp_bot
  top_le_sup_compl := Quot.ind top_imp_sup_not

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
