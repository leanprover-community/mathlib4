/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.Data.Finset.Basic
import Mathlib.ModelTheory.Syntax.Basic
import Mathlib.Data.List.ProdSigma

/-!
# Basics on First-Order Semantics
This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions

## Main Results

## Implementation Notes

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/


universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language}
variable {M : Type w} {N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]
variable {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder Cardinal

open Structure Cardinal Fin

namespace Term

-- Porting note: universes in different order
/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
def realize (v : α → M) : ∀ _t : L.Term α, M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).realize v

/- Porting note: The equation lemma of `realize` is too strong; it simplifies terms like the LHS of
`realize_functions_apply₁`. Even `eqns` can't fix this. We removed `simp` attr from `realize` and
prepare new simp lemmas for `realize`. -/

@[simp]
theorem realize_var (v : α → M) (k) : realize v (var k : L.Term α) = v k := rfl

@[simp]
theorem realize_func (v : α → M) {n} (f : L.Functions n) (ts) :
    realize v (func f ts : L.Term α) = funMap f fun i => (ts i).realize v := rfl

@[simp]
theorem realize_constants {c : L.Constants} {v : α → M} : c.term.realize v = c :=
  funMap_eq_coe_constants

@[simp]
theorem realize_functions_apply₁ {f : L.Functions 1} {t : L.Term α} {v : α → M} :
    (f.apply₁ t).realize v = funMap f ![t.realize v] := by
  rw [Functions.apply₁, Term.realize]
  refine congr rfl (funext fun i => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
theorem realize_functions_apply₂ {f : L.Functions 2} {t₁ t₂ : L.Term α} {v : α → M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ![t₁.realize v, t₂.realize v] := by
  rw [Functions.apply₂, Term.realize]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

theorem realize_con {A : Set M} {a : A} {v : α → M} : (L.con a).term.realize v = a :=
  rfl

end Term

variable {n : ℕ}

namespace BoundedFormula

open Term

-- Porting note: universes in different order
/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def Realize : ∀ {l} (_f : L.BoundedFormula α l) (_v : α → M) (_xs : Fin l → M), Prop
  | _, falsum, _v, _xs => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, imp f₁ f₂, v, xs => Realize f₁ v xs → Realize f₂ v xs
  | _, all f, v, xs => ∀ x : M, Realize f v (snoc xs x)

variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}
variable {v : α → M} {xs : Fin l → M}

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormula α l).Realize v xs ↔ False :=
  Iff.rfl

@[simp]
theorem realize_not : φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl

@[simp]
theorem realize_bdEqual (t₁ t₂ : L.Term (α ⊕ (Fin l))) :
    (t₁.bdEqual t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.BoundedFormula α l).Realize v xs ↔ True := by simp [Top.top]

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp [Inf.inf, Realize]

@[simp]
theorem realize_foldr_inf (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ ∀ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction' l with φ l ih
  · simp
  · simp [ih]

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs := by
  simp only [Realize]

@[simp]
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.Term _} :
    (R.boundedFormula ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  Iff.rfl

@[simp]
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.boundedFormula₁ t).Realize v xs ↔ RelMap R ![t.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₁, realize_rel, iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.boundedFormula₂ t₁ t₂).Realize v xs ↔
      RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₂, realize_rel, iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [realize, Sup.sup, realize_not, eq_iff_iff]
  tauto

@[simp]
theorem realize_foldr_sup (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction' l with φ l ih
  · simp
  · simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
      exists_eq_left]

@[simp]
theorem realize_all : (all θ).Realize v xs ↔ ∀ a : M, θ.Realize v (Fin.snoc xs a) :=
  Iff.rfl

@[simp]
theorem realize_ex : θ.ex.Realize v xs ↔ ∃ a : M, θ.Realize v (Fin.snoc xs a) := by
  rw [BoundedFormula.ex, realize_not, realize_all, not_forall]
  simp_rw [realize_not, Classical.not_not]

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormula.iff, realize_inf, realize_imp, and_imp, ← iff_def]

end BoundedFormula

@[simp]
theorem Hom.realize_term (g : M →[L] N) {t : L.Term α} {v : α → M} :
    t.realize (g ∘ v) = g (t.realize v) := by
  induction t
  · rfl
  · rw [Term.realize, Term.realize, g.map_fun]
    refine congr rfl ?_
    ext x
    simp [*]

@[simp]
theorem Embedding.realize_term {v : α → M} (t : L.Term α) (g : M ↪[L] N) :
    t.realize (g ∘ v) = g (t.realize v) :=
  g.toHom.realize_term

@[simp]
theorem Equiv.realize_term {v : α → M} (t : L.Term α) (g : M ≃[L] N) :
    t.realize (g ∘ v) = g (t.realize v) :=
  g.toHom.realize_term


end Language

end FirstOrder
