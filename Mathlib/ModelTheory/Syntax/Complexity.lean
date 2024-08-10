/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.ModelTheory.Syntax.Formula


/-!
# Basics on First-Order Syntax
This file defines first-order terms, formulas, sentences, and theories in a style inspired by the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions


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
variable {n l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}
variable {v : α → M} {xs : Fin l → M}

open FirstOrder

open Structure Fin

namespace BoundedFormula

/-- An atomic formula is either equality or a relation symbol applied to terms.
  Note that `⊥` and `⊤` are not considered atomic in this convention. -/
inductive IsAtomic : L.BoundedFormula α n → Prop
  | equal (t₁ t₂ : L.Term (α ⊕ (Fin n))) : IsAtomic (t₁.bdEqual t₂)
  | rel {l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ (Fin n))) :
    IsAtomic (R.boundedFormula ts)

theorem not_all_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic := fun con => by
  cases con

theorem not_ex_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic := fun con => by cases con

theorem IsAtomic.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsAtomic)
    (f : α → β ⊕ (Fin n)) : (φ.relabel f).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

theorem IsAtomic.liftAt {k m : ℕ} (h : IsAtomic φ) : (φ.liftAt k m).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

theorem IsAtomic.castLE {h : l ≤ n} (hφ : IsAtomic φ) : (φ.castLE h).IsAtomic :=
  IsAtomic.recOn hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

/-- A quantifier-free formula is a formula defined without quantifiers. These are all equivalent
to boolean combinations of atomic formulas. -/
inductive IsQF : L.BoundedFormula α n → Prop
  | falsum : IsQF falsum
  | of_isAtomic {φ} (h : IsAtomic φ) : IsQF φ
  | imp {φ₁ φ₂} (h₁ : IsQF φ₁) (h₂ : IsQF φ₂) : IsQF (φ₁.imp φ₂)

theorem IsAtomic.isQF {φ : L.BoundedFormula α n} : IsAtomic φ → IsQF φ :=
  IsQF.of_isAtomic

theorem isQF_bot : IsQF (⊥ : L.BoundedFormula α n) :=
  IsQF.falsum

theorem IsQF.not {φ : L.BoundedFormula α n} (h : IsQF φ) : IsQF φ.not :=
  h.imp isQF_bot

theorem IsQF.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsQF) (f : α → β ⊕ (Fin n)) :
    (φ.relabel f).IsQF :=
  IsQF.recOn h isQF_bot (fun h => (h.relabel f).isQF) fun _ _ h1 h2 => h1.imp h2

theorem IsQF.liftAt {k m : ℕ} (h : IsQF φ) : (φ.liftAt k m).IsQF :=
  IsQF.recOn h isQF_bot (fun ih => ih.liftAt.isQF) fun _ _ ih1 ih2 => ih1.imp ih2

theorem IsQF.castLE {h : l ≤ n} (hφ : IsQF φ) : (φ.castLE h).IsQF :=
  IsQF.recOn hφ isQF_bot (fun ih => ih.castLE.isQF) fun _ _ ih1 ih2 => ih1.imp ih2

theorem not_all_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsQF := fun con => by
  cases' con with _ con
  exact φ.not_all_isAtomic con

theorem not_ex_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsQF := fun con => by
  cases' con with _ con _ _ con
  · exact φ.not_ex_isAtomic con
  · exact not_all_isQF _ con

/-- Indicates that a bounded formula is in prenex normal form - that is, it consists of quantifiers
  applied to a quantifier-free formula. -/
inductive IsPrenex : ∀ {n}, L.BoundedFormula α n → Prop
  | of_isQF {n} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsPrenex φ
  | all {n} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.all
  | ex {n} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.ex

theorem IsQF.isPrenex {φ : L.BoundedFormula α n} : IsQF φ → IsPrenex φ :=
  IsPrenex.of_isQF

theorem IsAtomic.isPrenex {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsPrenex φ :=
  h.isQF.isPrenex

theorem IsPrenex.induction_on_all_not {P : ∀ {n}, L.BoundedFormula α n → Prop}
    {φ : L.BoundedFormula α n} (h : IsPrenex φ)
    (hq : ∀ {m} {ψ : L.BoundedFormula α m}, ψ.IsQF → P ψ)
    (ha : ∀ {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ → P ψ.all)
    (hn : ∀ {m} {ψ : L.BoundedFormula α m}, P ψ → P ψ.not) : P φ :=
  IsPrenex.recOn h hq (fun _ => ha) fun _ ih => hn (ha (hn ih))

theorem IsPrenex.relabel {m : ℕ} {φ : L.BoundedFormula α m} (h : φ.IsPrenex)
    (f : α → β ⊕ (Fin n)) : (φ.relabel f).IsPrenex :=
  IsPrenex.recOn h (fun h => (h.relabel f).isPrenex) (fun _ h => by simp [h.all])
    fun _ h => by simp [h.ex]

theorem IsPrenex.castLE (hφ : IsPrenex φ) : ∀ {n} {h : l ≤ n}, (φ.castLE h).IsPrenex :=
  IsPrenex.recOn (motive := @fun l φ _ => ∀ (n : ℕ) (h : l ≤ n), (φ.castLE h).IsPrenex) hφ
    (@fun _ _ ih _ _ => ih.castLE.isPrenex)
    (@fun _ _ _ ih _ _ => (ih _ _).all)
    (@fun _ _ _ ih _ _ => (ih _ _).ex) _ _

theorem IsPrenex.liftAt {k m : ℕ} (h : IsPrenex φ) : (φ.liftAt k m).IsPrenex :=
  IsPrenex.recOn h (fun ih => ih.liftAt.isPrenex) (fun _ ih => ih.castLE.all)
    fun _ ih => ih.castLE.ex

-- Porting note: universes in different order
/-- An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` is quantifier-free and `ψ` is in prenex normal form, then `φ.toPrenexImpRight ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImpRight : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, φ, BoundedFormula.ex ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).ex
  | n, φ, all ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).all
  | _n, φ, ψ => φ.imp ψ

theorem IsQF.toPrenexImpRight {φ : L.BoundedFormula α n} :
    ∀ {ψ : L.BoundedFormula α n}, IsQF ψ → φ.toPrenexImpRight ψ = φ.imp ψ
  | _, IsQF.falsum => rfl
  | _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, IsQF.imp IsQF.falsum _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, IsQF.imp (IsQF.imp _ _) _ => rfl

theorem isPrenex_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImpRight ψ) := by
  induction' hψ with _ _ hψ _ _ _ ih1 _ _ _ ih2
  · rw [hψ.toPrenexImpRight]
    exact (hφ.imp hψ).isPrenex
  · exact (ih1 hφ.liftAt).all
  · exact (ih2 hφ.liftAt).ex

-- Porting note: universes in different order
/-- An auxiliary operation to `FirstOrder.Language.BoundedFormula.toPrenex`.
  If `φ` and `ψ` are in prenex normal form, then `φ.toPrenexImp ψ`
  is a prenex normal form for `φ.imp ψ`. -/
def toPrenexImp : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n → L.BoundedFormula α n
  | n, BoundedFormula.ex φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).all
  | n, all φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).ex
  | _, φ, ψ => φ.toPrenexImpRight ψ

theorem IsQF.toPrenexImp :
    ∀ {φ ψ : L.BoundedFormula α n}, φ.IsQF → φ.toPrenexImp ψ = φ.toPrenexImpRight ψ
  | _, _, IsQF.falsum => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, _, IsQF.imp IsQF.falsum _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.imp _ _) _ => rfl

theorem isPrenex_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImp ψ) := by
  induction' hφ with _ _ hφ _ _ _ ih1 _ _ _ ih2
  · rw [hφ.toPrenexImp]
    exact isPrenex_toPrenexImpRight hφ hψ
  · exact (ih1 hψ.liftAt).ex
  · exact (ih2 hψ.liftAt).all

-- Porting note: universes in different order
/-- For any bounded formula `φ`, `φ.toPrenex` is a semantically-equivalent formula in prenex normal
  form. -/
def toPrenex : ∀ {n}, L.BoundedFormula α n → L.BoundedFormula α n
  | _, falsum => ⊥
  | _, equal t₁ t₂ => t₁.bdEqual t₂
  | _, rel R ts => rel R ts
  | _, imp f₁ f₂ => f₁.toPrenex.toPrenexImp f₂.toPrenex
  | _, all f => f.toPrenex.all

theorem toPrenex_isPrenex (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex :=
  BoundedFormula.recOn φ isQF_bot.isPrenex (fun _ _ => (IsAtomic.equal _ _).isPrenex)
    (fun _ _ => (IsAtomic.rel _ _).isPrenex) (fun _ _ h1 h2 => isPrenex_toPrenexImp h1 h2)
    fun _ => IsPrenex.all

end BoundedFormula

namespace Formula

theorem isAtomic_graph (f : L.Functions n) : (graph f).IsAtomic :=
  BoundedFormula.IsAtomic.equal _ _

end Formula

end Language

end FirstOrder
