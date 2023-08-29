/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.Data.Finset.Basic
import Mathlib.ModelTheory.Syntax

#align_import model_theory.semantics from "leanprover-community/mathlib"@"d565b3df44619c1498326936be16f1a935df0728"

/-!
# Basics on First-Order Semantics
This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions
* `FirstOrder.Language.Term.realize` is defined so that `t.realize v` is the term `t` evaluated at
variables `v`.
* `FirstOrder.Language.BoundedFormula.Realize` is defined so that `φ.Realize v xs` is the bounded
formula `φ` evaluated at tuples of variables `v` and `xs`.
* `FirstOrder.Language.Formula.Realize` is defined so that `φ.Realize v` is the formula `φ`
evaluated at variables `v`.
* `FirstOrder.Language.Sentence.Realize` is defined so that `φ.Realize M` is the sentence `φ`
evaluated in the structure `M`. Also denoted `M ⊨ φ`.
* `FirstOrder.Language.Theory.Model` is defined so that `T.Model M` is true if and only if every
sentence of `T` is realized in `M`. Also denoted `T ⊨ φ`.

## Main Results
* `FirstOrder.Language.BoundedFormula.realize_toPrenex` shows that the prenex normal form of a
formula has the same realization as the original formula.
* Several results in this file show that syntactic constructions such as `relabel`, `castLE`,
`liftAt`, `subst`, and the actions of language maps commute with realization of terms, formulas,
sentences, and theories.

## Implementation Notes
* Formulas use a modified version of de Bruijn variables. Specifically, a `L.BoundedFormula α n`
is a formula with some variables indexed by a type `α`, which cannot be quantified over, and some
indexed by `Fin n`, which can. For any `φ : L.BoundedFormula α (n + 1)`, we define the formula
`∀' φ : L.BoundedFormula α n` by universally quantifying over the variable indexed by
`n : Fin (n + 1)`.

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

variable {α : Type u'} {β : Type v'}

open FirstOrder Cardinal

open Structure Cardinal Fin

namespace Term

--Porting note: universes in different order
/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
def realize (v : α → M) : ∀ _t : L.Term α, M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).realize v
#align first_order.language.term.realize FirstOrder.Language.Term.realize

/- Porting note: The equation lemma of `realize` is too strong; it simplifies terms like the LHS of
`realize_functions_apply₁`. Even `eqns` can't fix this. We removed `simp` attr from `realize` and
prepare new simp lemmas for `realize`. -/

@[simp]
theorem realize_var (v : α → M) (k) : realize v (var k : L.Term α) = v k := rfl

@[simp]
theorem realize_func (v : α → M) {n} (f : L.Functions n) (ts) :
    realize v (func f ts : L.Term α) = funMap f fun i => (ts i).realize v := rfl

@[simp]
theorem realize_relabel {t : L.Term α} {g : α → β} {v : β → M} :
    (t.relabel g).realize v = t.realize (v ∘ g) := by
  induction' t with _ n f ts ih
  -- ⊢ realize v (relabel g (var _a✝)) = realize (v ∘ g) (var _a✝)
  · rfl
    -- 🎉 no goals
  · simp [ih]
    -- 🎉 no goals
#align first_order.language.term.realize_relabel FirstOrder.Language.Term.realize_relabel

@[simp]
theorem realize_liftAt {n n' m : ℕ} {t : L.Term (Sum α (Fin n))} {v : Sum α (Fin (n + n')) → M} :
    (t.liftAt n' m).realize v =
      t.realize (v ∘ Sum.map id fun i : Fin _ =>
        if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') :=
  realize_relabel
#align first_order.language.term.realize_lift_at FirstOrder.Language.Term.realize_liftAt

@[simp]
theorem realize_constants {c : L.Constants} {v : α → M} : c.term.realize v = c :=
  funMap_eq_coe_constants
#align first_order.language.term.realize_constants FirstOrder.Language.Term.realize_constants

@[simp]
theorem realize_functions_apply₁ {f : L.Functions 1} {t : L.Term α} {v : α → M} :
    (f.apply₁ t).realize v = funMap f ![t.realize v] := by
  rw [Functions.apply₁, Term.realize]
  -- ⊢ (funMap f fun i => realize v (Matrix.vecCons t ![] i)) = funMap f ![realize  …
  refine' congr rfl (funext fun i => _)
  -- ⊢ realize v (Matrix.vecCons t ![] i) = Matrix.vecCons (realize v t) ![] i
  simp only [Matrix.cons_val_fin_one]
  -- 🎉 no goals
#align first_order.language.term.realize_functions_apply₁ FirstOrder.Language.Term.realize_functions_apply₁

@[simp]
theorem realize_functions_apply₂ {f : L.Functions 2} {t₁ t₂ : L.Term α} {v : α → M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ![t₁.realize v, t₂.realize v] := by
  rw [Functions.apply₂, Term.realize]
  -- ⊢ (funMap f fun i => realize v (Matrix.vecCons t₁ ![t₂] i)) = funMap f ![reali …
  refine' congr rfl (funext (Fin.cases _ _))
  -- ⊢ realize v (Matrix.vecCons t₁ ![t₂] 0) = Matrix.vecCons (realize v t₁) ![real …
  · simp only [Matrix.cons_val_zero]
    -- 🎉 no goals
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
    -- 🎉 no goals
#align first_order.language.term.realize_functions_apply₂ FirstOrder.Language.Term.realize_functions_apply₂

theorem realize_con {A : Set M} {a : A} {v : α → M} : (L.con a).term.realize v = a :=
  rfl
#align first_order.language.term.realize_con FirstOrder.Language.Term.realize_con

@[simp]
theorem realize_subst {t : L.Term α} {tf : α → L.Term β} {v : β → M} :
    (t.subst tf).realize v = t.realize fun a => (tf a).realize v := by
  induction' t with _ _ _ _ ih
  -- ⊢ realize v (subst (var _a✝) tf) = realize (fun a => realize v (tf a)) (var _a✝)
  · rfl
    -- 🎉 no goals
  · simp [ih]
    -- 🎉 no goals
#align first_order.language.term.realize_subst FirstOrder.Language.Term.realize_subst

@[simp]
theorem realize_restrictVar [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset ⊆ s)
    {v : α → M} : (t.restrictVar (Set.inclusion h)).realize (v ∘ (↑)) = t.realize v := by
  induction' t with _ _ _ _ ih
  -- ⊢ realize (v ∘ Subtype.val) (restrictVar (var _a✝) (Set.inclusion h)) = realiz …
  · rfl
    -- 🎉 no goals
  · simp_rw [varFinset, Finset.coe_biUnion, Set.iUnion_subset_iff] at h
    -- ⊢ realize (v ∘ Subtype.val) (restrictVar (func _f✝ _ts✝) (Set.inclusion h✝)) = …
    exact congr rfl (funext fun i => ih i (h i (Finset.mem_univ i)))
    -- 🎉 no goals
#align first_order.language.term.realize_restrict_var FirstOrder.Language.Term.realize_restrictVar

@[simp]
theorem realize_restrictVarLeft [DecidableEq α] {γ : Type*} {t : L.Term (Sum α γ)} {s : Set α}
    (h : ↑t.varFinsetLeft ⊆ s) {v : α → M} {xs : γ → M} :
    (t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ (↑)) xs) =
      t.realize (Sum.elim v xs) := by
  induction' t with a _ _ _ ih
  -- ⊢ realize (Sum.elim (v ∘ Subtype.val) xs) (restrictVarLeft (var a) (Set.inclus …
  · cases a <;> rfl
    -- ⊢ realize (Sum.elim (v ∘ Subtype.val) xs) (restrictVarLeft (var (Sum.inl val✝) …
                -- 🎉 no goals
                -- 🎉 no goals
  · simp_rw [varFinsetLeft, Finset.coe_biUnion, Set.iUnion_subset_iff] at h
    -- ⊢ realize (Sum.elim (v ∘ Subtype.val) xs) (restrictVarLeft (func _f✝ _ts✝) (Se …
    exact congr rfl (funext fun i => ih i (h i (Finset.mem_univ i)))
    -- 🎉 no goals
#align first_order.language.term.realize_restrict_var_left FirstOrder.Language.Term.realize_restrictVarLeft

@[simp]
theorem realize_constantsToVars [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L[[α]].Term β} {v : β → M} :
    t.constantsToVars.realize (Sum.elim (fun a => ↑(L.con a)) v) = t.realize v := by
  induction' t with _ n f ts ih
  -- ⊢ realize (Sum.elim (fun a => ↑(Language.con L a)) v) (constantsToVars (var _a …
  · simp
    -- 🎉 no goals
  · cases n
    -- ⊢ realize (Sum.elim (fun a => ↑(Language.con L a)) v) (constantsToVars (func f …
    · cases f
      -- ⊢ realize (Sum.elim (fun a => ↑(Language.con L a)) v) (constantsToVars (func ( …
      · simp only [realize, ih, Nat.zero_eq, constantsOn, mk₂_Functions]
        -- ⊢ (funMap val✝ fun i => realize v (ts i)) = funMap (Sum.inl val✝) fun i => rea …
        --Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sum_inl]
        -- 🎉 no goals
      · simp only [realize, constantsToVars, Sum.elim_inl, funMap_eq_coe_constants]
        -- ⊢ ↑(Language.con L val✝) = ↑(Sum.inr val✝)
        rfl
        -- 🎉 no goals
    · cases' f with _ f
      -- ⊢ realize (Sum.elim (fun a => ↑(Language.con L a)) v) (constantsToVars (func ( …
      · simp only [realize, ih, constantsOn, mk₂_Functions]
        -- ⊢ (funMap val✝ fun i => realize v (ts i)) = funMap (Sum.inl val✝) fun i => rea …
        --Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sum_inl]
        -- 🎉 no goals
      · exact isEmptyElim f
        -- 🎉 no goals
#align first_order.language.term.realize_constants_to_vars FirstOrder.Language.Term.realize_constantsToVars

@[simp]
theorem realize_varsToConstants [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L.Term (Sum α β)} {v : β → M} :
    t.varsToConstants.realize v = t.realize (Sum.elim (fun a => ↑(L.con a)) v) := by
  induction' t with ab n f ts ih
  -- ⊢ realize v (varsToConstants (var ab)) = realize (Sum.elim (fun a => ↑(Languag …
  · cases' ab with a b
    -- ⊢ realize v (varsToConstants (var (Sum.inl a))) = realize (Sum.elim (fun a =>  …
    --Porting note: both cases were `simp [Language.con]`
    · simp [Language.con, realize, constantMap, funMap_eq_coe_constants]
      -- 🎉 no goals
    · simp [realize, constantMap]
      -- 🎉 no goals
  · simp only [realize, constantsOn, mk₂_Functions, ih]
    -- ⊢ (funMap (Sum.inl f) fun i => realize (Sum.elim (fun a => ↑(Language.con L a) …
    --Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sum_inl]
    -- 🎉 no goals
#align first_order.language.term.realize_vars_to_constants FirstOrder.Language.Term.realize_varsToConstants

theorem realize_constantsVarsEquivLeft [L[[α]].Structure M]
    [(lhomWithConstants L α).IsExpansionOn M] {n} {t : L[[α]].Term (Sum β (Fin n))} {v : β → M}
    {xs : Fin n → M} :
    (constantsVarsEquivLeft t).realize (Sum.elim (Sum.elim (fun a => ↑(L.con a)) v) xs) =
      t.realize (Sum.elim v xs) := by
  simp only [constantsVarsEquivLeft, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constantsVarsEquiv_apply, relabelEquiv_symm_apply]
  refine' _root_.trans _ realize_constantsToVars
  -- ⊢ realize (Sum.elim (Sum.elim (fun a => ↑(Language.con L a)) v) xs ∘ ↑(Equiv.s …
  rcongr x
  -- ⊢ (Sum.elim (Sum.elim (fun a => ↑(Language.con L a)) v) xs ∘ ↑(Equiv.sumAssoc  …
  rcases x with (a | (b | i)) <;> simp
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align first_order.language.term.realize_constants_vars_equiv_left FirstOrder.Language.Term.realize_constantsVarsEquivLeft

end Term

namespace LHom

@[simp]
theorem realize_onTerm [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
    (v : α → M) : (φ.onTerm t).realize v = t.realize v := by
  induction' t with _ n f ts ih
  -- ⊢ Term.realize v (onTerm φ (var _a✝)) = Term.realize v (var _a✝)
  · rfl
    -- 🎉 no goals
  · simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.realize_on_term FirstOrder.Language.LHom.realize_onTerm

end LHom

@[simp]
theorem Hom.realize_term (g : M →[L] N) {t : L.Term α} {v : α → M} :
    t.realize (g ∘ v) = g (t.realize v) := by
  induction t
  -- ⊢ Term.realize (↑g ∘ v) (var _a✝) = ↑g (Term.realize v (var _a✝))
  · rfl
    -- 🎉 no goals
  · rw [Term.realize, Term.realize, g.map_fun]
    -- ⊢ (funMap _f✝ fun i => Term.realize (↑g ∘ v) (_ts✝ i)) = funMap _f✝ (↑g ∘ fun  …
    refine' congr rfl _
    -- ⊢ (fun i => Term.realize (↑g ∘ v) (_ts✝ i)) = ↑g ∘ fun i => Term.realize v (_t …
    ext x
    -- ⊢ Term.realize (↑g ∘ v) (_ts✝ x) = (↑g ∘ fun i => Term.realize v (_ts✝ i)) x
    simp [*]
    -- 🎉 no goals
#align first_order.language.hom.realize_term FirstOrder.Language.Hom.realize_term

@[simp]
theorem Embedding.realize_term {v : α → M} (t : L.Term α) (g : M ↪[L] N) :
    t.realize (g ∘ v) = g (t.realize v) :=
  g.toHom.realize_term
#align first_order.language.embedding.realize_term FirstOrder.Language.Embedding.realize_term

@[simp]
theorem Equiv.realize_term {v : α → M} (t : L.Term α) (g : M ≃[L] N) :
    t.realize (g ∘ v) = g (t.realize v) :=
  g.toHom.realize_term
#align first_order.language.equiv.realize_term FirstOrder.Language.Equiv.realize_term

variable {n : ℕ}

namespace BoundedFormula

open Term

--Porting note: universes in different order
/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
def Realize : ∀ {l} (_f : L.BoundedFormula α l) (_v : α → M) (_xs : Fin l → M), Prop
  | _, falsum, _v, _xs => False
  | _, equal t₁ t₂, v, xs => t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
  | _, rel R ts, v, xs => RelMap R fun i => (ts i).realize (Sum.elim v xs)
  | _, imp f₁ f₂, v, xs => Realize f₁ v xs → Realize f₂ v xs
  | _, all f, v, xs => ∀ x : M, Realize f v (snoc xs x)
#align first_order.language.bounded_formula.realize FirstOrder.Language.BoundedFormula.Realize

variable {l : ℕ} {φ ψ : L.BoundedFormula α l} {θ : L.BoundedFormula α l.succ}

variable {v : α → M} {xs : Fin l → M}

@[simp]
theorem realize_bot : (⊥ : L.BoundedFormula α l).Realize v xs ↔ False :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_bot FirstOrder.Language.BoundedFormula.realize_bot

@[simp]
theorem realize_not : φ.not.Realize v xs ↔ ¬φ.Realize v xs :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_not FirstOrder.Language.BoundedFormula.realize_not

@[simp]
theorem realize_bdEqual (t₁ t₂ : L.Term (Sum α (Fin l))) :
    (t₁.bdEqual t₂).Realize v xs ↔ t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs) :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_bd_equal FirstOrder.Language.BoundedFormula.realize_bdEqual

@[simp]
theorem realize_top : (⊤ : L.BoundedFormula α l).Realize v xs ↔ True := by simp [Top.top]
                                                                           -- 🎉 no goals
#align first_order.language.bounded_formula.realize_top FirstOrder.Language.BoundedFormula.realize_top

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp [Inf.inf, Realize]; tauto
  -- ⊢ (Realize φ v xs → Realize ψ v xs → False) → False ↔ Realize φ v xs ∧ Realize …
                           -- 🎉 no goals
#align first_order.language.bounded_formula.realize_inf FirstOrder.Language.BoundedFormula.realize_inf

@[simp]
theorem realize_foldr_inf (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ ∀ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction' l with φ l ih
  -- ⊢ Realize (List.foldr (fun x x_1 => x ⊓ x_1) ⊤ []) v xs ↔ ∀ (φ : BoundedFormul …
  · simp
    -- 🎉 no goals
  · simp [ih]
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_foldr_inf FirstOrder.Language.BoundedFormula.realize_foldr_inf

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs := by
  simp only [Realize]
  -- 🎉 no goals
#align first_order.language.bounded_formula.realize_imp FirstOrder.Language.BoundedFormula.realize_imp

@[simp]
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.Term _} :
    (R.boundedFormula ts).Realize v xs ↔ RelMap R fun i => (ts i).realize (Sum.elim v xs) :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_rel FirstOrder.Language.BoundedFormula.realize_rel

@[simp]
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.boundedFormula₁ t).Realize v xs ↔ RelMap R ![t.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₁, realize_rel, iff_eq_eq]
  -- ⊢ (RelMap R fun i => realize (Sum.elim v xs) (Matrix.vecCons t ![] i)) = RelMa …
  refine' congr rfl (funext fun _ => _)
  -- ⊢ realize (Sum.elim v xs) (Matrix.vecCons t ![] x✝) = Matrix.vecCons (realize  …
  simp only [Matrix.cons_val_fin_one]
  -- 🎉 no goals
#align first_order.language.bounded_formula.realize_rel₁ FirstOrder.Language.BoundedFormula.realize_rel₁

@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.boundedFormula₂ t₁ t₂).Realize v xs ↔
      RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₂, realize_rel, iff_eq_eq]
  -- ⊢ (RelMap R fun i => realize (Sum.elim v xs) (Matrix.vecCons t₁ ![t₂] i)) = Re …
  refine' congr rfl (funext (Fin.cases _ _))
  -- ⊢ realize (Sum.elim v xs) (Matrix.vecCons t₁ ![t₂] 0) = Matrix.vecCons (realiz …
  · simp only [Matrix.cons_val_zero]
    -- 🎉 no goals
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_rel₂ FirstOrder.Language.BoundedFormula.realize_rel₂

@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [realize, Sup.sup, realize_not, eq_iff_iff]
  -- ⊢ Realize (∼φ ⟹ ψ) v xs ↔ Realize φ v xs ∨ Realize ψ v xs
  tauto
  -- 🎉 no goals
#align first_order.language.bounded_formula.realize_sup FirstOrder.Language.BoundedFormula.realize_sup

@[simp]
theorem realize_foldr_sup (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction' l with φ l ih
  -- ⊢ Realize (List.foldr (fun x x_1 => x ⊔ x_1) ⊥ []) v xs ↔ ∃ φ, φ ∈ [] ∧ Realiz …
  · simp
    -- 🎉 no goals
  · simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
      exists_eq_left]
#align first_order.language.bounded_formula.realize_foldr_sup FirstOrder.Language.BoundedFormula.realize_foldr_sup

@[simp]
theorem realize_all : (all θ).Realize v xs ↔ ∀ a : M, θ.Realize v (Fin.snoc xs a) :=
  Iff.rfl
#align first_order.language.bounded_formula.realize_all FirstOrder.Language.BoundedFormula.realize_all

@[simp]
theorem realize_ex : θ.ex.Realize v xs ↔ ∃ a : M, θ.Realize v (Fin.snoc xs a) := by
  rw [BoundedFormula.ex, realize_not, realize_all, not_forall]
  -- ⊢ (∃ x, ¬Realize (∼θ) v (snoc xs x)) ↔ ∃ a, Realize θ v (snoc xs a)
  simp_rw [realize_not, Classical.not_not]
  -- 🎉 no goals
#align first_order.language.bounded_formula.realize_ex FirstOrder.Language.BoundedFormula.realize_ex

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormula.iff, realize_inf, realize_imp, and_imp, ← iff_def]
  -- 🎉 no goals
#align first_order.language.bounded_formula.realize_iff FirstOrder.Language.BoundedFormula.realize_iff

theorem realize_castLE_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} {φ : L.BoundedFormula α m}
    {v : α → M} {xs : Fin n → M} : (φ.castLE h').Realize v xs ↔ φ.Realize v (xs ∘ castIso h) := by
  subst h
  -- ⊢ Realize (castLE h' φ) v xs ↔ Realize φ v (xs ∘ ↑(castIso (_ : m = m)))
  simp only [castLE_rfl, castIso_refl, OrderIso.coe_refl, Function.comp.right_id]
  -- 🎉 no goals
#align first_order.language.bounded_formula.realize_cast_le_of_eq FirstOrder.Language.BoundedFormula.realize_castLE_of_eq

theorem realize_mapTermRel_id [L'.Structure M]
    {ft : ∀ n, L.Term (Sum α (Fin n)) → L'.Term (Sum β (Fin n))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n} {v : α → M}
    {v' : β → M} {xs : Fin n → M}
    (h1 :
      ∀ (n) (t : L.Term (Sum α (Fin n))) (xs : Fin n → M),
        (ft n t).realize (Sum.elim v' xs) = t.realize (Sum.elim v xs))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x) :
    (φ.mapTermRel ft fr fun _ => id).Realize v' xs ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih
  · rfl
    -- 🎉 no goals
  · simp [mapTermRel, Realize, h1]
    -- 🎉 no goals
  · simp [mapTermRel, Realize, h1, h2]
    -- 🎉 no goals
  · simp [mapTermRel, Realize, ih1, ih2]
    -- 🎉 no goals
  · simp only [mapTermRel, Realize, ih, id.def]
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_map_term_rel_id FirstOrder.Language.BoundedFormula.realize_mapTermRel_id

theorem realize_mapTermRel_add_castLe [L'.Structure M] {k : ℕ}
    {ft : ∀ n, L.Term (Sum α (Fin n)) → L'.Term (Sum β (Fin (k + n)))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n}
    (v : ∀ {n}, (Fin (k + n) → M) → α → M) {v' : β → M} (xs : Fin (k + n) → M)
    (h1 :
      ∀ (n) (t : L.Term (Sum α (Fin n))) (xs' : Fin (k + n) → M),
        (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x)
    (hv : ∀ (n) (xs : Fin (k + n) → M) (x : M), @v (n + 1) (snoc xs x : Fin _ → M) = v xs) :
    (φ.mapTermRel ft fr fun n => castLE (add_assoc _ _ _).symm.le).Realize v' xs ↔
      φ.Realize (v xs) (xs ∘ Fin.natAdd _) := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih
  · rfl
    -- 🎉 no goals
  · simp [mapTermRel, Realize, h1]
    -- 🎉 no goals
  · simp [mapTermRel, Realize, h1, h2]
    -- 🎉 no goals
  · simp [mapTermRel, Realize, ih1, ih2]
    -- 🎉 no goals
  · simp [mapTermRel, Realize, ih, hv]
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_map_term_rel_add_cast_le FirstOrder.Language.BoundedFormula.realize_mapTermRel_add_castLe

theorem realize_relabel {m n : ℕ} {φ : L.BoundedFormula α n} {g : α → Sum β (Fin m)} {v : β → M}
    {xs : Fin (m + n) → M} :
    (φ.relabel g).Realize v xs ↔
      φ.Realize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) :=
  by rw [relabel, realize_mapTermRel_add_castLe] <;> intros <;> simp
                                                     -- ⊢ realize (Sum.elim v xs'✝) (Term.relabel (relabelAux g n✝) t✝) = realize (Sum …
                                                     -- ⊢ RelMap (id R✝) x✝ = RelMap R✝ x✝
                                                     -- ⊢ Sum.elim v (snoc xs✝ x✝ ∘ castAdd (n✝ + 1)) ∘ g = Sum.elim v (xs✝ ∘ castAdd  …
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals
#align first_order.language.bounded_formula.realize_relabel FirstOrder.Language.BoundedFormula.realize_relabel

theorem realize_liftAt {n n' m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + n') → M}
    (hmn : m + n' ≤ n + 1) :
    (φ.liftAt n' m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') := by
  rw [liftAt]
  -- ⊢ Realize (mapTermRel (fun k t => Term.liftAt n' m t) (fun x => id) (fun x =>  …
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 k _ ih3
  · simp [mapTermRel, Realize]
    -- 🎉 no goals
  · simp [mapTermRel, Realize, realize_rel, realize_liftAt, Sum.elim_comp_map]
    -- 🎉 no goals
  · simp [mapTermRel, Realize, realize_rel, realize_liftAt, Sum.elim_comp_map]
    -- 🎉 no goals
  · simp only [mapTermRel, Realize, ih1 hmn, ih2 hmn]
    -- 🎉 no goals
  · have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
    -- ⊢ Realize (mapTermRel (fun k t => Term.liftAt n' m t) (fun x => id) (fun x =>  …
    simp only [mapTermRel, Realize, realize_castLE_of_eq h, ih3 (hmn.trans k.succ.le_succ)]
    -- ⊢ (∀ (x : M), Realize f✝ v ((snoc xs x ∘ ↑(castIso h)) ∘ fun i => if ↑i < m th …
    refine' forall_congr' fun x => iff_eq_eq.mpr (congr rfl (funext (Fin.lastCases _ fun i => _)))
    -- ⊢ ((snoc xs x ∘ ↑(castIso h)) ∘ fun i => if ↑i < m then castAdd n' i else addN …
    · simp only [Function.comp_apply, val_last, snoc_last]
      -- ⊢ snoc xs x (↑(castIso h) (if k < m then castAdd n' (last k) else addNat (last …
      by_cases h : k < m
      -- ⊢ snoc xs x (↑(castIso h✝) (if k < m then castAdd n' (last k) else addNat (las …
      · rw [if_pos h]
        -- ⊢ snoc xs x (↑(castIso h✝) (castAdd n' (last k))) = x
        refine' (congr rfl (ext _)).trans (snoc_last _ _)
        -- ⊢ ↑(↑(castIso h✝) (castAdd n' (last k))) = ↑(last (k + n'))
        simp only [coe_orderIso_apply, coe_castAdd, val_last, self_eq_add_right]
        -- ⊢ n' = 0
        refine'
          le_antisymm (le_of_add_le_add_left ((hmn.trans (Nat.succ_le_of_lt h)).trans _)) n'.zero_le
        rw [add_zero]
        -- 🎉 no goals
      · rw [if_neg h]
        -- ⊢ snoc xs x (↑(castIso h✝) (addNat (last k) n')) = x
        refine' (congr rfl (ext _)).trans (snoc_last _ _)
        -- ⊢ ↑(↑(castIso h✝) (addNat (last k) n')) = ↑(last (k + n'))
        simp
        -- 🎉 no goals
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      -- ⊢ snoc xs x (↑(castIso h) (if ↑(castSucc i) < m then castAdd n' (castSucc i) e …
      refine' (congr rfl (ext _)).trans (snoc_castSucc _ _ _)
      -- ⊢ ↑(↑(castIso h) (if ↑(castSucc i) < m then castAdd n' (castSucc i) else addNa …
      simp only [coe_castSucc, coe_orderIso_apply]
      -- ⊢ ↑(if ↑i < m then castAdd n' (castSucc i) else addNat (castSucc i) n') = ↑(if …
      split_ifs <;> simp
      -- ⊢ ↑(castAdd n' (castSucc i)) = ↑(castAdd n' i)
                    -- 🎉 no goals
                    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_lift_at FirstOrder.Language.BoundedFormula.realize_liftAt

theorem realize_liftAt_one {n m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + 1) → M}
    (hmn : m ≤ n) :
    (φ.liftAt 1 m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then castSucc i else i.succ) := by
  simp [realize_liftAt (add_le_add_right hmn 1), castSucc]
  -- 🎉 no goals
#align first_order.language.bounded_formula.realize_lift_at_one FirstOrder.Language.BoundedFormula.realize_liftAt_one

@[simp]
theorem realize_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin (n + 1) → M} : (φ.liftAt 1 n).Realize v xs ↔ φ.Realize v (xs ∘ castSucc) := by
  rw [realize_liftAt_one (refl n), iff_eq_eq]
  -- ⊢ Realize φ v (xs ∘ fun i => if ↑i < n then castSucc i else succ i) = Realize  …
  refine' congr rfl (congr rfl (funext fun i => _))
  -- ⊢ (if ↑i < n then castSucc i else succ i) = castSucc i
  rw [if_pos i.is_lt]
  -- 🎉 no goals
#align first_order.language.bounded_formula.realize_lift_at_one_self FirstOrder.Language.BoundedFormula.realize_liftAt_one_self

theorem realize_subst {φ : L.BoundedFormula α n} {tf : α → L.Term β} {v : β → M} {xs : Fin n → M} :
    (φ.subst tf).Realize v xs ↔ φ.Realize (fun a => (tf a).realize v) xs :=
  realize_mapTermRel_id
    (fun n t x => by
      rw [Term.realize_subst]
      -- ⊢ realize (fun a => realize (Sum.elim v x) (Sum.elim (Term.relabel Sum.inl ∘ t …
      rcongr a
      -- ⊢ realize (Sum.elim v x) (Sum.elim (Term.relabel Sum.inl ∘ tf) (var ∘ Sum.inr) …
      · cases a
        -- ⊢ realize (Sum.elim v x) (Sum.elim (Term.relabel Sum.inl ∘ tf) (var ∘ Sum.inr) …
        · simp only [Sum.elim_inl, Function.comp_apply, Term.realize_relabel, Sum.elim_comp_inl]
          -- 🎉 no goals
        · rfl)
          -- 🎉 no goals
    (by simp)
        -- 🎉 no goals
#align first_order.language.bounded_formula.realize_subst FirstOrder.Language.BoundedFormula.realize_subst

@[simp]
theorem realize_restrictFreeVar [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n} {s : Set α}
    (h : ↑φ.freeVarFinset ⊆ s) {v : α → M} {xs : Fin n → M} :
    (φ.restrictFreeVar (Set.inclusion h)).Realize (v ∘ (↑)) xs ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    -- 🎉 no goals
  · simp [restrictFreeVar, Realize]
    -- 🎉 no goals
  · simp [restrictFreeVar, Realize]
    -- 🎉 no goals
  · simp [restrictFreeVar, Realize, ih1, ih2]
    -- 🎉 no goals
  · simp [restrictFreeVar, Realize, ih3]
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_restrict_free_var FirstOrder.Language.BoundedFormula.realize_restrictFreeVar

theorem realize_constantsVarsEquiv [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {φ : L[[α]].BoundedFormula β n} {v : β → M} {xs : Fin n → M} :
    (constantsVarsEquiv φ).Realize (Sum.elim (fun a => ↑(L.con a)) v) xs ↔ φ.Realize v xs := by
  refine' realize_mapTermRel_id (fun n t xs => realize_constantsVarsEquivLeft) fun n R xs => _
  -- ⊢ RelMap (↑((fun x => Equiv.sumEmpty (Relations L x) (Relations (constantsOn α …
  rw [← (lhomWithConstants L α).map_onRelation
      (Equiv.sumEmpty (L.Relations n) ((constantsOn α).Relations n) R) xs]
  rcongr
  -- ⊢ RelMap (LHom.onRelation (lhomWithConstants L α) (↑(Equiv.sumEmpty (Relations …
  cases' R with R R
  -- ⊢ RelMap (LHom.onRelation (lhomWithConstants L α) (↑(Equiv.sumEmpty (Relations …
  · simp
    -- 🎉 no goals
  · exact isEmptyElim R
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_constants_vars_equiv FirstOrder.Language.BoundedFormula.realize_constantsVarsEquiv

@[simp]
theorem realize_relabelEquiv {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β → M}
    {xs : Fin k → M} : (relabelEquiv g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  -- ⊢ Realize (mapTermRel (fun n => ↑(Term.relabelEquiv (Equiv.sumCongr g (_root_. …
  refine' realize_mapTermRel_id (fun n t xs => _) fun _ _ _ => rfl
  -- ⊢ realize (Sum.elim v xs) (↑(Term.relabelEquiv (Equiv.sumCongr g (_root_.Equiv …
  simp only [relabelEquiv_apply, Term.realize_relabel]
  -- ⊢ realize (Sum.elim v xs ∘ ↑(Equiv.sumCongr g (_root_.Equiv.refl (Fin n)))) t  …
  refine' congr (congr rfl _) rfl
  -- ⊢ Sum.elim v xs ∘ ↑(Equiv.sumCongr g (_root_.Equiv.refl (Fin n))) = Sum.elim ( …
  ext (i | i) <;> rfl
  -- ⊢ (Sum.elim v xs ∘ ↑(Equiv.sumCongr g (_root_.Equiv.refl (Fin n)))) (Sum.inl i …
                  -- 🎉 no goals
                  -- 🎉 no goals
#align first_order.language.bounded_formula.realize_relabel_equiv FirstOrder.Language.BoundedFormula.realize_relabelEquiv

variable [Nonempty M]

theorem realize_all_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin n → M} : (φ.liftAt 1 n).all.Realize v xs ↔ φ.Realize v xs := by
  inhabit M
  -- ⊢ Realize (∀'liftAt 1 n φ) v xs ↔ Realize φ v xs
  simp only [realize_all, realize_liftAt_one_self]
  -- ⊢ (∀ (a : M), Realize φ v (snoc xs a ∘ castSucc)) ↔ Realize φ v xs
  refine' ⟨fun h => _, fun h a => _⟩
  -- ⊢ Realize φ v xs
  · refine' (congr rfl (funext fun i => _)).mp (h default)
    -- ⊢ (snoc xs default ∘ castSucc) i = xs i
    simp
    -- 🎉 no goals
  · refine' (congr rfl (funext fun i => _)).mp h
    -- ⊢ xs i = (snoc xs a ∘ castSucc) i
    simp
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_all_lift_at_one_self FirstOrder.Language.BoundedFormula.realize_all_liftAt_one_self

theorem realize_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} :
    (φ.toPrenexImpRight ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  induction' hψ with _ _ hψ _ _ _hψ ih _ _ _hψ ih
  · rw [hψ.toPrenexImpRight]
    -- 🎉 no goals
  · refine' _root_.trans (forall_congr' fun _ => ih hφ.liftAt) _
    -- ⊢ (∀ (a : M), Realize (liftAt 1 n✝ φ ⟹ φ✝) v (snoc xs a)) ↔ Realize (φ ⟹ ∀'φ✝) …
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    -- ⊢ (∀ (a : M), Realize φ v xs → Realize φ✝ v (snoc xs a)) ↔ Realize φ v xs → ∀  …
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
    -- 🎉 no goals
  · unfold toPrenexImpRight
    -- ⊢ Realize (∃'toPrenexImpRight (liftAt 1 n✝ φ) φ✝) v xs ↔ Realize (φ ⟹ ∃'φ✝) v xs
    rw [realize_ex]
    -- ⊢ (∃ a, Realize (toPrenexImpRight (liftAt 1 n✝ φ) φ✝) v (snoc xs a)) ↔ Realize …
    refine' _root_.trans (exists_congr fun _ => ih hφ.liftAt) _
    -- ⊢ (∃ a, Realize (liftAt 1 n✝ φ ⟹ φ✝) v (snoc xs a)) ↔ Realize (φ ⟹ ∃'φ✝) v xs
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_ex]
    -- ⊢ (∃ a, Realize φ v xs → Realize φ✝ v (snoc xs a)) ↔ Realize φ v xs → ∃ a, Rea …
    refine' ⟨_, fun h' => _⟩
    -- ⊢ (∃ a, Realize φ v xs → Realize φ✝ v (snoc xs a)) → Realize φ v xs → ∃ a, Rea …
    · rintro ⟨a, ha⟩ h
      -- ⊢ ∃ a, Realize φ✝ v (snoc xs a)
      exact ⟨a, ha h⟩
      -- 🎉 no goals
    · by_cases φ.Realize v xs
      -- ⊢ ∃ a, Realize φ v xs → Realize φ✝ v (snoc xs a)
      -- ⊢ ∃ a, Realize φ v xs → Realize φ✝ v (snoc xs a)
      · obtain ⟨a, ha⟩ := h' h
        -- ⊢ ∃ a, Realize φ v xs → Realize φ✝ v (snoc xs a)
        exact ⟨a, fun _ => ha⟩
        -- 🎉 no goals
      · inhabit M
        -- ⊢ ∃ a, Realize φ v xs → Realize φ✝ v (snoc xs a)
        exact ⟨default, fun h'' => (h h'').elim⟩
        -- 🎉 no goals
#align first_order.language.bounded_formula.realize_to_prenex_imp_right FirstOrder.Language.BoundedFormula.realize_toPrenexImpRight

theorem realize_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} : (φ.toPrenexImp ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  revert ψ
  -- ⊢ ∀ {ψ : BoundedFormula L α n}, IsPrenex ψ → (Realize (toPrenexImp φ ψ) v xs ↔ …
  induction' hφ with _ _ hφ _ _ _hφ ih _ _ _hφ ih <;> intro ψ hψ
                                                      -- ⊢ Realize (toPrenexImp φ✝ ψ) v xs ↔ Realize (φ✝ ⟹ ψ) v xs
                                                      -- ⊢ Realize (toPrenexImp (∀'φ✝) ψ) v xs ↔ Realize (∀'φ✝ ⟹ ψ) v xs
                                                      -- ⊢ Realize (toPrenexImp (∃'φ✝) ψ) v xs ↔ Realize (∃'φ✝ ⟹ ψ) v xs
  · rw [hφ.toPrenexImp]
    -- ⊢ Realize (toPrenexImpRight φ✝ ψ) v xs ↔ Realize (φ✝ ⟹ ψ) v xs
    exact realize_toPrenexImpRight hφ hψ
    -- 🎉 no goals
  · unfold toPrenexImp
    -- ⊢ Realize (∃'toPrenexImp φ✝ (liftAt 1 n✝ ψ)) v xs ↔ Realize (∀'φ✝ ⟹ ψ) v xs
    rw [realize_ex]
    -- ⊢ (∃ a, Realize (toPrenexImp φ✝ (liftAt 1 n✝ ψ)) v (snoc xs a)) ↔ Realize (∀'φ …
    refine' _root_.trans (exists_congr fun _ => ih hψ.liftAt) _
    -- ⊢ (∃ a, Realize (φ✝ ⟹ liftAt 1 n✝ ψ) v (snoc xs a)) ↔ Realize (∀'φ✝ ⟹ ψ) v xs
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    -- ⊢ (∃ a, Realize φ✝ v (snoc xs a) → Realize ψ v xs) ↔ (∀ (a : M), Realize φ✝ v  …
    refine' ⟨_, fun h' => _⟩
    -- ⊢ (∃ a, Realize φ✝ v (snoc xs a) → Realize ψ v xs) → (∀ (a : M), Realize φ✝ v  …
    · rintro ⟨a, ha⟩ h
      -- ⊢ Realize ψ v xs
      exact ha (h a)
      -- 🎉 no goals
    · by_cases ψ.Realize v xs
      -- ⊢ ∃ a, Realize φ✝ v (snoc xs a) → Realize ψ v xs
      -- ⊢ ∃ a, Realize φ✝ v (snoc xs a) → Realize ψ v xs
      · inhabit M
        -- ⊢ ∃ a, Realize φ✝ v (snoc xs a) → Realize ψ v xs
        exact ⟨default, fun _h'' => h⟩
        -- 🎉 no goals
      · obtain ⟨a, ha⟩ := not_forall.1 (h ∘ h')
        -- ⊢ ∃ a, Realize φ✝ v (snoc xs a) → Realize ψ v xs
        exact ⟨a, fun h => (ha h).elim⟩
        -- 🎉 no goals
  · refine' _root_.trans (forall_congr' fun _ => ih hψ.liftAt) _
    -- ⊢ (∀ (a : M), Realize (φ✝ ⟹ liftAt 1 n✝ ψ) v (snoc xs a)) ↔ Realize (∃'φ✝ ⟹ ψ) …
    simp
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_to_prenex_imp FirstOrder.Language.BoundedFormula.realize_toPrenexImp

@[simp]
theorem realize_toPrenex (φ : L.BoundedFormula α n) {v : α → M} :
    ∀ {xs : Fin n → M}, φ.toPrenex.Realize v xs ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ f1 f2 h1 h2 _ _ h
  · exact Iff.rfl
    -- 🎉 no goals
  · exact Iff.rfl
    -- 🎉 no goals
  · exact Iff.rfl
    -- 🎉 no goals
  · intros
    -- ⊢ Realize (toPrenex (f1 ⟹ f2)) v xs✝ ↔ Realize (f1 ⟹ f2) v xs✝
    rw [toPrenex, realize_toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex, realize_imp,
      realize_imp, h1, h2]
  · intros
    -- ⊢ Realize (toPrenex (∀'f✝)) v xs✝ ↔ Realize (∀'f✝) v xs✝
    rw [realize_all, toPrenex, realize_all]
    -- ⊢ (∀ (a : M), Realize (toPrenex f✝) v (snoc xs✝ a)) ↔ ∀ (a : M), Realize f✝ v  …
    exact forall_congr' fun a => h
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_to_prenex FirstOrder.Language.BoundedFormula.realize_toPrenex

end BoundedFormula


--Porting note: no `protected` attribute in Lean4
-- attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel

-- attribute [protected] bounded_formula.imp bounded_formula.all

namespace LHom

open BoundedFormula

@[simp]
theorem realize_onBoundedFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] {n : ℕ}
    (ψ : L.BoundedFormula α n) {v : α → M} {xs : Fin n → M} :
    (φ.onBoundedFormula ψ).Realize v xs ↔ ψ.Realize v xs := by
  induction' ψ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    -- 🎉 no goals
  · simp only [onBoundedFormula, realize_bdEqual, realize_onTerm]
    -- ⊢ Term.realize (Sum.elim v xs) t₁✝ = Term.realize (Sum.elim v xs) t₂✝ ↔ Realiz …
    rfl
    -- 🎉 no goals
  · simp only [onBoundedFormula, realize_rel, LHom.map_onRelation,
      Function.comp_apply, realize_onTerm]
    rfl
    -- 🎉 no goals
  · simp only [onBoundedFormula, ih1, ih2, realize_imp]
    -- 🎉 no goals
  · simp only [onBoundedFormula, ih3, realize_all]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.realize_on_bounded_formula FirstOrder.Language.LHom.realize_onBoundedFormula

end LHom

--Porting note: no `protected` attribute in Lean4
-- attribute [protected] bounded_formula.falsum bounded_formula.equal bounded_formula.rel

-- attribute [protected] bounded_formula.imp bounded_formula.all

namespace Formula

/-- A formula can be evaluated as true or false by giving values to each free variable. -/
nonrec def Realize (φ : L.Formula α) (v : α → M) : Prop :=
  φ.Realize v default
#align first_order.language.formula.realize FirstOrder.Language.Formula.Realize

variable {φ ψ : L.Formula α} {v : α → M}

@[simp]
theorem realize_not : φ.not.Realize v ↔ ¬φ.Realize v :=
  Iff.rfl
#align first_order.language.formula.realize_not FirstOrder.Language.Formula.realize_not

@[simp]
theorem realize_bot : (⊥ : L.Formula α).Realize v ↔ False :=
  Iff.rfl
#align first_order.language.formula.realize_bot FirstOrder.Language.Formula.realize_bot

@[simp]
theorem realize_top : (⊤ : L.Formula α).Realize v ↔ True :=
  BoundedFormula.realize_top
#align first_order.language.formula.realize_top FirstOrder.Language.Formula.realize_top

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v :=
  BoundedFormula.realize_inf
#align first_order.language.formula.realize_inf FirstOrder.Language.Formula.realize_inf

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v ↔ φ.Realize v → ψ.Realize v :=
  BoundedFormula.realize_imp
#align first_order.language.formula.realize_imp FirstOrder.Language.Formula.realize_imp

@[simp]
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.Term α} :
    (R.formula ts).Realize v ↔ RelMap R fun i => (ts i).realize v :=
  BoundedFormula.realize_rel.trans (by simp)
                                       -- 🎉 no goals
#align first_order.language.formula.realize_rel FirstOrder.Language.Formula.realize_rel

@[simp]
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.formula₁ t).Realize v ↔ RelMap R ![t.realize v] := by
  rw [Relations.formula₁, realize_rel, iff_eq_eq]
  -- ⊢ (RelMap R fun i => Term.realize v (Matrix.vecCons t ![] i)) = RelMap R ![Ter …
  refine' congr rfl (funext fun _ => _)
  -- ⊢ Term.realize v (Matrix.vecCons t ![] x✝) = Matrix.vecCons (Term.realize v t) …
  simp only [Matrix.cons_val_fin_one]
  -- 🎉 no goals
#align first_order.language.formula.realize_rel₁ FirstOrder.Language.Formula.realize_rel₁

@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.formula₂ t₁ t₂).Realize v ↔ RelMap R ![t₁.realize v, t₂.realize v] := by
  rw [Relations.formula₂, realize_rel, iff_eq_eq]
  -- ⊢ (RelMap R fun i => Term.realize v (Matrix.vecCons t₁ ![t₂] i)) = RelMap R ![ …
  refine' congr rfl (funext (Fin.cases _ _))
  -- ⊢ Term.realize v (Matrix.vecCons t₁ ![t₂] 0) = Matrix.vecCons (Term.realize v  …
  · simp only [Matrix.cons_val_zero]
    -- 🎉 no goals
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
    -- 🎉 no goals
#align first_order.language.formula.realize_rel₂ FirstOrder.Language.Formula.realize_rel₂

@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v :=
  BoundedFormula.realize_sup
#align first_order.language.formula.realize_sup FirstOrder.Language.Formula.realize_sup

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v ↔ (φ.Realize v ↔ ψ.Realize v) :=
  BoundedFormula.realize_iff
#align first_order.language.formula.realize_iff FirstOrder.Language.Formula.realize_iff

@[simp]
theorem realize_relabel {φ : L.Formula α} {g : α → β} {v : β → M} :
    (φ.relabel g).Realize v ↔ φ.Realize (v ∘ g) := by
  rw [Realize, Realize, relabel, BoundedFormula.realize_relabel, iff_eq_eq, Fin.castAdd_zero]
  -- ⊢ BoundedFormula.Realize φ (Sum.elim v (default ∘ Fin.cast (_ : 0 = 0)) ∘ Sum. …
  exact congr rfl (funext finZeroElim)
  -- 🎉 no goals
#align first_order.language.formula.realize_relabel FirstOrder.Language.Formula.realize_relabel

theorem realize_relabel_sum_inr (φ : L.Formula (Fin n)) {v : Empty → M} {x : Fin n → M} :
    (BoundedFormula.relabel Sum.inr φ).Realize v x ↔ φ.Realize x := by
  rw [BoundedFormula.realize_relabel, Formula.Realize, Sum.elim_comp_inr, Fin.castAdd_zero,
    cast_refl, Function.comp.right_id,
    Subsingleton.elim (x ∘ (natAdd n : Fin 0 → Fin n)) default]
#align first_order.language.formula.realize_relabel_sum_inr FirstOrder.Language.Formula.realize_relabel_sum_inr

@[simp]
theorem realize_equal {t₁ t₂ : L.Term α} {x : α → M} :
    (t₁.equal t₂).Realize x ↔ t₁.realize x = t₂.realize x := by simp [Term.equal, Realize]
                                                                -- 🎉 no goals
#align first_order.language.formula.realize_equal FirstOrder.Language.Formula.realize_equal

@[simp]
theorem realize_graph {f : L.Functions n} {x : Fin n → M} {y : M} :
    (Formula.graph f).Realize (Fin.cons y x : _ → M) ↔ funMap f x = y := by
  simp only [Formula.graph, Term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  -- ⊢ (y = funMap f fun i => x i) ↔ funMap f x = y
  rw [eq_comm]
  -- 🎉 no goals
#align first_order.language.formula.realize_graph FirstOrder.Language.Formula.realize_graph

end Formula

@[simp]
theorem LHom.realize_onFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (ψ : L.Formula α)
    {v : α → M} : (φ.onFormula ψ).Realize v ↔ ψ.Realize v :=
  φ.realize_onBoundedFormula ψ
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.realize_on_formula FirstOrder.Language.LHom.realize_onFormula

@[simp]
theorem LHom.setOf_realize_onFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Formula α) : (setOf (φ.onFormula ψ).Realize : Set (α → M)) = setOf ψ.Realize := by
  ext
  -- ⊢ x✝ ∈ setOf (Formula.Realize (onFormula φ ψ)) ↔ x✝ ∈ setOf (Formula.Realize ψ)
  simp
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.set_of_realize_on_formula FirstOrder.Language.LHom.setOf_realize_onFormula

variable (M)

/-- A sentence can be evaluated as true or false in a structure. -/
nonrec def Sentence.Realize (φ : L.Sentence) : Prop :=
  φ.Realize (default : _ → M)
#align first_order.language.sentence.realize FirstOrder.Language.Sentence.Realize

-- input using \|= or \vDash, but not using \models
@[inherit_doc Sentence.Realize]
infixl:51 " ⊨ " => Sentence.Realize

@[simp]
theorem Sentence.realize_not {φ : L.Sentence} : M ⊨ φ.not ↔ ¬M ⊨ φ :=
  Iff.rfl
#align first_order.language.sentence.realize_not FirstOrder.Language.Sentence.realize_not

namespace Formula

@[simp]
theorem realize_equivSentence_symm_con [L[[α]].Structure M]
    [(L.lhomWithConstants α).IsExpansionOn M] (φ : L[[α]].Sentence) :
    ((equivSentence.symm φ).Realize fun a => (L.con a : M)) ↔ φ.Realize M := by
  simp only [equivSentence, Equiv.symm_symm, Equiv.coe_trans, Realize,
    BoundedFormula.realize_relabelEquiv, Function.comp]
  refine' _root_.trans _ BoundedFormula.realize_constantsVarsEquiv
  -- ⊢ BoundedFormula.Realize (↑BoundedFormula.constantsVarsEquiv φ) (fun x => ↑(La …
  rw [iff_iff_eq]
  -- ⊢ BoundedFormula.Realize (↑BoundedFormula.constantsVarsEquiv φ) (fun x => ↑(La …
  congr with (_ | a)
  -- ⊢ ↑(Language.con L (↑(Equiv.sumEmpty α Empty) (Sum.inl val✝))) = Sum.elim (fun …
  · simp
    -- 🎉 no goals
  · cases a
    -- 🎉 no goals
#align first_order.language.formula.realize_equiv_sentence_symm_con FirstOrder.Language.Formula.realize_equivSentence_symm_con

@[simp]
theorem realize_equivSentence [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]
    (φ : L.Formula α) : (equivSentence φ).Realize M ↔ φ.Realize fun a => (L.con a : M) := by
  rw [← realize_equivSentence_symm_con M (equivSentence φ), _root_.Equiv.symm_apply_apply]
  -- 🎉 no goals
#align first_order.language.formula.realize_equiv_sentence FirstOrder.Language.Formula.realize_equivSentence

theorem realize_equivSentence_symm (φ : L[[α]].Sentence) (v : α → M) :
    (equivSentence.symm φ).Realize v ↔
      @Sentence.Realize _ M (@Language.withConstantsStructure L M _ α (constantsOn.structure v))
        φ :=
  letI := constantsOn.structure v
  realize_equivSentence_symm_con M φ
#align first_order.language.formula.realize_equiv_sentence_symm FirstOrder.Language.Formula.realize_equivSentence_symm

end Formula

@[simp]
theorem LHom.realize_onSentence [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Sentence) : M ⊨ φ.onSentence ψ ↔ M ⊨ ψ :=
  φ.realize_onFormula ψ
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.realize_on_sentence FirstOrder.Language.LHom.realize_onSentence

variable (L)

/-- The complete theory of a structure `M` is the set of all sentences `M` satisfies. -/
def completeTheory : L.Theory :=
  { φ | M ⊨ φ }
#align first_order.language.complete_theory FirstOrder.Language.completeTheory

variable (N)

/-- Two structures are elementarily equivalent when they satisfy the same sentences. -/
def ElementarilyEquivalent : Prop :=
  L.completeTheory M = L.completeTheory N
#align first_order.language.elementarily_equivalent FirstOrder.Language.ElementarilyEquivalent

@[inherit_doc FirstOrder.Language.ElementarilyEquivalent]
scoped[FirstOrder]
  notation:25 A " ≅[" L "] " B:50 => FirstOrder.Language.ElementarilyEquivalent L A B

variable {L} {M} {N}

@[simp]
theorem mem_completeTheory {φ : Sentence L} : φ ∈ L.completeTheory M ↔ M ⊨ φ :=
  Iff.rfl
#align first_order.language.mem_complete_theory FirstOrder.Language.mem_completeTheory

theorem elementarilyEquivalent_iff : M ≅[L] N ↔ ∀ φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ := by
  simp only [ElementarilyEquivalent, Set.ext_iff, completeTheory, Set.mem_setOf_eq]
  -- 🎉 no goals
#align first_order.language.elementarily_equivalent_iff FirstOrder.Language.elementarilyEquivalent_iff

variable (M)

/-- A model of a theory is a structure in which every sentence is realized as true. -/
class Theory.Model (T : L.Theory) : Prop where
  realize_of_mem : ∀ φ ∈ T, M ⊨ φ
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.model FirstOrder.Language.Theory.Model

-- input using \|= or \vDash, but not using \models
@[inherit_doc Theory.Model]
infixl:51 " ⊨ " => Theory.Model

variable {M} (T : L.Theory)

@[simp default-10]
theorem Theory.model_iff : M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ :=
  ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.model_iff FirstOrder.Language.Theory.model_iff

theorem Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.Sentence} (h : φ ∈ T) : M ⊨ φ :=
  Theory.Model.realize_of_mem φ h
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.realize_sentence_of_mem FirstOrder.Language.Theory.realize_sentence_of_mem

@[simp]
theorem LHom.onTheory_model [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (T : L.Theory) :
    M ⊨ φ.onTheory T ↔ M ⊨ T := by simp [Theory.model_iff, LHom.onTheory]
                                   -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.on_Theory_model FirstOrder.Language.LHom.onTheory_model

variable {T}

instance model_empty : M ⊨ (∅ : L.Theory) :=
  ⟨fun φ hφ => (Set.not_mem_empty φ hφ).elim⟩
#align first_order.language.model_empty FirstOrder.Language.model_empty

namespace Theory

theorem Model.mono {T' : L.Theory} (_h : M ⊨ T') (hs : T ⊆ T') : M ⊨ T :=
  ⟨fun _φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.model.mono FirstOrder.Language.Theory.Model.mono

theorem Model.union {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T') : M ⊨ T ∪ T' := by
  simp only [model_iff, Set.mem_union] at *
  -- ⊢ ∀ (φ : Sentence L), φ ∈ T ∨ φ ∈ T' → M ⊨ φ
  exact fun φ hφ => hφ.elim (h _) (h' _)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.model.union FirstOrder.Language.Theory.Model.union

@[simp]
theorem model_union_iff {T' : L.Theory} : M ⊨ T ∪ T' ↔ M ⊨ T ∧ M ⊨ T' :=
  ⟨fun h => ⟨h.mono (T.subset_union_left T'), h.mono (T.subset_union_right T')⟩, fun h =>
    h.1.union h.2⟩
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.model_union_iff FirstOrder.Language.Theory.model_union_iff

theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by simp
                                                                                  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.model_singleton_iff FirstOrder.Language.Theory.model_singleton_iff

theorem model_iff_subset_completeTheory : M ⊨ T ↔ T ⊆ L.completeTheory M :=
  T.model_iff
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.model_iff_subset_complete_theory FirstOrder.Language.Theory.model_iff_subset_completeTheory

theorem completeTheory.subset [MT : M ⊨ T] : T ⊆ L.completeTheory M :=
  model_iff_subset_completeTheory.1 MT
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.complete_theory.subset FirstOrder.Language.Theory.completeTheory.subset

end Theory

instance model_completeTheory : M ⊨ L.completeTheory M :=
  Theory.model_iff_subset_completeTheory.2 (subset_refl _)
#align first_order.language.model_complete_theory FirstOrder.Language.model_completeTheory

variable (M N)

theorem realize_iff_of_model_completeTheory [N ⊨ L.completeTheory M] (φ : L.Sentence) :
    N ⊨ φ ↔ M ⊨ φ := by
  refine' ⟨fun h => _, (L.completeTheory M).realize_sentence_of_mem⟩
  -- ⊢ M ⊨ φ
  contrapose! h
  -- ⊢ ¬N ⊨ φ
  rw [← Sentence.realize_not] at *
  -- ⊢ N ⊨ Formula.not φ
  exact (L.completeTheory M).realize_sentence_of_mem (mem_completeTheory.2 h)
  -- 🎉 no goals
#align first_order.language.realize_iff_of_model_complete_theory FirstOrder.Language.realize_iff_of_model_completeTheory

variable {M N}

namespace BoundedFormula

@[simp]
theorem realize_alls {φ : L.BoundedFormula α n} {v : α → M} :
    φ.alls.Realize v ↔ ∀ xs : Fin n → M, φ.Realize v xs := by
  induction' n with n ih
  -- ⊢ Formula.Realize (alls φ) v ↔ ∀ (xs : Fin Nat.zero → M), Realize φ v xs
  · exact Unique.forall_iff.symm
    -- 🎉 no goals
  · simp only [alls, ih, Realize]
    -- ⊢ (∀ (xs : Fin n → M) (x : M), Realize φ v (snoc xs x)) ↔ ∀ (xs : Fin (Nat.suc …
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩
    -- 🎉 no goals
#align first_order.language.bounded_formula.realize_alls FirstOrder.Language.BoundedFormula.realize_alls

@[simp]
theorem realize_exs {φ : L.BoundedFormula α n} {v : α → M} :
    φ.exs.Realize v ↔ ∃ xs : Fin n → M, φ.Realize v xs := by
  induction' n with n ih
  -- ⊢ Formula.Realize (exs φ) v ↔ ∃ xs, Realize φ v xs
  · exact Unique.exists_iff.symm
    -- 🎉 no goals
  · simp only [BoundedFormula.exs, ih, realize_ex]
    -- ⊢ (∃ xs a, Realize φ v (snoc xs a)) ↔ ∃ xs, Realize φ v xs
    constructor
    -- ⊢ (∃ xs a, Realize φ v (snoc xs a)) → ∃ xs, Realize φ v xs
    · rintro ⟨xs, x, h⟩
      -- ⊢ ∃ xs, Realize φ v xs
      exact ⟨_, h⟩
      -- 🎉 no goals
    · rintro ⟨xs, h⟩
      -- ⊢ ∃ xs a, Realize φ v (snoc xs a)
      rw [← Fin.snoc_init_self xs] at h
      -- ⊢ ∃ xs a, Realize φ v (snoc xs a)
      exact ⟨_, _, h⟩
      -- 🎉 no goals
#align first_order.language.bounded_formula.realize_exs FirstOrder.Language.BoundedFormula.realize_exs

@[simp]
theorem realize_toFormula (φ : L.BoundedFormula α n) (v : Sum α (Fin n) → M) :
    φ.toFormula.Realize v ↔ φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3 a8 a9 a0
  · rfl
    -- 🎉 no goals
  · simp [BoundedFormula.Realize]
    -- 🎉 no goals
  · simp [BoundedFormula.Realize]
    -- 🎉 no goals
  · rw [toFormula, Formula.Realize, realize_imp, ← Formula.Realize, ih1, ← Formula.Realize, ih2,
      realize_imp]
  · rw [toFormula, Formula.Realize, realize_all, realize_all]
    -- ⊢ (∀ (a : M), Realize (relabel (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr  …
    refine' forall_congr' fun a => _
    -- ⊢ Realize (relabel (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ ↑finSum …
    have h := ih3 (Sum.elim (v ∘ Sum.inl) (snoc (v ∘ Sum.inr) a))
    -- ⊢ Realize (relabel (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ ↑finSum …
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    -- ⊢ Realize (relabel (Sum.elim (Sum.inl ∘ Sum.inl) (Sum.map Sum.inr id ∘ ↑finSum …
    rw [← h, realize_relabel, Formula.Realize, iff_iff_eq]
    -- ⊢ Realize (toFormula f✝) (Sum.elim v (snoc default a ∘ castAdd 0) ∘ Sum.elim ( …
    simp only [Function.comp]
    -- ⊢ (Realize (toFormula f✝) (fun x => Sum.elim v (fun x => snoc default a (castA …
    congr with x
    -- ⊢ Sum.elim v (fun x => snoc default a (castAdd 0 x)) (Sum.elim (fun x => Sum.i …
    · cases' x with _ x
      -- ⊢ Sum.elim v (fun x => snoc default a (castAdd 0 x)) (Sum.elim (fun x => Sum.i …
      · simp
        -- 🎉 no goals
      · refine' Fin.lastCases _ _ x
        -- ⊢ Sum.elim v (fun x => snoc default a (castAdd 0 x)) (Sum.elim (fun x => Sum.i …
        · rw [Sum.elim_inr, Sum.elim_inr,
            finSumFinEquiv_symm_last, Sum.map_inr, Sum.elim_inr]
          simp [Fin.snoc]
          -- 🎉 no goals
        · simp only [castSucc, Function.comp_apply, Sum.elim_inr,
            finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, Sum.elim_inl]
          rw [← castSucc]
          -- ⊢ ∀ (i : Fin n✝), v (Sum.inr i) = snoc (fun x => v (Sum.inr x)) a (castSucc i)
          simp
          -- 🎉 no goals
    · exact Fin.elim0 x
      -- 🎉 no goals
#align first_order.language.bounded_formula.realize_to_formula FirstOrder.Language.BoundedFormula.realize_toFormula

end BoundedFormula

namespace Equiv

@[simp]
theorem realize_boundedFormula (g : M ≃[L] N) (φ : L.BoundedFormula α n) {v : α → M}
    {xs : Fin n → M} : φ.Realize (g ∘ v) (g ∘ xs) ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
    -- 🎉 no goals
  · simp only [BoundedFormula.Realize, ← Sum.comp_elim, Equiv.realize_term, g.injective.eq_iff]
    -- 🎉 no goals
  · simp only [BoundedFormula.Realize, ← Sum.comp_elim, Equiv.realize_term]
    -- ⊢ (RelMap R✝ fun i => ↑g (Term.realize (Sum.elim v xs) (ts✝ i))) ↔ RelMap R✝ f …
    exact g.map_rel _ _
    -- 🎉 no goals
  · rw [BoundedFormula.Realize, ih1, ih2, BoundedFormula.Realize]
    -- 🎉 no goals
  · rw [BoundedFormula.Realize, BoundedFormula.Realize]
    -- ⊢ (∀ (x : N), BoundedFormula.Realize f✝ (↑g ∘ v) (snoc (↑g ∘ xs) x)) ↔ ∀ (x :  …
    constructor
    -- ⊢ (∀ (x : N), BoundedFormula.Realize f✝ (↑g ∘ v) (snoc (↑g ∘ xs) x)) → ∀ (x :  …
    · intro h a
      -- ⊢ BoundedFormula.Realize f✝ v (snoc xs a)
      have h' := h (g a)
      -- ⊢ BoundedFormula.Realize f✝ v (snoc xs a)
      rw [← Fin.comp_snoc, ih3] at h'
      -- ⊢ BoundedFormula.Realize f✝ v (snoc xs a)
      exact h'
      -- 🎉 no goals
    · intro h a
      -- ⊢ BoundedFormula.Realize f✝ (↑g ∘ v) (snoc (↑g ∘ xs) a)
      have h' := h (g.symm a)
      -- ⊢ BoundedFormula.Realize f✝ (↑g ∘ v) (snoc (↑g ∘ xs) a)
      rw [← ih3, Fin.comp_snoc, g.apply_symm_apply] at h'
      -- ⊢ BoundedFormula.Realize f✝ (↑g ∘ v) (snoc (↑g ∘ xs) a)
      exact h'
      -- 🎉 no goals
#align first_order.language.equiv.realize_bounded_formula FirstOrder.Language.Equiv.realize_boundedFormula

@[simp]
theorem realize_formula (g : M ≃[L] N) (φ : L.Formula α) {v : α → M} :
    φ.Realize (g ∘ v) ↔ φ.Realize v := by
  rw [Formula.Realize, Formula.Realize, ← g.realize_boundedFormula φ, iff_eq_eq,
    Unique.eq_default (g ∘ default)]
#align first_order.language.equiv.realize_formula FirstOrder.Language.Equiv.realize_formula

theorem realize_sentence (g : M ≃[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize, Sentence.Realize, ← g.realize_formula, Unique.eq_default (g ∘ default)]
  -- 🎉 no goals
#align first_order.language.equiv.realize_sentence FirstOrder.Language.Equiv.realize_sentence

theorem theory_model (g : M ≃[L] N) [M ⊨ T] : N ⊨ T :=
  ⟨fun φ hφ => (g.realize_sentence φ).1 (Theory.realize_sentence_of_mem T hφ)⟩
set_option linter.uppercaseLean3 false in
#align first_order.language.equiv.Theory_model FirstOrder.Language.Equiv.theory_model

theorem elementarilyEquivalent (g : M ≃[L] N) : M ≅[L] N :=
  elementarilyEquivalent_iff.2 g.realize_sentence
#align first_order.language.equiv.elementarily_equivalent FirstOrder.Language.Equiv.elementarilyEquivalent

end Equiv

namespace Relations

open BoundedFormula

variable {r : L.Relations 2}

@[simp]
theorem realize_reflexive : M ⊨ r.reflexive ↔ Reflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => realize_rel₂
#align first_order.language.relations.realize_reflexive FirstOrder.Language.Relations.realize_reflexive

@[simp]
theorem realize_irreflexive : M ⊨ r.irreflexive ↔ Irreflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => not_congr realize_rel₂
#align first_order.language.relations.realize_irreflexive FirstOrder.Language.Relations.realize_irreflexive

@[simp]
theorem realize_symmetric : M ⊨ r.symmetric ↔ Symmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr realize_rel₂ realize_rel₂
#align first_order.language.relations.realize_symmetric FirstOrder.Language.Relations.realize_symmetric

@[simp]
theorem realize_antisymmetric :
    M ⊨ r.antisymmetric ↔ AntiSymmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ Iff.rfl)
#align first_order.language.relations.realize_antisymmetric FirstOrder.Language.Relations.realize_antisymmetric

@[simp]
theorem realize_transitive : M ⊨ r.transitive ↔ Transitive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ =>
      forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ realize_rel₂)
#align first_order.language.relations.realize_transitive FirstOrder.Language.Relations.realize_transitive

@[simp]
theorem realize_total : M ⊨ r.total ↔ Total fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => realize_sup.trans (or_congr realize_rel₂ realize_rel₂)
#align first_order.language.relations.realize_total FirstOrder.Language.Relations.realize_total

end Relations

section Cardinality

variable (L)
@[simp]
theorem Sentence.realize_cardGe (n) : M ⊨ Sentence.cardGe L n ↔ ↑n ≤ #M := by
  rw [← lift_mk_fin, ← lift_le.{0}, lift_lift, lift_mk_le, Sentence.cardGe, Sentence.Realize,
    BoundedFormula.realize_exs]
  simp_rw [BoundedFormula.realize_foldr_inf]
  -- ⊢ (∃ xs, ∀ (φ : BoundedFormula L Empty n), φ ∈ List.map (fun ij => ∼((var ∘ Su …
  simp only [Function.comp_apply, List.mem_map, Prod.exists, Ne.def, List.mem_product,
    List.mem_finRange, forall_exists_index, and_imp, List.mem_filter, true_and_iff]
  refine' ⟨_, fun xs => ⟨xs.some, _⟩⟩
  -- ⊢ (∃ xs, ∀ (φ : BoundedFormula L Empty n) (x x_1 : Fin n), (decide ¬x = x_1) = …
  · rintro ⟨xs, h⟩
    -- ⊢ Nonempty (Fin n ↪ M)
    refine' ⟨⟨xs, fun i j ij => _⟩⟩
    -- ⊢ i = j
    contrapose! ij
    -- ⊢ xs i ≠ xs j
    have hij := h _ i j (by simpa using ij) rfl
    -- ⊢ xs i ≠ xs j
    simp only [BoundedFormula.realize_not, Term.realize, BoundedFormula.realize_bdEqual,
      Sum.elim_inr] at hij
    exact hij
    -- 🎉 no goals
  · rintro _ i j ij rfl
    -- ⊢ BoundedFormula.Realize (∼(var (Sum.inr i) =' var (Sum.inr j))) default ↑(Non …
    simpa using ij
    -- 🎉 no goals
#align first_order.language.sentence.realize_card_ge FirstOrder.Language.Sentence.realize_cardGe

@[simp]
theorem model_infiniteTheory_iff : M ⊨ L.infiniteTheory ↔ Infinite M := by
  simp [infiniteTheory, infinite_iff, aleph0_le]
  -- 🎉 no goals
#align first_order.language.model_infinite_theory_iff FirstOrder.Language.model_infiniteTheory_iff

instance model_infiniteTheory [h : Infinite M] : M ⊨ L.infiniteTheory :=
  L.model_infiniteTheory_iff.2 h
#align first_order.language.model_infinite_theory FirstOrder.Language.model_infiniteTheory

@[simp]
theorem model_nonemptyTheory_iff : M ⊨ L.nonemptyTheory ↔ Nonempty M := by
  simp only [nonemptyTheory, Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    Sentence.realize_cardGe, Nat.cast_one, one_le_iff_ne_zero, mk_ne_zero_iff]
#align first_order.language.model_nonempty_theory_iff FirstOrder.Language.model_nonemptyTheory_iff

instance model_nonempty [h : Nonempty M] : M ⊨ L.nonemptyTheory :=
  L.model_nonemptyTheory_iff.2 h
#align first_order.language.model_nonempty FirstOrder.Language.model_nonempty

theorem model_distinctConstantsTheory {M : Type w} [L[[α]].Structure M] (s : Set α) :
    M ⊨ L.distinctConstantsTheory s ↔ Set.InjOn (fun i : α => (L.con i : M)) s := by
  simp only [distinctConstantsTheory, Theory.model_iff, Set.mem_image, Set.mem_inter,
    Set.mem_prod, Set.mem_compl, Prod.exists, forall_exists_index, and_imp]
  refine' ⟨fun h a as b bs ab => _, _⟩
  -- ⊢ a = b
  · contrapose! ab
    -- ⊢ ↑(Language.con L a) ≠ ↑(Language.con L b)
    have h' := h _ a b ⟨⟨as, bs⟩, ab⟩ rfl
    -- ⊢ ↑(Language.con L a) ≠ ↑(Language.con L b)
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal,
      Term.realize_constants] at h'
    exact h'
    -- 🎉 no goals
  · rintro h φ a b ⟨⟨as, bs⟩, ab⟩ rfl
    -- ⊢ M ⊨ Formula.not (Term.equal (Constants.term (Language.con L a)) (Constants.t …
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal, Term.realize_constants]
    -- ⊢ ¬↑(Language.con L a) = ↑(Language.con L b)
    exact fun contra => ab (h as bs contra)
    -- 🎉 no goals
#align first_order.language.model_distinct_constants_theory FirstOrder.Language.model_distinctConstantsTheory

theorem card_le_of_model_distinctConstantsTheory (s : Set α) (M : Type w) [L[[α]].Structure M]
    [h : M ⊨ L.distinctConstantsTheory s] : Cardinal.lift.{w} #s ≤ Cardinal.lift.{u'} #M :=
  lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsTheory s).1 h)⟩⟩
#align first_order.language.card_le_of_model_distinct_constants_theory FirstOrder.Language.card_le_of_model_distinctConstantsTheory

end Cardinality

namespace ElementarilyEquivalent

@[symm]
nonrec theorem symm (h : M ≅[L] N) : N ≅[L] M :=
  h.symm
#align first_order.language.elementarily_equivalent.symm FirstOrder.Language.ElementarilyEquivalent.symm

@[trans]
nonrec theorem trans (MN : M ≅[L] N) (NP : N ≅[L] P) : M ≅[L] P :=
  MN.trans NP
#align first_order.language.elementarily_equivalent.trans FirstOrder.Language.ElementarilyEquivalent.trans

theorem completeTheory_eq (h : M ≅[L] N) : L.completeTheory M = L.completeTheory N :=
  h
#align first_order.language.elementarily_equivalent.complete_theory_eq FirstOrder.Language.ElementarilyEquivalent.completeTheory_eq

theorem realize_sentence (h : M ≅[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  (elementarilyEquivalent_iff.1 h) φ
#align first_order.language.elementarily_equivalent.realize_sentence FirstOrder.Language.ElementarilyEquivalent.realize_sentence

theorem theory_model_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T := by
  rw [Theory.model_iff_subset_completeTheory, Theory.model_iff_subset_completeTheory,
    h.completeTheory_eq]
set_option linter.uppercaseLean3 false in
#align first_order.language.elementarily_equivalent.Theory_model_iff FirstOrder.Language.ElementarilyEquivalent.theory_model_iff

theorem theory_model [MT : M ⊨ T] (h : M ≅[L] N) : N ⊨ T :=
  h.theory_model_iff.1 MT
set_option linter.uppercaseLean3 false in
#align first_order.language.elementarily_equivalent.Theory_model FirstOrder.Language.ElementarilyEquivalent.theory_model

theorem nonempty_iff (h : M ≅[L] N) : Nonempty M ↔ Nonempty N :=
  (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans (model_nonemptyTheory_iff L))
#align first_order.language.elementarily_equivalent.nonempty_iff FirstOrder.Language.ElementarilyEquivalent.nonempty_iff

theorem nonempty [Mn : Nonempty M] (h : M ≅[L] N) : Nonempty N :=
  h.nonempty_iff.1 Mn
#align first_order.language.elementarily_equivalent.nonempty FirstOrder.Language.ElementarilyEquivalent.nonempty

theorem infinite_iff (h : M ≅[L] N) : Infinite M ↔ Infinite N :=
  (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))
#align first_order.language.elementarily_equivalent.infinite_iff FirstOrder.Language.ElementarilyEquivalent.infinite_iff

theorem infinite [Mi : Infinite M] (h : M ≅[L] N) : Infinite N :=
  h.infinite_iff.1 Mi
#align first_order.language.elementarily_equivalent.infinite FirstOrder.Language.ElementarilyEquivalent.infinite

end ElementarilyEquivalent

end Language

end FirstOrder
