/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.Data.Finset.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.List.ProdSigma

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
variable {α : Type u'} {β : Type v'} {γ : Type*}

open FirstOrder Cardinal

open Structure Cardinal Fin

namespace Term

-- Porting note: universes in different order
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
  · rfl
  · simp [ih]
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
  refine congr rfl (funext fun i => ?_)
  simp only [Matrix.cons_val_fin_one]
#align first_order.language.term.realize_functions_apply₁ FirstOrder.Language.Term.realize_functions_apply₁

@[simp]
theorem realize_functions_apply₂ {f : L.Functions 2} {t₁ t₂ : L.Term α} {v : α → M} :
    (f.apply₂ t₁ t₂).realize v = funMap f ![t₁.realize v, t₂.realize v] := by
  rw [Functions.apply₂, Term.realize]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
#align first_order.language.term.realize_functions_apply₂ FirstOrder.Language.Term.realize_functions_apply₂

theorem realize_con {A : Set M} {a : A} {v : α → M} : (L.con a).term.realize v = a :=
  rfl
#align first_order.language.term.realize_con FirstOrder.Language.Term.realize_con

@[simp]
theorem realize_subst {t : L.Term α} {tf : α → L.Term β} {v : β → M} :
    (t.subst tf).realize v = t.realize fun a => (tf a).realize v := by
  induction' t with _ _ _ _ ih
  · rfl
  · simp [ih]
#align first_order.language.term.realize_subst FirstOrder.Language.Term.realize_subst

@[simp]
theorem realize_restrictVar [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset ⊆ s)
    {v : α → M} : (t.restrictVar (Set.inclusion h)).realize (v ∘ (↑)) = t.realize v := by
  induction' t with _ _ _ _ ih
  · rfl
  · simp_rw [varFinset, Finset.coe_biUnion, Set.iUnion_subset_iff] at h
    exact congr rfl (funext fun i => ih i (h i (Finset.mem_univ i)))
#align first_order.language.term.realize_restrict_var FirstOrder.Language.Term.realize_restrictVar

@[simp]
theorem realize_restrictVarLeft [DecidableEq α] {γ : Type*} {t : L.Term (Sum α γ)} {s : Set α}
    (h : ↑t.varFinsetLeft ⊆ s) {v : α → M} {xs : γ → M} :
    (t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ (↑)) xs) =
      t.realize (Sum.elim v xs) := by
  induction' t with a _ _ _ ih
  · cases a <;> rfl
  · simp_rw [varFinsetLeft, Finset.coe_biUnion, Set.iUnion_subset_iff] at h
    exact congr rfl (funext fun i => ih i (h i (Finset.mem_univ i)))
#align first_order.language.term.realize_restrict_var_left FirstOrder.Language.Term.realize_restrictVarLeft

@[simp]
theorem realize_constantsToVars [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L[[α]].Term β} {v : β → M} :
    t.constantsToVars.realize (Sum.elim (fun a => ↑(L.con a)) v) = t.realize v := by
  induction' t with _ n f ts ih
  · simp
  · cases n
    · cases f
      · simp only [realize, ih, Nat.zero_eq, constantsOn, mk₂_Functions]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sum_inl]
      · simp only [realize, constantsToVars, Sum.elim_inl, funMap_eq_coe_constants]
        rfl
    · cases' f with _ f
      · simp only [realize, ih, constantsOn, mk₂_Functions]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sum_inl]
      · exact isEmptyElim f
#align first_order.language.term.realize_constants_to_vars FirstOrder.Language.Term.realize_constantsToVars

@[simp]
theorem realize_varsToConstants [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L.Term (Sum α β)} {v : β → M} :
    t.varsToConstants.realize v = t.realize (Sum.elim (fun a => ↑(L.con a)) v) := by
  induction' t with ab n f ts ih
  · cases' ab with a b
    -- Porting note: both cases were `simp [Language.con]`
    · simp [Language.con, realize, funMap_eq_coe_constants]
    · simp [realize, constantMap]
  · simp only [realize, constantsOn, mk₂_Functions, ih]
    -- Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sum_inl]
#align first_order.language.term.realize_vars_to_constants FirstOrder.Language.Term.realize_varsToConstants

theorem realize_constantsVarsEquivLeft [L[[α]].Structure M]
    [(lhomWithConstants L α).IsExpansionOn M] {n} {t : L[[α]].Term (Sum β (Fin n))} {v : β → M}
    {xs : Fin n → M} :
    (constantsVarsEquivLeft t).realize (Sum.elim (Sum.elim (fun a => ↑(L.con a)) v) xs) =
      t.realize (Sum.elim v xs) := by
  simp only [constantsVarsEquivLeft, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constantsVarsEquiv_apply, relabelEquiv_symm_apply]
  refine _root_.trans ?_ realize_constantsToVars
  rcongr x
  rcases x with (a | (b | i)) <;> simp
#align first_order.language.term.realize_constants_vars_equiv_left FirstOrder.Language.Term.realize_constantsVarsEquivLeft

end Term

namespace LHom

@[simp]
theorem realize_onTerm [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
    (v : α → M) : (φ.onTerm t).realize v = t.realize v := by
  induction' t with _ n f ts ih
  · rfl
  · simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.realize_on_term FirstOrder.Language.LHom.realize_onTerm

end LHom

@[simp]
theorem Hom.realize_term (g : M →[L] N) {t : L.Term α} {v : α → M} :
    t.realize (g ∘ v) = g (t.realize v) := by
  induction t
  · rfl
  · rw [Term.realize, Term.realize, g.map_fun]
    refine congr rfl ?_
    ext x
    simp [*]
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

-- Porting note: universes in different order
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
#align first_order.language.bounded_formula.realize_top FirstOrder.Language.BoundedFormula.realize_top

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v xs ↔ φ.Realize v xs ∧ ψ.Realize v xs := by
  simp [Inf.inf, Realize]
#align first_order.language.bounded_formula.realize_inf FirstOrder.Language.BoundedFormula.realize_inf

@[simp]
theorem realize_foldr_inf (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ ∀ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction' l with φ l ih
  · simp
  · simp [ih]
#align first_order.language.bounded_formula.realize_foldr_inf FirstOrder.Language.BoundedFormula.realize_foldr_inf

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs := by
  simp only [Realize]
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
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]
#align first_order.language.bounded_formula.realize_rel₁ FirstOrder.Language.BoundedFormula.realize_rel₁

@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.boundedFormula₂ t₁ t₂).Realize v xs ↔
      RelMap R ![t₁.realize (Sum.elim v xs), t₂.realize (Sum.elim v xs)] := by
  rw [Relations.boundedFormula₂, realize_rel, iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
#align first_order.language.bounded_formula.realize_rel₂ FirstOrder.Language.BoundedFormula.realize_rel₂

@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v xs ↔ φ.Realize v xs ∨ ψ.Realize v xs := by
  simp only [realize, Sup.sup, realize_not, eq_iff_iff]
  tauto
#align first_order.language.bounded_formula.realize_sup FirstOrder.Language.BoundedFormula.realize_sup

@[simp]
theorem realize_foldr_sup (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction' l with φ l ih
  · simp
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
  simp_rw [realize_not, Classical.not_not]
#align first_order.language.bounded_formula.realize_ex FirstOrder.Language.BoundedFormula.realize_ex

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v xs ↔ (φ.Realize v xs ↔ ψ.Realize v xs) := by
  simp only [BoundedFormula.iff, realize_inf, realize_imp, and_imp, ← iff_def]
#align first_order.language.bounded_formula.realize_iff FirstOrder.Language.BoundedFormula.realize_iff

theorem realize_castLE_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} {φ : L.BoundedFormula α m}
    {v : α → M} {xs : Fin n → M} : (φ.castLE h').Realize v xs ↔ φ.Realize v (xs ∘ cast h) := by
  subst h
  simp only [castLE_rfl, cast_refl, OrderIso.coe_refl, Function.comp_id]
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
  · simp [mapTermRel, Realize, h1]
  · simp [mapTermRel, Realize, h1, h2]
  · simp [mapTermRel, Realize, ih1, ih2]
  · simp only [mapTermRel, Realize, ih, id]
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
  · simp [mapTermRel, Realize, h1]
  · simp [mapTermRel, Realize, h1, h2]
  · simp [mapTermRel, Realize, ih1, ih2]
  · simp [mapTermRel, Realize, ih, hv]
#align first_order.language.bounded_formula.realize_map_term_rel_add_cast_le FirstOrder.Language.BoundedFormula.realize_mapTermRel_add_castLe

@[simp]
theorem realize_relabel {m n : ℕ} {φ : L.BoundedFormula α n} {g : α → Sum β (Fin m)} {v : β → M}
    {xs : Fin (m + n) → M} :
    (φ.relabel g).Realize v xs ↔
      φ.Realize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
  rw [relabel, realize_mapTermRel_add_castLe] <;> intros <;> simp
#align first_order.language.bounded_formula.realize_relabel FirstOrder.Language.BoundedFormula.realize_relabel

theorem realize_liftAt {n n' m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + n') → M}
    (hmn : m + n' ≤ n + 1) :
    (φ.liftAt n' m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') := by
  rw [liftAt]
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 k _ ih3
  · simp [mapTermRel, Realize]
  · simp [mapTermRel, Realize, realize_rel, realize_liftAt, Sum.elim_comp_map]
  · simp [mapTermRel, Realize, realize_rel, realize_liftAt, Sum.elim_comp_map]
  · simp only [mapTermRel, Realize, ih1 hmn, ih2 hmn]
  · have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
    simp only [mapTermRel, Realize, realize_castLE_of_eq h, ih3 (hmn.trans k.succ.le_succ)]
    refine forall_congr' fun x => iff_eq_eq.mpr (congr rfl (funext (Fin.lastCases ?_ fun i => ?_)))
    · simp only [Function.comp_apply, val_last, snoc_last]
      by_cases h : k < m
      · rw [if_pos h]
        refine (congr rfl (ext ?_)).trans (snoc_last _ _)
        simp only [coe_cast, coe_castAdd, val_last, self_eq_add_right]
        refine le_antisymm
          (le_of_add_le_add_left ((hmn.trans (Nat.succ_le_of_lt h)).trans ?_)) n'.zero_le
        rw [add_zero]
      · rw [if_neg h]
        refine (congr rfl (ext ?_)).trans (snoc_last _ _)
        simp
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      refine (congr rfl (ext ?_)).trans (snoc_castSucc _ _ _)
      simp only [coe_castSucc, coe_cast]
      split_ifs <;> simp
#align first_order.language.bounded_formula.realize_lift_at FirstOrder.Language.BoundedFormula.realize_liftAt

theorem realize_liftAt_one {n m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + 1) → M}
    (hmn : m ≤ n) :
    (φ.liftAt 1 m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then castSucc i else i.succ) := by
  simp [realize_liftAt (add_le_add_right hmn 1), castSucc]
#align first_order.language.bounded_formula.realize_lift_at_one FirstOrder.Language.BoundedFormula.realize_liftAt_one

@[simp]
theorem realize_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin (n + 1) → M} : (φ.liftAt 1 n).Realize v xs ↔ φ.Realize v (xs ∘ castSucc) := by
  rw [realize_liftAt_one (refl n), iff_eq_eq]
  refine congr rfl (congr rfl (funext fun i => ?_))
  rw [if_pos i.is_lt]
#align first_order.language.bounded_formula.realize_lift_at_one_self FirstOrder.Language.BoundedFormula.realize_liftAt_one_self

@[simp]
theorem realize_subst {φ : L.BoundedFormula α n} {tf : α → L.Term β} {v : β → M} {xs : Fin n → M} :
    (φ.subst tf).Realize v xs ↔ φ.Realize (fun a => (tf a).realize v) xs :=
  realize_mapTermRel_id
    (fun n t x => by
      rw [Term.realize_subst]
      rcongr a
      cases a
      · simp only [Sum.elim_inl, Function.comp_apply, Term.realize_relabel, Sum.elim_comp_inl]
      · rfl)
    (by simp)
#align first_order.language.bounded_formula.realize_subst FirstOrder.Language.BoundedFormula.realize_subst

@[simp]
theorem realize_restrictFreeVar [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n} {s : Set α}
    (h : ↑φ.freeVarFinset ⊆ s) {v : α → M} {xs : Fin n → M} :
    (φ.restrictFreeVar (Set.inclusion h)).Realize (v ∘ (↑)) xs ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp [restrictFreeVar, Realize]
  · simp [restrictFreeVar, Realize]
  · simp [restrictFreeVar, Realize, ih1, ih2]
  · simp [restrictFreeVar, Realize, ih3]
#align first_order.language.bounded_formula.realize_restrict_free_var FirstOrder.Language.BoundedFormula.realize_restrictFreeVar

theorem realize_constantsVarsEquiv [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {φ : L[[α]].BoundedFormula β n} {v : β → M} {xs : Fin n → M} :
    (constantsVarsEquiv φ).Realize (Sum.elim (fun a => ↑(L.con a)) v) xs ↔ φ.Realize v xs := by
  refine realize_mapTermRel_id (fun n t xs => realize_constantsVarsEquivLeft) fun n R xs => ?_
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [← (lhomWithConstants L α).map_onRelation
      (Equiv.sumEmpty (L.Relations n) ((constantsOn α).Relations n) R) xs]
  rcongr
  cases' R with R R
  · -- This used to be `simp` before leanprover/lean4#2644
    simp; erw [Equiv.sumEmpty_apply_inl]
  · exact isEmptyElim R
#align first_order.language.bounded_formula.realize_constants_vars_equiv FirstOrder.Language.BoundedFormula.realize_constantsVarsEquiv

@[simp]
theorem realize_relabelEquiv {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β → M}
    {xs : Fin k → M} : (relabelEquiv g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  refine realize_mapTermRel_id (fun n t xs => ?_) fun _ _ _ => rfl
  simp only [relabelEquiv_apply, Term.realize_relabel]
  refine congr (congr rfl ?_) rfl
  ext (i | i) <;> rfl
#align first_order.language.bounded_formula.realize_relabel_equiv FirstOrder.Language.BoundedFormula.realize_relabelEquiv

variable [Nonempty M]

theorem realize_all_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin n → M} : (φ.liftAt 1 n).all.Realize v xs ↔ φ.Realize v xs := by
  inhabit M
  simp only [realize_all, realize_liftAt_one_self]
  refine ⟨fun h => ?_, fun h a => ?_⟩
  · refine (congr rfl (funext fun i => ?_)).mp (h default)
    simp
  · refine (congr rfl (funext fun i => ?_)).mp h
    simp
#align first_order.language.bounded_formula.realize_all_lift_at_one_self FirstOrder.Language.BoundedFormula.realize_all_liftAt_one_self

theorem realize_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} :
    (φ.toPrenexImpRight ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  induction' hψ with _ _ hψ _ _ _hψ ih _ _ _hψ ih
  · rw [hψ.toPrenexImpRight]
  · refine _root_.trans (forall_congr' fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
  · unfold toPrenexImpRight
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_ex]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ⟨a, ha h⟩
    · by_cases h : φ.Realize v xs
      · obtain ⟨a, ha⟩ := h' h
        exact ⟨a, fun _ => ha⟩
      · inhabit M
        exact ⟨default, fun h'' => (h h'').elim⟩
#align first_order.language.bounded_formula.realize_to_prenex_imp_right FirstOrder.Language.BoundedFormula.realize_toPrenexImpRight

theorem realize_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ)
    {v : α → M} {xs : Fin n → M} : (φ.toPrenexImp ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  revert ψ
  induction' hφ with _ _ hφ _ _ _hφ ih _ _ _hφ ih <;> intro ψ hψ
  · rw [hφ.toPrenexImp]
    exact realize_toPrenexImpRight hφ hψ
  · unfold toPrenexImp
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hψ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ha (h a)
    · by_cases h : ψ.Realize v xs
      · inhabit M
        exact ⟨default, fun _h'' => h⟩
      · obtain ⟨a, ha⟩ := not_forall.1 (h ∘ h')
        exact ⟨a, fun h => (ha h).elim⟩
  · refine _root_.trans (forall_congr' fun _ => ih hψ.liftAt) ?_
    simp
#align first_order.language.bounded_formula.realize_to_prenex_imp FirstOrder.Language.BoundedFormula.realize_toPrenexImp

@[simp]
theorem realize_toPrenex (φ : L.BoundedFormula α n) {v : α → M} :
    ∀ {xs : Fin n → M}, φ.toPrenex.Realize v xs ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ f1 f2 h1 h2 _ _ h
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · intros
    rw [toPrenex, realize_toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex, realize_imp,
      realize_imp, h1, h2]
  · intros
    rw [realize_all, toPrenex, realize_all]
    exact forall_congr' fun a => h
#align first_order.language.bounded_formula.realize_to_prenex FirstOrder.Language.BoundedFormula.realize_toPrenex

end BoundedFormula


-- Porting note: no `protected` attribute in Lean4
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
  · simp only [onBoundedFormula, realize_bdEqual, realize_onTerm]
    rfl
  · simp only [onBoundedFormula, realize_rel, LHom.map_onRelation,
      Function.comp_apply, realize_onTerm]
    rfl
  · simp only [onBoundedFormula, ih1, ih2, realize_imp]
  · simp only [onBoundedFormula, ih3, realize_all]
set_option linter.uppercaseLean3 false in
#align first_order.language.Lhom.realize_on_bounded_formula FirstOrder.Language.LHom.realize_onBoundedFormula

end LHom

-- Porting note: no `protected` attribute in Lean4
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
#align first_order.language.formula.realize_rel FirstOrder.Language.Formula.realize_rel

@[simp]
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.formula₁ t).Realize v ↔ RelMap R ![t.realize v] := by
  rw [Relations.formula₁, realize_rel, iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]
#align first_order.language.formula.realize_rel₁ FirstOrder.Language.Formula.realize_rel₁

@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.formula₂ t₁ t₂).Realize v ↔ RelMap R ![t₁.realize v, t₂.realize v] := by
  rw [Relations.formula₂, realize_rel, iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]
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
  exact congr rfl (funext finZeroElim)
#align first_order.language.formula.realize_relabel FirstOrder.Language.Formula.realize_relabel

theorem realize_relabel_sum_inr (φ : L.Formula (Fin n)) {v : Empty → M} {x : Fin n → M} :
    (BoundedFormula.relabel Sum.inr φ).Realize v x ↔ φ.Realize x := by
  rw [BoundedFormula.realize_relabel, Formula.Realize, Sum.elim_comp_inr, Fin.castAdd_zero,
    cast_refl, Function.comp_id,
    Subsingleton.elim (x ∘ (natAdd n : Fin 0 → Fin n)) default]
#align first_order.language.formula.realize_relabel_sum_inr FirstOrder.Language.Formula.realize_relabel_sum_inr

@[simp]
theorem realize_equal {t₁ t₂ : L.Term α} {x : α → M} :
    (t₁.equal t₂).Realize x ↔ t₁.realize x = t₂.realize x := by simp [Term.equal, Realize]
#align first_order.language.formula.realize_equal FirstOrder.Language.Formula.realize_equal

@[simp]
theorem realize_graph {f : L.Functions n} {x : Fin n → M} {y : M} :
    (Formula.graph f).Realize (Fin.cons y x : _ → M) ↔ funMap f x = y := by
  simp only [Formula.graph, Term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  rw [eq_comm]
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
  simp
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
  simp only [equivSentence, _root_.Equiv.symm_symm, Equiv.coe_trans, Realize,
    BoundedFormula.realize_relabelEquiv, Function.comp]
  refine _root_.trans ?_ BoundedFormula.realize_constantsVarsEquiv
  rw [iff_iff_eq]
  congr with (_ | a)
  · simp
  · cases a
#align first_order.language.formula.realize_equiv_sentence_symm_con FirstOrder.Language.Formula.realize_equivSentence_symm_con

@[simp]
theorem realize_equivSentence [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]
    (φ : L.Formula α) : (equivSentence φ).Realize M ↔ φ.Realize fun a => (L.con a : M) := by
  rw [← realize_equivSentence_symm_con M (equivSentence φ), _root_.Equiv.symm_apply_apply]
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
  exact fun φ hφ => hφ.elim (h _) (h' _)
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.model.union FirstOrder.Language.Theory.Model.union

@[simp]
theorem model_union_iff {T' : L.Theory} : M ⊨ T ∪ T' ↔ M ⊨ T ∧ M ⊨ T' :=
  ⟨fun h => ⟨h.mono (T.subset_union_left T'), h.mono (T.subset_union_right T')⟩, fun h =>
    h.1.union h.2⟩
set_option linter.uppercaseLean3 false in
#align first_order.language.Theory.model_union_iff FirstOrder.Language.Theory.model_union_iff

theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by simp
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
  refine ⟨fun h => ?_, (L.completeTheory M).realize_sentence_of_mem⟩
  contrapose! h
  rw [← Sentence.realize_not] at *
  exact (L.completeTheory M).realize_sentence_of_mem (mem_completeTheory.2 h)
#align first_order.language.realize_iff_of_model_complete_theory FirstOrder.Language.realize_iff_of_model_completeTheory

variable {M N}

namespace BoundedFormula

@[simp]
theorem realize_alls {φ : L.BoundedFormula α n} {v : α → M} :
    φ.alls.Realize v ↔ ∀ xs : Fin n → M, φ.Realize v xs := by
  induction' n with n ih
  · exact Unique.forall_iff.symm
  · simp only [alls, ih, Realize]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩
#align first_order.language.bounded_formula.realize_alls FirstOrder.Language.BoundedFormula.realize_alls

@[simp]
theorem realize_exs {φ : L.BoundedFormula α n} {v : α → M} :
    φ.exs.Realize v ↔ ∃ xs : Fin n → M, φ.Realize v xs := by
  induction' n with n ih
  · exact Unique.exists_iff.symm
  · simp only [BoundedFormula.exs, ih, realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      rw [← Fin.snoc_init_self xs] at h
      exact ⟨_, _, h⟩
#align first_order.language.bounded_formula.realize_exs FirstOrder.Language.BoundedFormula.realize_exs

@[simp]
theorem _root_.FirstOrder.Language.Formula.realize_iAlls
    [Finite γ] {f : α → β ⊕ γ}
    {φ : L.Formula α} {v : β → M} : (φ.iAlls f).Realize v ↔
      ∀ (i : γ → M), φ.Realize (fun a => Sum.elim v i (f a)) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iAlls]
  simp only [Nat.add_zero, realize_alls, realize_relabel, Function.comp,
    castAdd_zero, finCongr_refl, OrderIso.refl_apply, Sum.elim_map, id_eq]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp],
      fun _ => by simp [Function.comp]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
theorem realize_iAlls [Finite γ] {f : α → β ⊕ γ}
    {φ : L.Formula α} {v : β → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iAlls f) v v' ↔
      ∀ (i : γ → M), φ.Realize (fun a => Sum.elim v i (f a)) := by
  rw [← Formula.realize_iAlls, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
theorem _root_.FirstOrder.Language.Formula.realize_iExs
    [Finite γ] {f : α → β ⊕ γ}
    {φ : L.Formula α} {v : β → M} : (φ.iExs f).Realize v ↔
      ∃ (i : γ → M), φ.Realize (fun a => Sum.elim v i (f a)) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iExs]
  simp only [Nat.add_zero, realize_exs, realize_relabel, Function.comp,
    castAdd_zero, finCongr_refl, OrderIso.refl_apply, Sum.elim_map, id_eq]
  rw [← not_iff_not, not_exists, not_exists]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp],
      fun _ => by simp [Function.comp]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
theorem realize_iExs [Finite γ] {f : α → β ⊕ γ}
    {φ : L.Formula α} {v : β → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iExs f) v v' ↔
      ∃ (i : γ → M), φ.Realize (fun a => Sum.elim v i (f a)) := by
  rw [← Formula.realize_iExs, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
theorem realize_toFormula (φ : L.BoundedFormula α n) (v : Sum α (Fin n) → M) :
    φ.toFormula.Realize v ↔ φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3 a8 a9 a0
  · rfl
  · simp [BoundedFormula.Realize]
  · simp [BoundedFormula.Realize]
  · rw [toFormula, Formula.Realize, realize_imp, ← Formula.Realize, ih1, ← Formula.Realize, ih2,
      realize_imp]
  · rw [toFormula, Formula.Realize, realize_all, realize_all]
    refine forall_congr' fun a => ?_
    have h := ih3 (Sum.elim (v ∘ Sum.inl) (snoc (v ∘ Sum.inr) a))
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    rw [← h, realize_relabel, Formula.Realize, iff_iff_eq]
    simp only [Function.comp]
    congr with x
    · cases' x with _ x
      · simp
      · refine Fin.lastCases ?_ ?_ x
        · rw [Sum.elim_inr, Sum.elim_inr,
            finSumFinEquiv_symm_last, Sum.map_inr, Sum.elim_inr]
          simp [Fin.snoc]
        · simp only [castSucc, Function.comp_apply, Sum.elim_inr,
            finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, Sum.elim_inl]
          rw [← castSucc]
          simp
    · exact Fin.elim0 x
#align first_order.language.bounded_formula.realize_to_formula FirstOrder.Language.BoundedFormula.realize_toFormula

@[simp]
theorem realize_iSup (s : Finset β) (f : β → L.BoundedFormula α n)
    (v : α → M) (v' : Fin n → M) :
    (iSup s f).Realize v v' ↔ ∃ b ∈ s, (f b).Realize v v' := by
  simp only [iSup, realize_foldr_sup, List.mem_map, Finset.mem_toList,
    exists_exists_and_eq_and]

@[simp]
theorem realize_iInf (s : Finset β) (f : β → L.BoundedFormula α n)
    (v : α → M) (v' : Fin n → M) :
    (iInf s f).Realize v v' ↔ ∀ b ∈ s, (f b).Realize v v' := by
  simp only [iInf, realize_foldr_inf, List.mem_map, Finset.mem_toList,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

end BoundedFormula

namespace Equiv

@[simp]
theorem realize_boundedFormula (g : M ≃[L] N) (φ : L.BoundedFormula α n) {v : α → M}
    {xs : Fin n → M} : φ.Realize (g ∘ v) (g ∘ xs) ↔ φ.Realize v xs := by
  induction' φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3
  · rfl
  · simp only [BoundedFormula.Realize, ← Sum.comp_elim, Equiv.realize_term, g.injective.eq_iff]
  · simp only [BoundedFormula.Realize, ← Sum.comp_elim, Equiv.realize_term]
    exact g.map_rel _ _
  · rw [BoundedFormula.Realize, ih1, ih2, BoundedFormula.Realize]
  · rw [BoundedFormula.Realize, BoundedFormula.Realize]
    constructor
    · intro h a
      have h' := h (g a)
      rw [← Fin.comp_snoc, ih3] at h'
      exact h'
    · intro h a
      have h' := h (g.symm a)
      rw [← ih3, Fin.comp_snoc, g.apply_symm_apply] at h'
      exact h'
#align first_order.language.equiv.realize_bounded_formula FirstOrder.Language.Equiv.realize_boundedFormula

@[simp]
theorem realize_formula (g : M ≃[L] N) (φ : L.Formula α) {v : α → M} :
    φ.Realize (g ∘ v) ↔ φ.Realize v := by
  rw [Formula.Realize, Formula.Realize, ← g.realize_boundedFormula φ, iff_eq_eq,
    Unique.eq_default (g ∘ default)]
#align first_order.language.equiv.realize_formula FirstOrder.Language.Equiv.realize_formula

theorem realize_sentence (g : M ≃[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize, Sentence.Realize, ← g.realize_formula, Unique.eq_default (g ∘ default)]
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
  simp only [Function.comp_apply, List.mem_map, Prod.exists, Ne, List.mem_product,
    List.mem_finRange, forall_exists_index, and_imp, List.mem_filter, true_and_iff]
  refine ⟨?_, fun xs => ⟨xs.some, ?_⟩⟩
  · rintro ⟨xs, h⟩
    refine ⟨⟨xs, fun i j ij => ?_⟩⟩
    contrapose! ij
    have hij := h _ i j (by simpa using ij) rfl
    simp only [BoundedFormula.realize_not, Term.realize, BoundedFormula.realize_bdEqual,
      Sum.elim_inr] at hij
    exact hij
  · rintro _ i j ij rfl
    simpa using ij
#align first_order.language.sentence.realize_card_ge FirstOrder.Language.Sentence.realize_cardGe

@[simp]
theorem model_infiniteTheory_iff : M ⊨ L.infiniteTheory ↔ Infinite M := by
  simp [infiniteTheory, infinite_iff, aleph0_le]
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
  refine ⟨fun h a as b bs ab => ?_, ?_⟩
  · contrapose! ab
    have h' := h _ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal,
      Term.realize_constants] at h'
    exact h'
  · rintro h φ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal, Term.realize_constants]
    exact fun contra => ab (h as bs contra)
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
