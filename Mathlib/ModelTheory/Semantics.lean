/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import Mathlib.Data.Finset.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.Data.List.ProdSigma

/-!
# Basics on First-Order Semantics

This file defines the interpretations of first-order terms, formulas, sentences, and theories
in a style inspired by the [Flypitch project](https://flypitch.github.io/).

## Main Definitions

- `FirstOrder.Language.Term.realize` is defined so that `t.realize v` is the term `t` evaluated at
  variables `v`.
- `FirstOrder.Language.BoundedFormula.Realize` is defined so that `φ.Realize v xs` is the bounded
  formula `φ` evaluated at tuples of variables `v` and `xs`.
- `FirstOrder.Language.Formula.Realize` is defined so that `φ.Realize v` is the formula `φ`
  evaluated at variables `v`.
- `FirstOrder.Language.Sentence.Realize` is defined so that `φ.Realize M` is the sentence `φ`
  evaluated in the structure `M`. Also denoted `M ⊨ φ`.
- `FirstOrder.Language.Theory.Model` is defined so that `T.Model M` is true if and only if every
  sentence of `T` is realized in `M`. Also denoted `T ⊨ φ`.

## Main Results

- Several results in this file show that syntactic constructions such as `relabel`, `castLE`,
  `liftAt`, `subst`, and the actions of language maps commute with realization of terms, formulas,
  sentences, and theories.

## Implementation Notes

- Formulas use a modified version of de Bruijn variables. Specifically, a `L.BoundedFormula α n`
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

open Structure Fin

namespace Term

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
def realize (v : α → M) : ∀ _t : L.Term α, M
  | var k => v k
  | func f ts => funMap f fun i => (ts i).realize v

@[simp]
theorem realize_var (v : α → M) (k) : realize v (var k : L.Term α) = v k := rfl

@[simp]
theorem realize_func (v : α → M) {n} (f : L.Functions n) (ts) :
    realize v (func f ts : L.Term α) = funMap f fun i => (ts i).realize v := rfl

@[simp]
theorem realize_function_term {n} (v : Fin n → M) (f : L.Functions n) :
    f.term.realize v = funMap f v := by
  rfl

@[simp]
theorem realize_relabel {t : L.Term α} {g : α → β} {v : β → M} :
    (t.relabel g).realize v = t.realize (v ∘ g) := by
  induction t with
  | var => rfl
  | func f ts ih => simp [ih]

@[simp]
theorem realize_liftAt {n n' m : ℕ} {t : L.Term (α ⊕ (Fin n))} {v : α ⊕ (Fin (n + n')) → M} :
    (t.liftAt n' m).realize v =
      t.realize (v ∘ Sum.map id fun i : Fin _ =>
        if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') :=
  realize_relabel

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

@[simp]
theorem realize_subst {t : L.Term α} {tf : α → L.Term β} {v : β → M} :
    (t.subst tf).realize v = t.realize fun a => (tf a).realize v := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

theorem realize_restrictVar [DecidableEq α] {t : L.Term α} {f : t.varFinset → β}
    {v : β → M} (v' : α → M) (hv' : ∀ a, v (f a) = v' a) :
    (t.restrictVar f).realize v = t.realize v' := by
  induction t with
  | var => simp [restrictVar, hv']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i ((by simp [Function.comp_apply, hv'])))

/-- A special case of `realize_restrictVar`, included because we can add the `simp` attribute
to it -/
@[simp]
theorem realize_restrictVar' [DecidableEq α] {t : L.Term α} {s : Set α} (h : ↑t.varFinset ⊆ s)
    {v : α → M} : (t.restrictVar (Set.inclusion h)).realize (v ∘ (↑)) = t.realize v :=
  realize_restrictVar _ (by simp)

theorem realize_restrictVarLeft [DecidableEq α] {γ : Type*} {t : L.Term (α ⊕ γ)}
    {f : t.varFinsetLeft → β}
    {xs : β ⊕ γ → M} (xs' : α → M) (hxs' : ∀ a, xs (Sum.inl (f a)) = xs' a) :
    (t.restrictVarLeft f).realize xs = t.realize (Sum.elim xs' (xs ∘ Sum.inr)) := by
  induction t with
  | var a => cases a <;> simp [restrictVarLeft, hxs']
  | func _ _ ih =>
    exact congr rfl (funext fun i => ih i (by simp [hxs']))

/-- A special case of `realize_restrictVarLeft`, included because we can add the `simp` attribute
to it -/
@[simp]
theorem realize_restrictVarLeft' [DecidableEq α] {γ : Type*} {t : L.Term (α ⊕ γ)} {s : Set α}
    (h : ↑t.varFinsetLeft ⊆ s) {v : α → M} {xs : γ → M} :
    (t.restrictVarLeft (Set.inclusion h)).realize (Sum.elim (v ∘ (↑)) xs) =
      t.realize (Sum.elim v xs) :=
  realize_restrictVarLeft _ (by simp)

@[simp]
theorem realize_constantsToVars [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L[[α]].Term β} {v : β → M} :
    t.constantsToVars.realize (Sum.elim (fun a => ↑(L.con a)) v) = t.realize v := by
  induction t with
  | var => simp
  | @func n f ts ih =>
    cases n
    · cases f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · simp only [realize, constantsToVars, Sum.elim_inl, funMap_eq_coe_constants]
        rfl
    · obtain - | f := f
      · simp only [realize, ih, constantsOn, constantsOnFunc, constantsToVars]
        -- Porting note: below lemma does not work with simp for some reason
        rw [withConstants_funMap_sumInl]
      · exact isEmptyElim f

@[simp]
theorem realize_varsToConstants [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {t : L.Term (α ⊕ β)} {v : β → M} :
    t.varsToConstants.realize v = t.realize (Sum.elim (fun a => ↑(L.con a)) v) := by
  induction t with
  | var ab => rcases ab with a | b <;> simp [Language.con]
  | func f ts ih =>
    simp only [realize, constantsOn, constantsOnFunc, ih, varsToConstants]
    -- Porting note: below lemma does not work with simp for some reason
    rw [withConstants_funMap_sumInl]

theorem realize_constantsVarsEquivLeft [L[[α]].Structure M]
    [(lhomWithConstants L α).IsExpansionOn M] {n} {t : L[[α]].Term (β ⊕ (Fin n))} {v : β → M}
    {xs : Fin n → M} :
    (constantsVarsEquivLeft t).realize (Sum.elim (Sum.elim (fun a => ↑(L.con a)) v) xs) =
      t.realize (Sum.elim v xs) := by
  simp only [constantsVarsEquivLeft, realize_relabel, Equiv.coe_trans, Function.comp_apply,
    constantsVarsEquiv_apply, relabelEquiv_symm_apply]
  refine _root_.trans ?_ realize_constantsToVars
  congr 1; funext x -- Note: was previously rcongr x
  rcases x with (a | (b | i)) <;> simp

end Term

namespace LHom

@[simp]
theorem realize_onTerm [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
    (v : α → M) : (φ.onTerm t).realize v = t.realize v := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.realize, LHom.onTerm, LHom.map_onFunction, ih]

end LHom

@[simp]
theorem HomClass.realize_term {F : Type*} [FunLike F M N] [HomClass L F M N]
    (g : F) {t : L.Term α} {v : α → M} :
    t.realize (g ∘ v) = g (t.realize v) := by
  induction t
  · rfl
  · rw [Term.realize, Term.realize, HomClass.map_fun]
    refine congr rfl ?_
    ext x
    simp [*]

variable {n : ℕ}

namespace BoundedFormula

open Term

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
  simp [Realize]

@[simp]
theorem realize_foldr_inf (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊓ ·) ⊤).Realize v xs ↔ ∀ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp
  | cons φ l ih => simp [ih]

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v xs ↔ φ.Realize v xs → ψ.Realize v xs := by
  simp only [Realize]

/-- List.foldr on BoundedFormula.imp gives a big "And" of input conditions. -/
theorem realize_foldr_imp {k : ℕ} (l : List (L.BoundedFormula α k))
    (f : L.BoundedFormula α k) :
    ∀ (v : α → M) xs,
      (l.foldr BoundedFormula.imp f).Realize v xs =
      ((∀ i ∈ l, i.Realize v xs) → f.Realize v xs) := by
  intro v xs
  induction l
  next => simp
  next f' _ _ => by_cases f'.Realize v xs <;> simp [*]

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
  simp only [max]
  tauto

@[simp]
theorem realize_foldr_sup (l : List (L.BoundedFormula α n)) (v : α → M) (xs : Fin n → M) :
    (l.foldr (· ⊔ ·) ⊥).Realize v xs ↔ ∃ φ ∈ l, BoundedFormula.Realize φ v xs := by
  induction l with
  | nil => simp
  | cons φ l ih =>
    simp_rw [List.foldr_cons, realize_sup, ih, List.mem_cons, or_and_right, exists_or,
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
  simp only [BoundedFormula.iff, realize_inf, realize_imp, ← iff_def]

theorem realize_castLE_of_eq {m n : ℕ} (h : m = n) {h' : m ≤ n} {φ : L.BoundedFormula α m}
    {v : α → M} {xs : Fin n → M} : (φ.castLE h').Realize v xs ↔ φ.Realize v (xs ∘ Fin.cast h) := by
  subst h
  simp only [castLE_rfl, cast_refl, Function.comp_id]

theorem realize_mapTermRel_id [L'.Structure M]
    {ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin n))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n} {v : α → M}
    {v' : β → M} {xs : Fin n → M}
    (h1 :
      ∀ (n) (t : L.Term (α ⊕ (Fin n))) (xs : Fin n → M),
        (ft n t).realize (Sum.elim v' xs) = t.realize (Sum.elim v xs))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x) :
    (φ.mapTermRel ft fr fun _ => id).Realize v' xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp only [mapTermRel, Realize, ih, id]

theorem realize_mapTermRel_add_castLe [L'.Structure M] {k : ℕ}
    {ft : ∀ n, L.Term (α ⊕ (Fin n)) → L'.Term (β ⊕ (Fin (k + n)))}
    {fr : ∀ n, L.Relations n → L'.Relations n} {n} {φ : L.BoundedFormula α n}
    (v : ∀ {n}, (Fin (k + n) → M) → α → M) {v' : β → M} (xs : Fin (k + n) → M)
    (h1 :
      ∀ (n) (t : L.Term (α ⊕ (Fin n))) (xs' : Fin (k + n) → M),
        (ft n t).realize (Sum.elim v' xs') = t.realize (Sum.elim (v xs') (xs' ∘ Fin.natAdd _)))
    (h2 : ∀ (n) (R : L.Relations n) (x : Fin n → M), RelMap (fr n R) x = RelMap R x)
    (hv : ∀ (n) (xs : Fin (k + n) → M) (x : M), @v (n + 1) (snoc xs x : Fin _ → M) = v xs) :
    (φ.mapTermRel ft fr fun _ => castLE (add_assoc _ _ _).symm.le).Realize v' xs ↔
      φ.Realize (v xs) (xs ∘ Fin.natAdd _) := by
  induction φ with
  | falsum => rfl
  | equal => simp [mapTermRel, Realize, h1]
  | rel => simp [mapTermRel, Realize, h1, h2]
  | imp _ _ ih1 ih2 => simp [mapTermRel, Realize, ih1, ih2]
  | all _ ih => simp [mapTermRel, Realize, ih, hv]

@[simp]
theorem realize_relabel {m n : ℕ} {φ : L.BoundedFormula α n} {g : α → β ⊕ (Fin m)} {v : β → M}
    {xs : Fin (m + n) → M} :
    (φ.relabel g).Realize v xs ↔
      φ.Realize (Sum.elim v (xs ∘ Fin.castAdd n) ∘ g) (xs ∘ Fin.natAdd m) := by
  apply realize_mapTermRel_add_castLe <;> simp

theorem realize_liftAt {n n' m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + n') → M}
    (hmn : m + n' ≤ n + 1) :
    (φ.liftAt n' m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then Fin.castAdd n' i else Fin.addNat i n') := by
  rw [liftAt]
  induction φ with
  | falsum => simp [mapTermRel, Realize]
  | equal => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | rel => simp [mapTermRel, Realize, Sum.elim_comp_map]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, Realize, ih1 hmn, ih2 hmn]
  | @all k _ ih3 =>
    have h : k + 1 + n' = k + n' + 1 := by rw [add_assoc, add_comm 1 n', ← add_assoc]
    simp only [mapTermRel, Realize, realize_castLE_of_eq h, ih3 (hmn.trans k.succ.le_succ)]
    refine forall_congr' fun x => iff_eq_eq.mpr (congr rfl (funext (Fin.lastCases ?_ fun i => ?_)))
    · simp only [Function.comp_apply, val_last, snoc_last]
      refine (congr rfl (Fin.ext ?_)).trans (snoc_last _ _)
      split_ifs <;> dsimp; cutsat
    · simp only [Function.comp_apply, Fin.snoc_castSucc]
      refine (congr rfl (Fin.ext ?_)).trans (snoc_castSucc _ _ _)
      simp only [coe_castSucc, coe_cast]
      split_ifs <;> simp

theorem realize_liftAt_one {n m : ℕ} {φ : L.BoundedFormula α n} {v : α → M} {xs : Fin (n + 1) → M}
    (hmn : m ≤ n) :
    (φ.liftAt 1 m).Realize v xs ↔
      φ.Realize v (xs ∘ fun i => if ↑i < m then castSucc i else i.succ) := by
  simp [realize_liftAt (add_le_add_right hmn 1), castSucc]

@[simp]
theorem realize_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin (n + 1) → M} : (φ.liftAt 1 n).Realize v xs ↔ φ.Realize v (xs ∘ castSucc) := by
  rw [realize_liftAt_one (refl n), iff_eq_eq]
  refine congr rfl (congr rfl (funext fun i => ?_))
  rw [if_pos i.is_lt]

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

theorem realize_restrictFreeVar [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n}
    {f : φ.freeVarFinset → β} {v : β → M} {xs : Fin n → M}
    (v' : α → M) (hv' : ∀ a, v (f a) = v' a) :
    (φ.restrictFreeVar f).Realize v xs ↔ φ.Realize v' xs := by
  induction φ with
  | falsum => rfl
  | equal =>
    simp only [Realize, restrictFreeVar, freeVarFinset.eq_2]
    rw [realize_restrictVarLeft v' (by simp [hv']), realize_restrictVarLeft v' (by simp [hv'])]
    simp
  | rel =>
    simp only [Realize, freeVarFinset.eq_3, Finset.biUnion_val, restrictFreeVar]
    congr!
    rw [realize_restrictVarLeft v' (by simp [hv'])]
    simp
  | imp _ _ ih1 ih2 =>
    simp only [Realize, restrictFreeVar, freeVarFinset.eq_4]
    rw [ih1, ih2] <;> simp [hv']
  | all _ ih3 =>
    simp only [restrictFreeVar, Realize]
    refine forall_congr' (fun _ => ?_)
    rw [ih3]; simp [hv']

/-- A special case of `realize_restrictFreeVar`, included because we can add the `simp` attribute
to it -/
@[simp]
theorem realize_restrictFreeVar' [DecidableEq α] {n : ℕ} {φ : L.BoundedFormula α n} {s : Set α}
    (h : ↑φ.freeVarFinset ⊆ s) {v : α → M} {xs : Fin n → M} :
    (φ.restrictFreeVar (Set.inclusion h)).Realize (v ∘ (↑)) xs ↔ φ.Realize v xs :=
  realize_restrictFreeVar _ (by simp)

theorem realize_constantsVarsEquiv [L[[α]].Structure M] [(lhomWithConstants L α).IsExpansionOn M]
    {n} {φ : L[[α]].BoundedFormula β n} {v : β → M} {xs : Fin n → M} :
    (constantsVarsEquiv φ).Realize (Sum.elim (fun a => ↑(L.con a)) v) xs ↔ φ.Realize v xs := by
  refine realize_mapTermRel_id (fun n t xs => realize_constantsVarsEquivLeft) fun n R xs => ?_
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [← (lhomWithConstants L α).map_onRelation
      (Equiv.sumEmpty (L.Relations n) ((constantsOn α).Relations n) R) xs]
  rcongr
  obtain - | R := R
  · simp
  · exact isEmptyElim R

@[simp]
theorem realize_relabelEquiv {g : α ≃ β} {k} {φ : L.BoundedFormula α k} {v : β → M}
    {xs : Fin k → M} : (relabelEquiv g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs := by
  simp only [relabelEquiv, mapTermRelEquiv_apply, Equiv.coe_refl]
  refine realize_mapTermRel_id (fun n t xs => ?_) fun _ _ _ => rfl
  simp only [relabelEquiv_apply, Term.realize_relabel]
  refine congr (congr rfl ?_) rfl
  ext (i | i) <;> rfl

variable [Nonempty M]

theorem realize_all_liftAt_one_self {n : ℕ} {φ : L.BoundedFormula α n} {v : α → M}
    {xs : Fin n → M} : (φ.liftAt 1 n).all.Realize v xs ↔ φ.Realize v xs := by
  simp

end BoundedFormula

namespace LHom

open BoundedFormula

@[simp]
theorem realize_onBoundedFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] {n : ℕ}
    (ψ : L.BoundedFormula α n) {v : α → M} {xs : Fin n → M} :
    (φ.onBoundedFormula ψ).Realize v xs ↔ ψ.Realize v xs := by
  induction ψ with
  | falsum => rfl
  | equal => simp only [onBoundedFormula, realize_bdEqual, realize_onTerm]; rfl
  | rel =>
    simp only [onBoundedFormula, realize_rel, LHom.map_onRelation,
      Function.comp_apply, realize_onTerm]
    rfl
  | imp _ _ ih1 ih2 => simp only [onBoundedFormula, ih1, ih2, realize_imp]
  | all _ ih3 => simp only [onBoundedFormula, ih3, realize_all]

end LHom

namespace Formula

/-- A formula can be evaluated as true or false by giving values to each free variable. -/
nonrec def Realize (φ : L.Formula α) (v : α → M) : Prop :=
  φ.Realize v default

variable {φ ψ : L.Formula α} {v : α → M}

@[simp]
theorem realize_not : φ.not.Realize v ↔ ¬φ.Realize v :=
  Iff.rfl

@[simp]
theorem realize_bot : (⊥ : L.Formula α).Realize v ↔ False :=
  Iff.rfl

@[simp]
theorem realize_top : (⊤ : L.Formula α).Realize v ↔ True :=
  BoundedFormula.realize_top

@[simp]
theorem realize_inf : (φ ⊓ ψ).Realize v ↔ φ.Realize v ∧ ψ.Realize v :=
  BoundedFormula.realize_inf

@[simp]
theorem realize_imp : (φ.imp ψ).Realize v ↔ φ.Realize v → ψ.Realize v :=
  BoundedFormula.realize_imp

@[simp]
theorem realize_rel {k : ℕ} {R : L.Relations k} {ts : Fin k → L.Term α} :
    (R.formula ts).Realize v ↔ RelMap R fun i => (ts i).realize v :=
  BoundedFormula.realize_rel.trans (by simp)

@[simp]
theorem realize_rel₁ {R : L.Relations 1} {t : L.Term _} :
    (R.formula₁ t).Realize v ↔ RelMap R ![t.realize v] := by
  rw [Relations.formula₁, realize_rel, iff_eq_eq]
  refine congr rfl (funext fun _ => ?_)
  simp only [Matrix.cons_val_fin_one]

@[simp]
theorem realize_rel₂ {R : L.Relations 2} {t₁ t₂ : L.Term _} :
    (R.formula₂ t₁ t₂).Realize v ↔ RelMap R ![t₁.realize v, t₂.realize v] := by
  rw [Relations.formula₂, realize_rel, iff_eq_eq]
  refine congr rfl (funext (Fin.cases ?_ ?_))
  · simp only [Matrix.cons_val_zero]
  · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, forall_const]

@[simp]
theorem realize_sup : (φ ⊔ ψ).Realize v ↔ φ.Realize v ∨ ψ.Realize v :=
  BoundedFormula.realize_sup

@[simp]
theorem realize_iff : (φ.iff ψ).Realize v ↔ (φ.Realize v ↔ ψ.Realize v) :=
  BoundedFormula.realize_iff

@[simp]
theorem realize_relabel {φ : L.Formula α} {g : α → β} {v : β → M} :
    (φ.relabel g).Realize v ↔ φ.Realize (v ∘ g) := by
  rw [Realize, Realize, relabel, BoundedFormula.realize_relabel, iff_eq_eq, Fin.castAdd_zero]
  exact congr rfl (funext finZeroElim)

theorem realize_relabel_sumInr (φ : L.Formula (Fin n)) {v : Empty → M} {x : Fin n → M} :
    (BoundedFormula.relabel Sum.inr φ).Realize v x ↔ φ.Realize x := by
  rw [BoundedFormula.realize_relabel, Formula.Realize, Sum.elim_comp_inr, Fin.castAdd_zero,
    cast_refl, Function.comp_id,
    Subsingleton.elim (x ∘ (natAdd n : Fin 0 → Fin n)) default]

@[simp]
theorem realize_equal {t₁ t₂ : L.Term α} {x : α → M} :
    (t₁.equal t₂).Realize x ↔ t₁.realize x = t₂.realize x := by simp [Term.equal, Realize]

@[simp]
theorem realize_graph {f : L.Functions n} {x : Fin n → M} {y : M} :
    (Formula.graph f).Realize (Fin.cons y x : _ → M) ↔ funMap f x = y := by
  simp only [Formula.graph, Term.realize, realize_equal, Fin.cons_zero, Fin.cons_succ]
  rw [eq_comm]

theorem boundedFormula_realize_eq_realize (φ : L.Formula α) (x : α → M) (y : Fin 0 → M) :
    BoundedFormula.Realize φ x y ↔ φ.Realize x := by
  rw [Formula.Realize, iff_iff_eq]
  congr
  ext i; exact Fin.elim0 i

end Formula

@[simp]
theorem LHom.realize_onFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (ψ : L.Formula α)
    {v : α → M} : (φ.onFormula ψ).Realize v ↔ ψ.Realize v :=
  φ.realize_onBoundedFormula ψ

@[simp]
theorem LHom.setOf_realize_onFormula [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Formula α) : (setOf (φ.onFormula ψ).Realize : Set (α → M)) = setOf ψ.Realize := by
  ext
  simp

variable (M)

/-- A sentence can be evaluated as true or false in a structure. -/
nonrec def Sentence.Realize (φ : L.Sentence) : Prop :=
  φ.Realize (default : _ → M)

-- input using \|= or \vDash, but not using \models
@[inherit_doc Sentence.Realize]
infixl:51 " ⊨ " => Sentence.Realize

@[simp]
theorem Sentence.realize_not {φ : L.Sentence} : M ⊨ φ.not ↔ ¬M ⊨ φ :=
  Iff.rfl

namespace Formula

@[simp]
theorem realize_equivSentence_symm_con [L[[α]].Structure M]
    [(L.lhomWithConstants α).IsExpansionOn M] (φ : L[[α]].Sentence) :
    ((equivSentence.symm φ).Realize fun a => (L.con a : M)) ↔ φ.Realize M := by
  simp only [equivSentence, _root_.Equiv.symm_symm, Equiv.coe_trans, Realize,
    BoundedFormula.realize_relabelEquiv, Function.comp]
  refine _root_.trans ?_ BoundedFormula.realize_constantsVarsEquiv
  rw [iff_iff_eq]
  congr 1 with (_ | a)
  · simp
  · cases a

@[simp]
theorem realize_equivSentence [L[[α]].Structure M] [(L.lhomWithConstants α).IsExpansionOn M]
    (φ : L.Formula α) : (equivSentence φ).Realize M ↔ φ.Realize fun a => (L.con a : M) := by
  rw [← realize_equivSentence_symm_con M (equivSentence φ), _root_.Equiv.symm_apply_apply]

theorem realize_equivSentence_symm (φ : L[[α]].Sentence) (v : α → M) :
    (equivSentence.symm φ).Realize v ↔
      @Sentence.Realize _ M (@Language.withConstantsStructure L M _ α (constantsOn.structure v))
        φ :=
  letI := constantsOn.structure v
  realize_equivSentence_symm_con M φ

end Formula

@[simp]
theorem LHom.realize_onSentence [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (ψ : L.Sentence) : M ⊨ φ.onSentence ψ ↔ M ⊨ ψ :=
  φ.realize_onFormula ψ

variable (L)

/-- The complete theory of a structure `M` is the set of all sentences `M` satisfies. -/
def completeTheory : L.Theory :=
  { φ | M ⊨ φ }

variable (N)

/-- Two structures are elementarily equivalent when they satisfy the same sentences. -/
def ElementarilyEquivalent : Prop :=
  L.completeTheory M = L.completeTheory N

@[inherit_doc FirstOrder.Language.ElementarilyEquivalent]
scoped[FirstOrder]
  notation:25 A " ≅[" L "] " B:50 => FirstOrder.Language.ElementarilyEquivalent L A B

variable {L} {M} {N}

@[simp]
theorem mem_completeTheory {φ : Sentence L} : φ ∈ L.completeTheory M ↔ M ⊨ φ :=
  Iff.rfl

theorem elementarilyEquivalent_iff : M ≅[L] N ↔ ∀ φ : L.Sentence, M ⊨ φ ↔ N ⊨ φ := by
  simp only [ElementarilyEquivalent, Set.ext_iff, completeTheory, Set.mem_setOf_eq]

variable (M)

/-- A model of a theory is a structure in which every sentence is realized as true. -/
class Theory.Model (T : L.Theory) : Prop where
  realize_of_mem : ∀ φ ∈ T, M ⊨ φ

-- input using \|= or \vDash, but not using \models
@[inherit_doc Theory.Model]
infixl:51 " ⊨ " => Theory.Model

variable {M} (T : L.Theory)

@[simp default - 10]
theorem Theory.model_iff : M ⊨ T ↔ ∀ φ ∈ T, M ⊨ φ :=
  ⟨fun h => h.realize_of_mem, fun h => ⟨h⟩⟩

theorem Theory.realize_sentence_of_mem [M ⊨ T] {φ : L.Sentence} (h : φ ∈ T) : M ⊨ φ :=
  Theory.Model.realize_of_mem φ h

@[simp]
theorem LHom.onTheory_model [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M] (T : L.Theory) :
    M ⊨ φ.onTheory T ↔ M ⊨ T := by simp [Theory.model_iff, LHom.onTheory]

variable {T}

instance model_empty : M ⊨ (∅ : L.Theory) :=
  ⟨fun φ hφ => (Set.notMem_empty φ hφ).elim⟩

namespace Theory

theorem Model.mono {T' : L.Theory} (_h : M ⊨ T') (hs : T ⊆ T') : M ⊨ T :=
  ⟨fun _φ hφ => T'.realize_sentence_of_mem (hs hφ)⟩

theorem Model.union {T' : L.Theory} (h : M ⊨ T) (h' : M ⊨ T') : M ⊨ T ∪ T' := by
  simp only [model_iff, Set.mem_union] at *
  exact fun φ hφ => hφ.elim (h _) (h' _)

@[simp]
theorem model_union_iff {T' : L.Theory} : M ⊨ T ∪ T' ↔ M ⊨ T ∧ M ⊨ T' :=
  ⟨fun h => ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩, fun h =>
    h.1.union h.2⟩

@[simp]
theorem model_singleton_iff {φ : L.Sentence} : M ⊨ ({φ} : L.Theory) ↔ M ⊨ φ := by simp

theorem model_insert_iff {φ : L.Sentence} : M ⊨ insert φ T ↔ M ⊨ φ ∧ M ⊨ T := by
  rw [Set.insert_eq, model_union_iff, model_singleton_iff]

theorem model_iff_subset_completeTheory : M ⊨ T ↔ T ⊆ L.completeTheory M :=
  T.model_iff

theorem completeTheory.subset [MT : M ⊨ T] : T ⊆ L.completeTheory M :=
  model_iff_subset_completeTheory.1 MT

end Theory

instance model_completeTheory : M ⊨ L.completeTheory M :=
  Theory.model_iff_subset_completeTheory.2 (subset_refl _)

variable (M N)

theorem realize_iff_of_model_completeTheory [N ⊨ L.completeTheory M] (φ : L.Sentence) :
    N ⊨ φ ↔ M ⊨ φ := by
  refine ⟨fun h => ?_, (L.completeTheory M).realize_sentence_of_mem⟩
  contrapose! h
  rw [← Sentence.realize_not] at *
  exact (L.completeTheory M).realize_sentence_of_mem (mem_completeTheory.2 h)

variable {M N}

namespace BoundedFormula

@[simp]
theorem realize_alls {φ : L.BoundedFormula α n} {v : α → M} :
    φ.alls.Realize v ↔ ∀ xs : Fin n → M, φ.Realize v xs := by
  induction n with
  | zero => exact Unique.forall_iff.symm
  | succ n ih =>
    simp only [alls, ih, Realize]
    exact ⟨fun h xs => Fin.snoc_init_self xs ▸ h _ _, fun h xs x => h (Fin.snoc xs x)⟩

@[simp]
theorem realize_exs {φ : L.BoundedFormula α n} {v : α → M} :
    φ.exs.Realize v ↔ ∃ xs : Fin n → M, φ.Realize v xs := by
  induction n with
  | zero => exact Unique.exists_iff.symm
  | succ n ih =>
    simp only [BoundedFormula.exs, ih, realize_ex]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨_, h⟩
    · rintro ⟨xs, h⟩
      rw [← Fin.snoc_init_self xs] at h
      exact ⟨_, _, h⟩

@[simp]
theorem _root_.FirstOrder.Language.Formula.realize_iAlls
    [Finite β] {φ : L.Formula (α ⊕ β)} {v : α → M} : (φ.iAlls β).Realize v ↔
      ∀ (i : β → M), φ.Realize (fun a => Sum.elim v i a) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin β))
  rw [Formula.iAlls]
  simp only [Nat.add_zero, realize_alls, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.forall_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
theorem realize_iAlls [Finite β] {φ : L.Formula (α ⊕ β)} {v : α → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iAlls β) v v' ↔
      ∀ (i : β → M), φ.Realize (fun a => Sum.elim v i a) := by
  rw [← Formula.realize_iAlls, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
theorem _root_.FirstOrder.Language.Formula.realize_iExs
    [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : α → M} : (φ.iExs γ).Realize v ↔
      ∃ (i : γ → M), φ.Realize (Sum.elim v i) := by
  let e := Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin γ))
  rw [Formula.iExs]
  simp only [Nat.add_zero, realize_exs, realize_relabel, Function.comp_def,
    castAdd_zero, Sum.elim_map, id_eq]
  refine Equiv.exists_congr ?_ ?_
  · exact ⟨fun v => v ∘ e, fun v => v ∘ e.symm,
      fun _ => by simp [Function.comp_def],
      fun _ => by simp [Function.comp_def]⟩
  · intro x
    rw [Formula.Realize, iff_iff_eq]
    congr
    funext i
    exact i.elim0

@[simp]
theorem realize_iExs [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : α → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iExs γ) v v' ↔
      ∃ (i : γ → M), φ.Realize (Sum.elim v i) := by
  rw [← Formula.realize_iExs, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

@[simp]
theorem realize_toFormula (φ : L.BoundedFormula α n) (v : α ⊕ (Fin n) → M) :
    φ.toFormula.Realize v ↔ φ.Realize (v ∘ Sum.inl) (v ∘ Sum.inr) := by
  induction φ with
  | falsum => rfl
  | equal => simp [BoundedFormula.Realize]
  | rel => simp [BoundedFormula.Realize]
  | imp _ _ ih1 ih2 =>
    rw [toFormula, Formula.Realize, realize_imp, ← Formula.Realize, ih1, ← Formula.Realize, ih2,
      realize_imp]
  | all _ ih3 =>
    rw [toFormula, Formula.Realize, realize_all, realize_all]
    refine forall_congr' fun a => ?_
    have h := ih3 (Sum.elim (v ∘ Sum.inl) (snoc (v ∘ Sum.inr) a))
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
    rw [← h, realize_relabel, Formula.Realize, iff_iff_eq]
    simp only [Function.comp_def]
    congr with x
    · rcases x with _ | x
      · simp
      · refine Fin.lastCases ?_ ?_ x
        · simp [Fin.snoc]
        · simp only [castSucc, Sum.elim_inr,
            finSumFinEquiv_symm_apply_castAdd, Sum.map_inl, Sum.elim_inl]
          rw [← castSucc]
          simp
    · exact Fin.elim0 x

@[simp]
theorem realize_iSup [Finite β] {f : β → L.BoundedFormula α n}
    {v : α → M} {v' : Fin n → M} :
    (iSup f).Realize v v' ↔ ∃ b, (f b).Realize v v' := by
  simp only [iSup, realize_foldr_sup, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    exists_exists_eq_and]

@[simp]
theorem realize_iInf [Finite β] {f : β → L.BoundedFormula α n}
    {v : α → M} {v' : Fin n → M} :
    (iInf f).Realize v v' ↔ ∀ b, (f b).Realize v v' := by
  simp only [iInf, realize_foldr_inf, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]

@[simp]
theorem _root_.FirstOrder.Language.Formula.realize_iSup [Finite β] {f : β → L.Formula α}
    {v : α → M} : (Formula.iSup f).Realize v ↔ ∃ b, (f b).Realize v := by
  simp [Formula.iSup, Formula.Realize]

@[simp]
theorem _root_.FirstOrder.Language.Formula.realize_iInf [Finite β] {f : β → L.Formula α}
    {v : α → M} : (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v := by
  simp [Formula.iInf, Formula.Realize]

theorem _root_.FirstOrder.Language.Formula.realize_iExsUnique [Finite γ]
    {φ : L.Formula (α ⊕ γ)} {v : α → M} : (φ.iExsUnique γ).Realize v ↔
      ∃! (i : γ → M), φ.Realize (Sum.elim v i) := by
  rw [Formula.iExsUnique, ExistsUnique]
  simp only [Formula.realize_iExs, Formula.realize_inf, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_relabel]
  simp only [Formula.Realize, Function.comp_def, Term.equal, Term.relabel, realize_iInf,
    realize_bdEqual, Term.realize_var, Sum.elim_inl, Sum.elim_inr, funext_iff]
  refine exists_congr (fun i => and_congr_right' (forall_congr' (fun y => ?_)))
  rw [iff_iff_eq]; congr with x
  cases x <;> simp

@[simp]
theorem realize_iExsUnique [Finite γ] {φ : L.Formula (α ⊕ γ)} {v : α → M} {v' : Fin 0 → M} :
    BoundedFormula.Realize (φ.iExsUnique γ) v v' ↔
      ∃! (i : γ → M), φ.Realize (Sum.elim v i) := by
  rw [← Formula.realize_iExsUnique, iff_iff_eq]; congr; simp [eq_iff_true_of_subsingleton]

end BoundedFormula

namespace StrongHomClass

variable {F : Type*} [EquivLike F M N] [StrongHomClass L F M N] (g : F)

@[simp]
theorem realize_boundedFormula (φ : L.BoundedFormula α n) {v : α → M}
    {xs : Fin n → M} : φ.Realize (g ∘ v) (g ∘ xs) ↔ φ.Realize v xs := by
  induction φ with
  | falsum => rfl
  | equal =>
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term,
      EmbeddingLike.apply_eq_iff_eq g]
  | rel =>
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    exact StrongHomClass.map_rel g _ _
  | imp _ _ ih1 ih2 => rw [BoundedFormula.Realize, ih1, ih2, BoundedFormula.Realize]
  | all _ ih3 =>
    rw [BoundedFormula.Realize, BoundedFormula.Realize]
    constructor
    · intro h a
      have h' := h (g a)
      rw [← Fin.comp_snoc, ih3] at h'
      exact h'
    · intro h a
      have h' := h (EquivLike.inv g a)
      rw [← ih3, Fin.comp_snoc, EquivLike.apply_inv_apply g] at h'
      exact h'

@[simp]
theorem realize_formula (φ : L.Formula α) {v : α → M} :
    φ.Realize (g ∘ v) ↔ φ.Realize v := by
  rw [Formula.Realize, Formula.Realize, ← realize_boundedFormula g φ, iff_eq_eq,
    Unique.eq_default (g ∘ default)]

include g

theorem realize_sentence (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize, Sentence.Realize, ← realize_formula g,
    Unique.eq_default (g ∘ default)]

theorem theory_model [M ⊨ T] : N ⊨ T :=
  ⟨fun φ hφ => (realize_sentence g φ).1 (Theory.realize_sentence_of_mem T hφ)⟩

theorem elementarilyEquivalent : M ≅[L] N :=
  elementarilyEquivalent_iff.2 (realize_sentence g)

end StrongHomClass

namespace Relations

open BoundedFormula

variable {r : L.Relations 2}

@[simp]
theorem realize_reflexive : M ⊨ r.reflexive ↔ Reflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => realize_rel₂

@[simp]
theorem realize_irreflexive : M ⊨ r.irreflexive ↔ Irreflexive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => not_congr realize_rel₂

@[simp]
theorem realize_symmetric : M ⊨ r.symmetric ↔ Symmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ => forall_congr' fun _ => imp_congr realize_rel₂ realize_rel₂

@[simp]
theorem realize_antisymmetric :
    M ⊨ r.antisymmetric ↔ AntiSymmetric fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ Iff.rfl)

@[simp]
theorem realize_transitive : M ⊨ r.transitive ↔ Transitive fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ =>
      forall_congr' fun _ => imp_congr realize_rel₂ (imp_congr realize_rel₂ realize_rel₂)

@[simp]
theorem realize_total : M ⊨ r.total ↔ Total fun x y : M => RelMap r ![x, y] :=
  forall_congr' fun _ =>
    forall_congr' fun _ => realize_sup.trans (or_congr realize_rel₂ realize_rel₂)

end Relations

section Cardinality

variable (L)
@[simp]
theorem Sentence.realize_cardGe (n) : M ⊨ Sentence.cardGe L n ↔ ↑n ≤ #M := by
  rw [← lift_mk_fin, ← lift_le.{0}, lift_lift, lift_mk_le, Sentence.cardGe, Sentence.Realize,
    BoundedFormula.realize_exs]
  simp_rw [BoundedFormula.realize_foldr_inf]
  simp only [Function.comp_apply, List.mem_map, Prod.exists, Ne, List.mem_product,
    List.mem_finRange, forall_exists_index, and_imp, List.mem_filter, true_and]
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

@[simp]
theorem model_infiniteTheory_iff : M ⊨ L.infiniteTheory ↔ Infinite M := by
  simp [infiniteTheory, infinite_iff, aleph0_le]

instance model_infiniteTheory [h : Infinite M] : M ⊨ L.infiniteTheory :=
  L.model_infiniteTheory_iff.2 h

@[simp]
theorem model_nonemptyTheory_iff : M ⊨ L.nonemptyTheory ↔ Nonempty M := by
  simp only [nonemptyTheory, Theory.model_iff, Set.mem_singleton_iff, forall_eq,
    Sentence.realize_cardGe, Nat.cast_one, one_le_iff_ne_zero, mk_ne_zero_iff]

instance model_nonempty [h : Nonempty M] : M ⊨ L.nonemptyTheory :=
  L.model_nonemptyTheory_iff.2 h

theorem model_distinctConstantsTheory {M : Type w} [L[[α]].Structure M] (s : Set α) :
    M ⊨ L.distinctConstantsTheory s ↔ Set.InjOn (fun i : α => (L.con i : M)) s := by
  simp only [distinctConstantsTheory, Theory.model_iff, Set.mem_image,
    Prod.exists, forall_exists_index, and_imp]
  refine ⟨fun h a as b bs ab => ?_, ?_⟩
  · contrapose! ab
    have h' := h _ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal,
      Term.realize_constants] at h'
    exact h'
  · rintro h φ a b ⟨⟨as, bs⟩, ab⟩ rfl
    simp only [Sentence.Realize, Formula.realize_not, Formula.realize_equal, Term.realize_constants]
    exact fun contra => ab (h as bs contra)

theorem card_le_of_model_distinctConstantsTheory (s : Set α) (M : Type w) [L[[α]].Structure M]
    [h : M ⊨ L.distinctConstantsTheory s] : Cardinal.lift.{w} #s ≤ Cardinal.lift.{u'} #M :=
  lift_mk_le'.2 ⟨⟨_, Set.injOn_iff_injective.1 ((L.model_distinctConstantsTheory s).1 h)⟩⟩

end Cardinality

namespace ElementarilyEquivalent

@[symm]
nonrec theorem symm (h : M ≅[L] N) : N ≅[L] M :=
  h.symm

@[trans]
nonrec theorem trans (MN : M ≅[L] N) (NP : N ≅[L] P) : M ≅[L] P :=
  MN.trans NP

theorem completeTheory_eq (h : M ≅[L] N) : L.completeTheory M = L.completeTheory N :=
  h

theorem realize_sentence (h : M ≅[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ :=
  (elementarilyEquivalent_iff.1 h) φ

theorem theory_model_iff (h : M ≅[L] N) : M ⊨ T ↔ N ⊨ T := by
  rw [Theory.model_iff_subset_completeTheory, Theory.model_iff_subset_completeTheory,
    h.completeTheory_eq]

theorem theory_model [MT : M ⊨ T] (h : M ≅[L] N) : N ⊨ T :=
  h.theory_model_iff.1 MT

theorem nonempty_iff (h : M ≅[L] N) : Nonempty M ↔ Nonempty N :=
  (model_nonemptyTheory_iff L).symm.trans (h.theory_model_iff.trans (model_nonemptyTheory_iff L))

theorem nonempty [Mn : Nonempty M] (h : M ≅[L] N) : Nonempty N :=
  h.nonempty_iff.1 Mn

theorem infinite_iff (h : M ≅[L] N) : Infinite M ↔ Infinite N :=
  (model_infiniteTheory_iff L).symm.trans (h.theory_model_iff.trans (model_infiniteTheory_iff L))

theorem infinite [Mi : Infinite M] (h : M ≅[L] N) : Infinite N :=
  h.infinite_iff.1 Mi

end ElementarilyEquivalent

end Language

end FirstOrder
