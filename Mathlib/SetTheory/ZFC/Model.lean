/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.ModelTheory.Semantics
import Mathlib.SetTheory.ZFC.Axioms
import Mathlib.SetTheory.ZFC.Class
set_option linter.style.header false
set_option linter.directoryDependency false

/-!
# Models of the theory of ZFC

This file defines the (Lean-internal) structures for models of (parts of) ZFC, and shows that these
structures satisfy (parts of) the axioms of ZFC, defined in
`FirstOrder.Set.ZFC` in `Mathlib.SetTheory.ZFC.Axioms.lean`.

## Main definitions

* `SetModel.Ext`: A type with an extensional equality, membership relation, and subset relation.
* `SetModel.BasicOp`: A type with basic set operations: singleton, insert, union, powerset, and
  arbitrary union.
* `SetModel.SimpleOp`: A type with basic set operations, empty set, and intersection.
* `SetModel.Inductive`: A type containing an inductive set.
* `SetModel.Regular`: A type with a well-founded membership relation.
* `SetModel.Choice`: A type with a choice function.
* `SetModel.SepRepl`: A type with a separation and replacement operation.
* `SetModel.ZF`: A type with all the axioms of ZF.
* `SetModel.ZFCWithoutInfinity`: A type with all the axioms of ZFC without infinity.
* `SetModel.ZFC`: A type with all the axioms of ZFC.

## Main results

* `ZFSet.ZFSet_model_ZFC`: The model `ZFSet` satisfies the axioms of ZFC.

-/

universe u u' v v' w

@[simp] lemma comp_vecCons {α β : Type*} {n : ℕ} (f : Fin n → α) (x : α) (g : α → β) :
    g ∘ Matrix.vecCons x f = Matrix.vecCons (g x) (g ∘ f) := by
  ext i; cases i using Fin.cases <;> simp

@[simp] lemma comp_vecEmpty {α β : Type*} {g : α → β} :
    g ∘ Matrix.vecEmpty = Matrix.vecEmpty :=
  funext nofun

namespace FirstOrder.Language.BoundedFormula

@[simp] lemma falsum_eq_bot {L : Language} (α : Type u) (n : ℕ) :
    (falsum : L.BoundedFormula α n) = ⊥ := rfl

@[simp] lemma equal_eq_bdEqual {L : Language} (α : Type u) (n : ℕ) (x y : L.Term (α ⊕ Fin n)) :
    equal x y = x =' y := rfl

@[simp] lemma rel_eq_rel {L : Language} {α : Type u} {n k : ℕ} (R : L.Relations n)
    (v : Fin n → L.Term (α ⊕ Fin k)) :
    rel R v = R.boundedFormula v := rfl

@[elab_as_elim] def rec' {L : Language} {α : Type u} {C : (n : ℕ) → L.BoundedFormula α n → Sort*}
    (bot : ∀ n, C n ⊥) (eq : ∀ {n} (x y : L.Term (α ⊕ Fin n)), C n (x =' y))
    (rel' : ∀ {n k} (R : L.Relations n) (v : Fin n → L.Term (α ⊕ Fin k)), C k (R.boundedFormula v))
    (imp' : ∀ {n} (φ ψ : L.BoundedFormula α n), C n φ → C n ψ → C n (φ ⟹ ψ))
    (all' : ∀ {n} (φ : L.BoundedFormula α (n + 1)), C (n + 1) φ → C n (∀' φ))
    {n : ℕ} (φ : L.BoundedFormula α n) : C n φ :=
  match φ with
  | ⊥ => bot n
  | equal x y => eq x y
  | rel R v => rel' R v
  | imp φ ψ => imp' φ ψ (rec' bot eq rel' imp' all' φ) (rec' bot eq rel' imp' all' ψ)
  | all φ => all' φ (rec' bot eq rel' imp' all' φ)


section castLE

variable {L : Language} {α : Type u'} {m n k : ℕ} (e : m ≤ n)
  (φ₁ φ₂ : L.BoundedFormula α m) (φ : L.BoundedFormula α (m + 1))

@[simp] lemma castLE_bot : castLE e (⊥ : L.BoundedFormula α m) = ⊥ := rfl

@[simp] lemma castLE_equal (x y : L.Term (α ⊕ Fin m)) :
    castLE e (x =' y) =
      x.relabel (Sum.map id <| Fin.castLE e) =' y.relabel (Sum.map id <| Fin.castLE e) := rfl

@[simp] lemma castLE_rel (R : L.Relations k) (v : Fin k → L.Term (α ⊕ Fin m)) :
    castLE e (R.boundedFormula v) =
      R.boundedFormula (fun i ↦ (v i).relabel (Sum.map id <| Fin.castLE e)) := rfl

@[simp] lemma castLE_imp : castLE e (φ₁ ⟹ φ₂) = castLE e φ₁ ⟹ castLE e φ₂ := rfl

@[simp] lemma castLE_all : castLE e (∀' φ) = ∀' (castLE (by simp [e]) φ) := rfl

end castLE


section mapTermRel

variable {L : Language} {L' : Language} {α : Type u'} {β : Type v'} {g : ℕ → ℕ}
  (ft : (n : ℕ) → L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin (g n)))
  (fr : (n : ℕ) → L.Relations n → L'.Relations n)
  (h : (n : ℕ) → L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1)) {n k : ℕ}

@[simp] lemma mapTermRel_bot : mapTermRel ft fr h (⊥ : L.BoundedFormula α n) = ⊥ := rfl

@[simp] lemma mapTermRel_equal (x y : L.Term (α ⊕ Fin n)) :
    mapTermRel ft fr h (x =' y : L.BoundedFormula α n) = ft n x =' ft n y := rfl

@[simp] lemma mapTermRel_rel (R : L.Relations n) (v : Fin n → L.Term (α ⊕ Fin k)) :
    mapTermRel ft fr h (R.boundedFormula v) = (fr n R).boundedFormula (ft k ∘ v) := rfl

lemma mapTermRel_mapTermRel' {L L' L'' : Language} {α β γ : Type*} {k l x : ℕ}
    (ft : (n : ℕ) → L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin (k + n)))
    (ft' : (n : ℕ) → L'.Term (β ⊕ Fin n) → L''.Term (γ ⊕ Fin (l + n)))
    (fr : (n : ℕ) → L.Relations n → L'.Relations n)
    (fr' : (n : ℕ) → L'.Relations n → L''.Relations n)
    (φ : L.BoundedFormula α x) :
    mapTermRel ft' fr' (fun _ ↦ id) (mapTermRel ft fr (fun _ ↦ id) φ) =
      castLE (by simp [add_assoc])
      (mapTermRel (g := fun n ↦ (l + k) + n)
        (fun x ↦ (Term.relabel (Sum.map id (Fin.cast (by simp [add_assoc])))) ∘ ft' _ ∘ ft x)
        (fun x ↦ fr' x ∘ fr x) (fun _ ↦ id) φ) := by
  induction φ using rec' with
  | bot => simp
  | eq x y => simp [Function.comp_def, Fin.castLE, ← Function.id_def]
  | rel' R v => simp [Function.comp_def, Fin.castLE, ← Function.id_def]
  | imp' φ ψ ihφ ihψ => simp [mapTermRel, ihφ, ihψ]
  | all' φ ih => simp [mapTermRel, ih]

lemma mapTermRel_mapTermRel'' {L L' L'' : Language} {α β γ : Type*} {k : ℕ}
    (ft : (n : ℕ) → L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin (k + n)))
    (ft' : (n : ℕ) → L'.Term (β ⊕ Fin n) → L''.Term (γ ⊕ Fin n))
    (fr : (n : ℕ) → L.Relations n → L'.Relations n)
    (fr' : (n : ℕ) → L'.Relations n → L''.Relations n)
    (φ : L.BoundedFormula α n) :
    mapTermRel ft' fr' (fun _ ↦ id) (mapTermRel ft fr (fun _ ↦ id) φ) =
      mapTermRel (fun x ↦ ft' _ ∘ ft x) (fun x ↦ fr' x ∘ fr x) (fun _ ↦ id) φ := by
  induction φ using rec' with
  | bot => simp
  | eq x y => simp
  | rel' R v => simp [Function.comp_assoc]
  | imp' φ ψ ihφ ihψ => simp [mapTermRel, ihφ, ihψ]
  | all' φ ih => simp [mapTermRel, ih]

lemma mapTermRel_mapTermRel''' {L L' L'' : Language} {α β γ : Type*} {l : ℕ}
    (ft : (n : ℕ) → L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin n))
    (ft' : (n : ℕ) → L'.Term (β ⊕ Fin n) → L''.Term (γ ⊕ Fin (l + n)))
    (fr : (n : ℕ) → L.Relations n → L'.Relations n)
    (fr' : (n : ℕ) → L'.Relations n → L''.Relations n)
    (φ : L.BoundedFormula α n) :
    mapTermRel ft' fr' (fun _ ↦ id) (mapTermRel ft fr (fun _ ↦ id) φ) =
      mapTermRel (fun x ↦ ft' _ ∘ ft x) (fun x ↦ fr' x ∘ fr x) (fun _ ↦ id) φ := by
  induction φ using rec' with
  | bot => simp
  | eq x y => simp
  | rel' R v => simp [Function.comp_assoc]
  | imp' φ ψ ihφ ihψ => simp [mapTermRel, ihφ, ihψ]
  | all' φ ih => simp [mapTermRel, ih]

end mapTermRel


section toFormula

variable {L : Language} {α : Type u'} {n k : ℕ}

@[simp] lemma toFormula_bot : (⊥ : L.BoundedFormula α n).toFormula = ⊥ := rfl

@[simp] lemma toFormula_equal (x y : L.Term (α ⊕ Fin n)) :
    (x =' y : L.BoundedFormula α n).toFormula = x.equal y := rfl

@[simp] lemma toFormula_rel (R : L.Relations n) (v : Fin n → L.Term (α ⊕ Fin k)) :
    (R.boundedFormula v).toFormula = R.formula v := rfl

end toFormula


@[simp] lemma Term.subst_relabel {L : Language} {α β γ : Type*} (f : α → β) (g : β → L.Term γ)
    (t : L.Term α) : (t.relabel f).subst g = t.subst (g ∘ f) := by
  induction t
  · rfl
  · simp [*]

@[simp] lemma Term.relabel_subst {L : Language} {α β γ : Type*} (f : α → L.Term β) (g : β → γ)
    (t : L.Term α) : (t.subst f).relabel g = t.subst (Term.relabel g ∘ f) := by
  induction t
  · rfl
  · simp [*]

@[simp] lemma Term.relabel_id {L : Language} {α : Type*} (t : L.Term α) :
    t.relabel id = t := by
  induction t
  · rfl
  · simp [*]

@[simp] lemma Term.relabel_id' {L : Language} {α : Type*} (t : L.Term α) :
    t.relabel (fun x ↦ x) = t :=
  Term.relabel_id t


section relabel

variable {L : Language} {α β : Type*} {n : ℕ} (f : α → β ⊕ Fin n) {k l : ℕ}
  (φ : L.BoundedFormula α k)

-- REPLACE RELABEL'S DEFINITION
lemma relabel_def : relabel f φ =
      φ.mapTermRel (fun x ↦ Term.relabel (relabelAux f x)) (fun _ ↦ id) fun _ ↦ id := by
  delta relabel; congr 1; ext x; exact castLE_rfl _ _

@[simp] lemma relabelAux_inl (k : ℕ) (i : α) :
    relabelAux f k (Sum.inl i) = Sum.map id (Fin.castAdd k) (f i) := by
  generalize h : f i = j; cases j <;> simp [relabelAux, h]

@[simp] lemma relabelAux_comp_inl :
    relabelAux f k ∘ Sum.inl = Sum.map id (Fin.castAdd k) ∘ f :=
  funext <| relabelAux_inl f k

@[simp] lemma relabel_equal (x y : L.Term (α ⊕ Fin k)) : relabel f (x =' y) =
      x.relabel (relabelAux f k) =' y.relabel (relabelAux f k) := rfl

@[simp] lemma relabel_rel (R : L.Relations k) (v : Fin k → L.Term (α ⊕ Fin l)) :
    relabel f (R.boundedFormula v) =
      R.boundedFormula (fun i ↦ (v i).relabel (relabelAux f l)) := rfl

end relabel


@[simp] lemma realize_liftAt' {L : Language} {M : Type u}
    [L.Structure M] {α : Type v} {n n' m : ℕ} {φ : L.BoundedFormula α n}
    {v : α → M} {p : Fin (n + n') → M} (hmn : m ≤ n) :
    (φ.liftAt n' m).Realize v p ↔
      φ.Realize v (p ∘ fun i ↦ if i.1 < m then i.castAdd n' else i.addNat n') := by
  delta liftAt
  induction φ
  · simp
  · simp [Sum.elim_comp_map]
  · simp [Sum.elim_comp_map]
  · simp [mapTermRel, Realize, *]
  case all n _ ih =>
    rw [mapTermRel, Realize, Realize]
    simp_rw [realize_castLE_of_eq (show n + 1 + n' = n + n' + 1 by omega), ih (by omega)]
    refine forall_congr' fun x ↦ iff_of_eq ?_; congr 1; ext i
    simp only [Function.comp_def]
    by_cases him : i.1 < m
    · simp_rw [Fin.snoc, if_pos him, Fin.coe_cast, Fin.coe_castAdd]
      rw [dif_pos (by omega), dif_pos (by omega), Fin.coe_castLT, cast_eq, cast_eq]
      simp [him, Fin.cast, Fin.castAdd, Fin.castLE]
    · by_cases hin : i.1 = n
      · simp_rw [Fin.snoc, if_neg him, Fin.coe_cast, Fin.coe_addNat]
        rw [dif_neg (by omega), dif_neg (by omega)]
      · simp_rw [Fin.snoc, Fin.coe_cast, if_neg him, Fin.coe_addNat, Fin.coe_castLT, if_neg him]
        rw [dif_pos (by omega), dif_pos (by omega)]; rfl

-- @[simp] lemma Sum.elim_inl_inr' {α β γ : Type*} (f : α ⊕ β → γ) :
--     Sum.elim (fun x ↦ f (Sum.inl x)) (fun x ↦ f (Sum.inr x)) = f :=
--   Sum.elim_comp_inl_inr f

section subst

variable {L : Language} {α : Type u'} {β : Type v'} {n k : ℕ} (f : α → L.Term β)
  (φ₁ φ₂ : L.BoundedFormula α n) (φ : L.BoundedFormula α (n + 1))

def substAux (n : ℕ) : α ⊕ Fin n → L.Term (β ⊕ Fin n) :=
  Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr)

@[simp] lemma subst_bot : (⊥ : L.BoundedFormula α n).subst f = ⊥ := rfl

@[simp] lemma subst_equal (x y : L.Term (α ⊕ Fin n)) :
    (x =' y).subst f = x.subst (substAux f n) =' y.subst (substAux f n) := rfl

@[simp] lemma subst_rel (R : L.Relations n) (v : Fin n → L.Term (α ⊕ Fin k)) :
    (R.boundedFormula v).subst f = R.boundedFormula (fun i ↦ (v i).subst <| substAux f k) := rfl

@[simp] lemma subst_imp : (φ₁ ⟹ φ₂).subst f = φ₁.subst f ⟹ φ₂.subst f := rfl

@[simp] lemma subst_all : (∀' φ).subst f = ∀' (φ.subst f) := rfl

end subst


section app

variable {L : Language} {α : Type u} {β : Type v} {l n k : ℕ} (f : α ⊕ Fin n → L.Term (β ⊕ Fin k))
  (φ₁ φ₂ : L.BoundedFormula α n) (φ : L.BoundedFormula α (n + 1))

@[simp] lemma app_falsum : (⊥ : L.BoundedFormula α n).app f = ⊥ := rfl

@[simp] lemma relabel_relabelAux_id_substAux_inl (i : α ⊕ Fin n) :
    Term.relabel (relabelAux id 0) (substAux f 0 (Sum.inl i)) = f i := by
  have : (Sum.map id finSumFinEquiv ∘ Equiv.sumAssoc β (Fin k) (Fin 0)) ∘ Sum.inl = id := by
    ext i; cases i <;> simp [finSumFinEquiv]
  simp_all [relabelAux, substAux]

@[simp] lemma app_equal (x y : L.Term (α ⊕ Fin n)) :
    (x =' y : L.BoundedFormula α n).app f = x.subst f =' y.subst f := by
  simp [app, Term.equal, Function.comp_def]

@[simp] lemma app_rel (R : L.Relations l) (v : Fin l → L.Term (α ⊕ Fin n)) :
    (R.boundedFormula v).app f = R.boundedFormula ((Term.subst · f) ∘ v) := by
  simp [app, Relations.formula, Term.subst_relabel, Function.comp_def, relabel_def]

@[simp] lemma app_imp : (φ₁ ⟹ φ₂).app f = φ₁.app f ⟹ φ₂.app f := rfl

def appExpand (l : ℕ) (x : α ⊕ Fin (n + l)) : L.Term (β ⊕ Fin (k + l)) :=
  Sum.elim (Term.relabel (Sum.map id (Fin.castAdd l)) ∘ f ∘ Sum.inl)
    (Fin.addCases (Term.relabel (Sum.map id (Fin.castAdd l)) ∘ f ∘ Sum.inr)
      (Term.var ∘ Sum.inr ∘ Fin.natAdd k)) x

@[simp] lemma app_all : (∀' φ).app f = ∀' (φ.app (appExpand f 1)) := by
  simp only [app, subst, Function.comp_def, toFormula, relabel_def, mapTermRel,
    mapTermRel_mapTermRel'', Term.subst_relabel, id_eq, mapTermRel_mapTermRel',
    Term.relabel_subst, mapTermRel_mapTermRel''', all.injEq, castLE_rfl]
  congr 1; ext l x; congr 1; ext i
  refine Sum.casesOn i (Sum.rec ?_ (Fin.addCases ?_ ?_)) ?_ <;>
  intros <;> simp only [add_assoc, add_zero, appExpand, Equiv.sumAssoc_apply_inl_inl,
    Equiv.sumAssoc_apply_inl_inr, Equiv.sumAssoc_apply_inr, Fin.addCases_left, Fin.addCases_right,
    Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, Fin.ext_iff, Fin.val_eq_zero,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Function.comp_apply, Function.comp_def, id_eq,
    Language.Term.relabel_relabel, relabelAux, Sum.elim_inl, Sum.elim_inr, Sum.inr.injEq,
    Sum.map_id_id, Sum.map_inl, Sum.map_inr, Sum.map_map, Term.relabel, Term.var.injEq,
    ← Function.id_def] <;> congr 1 <;> ext j <;> cases j <;> simp [Fin.ext_iff]

@[simp] lemma realize_app {L : Language} {M : Type u}
    [L.Structure M] {α : Type v} {β : Type w} {n k : ℕ} (φ : L.BoundedFormula α n)
    (f : α ⊕ Fin n → L.Term (β ⊕ Fin k)) (v : β → M) (p : Fin k → M) :
    (φ.app f).Realize v p = φ.Realize (Term.realize (Sum.elim v p) ∘ f ∘ Sum.inl)
      (Term.realize (Sum.elim v p) ∘ f ∘ Sum.inr) := by
  induction φ using rec' generalizing k
  · simp
  · simp [← Function.comp_assoc, ← Function.comp_def]
  · simp [← Function.comp_assoc, ← Function.comp_def]
  · simp [*]
  · simp only [app_all, realize_all, Function.comp_def, appExpand, *]
    refine forall_congr fun x ↦ ?_; congr 2
    · ext i; simp [Function.comp_def, Sum.elim_map, Fin.snoc]
    · ext i; cases i using Fin.addCases <;> simp [Function.comp_def, Sum.elim_map, Fin.snoc]

end app

end FirstOrder.Language.BoundedFormula


namespace SetModel

open FirstOrder Set Language Sentence BoundedFormula
open scoped FirstOrder

variable (M : Type u)

/-- An extensional type. -/
class Ext extends Membership M M, HasSubset M where
  ext' {x y : M} (h : ∀ {t}, t ∈ x ↔ t ∈ y) : x = y
  subset_iff {x y : M} : x ⊆ y ↔ ∀ z, z ∈ x → z ∈ y := by exact Iff.rfl

instance [Ext M] : set.Structure M where
  RelMap := setRel.rec fun xy ↦ xy 0 ∈ xy 1

/-- Satisfying the basic set operations: singleton, insert, power set, binary union, and arbitrary
union.

This corresponds to satisfying pair, power set, and arbitrary union. -/
class BasicOp extends Ext M, Singleton M M, Insert M M, Union M where
  powerset : M → M
  sUnion : M → M
  mem_singleton_iff {x y : M} : x ∈ ({y} : M) ↔ x = y := by simp
  mem_insert_iff {x y z : M} : x ∈ insert y z ↔ x = y ∨ x ∈ z := by simp
  mem_union_iff {x y z : M} : x ∈ y ∪ z ↔ x ∈ y ∨ x ∈ z := by simp
  mem_powerset_iff {x y : M} : x ∈ powerset y ↔ x ⊆ y := by simp
  mem_sUnion_iff {x y : M} : x ∈ sUnion y ↔ ∃ z ∈ y, x ∈ z := by simp

attribute [simp] BasicOp.mem_singleton_iff BasicOp.mem_insert_iff
  BasicOp.mem_union_iff BasicOp.mem_powerset_iff BasicOp.mem_sUnion_iff
attribute [ext] Ext.ext'

alias ext_iff := Ext.ext'_iff

@[inherit_doc] scoped prefix:100 "𝔓" => BasicOp.powerset
@[inherit_doc] scoped prefix:100 "⋃ˢ" => BasicOp.sUnion

variable {M} in
def succ [BasicOp M] (x : M) : M :=
  x ∪ {x}

class CanonicalEmpty extends Ext M, EmptyCollection M where
  notMem_empty {x : M} : x ∉ (∅ : M) := by simp

class CanonicalInter extends Ext M, Inter M where
  mem_inter_iff {x y z : M} : x ∈ (y ∩ z : M) ↔ x ∈ y ∧ x ∈ z := by simp

class SimpleOp extends BasicOp M, CanonicalEmpty M, CanonicalInter M

attribute [simp] CanonicalEmpty.notMem_empty CanonicalInter.mem_inter_iff

/-- Has empty set and omega (an encoding of `ℕ`). This corresponds to the axiom of infinity. -/
class Inductive extends BasicOp M, CanonicalEmpty M where
  omega : M
  empty_mem_omega : ∅ ∈ omega := by simp
  succ_mem_omega {x : M} (h : x ∈ omega) : succ x ∈ omega := by simp_all
  omega_subset {x : M} (h0 : ∅ ∈ x) (ih : ∀ y ∈ x, succ y ∈ x) : omega ⊆ x

attribute [simp] Inductive.empty_mem_omega Inductive.succ_mem_omega

structure Separation [Ext M] (admissiblePred : Set (M → Prop)) where
  sep (x : M) {p : M → Prop} (h : p ∈ admissiblePred) : M
  mem_sep_iff {x : M} {p : M → Prop} (h : p ∈ admissiblePred) {y : M} :
    y ∈ sep x h ↔ y ∈ x ∧ p y := by simp

structure Replacement [Ext M] (admissibleFunc : Set (M → M)) where
  range (x : M) {f : M → M} (h : f ∈ admissibleFunc) : M
  mem_range_iff {x : M} {f : M → M} (h : f ∈ admissibleFunc) {y : M} :
    y ∈ range x h ↔ ∃ z ∈ x, f z = y := by simp

attribute [simp] Separation.mem_sep_iff Replacement.mem_range_iff

def oneParamPred [Ext M] : Set (M → Prop) :=
  { P | ∃ C : Class (Fin 1) 0, ∃ p, ∀ x, C.Realize ![p] ![x] ↔ P x }

def oneParamFunc [Ext M] : Set (M → M) :=
  { f | ∃ F : set.BoundedFormula (Fin 3) 0, ∃ p, ∀ x y, F.Realize ![x, y, p] default ↔ f x = y }

/-- We use a reformulation of choice that does not mention functions. -/
class Choice extends Ext M where
  choice {x : M} (h1 : ∀ y ∈ x, ∃ t, t ∈ y) (h2 : ∀ y ∈ x, ∀ z ∈ x, ∀ t ∈ y, t ∈ z → y = z) :
    ∃ c : M, ∀ y ∈ x, ∃ cy : M, (∀ t, t ∈ cy ↔ t ∈ c ∧ t ∈ y) ∧ (∃! t, t ∈ cy)

class Regular extends Ext M where
  regular : IsWellFounded M (· ∈ ·)

attribute [instance] Regular.regular

class SepRepl extends Ext M, CanonicalInter M where
  sep : Separation M (oneParamPred M)
  repl : Replacement M (oneParamFunc M)

class ZF extends SimpleOp M, Inductive M, Regular M, SepRepl M

class ZFCWithoutInfinity extends SimpleOp M, Regular M, SepRepl M, Choice M

class ZFC extends ZF M, ZFCWithoutInfinity M where

section Ext

variable [Ext M]
variable {α : Type v} {n : ℕ} (C C₁ C₂ : Class α n) (C' C'₁ C'₂ : Class α (n + 1))
  (v : α → M) (p : Fin n → M)

variable {M}

@[simp] lemma relMap_memRel (p : Fin 2 → M) :
    Structure.RelMap memRel p ↔ p 0 ∈ p 1 := Iff.rfl

def toSet (x : M) : Set M :=
  { t | t ∈ x }

@[simp] lemma mem_toSet_iff (x y : M) : x ∈ toSet y ↔ x ∈ y := Iff.rfl

@[simp] lemma toSet_inj (x y : M) : toSet x = toSet y ↔ x = y := by
  simp_rw [Set.ext_iff, ext_iff, mem_toSet_iff]

lemma toSet_injective : Function.Injective (toSet : M → Set M) :=
  fun x y ↦ (toSet_inj x y).1

@[simp] lemma toSet_subset (x y : M) : toSet x ⊆ toSet y ↔ x ⊆ y := by
  simp [Ext.subset_iff, Set.subset_def]

variable (M) in
@[simp] theorem realize_ext : M ⊨ Sentence.extensionality :=
  fun x y ↦ by simp [Fin.snoc, ext_iff]

def realize : Set M :=
  { x | BoundedFormula.Realize C v (Fin.snoc p x) }

lemma realize_def (x : M) : x ∈ realize C v p ↔ Realize C v (Fin.snoc p x) := Iff.rfl

@[simp] lemma realize_forall :
    realize (∀' C') v p = { x | ∀ y, y ∈ realize C' v (Fin.snoc p x) } := by
  simp [realize]

@[simp] lemma realize_exists :
    realize (∃' C') v p = { x | ∃ y, y ∈ realize C' v (Fin.snoc p x) } := by
  simp [realize]

@[simp] lemma realize_imp :
    realize (C₁ ⟹ C₂) v p = { x | x ∈ realize C₁ v p → x ∈ realize C₂ v p } := by
  simp [realize]

@[simp] lemma realize_mem (x y : set.Term (α ⊕ Fin (n + 1))) :
    realize (x ∈' y) v p =
      { z | x.realize (Sum.elim v (Fin.snoc p z)) ∈ y.realize (Sum.elim v (Fin.snoc p z)) } := by
  simp [realize]

def Small (P : Set M) : Prop :=
  ∃ x : M, toSet x = P

noncomputable def Small.out {P : Set M} (h : Small P) : M :=
  Classical.choose h

@[simp] lemma realize_lift (k : ℕ) (p : Fin (n + k) → M) :
    realize (↑'[k] C) v p = realize C v (p ∘ Fin.castAdd k) := by
  simp_rw [Class.lift, realize,
    realize_castLE_of_eq (show n + 1 + k = n + k + 1 by omega),
    realize_liftAt' (show n ≤ n + 1 by omega)]
  refine congrArg _ <| funext fun x ↦ congrArg _ <| funext fun i ↦ ?_
  by_cases hi : i.1 = n
  · simp [Fin.snoc, hi]
  · simp [Fin.snoc, show i.1 < n by omega, show i.1 < n + k by omega,
      Fin.cast, Fin.castAdd, Fin.castLE]

@[simp] lemma realize_mkC (x : set.Term (α ⊕ Fin n)) :
    realize (Class.mkC x) v p = toSet (x.realize (Sum.elim v p)) := by
  simp [realize, Class.mkC, toSet, Sum.elim_comp_map]

@[simp] lemma realize_eqC : (C₁ =ᶜ C₂).Realize v p ↔ realize C₁ v p = realize C₂ v p := by
  simp [Class.eqC, Set.ext_iff, realize]

@[simp] lemma realize_eqC' :
    realize (C'₁ =ᶜ C'₂) v p =
      { x | realize C'₁ v (Fin.snoc p x) = realize C'₂ v (Fin.snoc p x) } := by
  simp [realize]

@[simp] lemma realize_singleton : realize {C} v p = { x | toSet x = realize C v p } := by
  simp [singleton, realize_eqC', Fin.snoc_comp_cast_add (m := 0)]

@[simp] lemma realize_union : realize (C₁ ∪ C₂) v p = realize C₁ v p ∪ realize C₂ v p := by
  simp [realize, Union.union, Set.union]

@[simp] lemma realize_inter : realize (C₁ ∩ C₂) v p = realize C₁ v p ∩ realize C₂ v p := by
  simp [realize, Inter.inter, Set.inter]

@[simp] lemma realize_and : realize (C₁ ⊓ C₂) v p = realize C₁ v p ∩ realize C₂ v p :=
  realize_inter ..

@[simp] lemma realize_memC : (C₁ ∈ᶜ C₂).Realize v p ↔
    ∃ x, toSet x = realize C₁ v p ∧ x ∈ realize C₂ v p := by
  simp [Class.memC, realize_ex, ← realize_def]

@[simp] lemma realize_memC' : realize (C'₁ ∈ᶜ C'₂) v p =
    { x | ∃ y, toSet y = realize C'₁ v (Fin.snoc p x) ∧ y ∈ realize C'₂ v (Fin.snoc p x) } := by
  simp [realize]

@[simp] lemma realize_insert :
    realize (Insert.insert C₁ C₂) v p = { x | toSet x = realize C₁ v p ∨ x ∈ realize C₂ v p } := by
  simp [Insert.insert, Set.ext_iff, Set.mem_union]

@[simp] lemma realize_pow : realize (pow C) v p = { x | toSet x ⊆ realize C v p } := by
  simp [pow, Fin.snoc, Fin.snoc_comp_cast_add (m := 0), subset_def]

@[simp] lemma realize_sUnion : realize (⋃ᶜ C) v p = { x | ∃ y ∈ realize C v p, x ∈ y } := by
  simp [FirstOrder.Set.sUnion, Fin.snoc, Fin.snoc_comp_cast_add (m := 0), and_comm]

@[simp] lemma realize_sInter : realize (⋂ᶜ C) v p = { x | ∀ y ∈ realize C v p, x ∈ y } := by
  simp [FirstOrder.Set.sInter, Fin.snoc, Fin.snoc_comp_cast_add (m := 0)]

@[simp] theorem realize_empty : realize ∅ v p = ∅ := by
  simp [EmptyCollection.emptyCollection, realize]

@[simp] theorem realize_zero : realize 0 v p = ∅ :=
  realize_empty v p

@[simp] theorem realize_succ :
    realize (Set.succ C) v p = realize C v p ∪ { x | toSet x = realize C v p } := by
  simp [Set.succ]

@[simp] theorem realize_equal (x y : set.Term (α ⊕ Fin (n + 1))) :
    realize (x =' y) v p =
      { z | x.realize (Sum.elim v (Fin.snoc p z)) = y.realize (Sum.elim v (Fin.snoc p z)) } := by
  simp [realize]

@[simp] theorem realize_isSingleton :
    realize isSingleton v p = { x | ∃! y, y ∈ x } := by
  simp [isSingleton, Fin.snoc_rev, ← Fin.succ_one_eq_two, -Fin.succ_one_eq_two', ExistsUnique]

@[simp] theorem realize_bind {β : Type w} {k : ℕ} (f : α ⊕ Fin n → β ⊕ Fin k)
    (v' : β → M) (p' : Fin k → M) :
    realize (C.bind f) v' p' =
      realize C (Sum.elim v' p' ∘ f ∘ Sum.inl) (Sum.elim v' p' ∘ f ∘ Sum.inr) :=
  have h1 (x : M) :
      Sum.elim v' (Fin.snoc p' x) ∘ Sum.elim Sum.inl (Sum.inr ∘ Fin.castSucc) = Sum.elim v' p' :=
    funext <| Sum.rec (by simp) (by simp)
  have h2 (x : M) : Sum.elim v' (Fin.snoc p' x) ∘
      Fin.snoc (Sum.elim Sum.inl (Sum.inr ∘ Fin.castSucc) ∘ f ∘ Sum.inr) (Sum.inr (Fin.last k)) =
      Fin.snoc (Sum.elim v' p' ∘ f ∘ Sum.inr) x := by
    refine funext <| Fin.lastCases (by simp) (fun i ↦ ?_)
    simp only [Function.comp_apply, Fin.snoc_castSucc]
    generalize f (Sum.inr i) = j; exact Sum.casesOn j (by simp) (by simp)
  Set.ext fun t ↦ by simp [Class.bind, realize, Formula.boundedFormula_realize_eq_realize,
    Function.comp_assoc, ← h1 t, h2]

end Ext


section BasicOp

variable [BasicOp M]

lemma succ_eq_insert (x : M) : succ x = insert x x := Ext.ext' <| by simp [succ, or_comm]

@[simp] theorem toSet_singleton (x : M) : toSet ({x} : M) = {x} := by
  simp [Set.ext_iff]

@[simp] theorem toSet_eq_singleton (x y : M) : toSet x = {y} ↔ x = {y} := by
  simp [← toSet_singleton]

@[simp] theorem toSet_insert (x y : M) : toSet (insert x y) = insert x (toSet y) := by
  simp [Set.ext_iff]

@[simp] theorem toSet_eq_insert (x y z : M) : toSet x = insert y (toSet z) ↔ x = insert y z := by
  simp [← toSet_insert]

@[simp] theorem toSet_union (x y : M) : toSet (x ∪ y) = toSet x ∪ toSet y := by
  simp [Set.ext_iff]

@[simp] theorem toSet_eq_union (x y z : M) : toSet x = toSet y ∪ toSet z ↔ x = y ∪ z := by
  simp [← toSet_union]

@[simp] theorem union_singleton_eq_insert (x y : M) : x ∪ {y} = insert y x := by
  simp [Ext.ext'_iff, or_comm]

@[simp] theorem toSet_powerset (x : M) : toSet (𝔓 x) = { y | y ⊆ x } := by
  simp [Set.ext_iff]

@[simp] theorem toSet_eq_powerset (x y : M) : toSet x = { z | z ⊆ y } ↔ x = 𝔓 y := by
  simp [← toSet_powerset]

@[simp] theorem toSet_sUnion (x : M) : toSet (⋃ˢ x) = ⋃ y ∈ x, toSet y := by
  simp [Set.ext_iff]

@[simp] theorem toSet_eq_sUnion (x y : M) : toSet x = ⋃ z ∈ y, toSet z ↔ x = ⋃ˢ y := by
  simp [← toSet_sUnion]

@[simp] lemma realize_existsC {α : Type v} {n : ℕ} (C : Class α n) (v : α → M) (p : Fin n → M) :
    C.existsC.Realize v p ↔ Small (realize C v p) := by
  simp [Class.existsC, Small, ← realize_def]

@[simp] theorem realize_pair : M ⊨ Sentence.pairing :=
  fun x y ↦ by simpa using Exists.intro {x, y} (by simp [Set.ext_iff, Fin.snoc])

@[simp] theorem realize_powerset : M ⊨ Sentence.powerset :=
  fun x ↦ by simpa using Exists.intro (𝔓 x) (by simp [Fin.snoc])

@[simp] theorem realize_union' : M ⊨ Sentence.union :=
  fun x ↦ by simpa using Exists.intro (⋃ˢ x) (by simp [Set.ext_iff, Fin.snoc])

end BasicOp


section Inductive

variable {M} [Inductive M]

scoped[SetModel] notation "ω[" M:arg "]" => Inductive.omega (M := M)

@[simp] theorem toSet_empty : toSet (∅ : M) = ∅ := by
  simp [toSet, CanonicalEmpty.notMem_empty]

@[simp] theorem toSet_eq_empty (x : M) : toSet x = ∅ ↔ x = ∅ := by
  simp [← toSet_empty]

@[simp] theorem insert_self_mem_omega (x : M) (hx : x ∈ ω[M]) : insert x x ∈ ω[M] := by
  simpa [succ] using Inductive.succ_mem_omega hx

variable (M) in
@[simp] theorem realize_infinity : M ⊨ Sentence.infinity := by
  simpa [infinity, Sentence.Realize, Formula.Realize, Fin.snoc] using
    Exists.intro ω[M] (And.intro Inductive.empty_mem_omega insert_self_mem_omega)

end Inductive


section Regular

variable {M} [Regular M]

@[elab_as_elim]
theorem memInductionOn {C : M → Prop} (t : M) (step : ∀ x, (∀ y ∈ x, C y) → C x) : C t :=
  IsWellFounded.induction (· ∈ ·) t fun x ih ↦ step x ih

@[simp] theorem mem_wf : WellFounded (α := M) (· ∈ ·) :=
  IsWellFounded.wf

variable (M) in
@[simp] theorem realize_regularity : M ⊨ Sentence.regularity := by
  intro x
  suffices h : ∀ y ∈ x, ∃ t ∈ x, ∀ z ∈ t, z ∉ x by simpa [Fin.snoc]
  exact fun y hy ↦ ⟨mem_wf.min (toSet x) ⟨y, hy⟩, mem_wf.min_mem _ _,
    fun z hz hzx ↦ mem_wf.not_lt_min _ _ hzx hz⟩

end Regular


section Choice

variable [Choice M]

@[simp] theorem realize_choice : M ⊨ Sentence.choice := by
  intro x
  suffices h : (∀ (y : M), (∀ (t : M), t ∉ y) → y ∉ x) →
    (∀ (a b c : M), c ∈ a → a ∈ x → c ∈ b → b ∈ x → a = b) →
      ∃ a, ∀ b ∈ x, ∃ t, (∀ (y : M), y ∈ t ↔ y ∈ a ∧ y ∈ b) ∧ ∃! y, y ∈ t by
    simpa [Fin.snoc, Set.ext_iff]
  exact fun h1 h2 ↦ let ⟨t, ht⟩ := Choice.choice (x := x) (by grind) (by grind)
    ⟨t, fun y hy ↦ let ⟨cy, hcy⟩ := ht y hy; ⟨cy, by grind⟩⟩

def Choice.mk' (M : Type u) [SimpleOp M]
    (h : ∀ x : M, ∅ ∉ x → (∀ y ∈ x, ∀ z ∈ x, ∀ t ∈ y, t ∈ z → y = z) →
      ∃ c : M, ∀ y ∈ x, ∃! z : M, z ∈ c ∩ y) : Choice M where
  choice h1 h2 := let ⟨c, hc⟩ := h _ (fun he ↦ by simpa using h1 _ he) h2
    ⟨c, fun y hy ↦ ⟨c ∩ y, by simpa using hc y hy⟩⟩

end Choice


section SepRepl

variable [SepRepl M]

@[simp] theorem realize_separation (C : Class (Fin 1) 0) : M ⊨ Sentence.separation C := by
  intro x p
  have h1 (v w : Fin 0 → M) : (Sum.elim v (Fin.snoc (Fin.snoc w x) p) ∘ ![Sum.inr 1]) = ![p] :=
    funext <| Fin.forall_fin_one.2 <| by simp [Fin.snoc]
  simpa [Class.existsC, ← realize_def] using by
    refine Exists.intro (SepRepl.sep.sep x ⟨C, p, fun t ↦ Iff.rfl⟩) ?_
    simpa [Set.ext_iff, realize, Fin.snoc] using by
      intro y hy; rw [iff_iff_eq]; congr 2 <;>
      exact funext <| Fin.forall_fin_one.2 <| by simp [Fin.snoc]

variable {M}

def IsFunction (F : set.BoundedFormula (Fin 3) 0) (p : M) : Prop :=
  ∀ x y z : M, F.Realize ![x, y, p] ![] → F.Realize ![x, z, p] ![] → y = z

/-- In the axiom of replacement, the given function `F` may not be total. Given the parameter `p`,
we extend the domain of `F` by setting the output to `p` outside the domain. -/
def extendDomain (F : set.BoundedFormula (Fin 3) 0) : set.BoundedFormula (Fin 3) 0 :=
  ((∃' F.app (Sum.elim ![#0, &0, #2] ![])) ⊓ F) ⊔
  (∼(∃' F.app (Sum.elim ![#0, &0, #2] ![])) ⊓ (#1 =' #2))

open Classical in
noncomputable def toFunc (F : set.BoundedFormula (Fin 3) 0) (p t : M) : M :=
  if h : ∃ y, F.Realize ![t, y, p] ![] then h.choose else p

open Classical in
@[simp] lemma realize_extendDomain_iff {F : set.BoundedFormula (Fin 3) 0} {p : M}
    (hf : IsFunction F p) (x y : M) :
    (extendDomain F).Realize ![x, y, p] default ↔ toFunc F p x = y := by
  suffices h : (∃ a, F.Realize ![x, a, p] ![]) ∧ F.Realize ![x, y, p] default ∨
      ¬(∃ a, F.Realize ![x, a, p] ![]) ∧ y = p ↔
      (if h : ∃ y, F.Realize ![x, y, p] ![] then h.choose else p) = y by
    simp_all [extendDomain, toFunc, Fin.snoc]
  split_ifs with h
  · rw [eq_true h, not_true, true_and, false_and, or_false]
    exact ⟨hf _ _ _ h.choose_spec, (· ▸ h.choose_spec)⟩
  · simp [-not_exists, h, eq_comm]

theorem toFunc_mem_oneParamFunc {F : set.BoundedFormula (Fin 3) 0} {p : M} (hf : IsFunction F p) :
    toFunc F p ∈ oneParamFunc M :=
  ⟨extendDomain F, p, fun x y ↦ by simp [hf]⟩

theorem ne_mem_oneParamPred (y : M) : (· ≠ y) ∈ oneParamPred M :=
  ⟨∼(&0 =' #0), y, fun z ↦ by simp⟩

def remove (x y : M) : M :=
  SepRepl.sep.sep x (ne_mem_oneParamPred y)

@[simp] lemma mem_remove_iff (x y z : M) : z ∈ remove x y ↔ z ∈ x ∧ z ≠ y := by
  simp [remove]

open Classical in
noncomputable def image {F : set.BoundedFormula (Fin 3) 0}
    {p : M} (hf : IsFunction F p) (x : M) : M :=
  if ∃ z ∈ x, F.Realize ![z, p, p] ![]
    then SepRepl.repl.range x (toFunc_mem_oneParamFunc hf)
    else remove (SepRepl.repl.range x (toFunc_mem_oneParamFunc hf)) p

@[simp] lemma mem_image_iff {F : set.BoundedFormula (Fin 3) 0}
    {p : M} (hf : IsFunction F p) (x t : M) :
    t ∈ image hf x ↔ ∃ z ∈ x, F.Realize ![z, t, p] ![] := by
  rw [image]; split_ifs with hp
  · rw [Replacement.mem_range_iff]
    refine ⟨fun ⟨z, hzx, ht⟩ ↦ ht ▸ ?_, fun ⟨z, hzx, ht⟩ ↦ ⟨z, hzx, ?_⟩⟩
    · rw [toFunc]; split_ifs with h
      · exact ⟨z, hzx, h.choose_spec⟩
      · exact hp
    · have hz : ∃ y, F.Realize ![z, y, p] ![] := ⟨t, ht⟩
      rw [toFunc, dif_pos hz]
      exact hf _ _ _ hz.choose_spec ht
  · rw [mem_remove_iff, Replacement.mem_range_iff]
    refine ⟨fun ⟨⟨z, hzx, ht⟩, htp⟩ ↦ ?_, fun ⟨z, hzx, hzt⟩ ↦ ⟨⟨z, hzx, ?_⟩, ?_⟩⟩
    · rw [toFunc] at ht; split_ifs at ht with h
      · exact ⟨z, hzx, ht ▸ h.choose_spec⟩
      · exact absurd ht.symm htp
    · rw [toFunc]
      have hz : ∃ y, F.Realize ![z, y, p] ![] := ⟨t, hzt⟩
      rw [dif_pos hz]
      exact hf _ _ _ hz.choose_spec hzt
    · rintro rfl; exact hp ⟨z, hzx, hzt⟩

variable (M) in
@[simp] theorem realize_replacement (F : set.BoundedFormula (Fin 3) 0) :
    M ⊨ Sentence.replacement F := by
  intro p
  suffices h : (∀ a b c, F.Realize ![a, b, p] ![] → F.Realize ![a, c, p] ![] → b = c) →
    ∀ x, ∃ y, ∀ t, t ∈ y ↔ ∃ z ∈ x, F.Realize ![z, t, p] ![] by
    simpa [Matrix.empty_eq]
  exact fun hfun x ↦ ⟨image hfun x, fun t ↦ by simp⟩

end SepRepl

end SetModel




namespace ZFSet

open SetModel FirstOrder Set Language Sentence
open scoped FirstOrder

-- MOVE?
lemma mem_mk_iff {x : ZFSet.{u}} {y : PSet.{u}} : x ∈ mk y ↔ ∃ b : y.Type, mk (y.Func b) = x :=
  Quotient.inductionOn x fun x ↦ exists_congr fun b ↦ by simp [← eq, eq_comm]

-- MOVE?
@[simp] lemma mk_omega_succ {m : ULift.{u} ℕ} : mk (PSet.omega.Func ⟨m.down + 1⟩) =
    insert (mk (PSet.omega.Func m)) (mk (PSet.omega.Func m)) :=
  rfl

lemma omega_subset {x : ZFSet.{u}} (h0 : ∅ ∈ x) (ih : ∀ y ∈ x, insert y y ∈ x) : omega ⊆ x := by
  intro n hn
  rw [omega, mem_mk_iff] at hn
  obtain ⟨⟨m⟩, hm⟩ := hn
  induction m generalizing n with
  | zero => rw [← hm]; exact h0
  | succ m ihm => rw [← hm, mk_omega_succ]; exact ih _ (ihm rfl)

instance : Inductive ZFSet.{u} where
  ext' {x y} := by simp [ZFSet.ext_iff]
  powerset x := x.powerset
  sUnion x := x.sUnion
  omega := omega
  omega_subset h0 ih n hn := by simp_rw [succ_eq_insert] at ih; exact omega_subset h0 ih hn
  succ_mem_omega h := by rw [succ_eq_insert]; exact omega_succ h

instance : SimpleOp ZFSet.{u} where

instance : Choice ZFSet.{u} :=
  Choice.mk' _ fun x hx₁ hx₂ ↦
    have hx (y) (hyx : y ∈ x) : ∃ t, t ∈ y :=
      not_forall_not.1 <| fun hy ↦ hx₁ <| (eq_empty y).2 hy ▸ hyx
    ⟨range fun t : x.toSet ↦ (hx t t.2).choose, fun y hyx ↦
    ⟨(hx y hyx).choose, mem_inter.2 ⟨mem_range.2 ⟨⟨y, hyx⟩, rfl⟩, (hx y hyx).choose_spec⟩,
    fun z hz ↦ let ⟨y', hy'⟩ := mem_range.1 (mem_inter.1 hz).1
      suffices y = y' from hy' ▸ this ▸ rfl
      hx₂ _ hyx _ y'.2 z (mem_inter.1 hz).2 <| hy' ▸ (hx y' y'.2).choose_spec⟩⟩

noncomputable instance : ZFC ZFSet.{u} where
  regular := inferInstance
  sep := ⟨fun x {p} _ ↦ x.sep p, by simp⟩
  repl := ⟨fun x {f} _ ↦ range fun t : x.toSet ↦ f t, by simp⟩

theorem ZFSet_model_ZFC : ZFSet.{u} ⊨ ZFC where
  realize_of_mem _ h := by cases h <;> simp

end ZFSet
