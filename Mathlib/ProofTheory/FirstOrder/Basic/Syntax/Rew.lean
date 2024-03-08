/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.ProofTheory.FirstOrder.Basic.Syntax.Term
import Mathlib.ProofTheory.FirstOrder.Basic.Syntax.Formula

/-!
# Rewriting System

Term/formula morphisms such as rewritings, substitutions, and embeddings are handled by the
structure `FirstOrder.Rew`.
- `FirstOrder.Rew.rewrite f` is a rewriting of the free variables occurring in the term by
  `f : ξ₁ → Semiterm L ξ₂ n`.
- `FirstOrder.Rew.substs v` is a substitution of the bounded variables occurring in the term by
  `v : Fin n → Semiterm L ξ n'`.
- `FirstOrder.Rew.bShift` is a transformation of the bounded variables occurring in the term by
  `#x ↦ #(Fin.succ x)`.
- `FirstOrder.Rew.shift` is a transformation of the free variables occurring in the term by
  `&x ↦ &(x + 1)`.
- `FirstOrder.Rew.emb` is a embedding of the term with no free variables.

Rewritings `FirstOrder.Rew` is naturally converted to formula rewritings by `FirstOrder.Rew.hom`.
-/

namespace ProofTheory

namespace FirstOrder

structure Rew (L : Language) (ξ₁ : Type*) (n₁ : ℕ) (ξ₂ : Type*) (n₂ : ℕ) where
  toFun : Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  func' : ∀ {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁), toFun (Semiterm.func f v) =
    Semiterm.func f (fun i => toFun (v i))

abbrev SyntacticRew (L : Language) (n₁ n₂ : ℕ) := Rew L ℕ n₁ ℕ n₂

namespace Rew

open Semiterm
variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {ξ ξ' : Type v} {ξ₁ : Type v₁} {ξ₂ : Type v₂} {ξ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}
variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

instance : FunLike (Rew L ξ₁ n₁ ξ₂ n₂) (Semiterm L ξ₁ n₁) (fun _ => Semiterm L ξ₂ n₂) where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by rcases f; rcases g; simp; exact h

instance : CoeFun (Rew L ξ₁ n₁ ξ₂ n₂) (fun _ => Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂) :=
  FunLike.hasCoeToFun

protected lemma func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f (fun i => ω (v i)) := ω.func' f v

lemma func'' {k} (f : L.Func k) (v : Fin k → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f (ω ∘ v) := ω.func' f v

@[simp] lemma func0 (f : L.Func 0) (v : Fin 0 → Semiterm L ξ₁ n₁) :
    ω (func f v) = func f ![] := by simp[Rew.func, Matrix.empty_eq]

@[simp] lemma func1 (f : L.Func 1) (t : Semiterm L ξ₁ n₁) :
    ω (func f ![t]) = func f ![ω t] := by simp[Matrix.constant_eq_singleton, Rew.func]

@[simp] lemma func2 (f : L.Func 2) (t₁ t₂ : Semiterm L ξ₁ n₁) :
    ω (func f ![t₁, t₂]) = func f ![ω t₁, ω t₂] := by simp[Rew.func]; funext i;
      induction i using Fin.induction <;> simp

@[simp] lemma func3 (f : L.Func 3) (t₁ t₂ t₃ : Semiterm L ξ₁ n₁) :
    ω (func f ![t₁, t₂, t₃]) = func f ![ω t₁, ω t₂, ω t₃] := by
  simp[Rew.func]; funext i; induction' i using Fin.induction with i <;> simp;
    induction' i using Fin.induction with i <;> simp

@[ext] lemma ext (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : ∀ x, ω₁ &x = ω₂ &x) :
    ω₁ = ω₂ := by
  apply FunLike.ext ω₁ ω₂; intro t
  induction t <;> simp[*, ω₁.func, ω₂.func]

lemma ext' {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} (h : ω₁ = ω₂) (t) : ω₁ t = ω₂ t := by simp[h]

protected def id : Rew L ξ n ξ n where
  toFun := id
  func' := fun _ _ => rfl

@[simp] lemma id_app (t : Semiterm L ξ n) : Rew.id t = t := rfl

protected def comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ n₁ ξ₃ n₃ where
  toFun := fun t => ω₂ (ω₁ t)
  func' := fun f v => by simp[func'']; rfl

lemma comp_app (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁) :
    (ω₂.comp ω₁) t = ω₂ (ω₁ t) := rfl

@[simp] lemma id_comp (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew.id.comp ω = ω := by ext <;> simp[comp_app]

@[simp] lemma comp_id (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω.comp Rew.id = ω := by ext <;> simp[comp_app]

def bindAux (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) :
    Semiterm L ξ₁ n₁ → Semiterm L ξ₂ n₂
  | (#x)       => b x
  | (&x)       => e x
  | (func f v) => func f (fun i => bindAux b e (v i))

def bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) : Rew L ξ₁ n₁ ξ₂ n₂ where
  toFun := bindAux b e
  func' := fun _ _ => rfl

def rewrite (f : ξ₁ → Semiterm L ξ₂ n) : Rew L ξ₁ n ξ₂ n := bind Semiterm.bvar f

def rewriteMap (e : ξ₁ → ξ₂) : Rew L ξ₁ n ξ₂ n := rewrite (fun m => &(e m))

def map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) : Rew L ξ₁ n₁ ξ₂ n₂ :=
  bind (fun n => #(b n)) (fun m => &(e m))

def substs {n'} (v : Fin n → Semiterm L ξ n') : Rew L ξ n ξ n' :=
  bind v fvar

def emb {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o n ξ n := map id h.elim

def empty {o : Type v₁} [h : IsEmpty o] {ξ : Type v₂} {n} : Rew L o 0 ξ n := map Fin.elim0 h.elim

def bShift : Rew L ξ n ξ (n + 1) :=
  map Fin.succ id

def bShiftAdd (m : ℕ) : Rew L ξ n ξ (n + m) :=
  map (Fin.addNat · m) id

def castLE {n n' : ℕ} (h : n ≤ n') : Rew L ξ n ξ n' :=
  map (Fin.castLE h) id

def toS : Rew L (Fin n) 0 Empty n := Rew.bind ![] (#·)

def toF : Rew L Empty n (Fin n) 0 := Rew.bind (&·) Empty.elim

def embSubsts (v : Fin k → Semiterm L ξ n) : Rew L Empty k ξ n := Rew.bind v Empty.elim

protected def q (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Rew L ξ₁ (n₁ + 1) ξ₂ (n₂ + 1) :=
  bind (#0 :> bShift ∘ ω ∘ bvar) (bShift ∘ ω ∘ fvar)

lemma eq_id_of_eq {ω : Rew L ξ n ξ n} (hb : ∀ x, ω #x = #x) (he : ∀ x, ω &x = &x) (t) :
    ω t = t := by
  have : ω = Rew.id := by ext <;> simp[*]
  simp[this]

def qpow (ω : Rew L ξ₁ n₁ ξ₂ n₂) : (k : ℕ) → Rew L ξ₁ (n₁ + k) ξ₂ (n₂ + k)
  | 0     => ω
  | k + 1 => (ω.qpow k).q

@[simp] lemma qpow_zero (ω : Rew L ξ₁ n₁ ξ₂ n₂) : qpow ω 0 = ω := rfl

@[simp] lemma qpow_succ (ω : Rew L ξ₁ n₁ ξ₂ n₂) (k : ℕ) : qpow ω (k + 1) = (ω.qpow k).q := rfl

section bind

variable (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂)

@[simp] lemma bind_fvar (m : ξ₁) : bind b e (&m : Semiterm L ξ₁ n₁) = e m := rfl

@[simp] lemma bind_bvar (n : Fin n₁) : bind b e (#n : Semiterm L ξ₁ n₁) = b n := rfl

lemma eq_bind (ω : Rew L ξ₁ n₁ ξ₂ n₂) : ω = bind (ω ∘ bvar) (ω ∘ fvar) := by
  ext t; induction t ; simp[Rew.func'']; funext; simp[*]

@[simp] lemma bind_eq_id_of_zero (f : Fin 0 → Semiterm L ξ₂ 0) : bind f fvar = Rew.id := by
  { ext x <;> simp; exact Fin.elim0 x }

end bind

section map

variable (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂)

@[simp] lemma map_fvar (m : ξ₁) : map b e (&m : Semiterm L ξ₁ n₁) = &(e m) := rfl

@[simp] lemma map_bvar (n : Fin n₁) : map b e (#n : Semiterm L ξ₁ n₁) = #(b n) := rfl

@[simp] lemma map_id : map (L := L) (id : Fin n → Fin n) (id : ξ → ξ) = Rew.id := by ext <;> simp

lemma map_inj {b : Fin n₁ → Fin n₂} {e : ξ₁ → ξ₂} (hb : Function.Injective b)
    (he : Function.Injective e) : Function.Injective $ map (L := L) b e
  | #x,                    t => by cases t <;> simp[Rew.func]; intro h; exact hb h
  | &x,                    t => by cases t <;> simp[Rew.func]; intro h; exact he h
  | func (arity := k) f v, t => by
    cases t <;> simp[*, Rew.func]
    case func =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact map_inj hb he (congr_fun h i)

end map

section rewrite

variable (f : ξ₁ → Semiterm L ξ₂ n)

@[simp] lemma rewrite_fvar (x : ξ₁) : rewrite f &x = f x := rfl

@[simp] lemma rewrite_bvar (x : Fin n) : rewrite e (#x : Semiterm L ξ₁ n) = #x := rfl

lemma rewrite_comp_rewrite (v : ξ₂ → Semiterm L ξ₃ n) (w : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite v).comp (rewrite w) = rewrite (rewrite v ∘ w) :=
  by ext <;> simp[comp_app]

@[simp] lemma rewrite_eq_id : (rewrite Semiterm.fvar : Rew L ξ n ξ n) = Rew.id := by ext <;> simp

end rewrite

section rewriteMap

variable (e : ξ₁ → ξ₂)

@[simp] lemma rewriteMap_fvar (x : ξ₁) : rewriteMap e (&x : Semiterm L ξ₁ n) = &(e x) := rfl

@[simp] lemma rewriteMap_bvar (x : Fin n) : rewriteMap e (#x : Semiterm L ξ₁ n) = #x := rfl

@[simp] lemma rewriteMap_id : rewriteMap (L := L) (n := n) (id : ξ → ξ) = Rew.id := by ext <;> simp

lemma eq_rewriteMap_of_funEqOn_fv [DecidableEq ξ₁] (t : Semiterm L ξ₁ n₁)
    (f g : ξ₁ → Semiterm L ξ₂ n₂) (h : Function.funEqOn (· ∈ t.fv) f g) :
    Rew.rewriteMap f t = Rew.rewriteMap g t := by
  induction t <;> simp [Rew.func]
  case fvar x => exact h x (by simp)
  case func f v ih =>
    funext i
    exact ih i (fun x hx ↦ h x (by simp [Semiterm.fv_func]; exact ⟨i, hx⟩))

end rewriteMap

section emb

variable {o : Type v₂} [IsEmpty o]

@[simp] lemma emb_bvar (x : Fin n) : emb (ξ := ξ) (#x : Semiterm L o n) = #x := rfl

@[simp] lemma emb_eq_id : (emb : Rew L o n o n) = Rew.id := by ext x <;> simp; exact isEmptyElim x

lemma eq_empty [h : IsEmpty ξ₁] (ω : Rew L ξ₁ 0 ξ₂ n) :
  ω = empty := by ext x; { exact x.elim0 }; { exact h.elim' x }

end emb

section bShift

@[simp] lemma bShift_bvar (x : Fin n) : bShift (#x : Semiterm L ξ n) = #(Fin.succ x) := rfl

@[simp] lemma bShift_fvar (x : ξ) : bShift (&x : Semiterm L ξ n) = &x := rfl

@[simp] lemma bShift_ne_zero (t : Semiterm L ξ n) : bShift t ≠ #0 := by
  cases t <;> simp[Rew.func, Fin.succ_ne_zero]

@[simp] lemma bShift_positive (t : Semiterm L ξ n) : (bShift t).Positive := by
  induction t <;> simp [Rew.func, *]

lemma positive_iff {t : Semiterm L ξ (n + 1)} : t.Positive ↔ ∃ t', t = bShift t' :=
  ⟨by induction t <;> simp
      case bvar x =>
        intro hx; exact ⟨#(x.pred (Fin.pos_iff_ne_zero.mp hx)), by simp⟩
      case fvar x => exact ⟨&x, by simp⟩
      case func k f v ih =>
        intro h
        have : ∀ i, ∃ t', v i = bShift t' := fun i => ih i (h i)
        choose w hw using this
        exact ⟨func f w, by simp [Rew.func]; funext i; exact hw i⟩,
   by rintro ⟨t', rfl⟩; simp⟩

@[simp] lemma leftConcat_bShift_comp_bvar :
    (#0 :> bShift ∘ bvar : Fin (n + 1) → Semiterm L ξ (n + 1)) = bvar :=
  funext (Fin.cases (by simp) (by simp))

@[simp] lemma bShift_comp_fvar :
    (bShift ∘ fvar : ξ → Semiterm L ξ (n + 1)) = fvar :=
  funext (by simp)

end bShift

section bShiftAdd

@[simp] lemma bShiftAdd_bvar (m) (x : Fin n) : bShiftAdd m
  (#x : Semiterm L ξ n) = #(Fin.addNat x m) := rfl

@[simp] lemma bShiftAdd_fvar (m) (x : ξ) : bShiftAdd m (&x : Semiterm L ξ n) = &x := rfl

end bShiftAdd

section substs

variable {n'} (w : Fin n → Semiterm L ξ n')

@[simp] lemma substs_bvar (x : Fin n) : substs w #x = w x :=
  by simp[substs]

@[simp] lemma substs_fvar (x : ξ) : substs w &x = &x :=
  by simp[substs]

@[simp] lemma substs_zero (w : Fin 0 → Term L ξ) : substs w = Rew.id :=
  by ext x <;> simp; { exact Fin.elim0 x }

lemma substs_comp_substs (v : Fin l → Semiterm L ξ k) (w : Fin k → Semiterm L ξ n) :
    (substs w).comp (substs v) = substs (substs w ∘ v) :=
  by ext <;> simp[comp_app]

@[simp] lemma substs_eq_id : (substs Semiterm.bvar : Rew L ξ n ξ n) = Rew.id := by ext <;> simp

end substs

section castLE

@[simp] lemma castLe_bvar {n'} (h : n ≤ n') (x : Fin n) : castLE h
  (#x : Semiterm L ξ n) = #(Fin.castLE h x) := rfl

@[simp] lemma castLe_fvar {n'} (h : n ≤ n') (x : ξ) : castLE h (&x : Semiterm L ξ n) = &x := rfl

@[simp] lemma castLe_eq_id {h} : (castLE h : Rew L ξ n ξ n) = Rew.id := by ext <;> simp

end castLE

section toS

@[simp] lemma toS_fvar {n} (x : Fin n) : toS (&x : Term L (Fin n)) = #x := rfl

end toS

section embSubsts

variable {k} (w : Fin k → Semiterm L ξ n)

@[simp] lemma embSubsts_bvar (x : Fin k) : embSubsts w #x = w x :=
  by simp[embSubsts]

@[simp] lemma embSubsts_zero (w : Fin 0 → Term L ξ) : embSubsts w = Rew.emb := by
  ext x <;> try simp
  · exact Fin.elim0 x
  · exact Empty.elim x

lemma substs_comp_embSubsts (v : Fin l → Semiterm L ξ k) (w : Fin k → Semiterm L ξ n) :
    (substs w).comp (embSubsts v) = embSubsts (substs w ∘ v) := by
  ext x <;> simp[comp_app]
  exact Empty.elim x

@[simp] lemma embSubsts_eq_id : (embSubsts Semiterm.bvar : Rew L Empty n ξ n) = Rew.emb := by
  ext x <;> try simp
  · exact Empty.elim x

end embSubsts

section q

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

@[simp] lemma q_bvar_zero : ω.q #0 = #0 := by simp[Rew.q]

@[simp] lemma q_bvar_succ (i : Fin n₁) : ω.q #(i.succ) = bShift (ω #i) := by simp[Rew.q]

@[simp] lemma q_fvar (x : ξ₁) : ω.q &x = bShift (ω &x) := by simp[Rew.q]

@[simp] lemma q_comp_bShift : ω.q.comp bShift = bShift.comp ω := by
  ext x <;> simp[comp_app]

@[simp] lemma q_comp_bShift_app (t : Semiterm L ξ₁ n₁) : ω.q (bShift t) = bShift (ω t) := by
  have := ext' (ω.q_comp_bShift) t; simpa only [comp_app] using this

@[simp] lemma q_id : (Rew.id : Rew L ξ n ξ n).q = Rew.id := by ext x;
  { cases x using Fin.cases <;> simp }; { simp }

@[simp] lemma q_eq_zero_iff : ω.q t = #0 ↔ t = #0 := by
  cases t <;> simp [Rew.func]
  case bvar i =>
    cases i using Fin.cases <;> simp [Fin.succ_ne_zero]

@[simp] lemma q_positive_iff : (ω.q t).Positive ↔ t.Positive := by
  induction t <;> simp [Rew.func, *]
  case bvar x =>
    cases x using Fin.cases <;> simp

@[simp] lemma qpow_id {k} : (Rew.id : Rew L ξ n ξ n).qpow k = Rew.id := by induction k <;> simp[*]

lemma q_comp (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (Rew.comp ω₂ ω₁).q = ω₂.q.comp ω₁.q := by ext x;
    { cases x using Fin.cases <;> simp[comp_app] }; { simp[comp_app] }

lemma qpow_comp (k) (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (Rew.comp ω₂ ω₁).qpow k = (ω₂.qpow k).comp (ω₁.qpow k) := by induction k <;> simp[*, q_comp]

lemma q_bind (b : Fin n₁ → Semiterm L ξ₂ n₂) (e : ξ₁ → Semiterm L ξ₂ n₂) :
    (bind b e).q = bind (#0 :> bShift ∘ b) (bShift ∘ e) := by ext x;
    { cases x using Fin.cases <;> simp }; { simp }

lemma q_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) :
    (map (L := L) b e).q = map (0 :> Fin.succ ∘ b) e := by ext x;
    { cases x using Fin.cases <;> simp }; { simp }

lemma q_rewrite (f : ξ₁ → Semiterm L ξ₂ n) :
    (rewrite f).q = rewrite (bShift ∘ f) := by ext x;
    { cases x using Fin.cases <;> simp[rewriteMap] }; { simp }

@[simp] lemma q_rewriteMap (e : ξ₁ → ξ₂) :
    (rewriteMap (L := L) (n := n) e).q = rewriteMap e := by ext x;
    { cases x using Fin.cases <;> simp[rewriteMap] }; { simp }

@[simp] lemma q_emb {o : Type v₁} [e : IsEmpty o] {n} :
    (emb (L := L) (o := o) (ξ := ξ₂) (n := n)).q = emb := by ext x;
    { cases x using Fin.cases <;> simp }; { exact e.elim x }

@[simp] lemma qpow_emb {o : Type v₁} [e : IsEmpty o] {n k} :
    (emb (L := L) (o := o) (ξ := ξ₂) (n := n)).qpow k = emb := by induction k <;> simp[*]

@[simp] lemma q_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L ξ n ξ n').q = castLE (Nat.add_le_add_right h 1) := by
  ext x <;> simp; cases x using Fin.cases <;> simp

lemma q_toS :
    (toS : Rew L (Fin n) 0 Empty n).q = bind ![#0] (#·.succ) := by
  ext x <;> simp; cases x using Fin.cases <;> try simp
  · exact Fin.elim0 (by assumption)

@[simp] lemma qpow_castLE {n n'} (h : n ≤ n') :
    (castLE h : Rew L ξ n ξ n').qpow k = castLE (Nat.add_le_add_right h k) := by
  induction k <;> simp[*]

lemma q_substs (w : Fin n → Semiterm L ξ n') :
    (substs w).q = substs (#0 :> bShift ∘ w) := by ext x; { cases x using Fin.cases <;> simp };
    { simp }

lemma q_embSubsts (w : Fin k → Semiterm L ξ n) :
    (embSubsts w).q = embSubsts (#0 :> bShift ∘ w) := by ext x;
    { cases x using Fin.cases <;> simp }; { simp; exact Empty.elim x }

end q

section Syntactic

/-
  #0 #1 ... #(n - 1) &0 &1 ...
   ↓shift
  #0 #1 ... #(n - 1) &1 &2 &3 ...
-/

def shift : SyntacticRew L n n := map id Nat.succ

/-
  #0 #1 ... #(n - 1) #n &0 &1 ...
   ↓free           ↑fix
  #0 #1 ... #(n - 1) &0 &1 &2 ...
 -/

def free : SyntacticRew L (n + 1) n := bind (bvar <: &0) (fun m => &(Nat.succ m))

def fix : SyntacticRew L n (n + 1) := bind (fun x => #(Fin.castSucc x)) (#(Fin.last n) :>ₙ fvar)

abbrev rewrite1 (t : SyntacticSemiterm L n) : SyntacticRew L n n := bind Semiterm.bvar (t :>ₙ fvar)

section shift

@[simp] lemma shift_bvar (x : Fin n) : shift (#x : SyntacticSemiterm L n) = #x := rfl

@[simp] lemma shift_fvar (x : ℕ) : shift (&x : SyntacticSemiterm L n) = &(x + 1) := rfl

lemma shift_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    shift (func f v) = func f (fun i => shift (v i)) := rfl

lemma shift_Injective : Function.Injective (@shift L n) :=
  Function.LeftInverse.injective (g := map id Nat.pred)
    (by intros p; simp[←comp_app]; apply eq_id_of_eq <;> simp[comp_app])

end shift

section free

@[simp] lemma free_bvar_castSucc (x : Fin n) : free (#(Fin.castSucc x) :
  SyntacticSemiterm L (n + 1)) = #x := by simp[free]

@[simp] lemma free_bvar_castSucc_zero : free (#0 : SyntacticSemiterm L (n + 1 + 1)) = #0 :=
  free_bvar_castSucc 0

@[simp] lemma free_bvar_last : free (#(Fin.last n) : SyntacticSemiterm L (n + 1)) = &0 := by
  simp[free]

@[simp] lemma free_bvar_last_zero : free (#0 : SyntacticSemiterm L 1) = &0 := free_bvar_last

@[simp] lemma free_fvar (x : ℕ) : free (&x : SyntacticSemiterm L (n + 1)) = &(x + 1) := by
  simp[free]

end free

section fix

@[simp] lemma fix_bvar (x : Fin n) : fix (#x : SyntacticSemiterm L n) = #(Fin.castSucc x) := by
  simp[fix]

@[simp] lemma fix_fvar_zero : fix (&0 : SyntacticSemiterm L n) = #(Fin.last n) := by simp[fix]

@[simp] lemma fix_fvar_succ (x : ℕ) : fix (&(x + 1) : SyntacticSemiterm L n) = &x := by simp[fix]

end fix

@[simp] lemma free_comp_fix : (free (L := L) (n := n)).comp fix = Rew.id := by
  ext x <;> simp[comp_app]; { cases x <;> simp }

@[simp] lemma fix_comp_free : (fix (L := L) (n := n)).comp free = Rew.id := by
  ext x <;> simp[comp_app]; { cases x using Fin.lastCases <;> simp }

@[simp] lemma bShift_free_eq_shift : (free (L := L) (n := 0)).comp bShift = shift := by
  ext x <;> simp[comp_app]; { exact Fin.elim0 x }

lemma bShift_comp_substs (v : Fin n₁ → Semiterm L ξ₂ n₂) :
  bShift.comp (substs v) = substs (bShift ∘ v) := by ext x <;> simp[comp_app]

lemma shift_comp_substs (v : Fin n₁ → SyntacticSemiterm L n₂) :
  shift.comp (substs v) = (substs (shift ∘ v)).comp shift := by ext x <;> simp[comp_app]

lemma shift_comp_substs1 (t : SyntacticSemiterm L n₂) :
  shift.comp (substs ![t]) = (substs ![shift t]).comp shift := by ext x <;> simp[comp_app]

@[simp] lemma rewrite_comp_emb {o : Type v₁} [e : IsEmpty o] (f : ξ₂ → Semiterm L ξ₃ n) :
  (rewrite f).comp emb = (emb : Rew L o n ξ₃ n) := by ext x <;> simp[comp_app];
  { exact IsEmpty.elim e x }

@[simp] lemma shift_comp_emb {o : Type v₁} [e : IsEmpty o] :
  shift.comp emb = (emb : Rew L o n ℕ n) := by ext x <;> simp[comp_app]; { exact IsEmpty.elim e x }

lemma rewrite_comp_free_eq_substs (t : SyntacticTerm L) :
    (rewrite (t :>ₙ Semiterm.fvar)).comp free = substs ![t] := by
  ext x <;> simp[comp_app, Fin.eq_zero]

lemma rewrite_comp_shift_eq_id (t : SyntacticTerm L) :
    (rewrite (t :>ₙ Semiterm.fvar)).comp shift = Rew.id := by ext x <;> simp[comp_app]

@[simp] lemma substs_mbar_zero_comp_shift_eq_free :
    (substs (L := L) ![&0]).comp shift = free := by ext x <;> simp[comp_app, Fin.eq_zero]

@[simp] lemma substs_comp_bShift_eq_id (v : Fin 1 → Semiterm L ξ 0) :
    (substs (L := L) v).comp bShift = Rew.id := by ext x <;> simp[comp_app]; exact Fin.elim0 x

lemma free_comp_substs_eq_substs_comp_shift {n'} (w : Fin n' → SyntacticSemiterm Lf (n + 1)) :
    free.comp (substs w) = (substs (free ∘ w)).comp shift :=
  by ext x <;> simp[comp_app]

@[simp] lemma rewriteMap_comp_rewriteMap (f : ξ₁ → ξ₂) (g : ξ₂ → ξ₃) :
  (rewriteMap (L := L) (n := n) g).comp (rewriteMap f) = rewriteMap (g ∘ f) := by
    ext x <;> simp [comp_app]

@[simp] lemma fix_free_app (t : SyntacticSemiterm L (n + 1)) : fix (free t) = t := by
  simp[←comp_app]

@[simp] lemma free_fix_app (t : SyntacticSemiterm L n) : free (fix t) = t := by
  simp[←comp_app]

@[simp] lemma free_bShift_app (t : SyntacticSemiterm L 0) : free (bShift t) = shift t := by
  simp[←comp_app]

@[simp] lemma substs_bShift_app (v : Fin 1 → Semiterm L ξ 0) : substs v (bShift t) = t := by
  simp[←comp_app]

lemma rewrite_comp_fix_eq_substs (t) :
    ((rewrite (t :>ₙ (&·))).comp free : SyntacticRew L 1 0) = substs ![t] := by
  ext x <;> simp[comp_app, Fin.eq_zero]

section q

variable (ω : SyntacticRew L n₁ n₂)

@[simp] lemma q_shift : (shift (L := L) (n := n)).q = shift := by ext x;
  { cases x using Fin.cases <;> simp }; { simp }

@[simp] lemma q_free : (free (L := L) (n := n)).q = free := by
  ext x; { cases' x using Fin.cases with x <;> simp;
  { cases x using Fin.lastCases <;> simp[Fin.succ_castSucc] } }; { simp }

@[simp] lemma q_fix : (fix (L := L) (n := n)).q = fix := by
  ext x; { cases x using Fin.cases <;> simp[Fin.succ_castSucc] }; { cases x <;> simp }

end q

end Syntactic

end Rew

scoped syntax (name := substsNotation) "[→ " term,* "]" : term

scoped macro_rules
  | `([→ $terms:term,*]) => `(Rew.substs ![$terms,*])

@[app_unexpander Rew.substs]
def substsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ ![$terms,*]) => `([→ $terms,*])
  | _ => throw ()

scoped notation "⇑" => Rew.shift

scoped syntax (name := embSubstsHomNotation) term:max ".[" term,* "]" : term

scoped macro_rules (kind := embSubstsHomNotation)
  | `($p:term .[$terms:term,*]) => `((Rew.embSubsts ![$terms,*]).hom $p)

/-!
### Rewriting system of terms

-/
namespace Semiterm

variable
  {L L' : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {ξ ξ' : Type v} {ξ₁ : Type v₁} {ξ₂ : Type v₂} {ξ₃ : Type v₃}
  {n n₁ n₂ n₃ : ℕ}

@[simp] lemma fvarList_emb {o : Type w} [e : IsEmpty o] {t : Semiterm L o n} : fvarList
    (Rew.emb t : Semiterm L ξ n) = [] := by
  induction t <;> simp[*, List.eq_nil_iff_forall_not_mem, Rew.func]
  case fvar x => { exact IsEmpty.elim' e x }

lemma rew_eq_of_funEqOn (ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂) (t : Semiterm L ξ₁ n₁)
  (hb : ∀ x, ω₁ #x = ω₂ #x)
  (he : Function.funEqOn t.fvar? (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) :
    ω₁ t = ω₂ t := by
  induction t <;> try simp[Rew.func, hb]
  case fvar => simpa[fvar?, Function.funEqOn] using he
  case func k f v ih =>
    funext i
    exact ih i (he.of_subset $ by simp[fvar?]; intro x hx; exact ⟨i, hx⟩)

section lMap

variable (Φ : L₁ →ᵥ L₂)
open Rew

lemma lMap_bind (b : Fin n₁ → Semiterm L₁ ξ₂ n₂) (e : ξ₁ → Semiterm L₁ ξ₂ n₂) (t) :
    lMap Φ (bind b e t) = bind (lMap Φ ∘ b) (lMap Φ ∘ e) (t.lMap Φ) :=
  by induction t <;> simp[*, lMap_func, Rew.func]

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) (t) :
    (map b e t).lMap Φ = map b e (t.lMap Φ) :=
  by simp[map, lMap_bind, Function.comp]

lemma lMap_bShift (t : Semiterm L₁ ξ₁ n) : (bShift t).lMap Φ = bShift (t.lMap Φ) :=
  by simp[bShift, lMap_map]

lemma lMap_shift (t : SyntacticSemiterm L₁ n) : (shift t).lMap Φ = shift (t.lMap Φ) :=
  by simp[shift, lMap_map]

lemma lMap_free (t : SyntacticSemiterm L₁ (n + 1)) : (free t).lMap Φ = free (t.lMap Φ) :=
  by simp[free, lMap_bind]; congr; exact funext $ Fin.lastCases (by simp) (by simp)

lemma lMap_fix (t : SyntacticSemiterm L₁ n) : (fix t).lMap Φ = fix (t.lMap Φ) :=
  by simp[fix, lMap_bind]; congr; funext x; cases x <;> simp

end lMap

end Semiterm

/-!
### Rewriting system of formulae

-/


namespace Rew

open Semiformula

variable
  {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {ξ : Type v} {ξ₁ : Type v₁} {ξ₂ : Type v₂} {ξ₃ : Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def loMap : ⦃n₁ n₂ : ℕ⦄ → Rew L ξ₁ n₁ ξ₂ n₂ → Semiformula L ξ₁ n₁ → Semiformula L ξ₂ n₂
  | _, _, _, ⊤        => ⊤
  | _, _, _, ⊥        => ⊥
  | _, _, ω, rel r v  => rel r (ω ∘ v)
  | _, _, ω, nrel r v => nrel r (ω ∘ v)
  | _, _, ω, p ⋏ q    => ω.loMap p ⋏ ω.loMap q
  | _, _, ω, p ⋎ q    => ω.loMap p ⋎ ω.loMap q
  | _, _, ω, ∀' p     => ∀' ω.q.loMap p
  | _, _, ω, ∃' p     => ∃' ω.q.loMap p

section

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

lemma loMap_neg (p : Semiformula L ξ₁ n₁) :
    ω.loMap (~p) = ~ω.loMap p :=
  by induction p using Semiformula.rec' generalizing n₂ <;> simp[*, loMap, ←Semiformula.neg_eq]

lemma ext_loMap' {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} (h : ω₁ = ω₂) (p : Semiformula L ξ₁ n₁) :
  ω₁.loMap p = ω₂.loMap p:= by simp[h]

lemma neg' (p : Semiformula L ξ₁ n₁) : ω.loMap (~p) = ~ω.loMap p := loMap_neg ω p

lemma or' (p q : Semiformula L ξ₁ n₁) : ω.loMap (p ⋎ q) = ω.loMap p ⋎ ω.loMap q := by rfl

def hom (ω : Rew L ξ₁ n₁ ξ₂ n₂) : Semiformula L ξ₁ n₁ →L Semiformula L ξ₂ n₂ where
  map_top' := by rfl
  map_bot' := by rfl
  map_neg' := ω.loMap_neg
  map_and' := fun p q => by rfl
  map_or' := fun p q => by rfl
  map_imply' := fun p q => by simp[Semiformula.imp_eq, neg', or']

/-
instance : FunLike (Rew L ξ₁ n₁ ξ₂ n₂) (Semiformula L ξ₁ n₁) (fun _ => Semiformula L ξ₂ n₂) where
  coe := fun ω => loMap ω
  coe_injective' := fun ω₁ ω₂ h => ext_loMap ω₁ ω₂ (congr_fun h)

instance : CoeFun (Rew L ξ₁ n₁ ξ₂ n₂) (fun _ => Semiformula L ξ₁ n₁ → Semiformula L ξ₂ n₂) :=
  FunLike.hasCoeToFun

scoped[FirstOrder] notation:max ω "ᵀ" => (ω : Semiterm _ _ _ → Semiterm _ _ _)

scoped[FirstOrder] notation:max ω "ᴾ" => (ω : Semiformula _ _ _ → Semiformula _ _ _)

lemma neg' (p : Semiformula L ξ₁ n₁) : ω (~p) = ~ω p := loMap_neg ω p

lemma or' (p q : Semiformula L ξ₁ n₁) : ω (p ⋎ q) = ω p ⋎ ω q := by rfl

instance : LogicSymbol.homClass (Rew L ξ₁ n₁ ξ₂ n₂) (Semiformula L ξ₁ n₁)
    (Semiformula L ξ₂ n₂) where
  map_top := fun ω => by rfl
  map_bot := fun ω => by rfl
  map_neg := loMap_neg
  map_and := fun ω p q => by rfl
  map_or := fun ω p q => by rfl
  map_imply := fun ω p q => by simp[Semiformula.imp_eq, neg', or']

-/

lemma hom_eq_loMap : ω.hom = ω.loMap := rfl

protected lemma rel {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω.hom (rel r v) = rel r (fun i => ω (v i)) := rfl

protected lemma nrel {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω.hom (nrel r v) = nrel r (fun i => ω (v i)) := by rfl

lemma rel' {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω.hom (rel r v) = rel r (ω ∘ v) := by rfl

lemma nrel' {k} {r : L.Rel k} {v : Fin k → Semiterm L ξ₁ n₁} :
    ω.hom (nrel r v) = nrel r (ω ∘ v) := by rfl

@[simp] lemma rel0 {r : L.Rel 0} {v : Fin 0 → Semiterm L ξ₁ n₁} :
    ω.hom (rel r v) = rel r ![] := by simp[ω.rel, Matrix.empty_eq]

@[simp] lemma rel1 {r : L.Rel 1} {t : Semiterm L ξ₁ n₁} :
    ω.hom (rel r ![t]) = rel r ![ω t] := by simp[ω.rel, Matrix.constant_eq_singleton]

@[simp] lemma rel2 {r : L.Rel 2} {t₁ t₂ : Semiterm L ξ₁ n₁} :
    ω.hom (rel r ![t₁, t₂]) = rel r ![ω t₁, ω t₂] := by simp[ω.rel]; funext i;
    induction i using Fin.induction <;> simp

@[simp] lemma rel3 {r : L.Rel 3} {t₁ t₂ t₃ : Semiterm L ξ₁ n₁} :
    ω.hom (rel r ![t₁, t₂, t₃]) = rel r ![ω t₁, ω t₂, ω t₃] := by
  simp[ω.rel]; funext i; induction' i using Fin.induction with i <;> simp;
    induction' i using Fin.induction with i <;> simp

@[simp] lemma nrel0 {r : L.Rel 0} {v : Fin 0 → Semiterm L ξ₁ n₁} :
    ω.hom (nrel r v) = nrel r ![] := by simp[ω.nrel, Matrix.empty_eq]

@[simp] lemma nrel1 {r : L.Rel 1} {t : Semiterm L ξ₁ n₁} :
    ω.hom (nrel r ![t]) = nrel r ![ω t] := by simp[ω.nrel, Matrix.constant_eq_singleton]

@[simp] lemma nrel2 {r : L.Rel 2} {t₁ t₂ : Semiterm L ξ₁ n₁} :
    ω.hom (nrel r ![t₁, t₂]) = nrel r ![ω t₁, ω t₂] := by simp[ω.nrel]; funext i;
    induction i using Fin.induction <;> simp

@[simp] lemma nrel3 {r : L.Rel 3} {t₁ t₂ t₃ : Semiterm L ξ₁ n₁} :
    ω.hom (nrel r ![t₁, t₂, t₃]) = nrel r ![ω t₁, ω t₂, ω t₃] := by
  simp[ω.nrel]; funext i; induction' i using Fin.induction with i <;> simp;
  induction' i using Fin.induction with i <;> simp

@[simp] protected lemma all {p : Semiformula L ξ₁ (n₁ + 1)} :
    ω.hom (∀' p) = ∀' ω.q.hom p := by rfl

@[simp] protected lemma ex {p : Semiformula L ξ₁ (n₁ + 1)} :
    ω.hom (∃' p) = ∃' ω.q.hom p := by rfl

@[simp] protected lemma ball {p q : Semiformula L ξ₁ (n₁ + 1)} :
    ω.hom (∀[p] q) = ∀[ω.q.hom p] ω.q.hom q := by simp[ball_eq]

@[simp] protected lemma bex {p q : Semiformula L ξ₁ (n₁ + 1)} :
    ω.hom (∃[p] q) = ∃[ω.q.hom p] ω.q.hom q := by simp[bex_eq]

attribute [irreducible] hom

@[simp] lemma complexity (p : Semiformula L ξ₁ n₁) : (ω.hom p).complexity = p.complexity := by
  induction p using Semiformula.rec' generalizing n₂ <;> simp[*, Rew.rel, Rew.nrel]

lemma hom_ext' {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} (h : ω₁ = ω₂) {p} : ω₁.hom p = ω₂.hom p := by simp[h]

end

@[simp] lemma hom_id_eq : (Rew.id.hom : Semiformula L ξ n →L Semiformula L ξ n) =
    LogicSymbol.Hom.id := by
  ext p; induction p using Semiformula.rec' <;> simp[Rew.rel, Rew.nrel, *]

lemma hom_comp_eq (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) :
    (ω₂.comp ω₁).hom = ω₂.hom.comp ω₁.hom := by
  ext p; simp; induction p using Semiformula.rec' generalizing n₂ n₃ <;>
  simp[Rew.rel, Rew.nrel, comp_app, q_comp, *]

lemma hom_comp_app (ω₂ : Rew L ξ₂ n₂ ξ₃ n₃) (ω₁ : Rew L ξ₁ n₁ ξ₂ n₂) (p : Semiformula L ξ₁ n₁) :
    (ω₂.comp ω₁).hom p = ω₂.hom (ω₁.hom p) := by simp[hom_comp_eq]

lemma mapl_inj : ∀ {n₁ n₂ ξ₁ ξ₂} {b : Fin n₁ → Fin n₂} {e : ξ₁ → ξ₂},
    (hb : Function.Injective b) → (hf : Function.Injective e) → Function.Injective $
    (map (L := L) b e).hom
  | _, _, _, _, _, _, _,  _,  ⊤,        p => by cases p using cases' <;> simp[Rew.rel, Rew.nrel]
  | _, _, _, _, _, _, _,  _,  ⊥,        p => by cases p using cases' <;> simp[Rew.rel, Rew.nrel]
  | _, _, _, _, _, _, hb, hf, rel r v,  p => by
    cases p using cases' <;> simp[Rew.rel, Rew.nrel]
    case hrel =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact map_inj hb hf (congr_fun h i)
  | _, _, _, _, _, _, hb, hf, nrel r v, p => by
    cases p using cases' <;> simp[Rew.rel, Rew.nrel]
    case hnrel =>
      rintro rfl; simp; rintro rfl h; simp
      funext i; exact map_inj hb hf (congr_fun h i)
  | _, _, _, _, _, _, hb, hf, p ⋏ q,    r => by
    cases r using cases' <;> simp[Rew.rel, Rew.nrel]
    intro hp hq; exact ⟨mapl_inj hb hf hp, mapl_inj hb hf hq⟩
  | _, _, _, _, _, _, hb, hf, p ⋎ q,    r => by
    cases r using cases' <;> simp[Rew.rel, Rew.nrel]
    intro hp hq; exact ⟨mapl_inj hb hf hp, mapl_inj hb hf hq⟩
  | _, _, _, _, b, e, hb, hf, ∀' p,     q => by
    cases q using cases' <;> simp[Rew.rel, Rew.nrel, q_map]
    intro h; exact mapl_inj (b := 0 :> Fin.succ ∘ b)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb)
      (fun _ => (Fin.succ_ne_zero _).symm)) hf h
  | _, _, _, _, b, e, hb, hf, ∃' p,     q => by
    cases q using cases' <;> simp[Rew.rel, Rew.nrel, q_map]
    intro h; exact mapl_inj (b := 0 :> Fin.succ ∘ b)
      (Matrix.injective_vecCons ((Fin.succ_injective _).comp hb)
      (fun _ => (Fin.succ_ne_zero _).symm)) hf h

lemma emb.hom_injective {o} [e : IsEmpty o] : Function.Injective
  (emb.hom : Semiformula L o n → Semiformula L ξ n) :=
  by simp[emb]; exact mapl_inj Function.injective_id (fun x => IsEmpty.elim e x)

lemma shift.hom_injective : Function.Injective
  (shift.hom : SyntacticSemiformula L n → SyntacticSemiformula L n) :=
  by simp[shift]; exact mapl_inj Function.injective_id Nat.succ_injective

@[simp] lemma hom_fix_free (p : SyntacticSemiformula L (n + 1)) :
    fix.hom (free.hom p) = p := by simp[←hom_comp_app]

@[simp] lemma hom_free_fix (p : SyntacticSemiformula L n) :
    free.hom (fix.hom p) = p := by simp[←hom_comp_app]

@[simp] lemma hom_substs_mbar_zero_comp_shift_eq_free (p : SyntacticSemiformula L 1) :
    (substs ![&0]).hom (Rew.shift.hom p) = free.hom p := by
  simp[←hom_comp_app, substs_mbar_zero_comp_shift_eq_free]

@[simp] protected lemma emb_univClosure {o} [e : IsEmpty o] {σ : Semiformula L o n} :
    (emb.hom (univClosure σ) : Semiformula L ξ 0) = univClosure (emb.hom σ) := by
  induction n <;> simp[*, univClosure_succ]

variable (ω : Rew L ξ₁ n₁ ξ₂ n₂)

@[simp] lemma eq_top_iff {p : Semiformula L ξ₁ n₁} : ω.hom p = ⊤ ↔ p = ⊤ := by
  cases p using Semiformula.rec' <;> simp[Rew.rel, Rew.nrel]

@[simp] lemma eq_bot_iff {p : Semiformula L ξ₁ n₁} : ω.hom p = ⊥ ↔ p = ⊥ := by
  cases p using Semiformula.rec' <;> simp[Rew.rel, Rew.nrel]

lemma eq_rel_iff {p : Semiformula L ξ₁ n₁} {k} {r : L.Rel k} {v} :
    ω.hom p = Semiformula.rel r v ↔ ∃ v', ω ∘ v' = v ∧ p = Semiformula.rel r v' := by
  cases p using Semiformula.rec' <;> simp[Rew.rel, Rew.nrel]
  case hrel k' r' v =>
    by_cases hk : k' = k <;> simp[hk]; rcases hk with rfl; simp
    by_cases hr : r' = r <;> simp[hr, Function.funext_iff]

lemma eq_nrel_iff {p : Semiformula L ξ₁ n₁} {k} {r : L.Rel k} {v} :
    ω.hom p = Semiformula.nrel r v ↔ ∃ v', ω ∘ v' = v ∧ p = Semiformula.nrel r v' := by
  cases p using Semiformula.rec' <;> simp[Rew.rel, Rew.nrel]
  case hnrel k' r' v =>
    by_cases hk : k' = k <;> simp[hk]; rcases hk with rfl; simp
    by_cases hr : r' = r <;> simp[hr, Function.funext_iff]

@[simp] lemma eq_and_iff {p : Semiformula L ξ₁ n₁} {q₁ q₂} :
    ω.hom p = q₁ ⋏ q₂ ↔ ∃ p₁ p₂, ω.hom p₁ = q₁ ∧ ω.hom p₂ = q₂ ∧ p = p₁ ⋏ p₂ := by
  cases p using Semiformula.rec' <;> simp[Rew.rel, Rew.nrel]

@[simp] lemma eq_or_iff {p : Semiformula L ξ₁ n₁} {q₁ q₂} :
    ω.hom p = q₁ ⋎ q₂ ↔ ∃ p₁ p₂, ω.hom p₁ = q₁ ∧ ω.hom p₂ = q₂ ∧ p = p₁ ⋎ p₂ := by
  cases p using Semiformula.rec' <;> simp[Rew.rel, Rew.nrel]

lemma eq_all_iff {p : Semiformula L ξ₁ n₁} {q} :
    ω.hom p = ∀' q ↔ ∃ p', ω.q.hom p' = q ∧ p = ∀' p' := by
  cases p using Semiformula.rec' <;> simp[Rew.rel, Rew.nrel]

lemma eq_ex_iff {p : Semiformula L ξ₁ n₁} {q} :
    ω.hom p = ∃' q ↔ ∃ p', ω.q.hom p' = q ∧ p = ∃' p' := by
  cases p using Semiformula.rec' <;> simp[Rew.rel, Rew.nrel]

@[simp] lemma eq_neg_iff {p : Semiformula L ξ₁ n₁} {q₁ q₂} :
    ω.hom p = q₁ ⟶ q₂ ↔ ∃ p₁ p₂, ω.hom p₁ = q₁ ∧ ω.hom p₂ = q₂ ∧ p = p₁ ⟶ p₂ := by
  simp[imp_eq]; constructor
  · rintro ⟨p₁, hp₁, q₂, rfl, rfl⟩; exact ⟨~p₁, by simp[hp₁]⟩
  · rintro ⟨p₁, rfl, p₂, rfl, rfl⟩; exact ⟨~p₁, by simp, p₂, by simp⟩

lemma eq_ball_iff {p : Semiformula L ξ₁ n₁} {q₁ q₂} :
    (ω.hom p = ∀[q₁] q₂) ↔ ∃ p₁ p₂, ω.q.hom p₁ = q₁ ∧ ω.q.hom p₂ = q₂ ∧ p = ∀[p₁] p₂ := by
  simp[LogicSymbol.ball, eq_all_iff]; constructor
  · rintro ⟨p', ⟨p₁, rfl, p₂, rfl, rfl⟩, rfl⟩; exact ⟨p₁, rfl, p₂, rfl, rfl⟩
  · rintro ⟨p₁, rfl, p₂, rfl, rfl⟩; simp

lemma eq_bex_iff {p : Semiformula L ξ₁ n₁} {q₁ q₂} :
    (ω.hom p = ∃[q₁] q₂) ↔ ∃ p₁ p₂, ω.q.hom p₁ = q₁ ∧ ω.q.hom p₂ = q₂ ∧ p = ∃[p₁] p₂ := by
  simp[LogicSymbol.bex, eq_ex_iff]; constructor
  · rintro ⟨p', ⟨p₁, rfl, p₂, rfl, rfl⟩, rfl⟩; exact ⟨p₁, rfl, p₂, rfl, rfl⟩
  · rintro ⟨p₁, rfl, p₂, rfl, rfl⟩; simp

lemma eq_hom_rewriteMap_of_funEqOn_fv {ξ₁ ξ₂ n₁ n₂} [DecidableEq ξ₁]
    (p : Semiformula L ξ₁ n₁) (f g : ξ₁ → Semiterm L ξ₂ n₂) (h : Function.funEqOn (· ∈ p.fv) f g) :
    (Rew.rewriteMap f).hom p = (Rew.rewriteMap g).hom p := by
  induction p using rec'
  case hverum => simp
  case hfalsum => simp
  case hrel r v =>
    simp [Rew.rel]; funext i
    exact eq_rewriteMap_of_funEqOn_fv (v i) f g (by intro x (hx : x ∈ (v i).fv);
    exact h _ (by simp [fv_rel]; exact ⟨i, hx⟩))
  case hnrel r v =>
    simp [Rew.nrel]; funext i
    exact eq_rewriteMap_of_funEqOn_fv (v i) f g (by intro x (hx : x ∈ (v i).fv);
    exact h _ (by simp [fv_nrel]; exact ⟨i, hx⟩))
  case hand p q ihp ihq =>
    simp; exact ⟨ihp (by intro x (hx : x ∈ p.fv);
    exact h _ (by simp [hx])), ihq (by intro x (hx : x ∈ q.fv); exact h _ (by simp [hx]))⟩
  case hor p q ihp ihq =>
    simp; exact ⟨ihp (by intro x (hx : x ∈ p.fv);
    exact h _ (by simp [hx])), ihq (by intro x (hx : x ∈ q.fv); exact h _ (by simp [hx]))⟩
  case hall p ih => simp; exact ih (by intro x (hx : x ∈ fv p); exact h _ (by simp [hx]))
  case hex p ih => simp; exact ih (by intro x (hx : x ∈ fv p); exact h _ (by simp [hx]))

end Rew

scoped syntax (name := substsHomNotation) term:max "/[" term,* "]" : term

scoped macro_rules (kind := substsHomNotation)
  | `($p:term /[$terms:term,*]) => `((Rew.substs ![$terms,*]).hom $p)

namespace Semiformula

variable {L : Language.{u}} {ξ : Type v} {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def shiftEmb : SyntacticSemiformula L n ↪ SyntacticSemiformula L n where
  toFun := Rew.shift.hom
  inj' := Rew.shift.hom_injective

lemma shiftEmb_eq_shift (p : SyntacticSemiformula L n) :
  shiftEmb p = Rew.shift.hom p := rfl

@[elab_as_elim]
def formulaRec {C : SyntacticFormula L → Sort _}
  (hverum  : C ⊤)
  (hfalsum : C ⊥)
  (hrel    : ∀ {l : ℕ} (r : L.Rel l) (v : Fin l → SyntacticTerm L), C (rel r v))
  (hnrel   : ∀ {l : ℕ} (r : L.Rel l) (v : Fin l → SyntacticTerm L), C (nrel r v))
  (hand    : ∀ (p q : SyntacticFormula L), C p → C q → C (p ⋏ q))
  (hor     : ∀ (p q : SyntacticFormula L), C p → C q → C (p ⋎ q))
  (hall    : ∀ (p : SyntacticSemiformula L 1), C (Rew.free.hom p) → C (∀' p))
  (hex     : ∀ (p : SyntacticSemiformula L 1), C (Rew.free.hom p) → C (∃' p)) :
    ∀ (p : SyntacticFormula L), C p
  | ⊤        => hverum
  | ⊥        => hfalsum
  | rel r v  => hrel r v
  | nrel r v => hnrel r v
  | p ⋏ q    => hand p q (formulaRec hverum hfalsum hrel hnrel hand hor hall hex p)
    (formulaRec hverum hfalsum hrel hnrel hand hor hall hex q)
  | p ⋎ q    => hor p q (formulaRec hverum hfalsum hrel hnrel hand hor hall hex p)
    (formulaRec hverum hfalsum hrel hnrel hand hor hall hex q)
  | ∀' p     => hall p (formulaRec hverum hfalsum hrel hnrel hand hor hall hex (Rew.free.hom p))
  | ∃' p     => hex p (formulaRec hverum hfalsum hrel hnrel hand hor hall hex (Rew.free.hom p))
  termination_by formulaRec _ _ _ _ _ _ _ _ p => p.complexity

@[simp] lemma fvarList_emb {o : Type w} [IsEmpty o] (p : Semiformula L o n) :
    fvarList (Rew.emb.hom p : Semiformula L ξ n) = [] := by
  induction p using rec' <;> simp[*, Rew.rel, Rew.nrel, fvarList, ←neg_eq]

lemma rew_eq_of_funEqOn {ω₁ ω₂ : Rew L ξ₁ n₁ ξ₂ n₂} {p}
    (hb : ∀ x, ω₁ #x = ω₂ #x) (hf : Function.funEqOn (fvar? p) (ω₁ ∘ Semiterm.fvar)
    (ω₂ ∘ Semiterm.fvar)) : ω₁.hom p = ω₂.hom p := by
  unfold fvar? at*
  induction p using rec' generalizing n₂ <;> simp[*, Rew.rel, Rew.nrel] <;> simp[fvarList] at hf
  case hrel =>
    funext i
    exact Semiterm.rew_eq_of_funEqOn _ _ _ hb
      (hf.of_subset (fun x hx ↦ ⟨i, hx⟩))
  case hnrel =>
    funext i
    exact Semiterm.rew_eq_of_funEqOn _ _ _ hb
      (hf.of_subset (fun x hx ↦ ⟨i, hx⟩))
  case hand ihp ihq =>
    exact ⟨ihp hb (hf.of_subset (fun x hx => Or.inl hx)), ihq hb
    (hf.of_subset (fun x hx => Or.inr hx))⟩
  case hor ihp ihq =>
    exact ⟨ihp hb (hf.of_subset (fun x hx => Or.inl hx)), ihq hb
    (hf.of_subset (fun x hx => Or.inr hx))⟩
  case hall ih =>
    exact ih (fun x => by cases x using Fin.cases <;> simp[hb])
    (fun x hx => by simp; exact congr_arg _ (hf x hx))
  case hex ih =>
    exact ih (fun x => by cases x using Fin.cases <;> simp[hb])
    (fun x hx => by simp; exact congr_arg _ (hf x hx))

lemma rew_eq_of_funEqOn₀ {ω₁ ω₂ : Rew L ξ₁ 0 ξ₂ n₂} {p} (hf : Function.funEqOn (fvar? p)
  (ω₁ ∘ Semiterm.fvar) (ω₂ ∘ Semiterm.fvar)) : ω₁.hom p = ω₂.hom p :=
  rew_eq_of_funEqOn (fun x => Fin.elim0 x) hf

@[simp] lemma ex_ne_subst (p : Semiformula L ξ 1) (t) : [→ t].hom p ≠ ∃' p :=
  ne_of_ne_complexity (by simp)

section lMap

variable {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {ξ : Type v} {Φ : L₁ →ᵥ L₂}

lemma lMap_bind (b : Fin n₁ → Semiterm L₁ ξ₂ n₂) (e : ξ₁ → Semiterm L₁ ξ₂ n₂) (p) :
    lMap Φ ((Rew.bind b e).hom p) = (Rew.bind (Semiterm.lMap Φ ∘ b)
    (Semiterm.lMap Φ ∘ e)).hom (lMap Φ p) := by
  induction p using rec' generalizing ξ₂ n₂ <;>
  simp[*, Rew.rel, Rew.nrel, lMap_rel, lMap_nrel, Semiterm.lMap_bind, Rew.q_bind,
    Matrix.comp_vecCons', Semiterm.lMap_bShift, Function.comp]

lemma lMap_map (b : Fin n₁ → Fin n₂) (e : ξ₁ → ξ₂) (p) :
    lMap Φ ((Rew.map b e).hom p) = (Rew.map b e).hom (lMap Φ p) := lMap_bind _ _ _

lemma lMap_rewrite (f : ξ → Semiterm L₁ ξ n) (p : Semiformula L₁ ξ n) :
    lMap Φ ((Rew.rewrite f).hom p) = (Rew.rewrite (Semiterm.lMap Φ ∘ f)).hom (lMap Φ p) :=
  by simp[Rew.rewrite, lMap_bind, Function.comp]

lemma lMap_substs (w : Fin k → Semiterm L₁ ξ n) (p : Semiformula L₁ ξ k) :
    lMap Φ ((Rew.substs w).hom p) = (Rew.substs (Semiterm.lMap Φ ∘ w)).hom (lMap Φ p) :=
    lMap_bind _ _ _

lemma lMap_shift (p : SyntacticSemiformula L₁ n) : lMap Φ (Rew.shift.hom p) = Rew.shift.hom
  (lMap Φ p) := lMap_bind _ _ _

lemma lMap_free (p : SyntacticSemiformula L₁ (n + 1)) : lMap Φ (Rew.free.hom p) = Rew.free.hom
    (lMap Φ p) := by
  simp[Rew.free, lMap_bind, Function.comp, Matrix.comp_vecConsLast]

lemma lMap_fix (p : SyntacticSemiformula L₁ n) : lMap Φ (Rew.fix.hom p) = Rew.fix.hom (lMap Φ p) :=
  by simp[Rew.fix, lMap_bind, Function.comp]; congr; { funext x; cases x <;> simp }

lemma lMap_emb {o : Type w} [IsEmpty o] (p : Semiformula L₁ o n) :
    (lMap Φ (Rew.emb.hom p) : Semiformula L₂ ξ n) = Rew.emb.hom (lMap Φ p) := lMap_bind _ _ _

end lMap

end Semiformula

def Formula.fvUnivClosure [DecidableEq ξ] (p : Formula L ξ) : Sentence L :=
  ∀* (Rew.toS.hom <| (Rew.rewriteMap (Semiformula.fvListing p)).hom p)

prefix:64 "∀ᶠ* " => Formula.fvUnivClosure

@[simp] lemma Formula.fv_univ_closure_sentence [h : IsEmpty ξ] [DecidableEq ξ] (σ : Formula L ξ) :
  Formula.fvUnivClosure σ = ∀' Rew.empty.hom σ := by
  simp [fvUnivClosure, ←Rew.hom_comp_app, Rew.eq_empty]
  have : σ.fvarList.length = 0 := by simp
  rw [this]; rfl

namespace Rew

variable {L : Language} {ξ ξ₁ ξ₂ : Type*} {n n₁ n₂} (ω : Rew L ξ₁ n₁ ξ₂ n₂)

@[simp] protected lemma open_iff {p : Semiformula L ξ₁ n₁} : (ω.hom p).Open ↔ p.Open := by
  induction p using Semiformula.rec' <;> try simp [Rew.rel, Rew.nrel, *]

end Rew

end FirstOrder

end ProofTheory
