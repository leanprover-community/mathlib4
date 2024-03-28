/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.ProofTheory.FirstOrder.Basic.Syntax.Term

/-!
# Formulas of first-order logic

This file defines the formulas of first-order logic.

`p : Semiformula L ξ n` is a (semi-)formula of language `L` with bounded variables of `Fin n` and
free variables of `ξ`. The quantification is represented by de Bruijn index.
-/

namespace ProofTheory

namespace FirstOrder

universe u u₁ u₂ u₃ v v₁ v₂ v₃

inductive Semiformula (L : Language.{u}) (ξ : Type v) : ℕ → Type (max u v) where
  | verum  {n} : Semiformula L ξ n
  | falsum {n} : Semiformula L ξ n
  | rel    {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | nrel   {n} : {arity : ℕ} → L.Rel arity → (Fin arity → Semiterm L ξ n) → Semiformula L ξ n
  | and    {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | or     {n} : Semiformula L ξ n → Semiformula L ξ n → Semiformula L ξ n
  | all    {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n
  | ex     {n} : Semiformula L ξ (n + 1) → Semiformula L ξ n

abbrev Formula (L : Language.{u}) (ξ : Type v) := Semiformula L ξ 0

abbrev Sentence (L : Language.{u}) := Formula L Empty

abbrev Semisentence (L : Language.{u}) (n : ℕ) := Semiformula L Empty n

abbrev SyntacticSemiformula (L : Language.{u}) (n : ℕ) := Semiformula L ℕ n

abbrev SyntacticFormula (L : Language.{u}) := SyntacticSemiformula L 0

namespace Semiformula

variable
  {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {ξ : Type v} {ξ₁ : Type v₁} {ξ₂ : Type v₂} {ξ₃ : Type v₃}
  {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def neg {n} : Semiformula L ξ n → Semiformula L ξ n
  | verum    => falsum
  | falsum   => verum
  | rel r v  => nrel r v
  | nrel r v => rel r v
  | and p q  => or (neg p) (neg q)
  | or p q   => and (neg p) (neg q)
  | all p    => ex (neg p)
  | ex p     => all (neg p)

lemma neg_neg (p : Semiformula L ξ n) : neg (neg p) = p :=
  by induction p <;> simp[*, neg]

instance : LogicSymbol (Semiformula L ξ n) where
  tilde := neg
  arrow := fun p q => or (neg p) q
  wedge := and
  vee := or
  top := verum
  bot := falsum

instance : DeMorgan (Semiformula L ξ n) where
  verum := rfl
  falsum := rfl
  imply := fun _ _ => rfl
  and := fun _ _ => rfl
  or := fun _ _ => rfl
  neg := neg_neg

instance : UnivQuantifier (Semiformula L ξ) := ⟨all⟩

instance : ExQuantifier (Semiformula L ξ) := ⟨ex⟩

section ToString

variable [∀ k, ToString (L.Func k)] [∀ k, ToString (L.Rel k)] [ToString ξ]

def toStr : ∀ {n}, Semiformula L ξ n → String
  | _, ⊤                         => "\\top"
  | _, ⊥                         => "\\bot"
  | _, rel (arity := 0) r _      => "{" ++ toString r ++ "}"
  | _, rel (arity := _ + 1) r v  => "{" ++ toString r ++ "} \\left(" ++ String.vecToStr
    (fun i => toString (v i)) ++ "\\right)"
  | _, nrel (arity := 0) r _     => "\\lnot {" ++ toString r ++ "}"
  | _, nrel (arity := _ + 1) r v => "\\lnot {" ++ toString r ++ "} \\left(" ++ String.vecToStr
    (fun i => toString (v i)) ++ "\\right)"
  | _, p ⋏ q                     => "\\left(" ++ toStr p ++ " \\land " ++ toStr q ++ "\\right)"
  | _, p ⋎ q                     => "\\left(" ++ toStr p ++ " \\lor "  ++ toStr q ++ "\\right)"
  | n, all p                     => "(\\forall x_{" ++ toString n ++ "}) " ++ toStr p
  | n, ex p                      => "(\\exists x_{" ++ toString n ++ "}) " ++ toStr p

instance : Repr (Semiformula L ξ n) := ⟨fun t _ => toStr t⟩

instance : ToString (Semiformula L ξ n) := ⟨toStr⟩

end ToString

@[simp] lemma neg_top : ~(⊤ : Semiformula L ξ n) = ⊥ := rfl

@[simp] lemma neg_bot : ~(⊥ : Semiformula L ξ n) = ⊤ := rfl

@[simp] lemma neg_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ~(rel r v) = nrel r v := rfl

@[simp] lemma neg_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : ~(nrel r v) = rel r v := rfl

@[simp] lemma neg_and (p q : Semiformula L ξ n) : ~(p ⋏ q) = ~p ⋎ ~q := rfl

@[simp] lemma neg_or (p q : Semiformula L ξ n) : ~(p ⋎ q) = ~p ⋏ ~q := rfl

@[simp] lemma neg_all (p : Semiformula L ξ (n + 1)) : ~(∀' p) = ∃' ~p := rfl

@[simp] lemma neg_ex (p : Semiformula L ξ (n + 1)) : ~(∃' p) = ∀' ~p := rfl

@[simp] lemma neg_neg' (p : Semiformula L ξ n) : ~~p = p := neg_neg p

@[simp] lemma neg_inj (p q : Semiformula L ξ n) : ~p = ~q ↔ p = q := by
  constructor
  · intro h; simpa using congr_arg (~·) h
  · exact congr_arg _

lemma neg_eq (p : Semiformula L ξ n) : ~p = neg p := rfl

lemma imp_eq (p q : Semiformula L ξ n) : p ⟶ q = ~p ⋎ q := rfl

lemma iff_eq (p q : Semiformula L ξ n) : p ⟷ q = (~p ⋎ q) ⋏ (~q ⋎ p) := rfl

lemma ball_eq (p q : Semiformula L ξ (n + 1)) : (∀[p] q) = ∀' (p ⟶ q) := rfl

lemma bex_eq (p q : Semiformula L ξ (n + 1)) : (∃[p] q) = ∃' (p ⋏ q) := rfl

@[simp] lemma neg_ball (p q : Semiformula L ξ (n + 1)) : ~(∀[p] q) = ∃[p] ~q := by
  simp[LogicSymbol.ball, LogicSymbol.bex, imp_eq]

@[simp] lemma neg_bex (p q : Semiformula L ξ (n + 1)) : ~(∃[p] q) = ∀[p] ~q := by
  simp[LogicSymbol.ball, LogicSymbol.bex, imp_eq]

@[simp] lemma and_inj (p₁ q₁ p₂ q₂ : Semiformula L ξ n) : p₁ ⋏ p₂ = q₁ ⋏ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[Wedge.wedge]

@[simp] lemma or_inj (p₁ q₁ p₂ q₂ : Semiformula L ξ n) : p₁ ⋎ p₂ = q₁ ⋎ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ :=
by simp[Vee.vee]

@[simp] lemma all_inj (p q : Semiformula L ξ (n + 1)) : ∀' p = ∀' q ↔ p = q :=
  by simp[UnivQuantifier.univ]

@[simp] lemma ex_inj (p q : Semiformula L ξ (n + 1)) : ∃' p = ∃' q ↔ p = q :=
  by simp[ExQuantifier.ex]

@[simp] lemma univClosure_inj (p q : Semiformula L ξ n) : ∀* p = ∀* q ↔ p = q := by
  induction n <;> simp [*, univClosure_succ]

@[simp] lemma exClosure_inj (p q : Semiformula L ξ n) : ∃* p = ∃* q ↔ p = q := by
  induction n <;> simp [*, exClosure_succ]

@[simp] lemma imp_inj {p₁ p₂ q₁ q₂ : Semiformula L ξ n} :
    p₁ ⟶ p₂ = q₁ ⟶ q₂ ↔ p₁ = q₁ ∧ p₂ = q₂ := by simp [imp_eq]

abbrev rel! (L : Language.{u}) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := rel r v

abbrev nrel! (L : Language.{u}) (k) (r : L.Rel k) (v : Fin k → Semiterm L ξ n) := nrel r v

def complexity : {n : ℕ} → Semiformula L ξ n → ℕ
  | _, ⊤        => 0
  | _, ⊥        => 0
  | _, rel _ _  => 0
  | _, nrel _ _ => 0
  | _, p ⋏ q    => max p.complexity q.complexity + 1
  | _, p ⋎ q    => max p.complexity q.complexity + 1
  | _, ∀' p     => p.complexity + 1
  | _, ∃' p     => p.complexity + 1

@[simp] lemma complexity_top : complexity (⊤ : Semiformula L ξ n) = 0 := rfl

@[simp] lemma complexity_bot : complexity (⊥ : Semiformula L ξ n) = 0 := rfl

@[simp] lemma complexity_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
  complexity (rel r v) = 0 := rfl

@[simp] lemma complexity_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
  complexity (nrel r v) = 0 := rfl

@[simp] lemma complexity_and (p q : Semiformula L ξ n) :
  complexity (p ⋏ q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_and' (p q : Semiformula L ξ n) :
  complexity (and p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_or (p q : Semiformula L ξ n) :
  complexity (p ⋎ q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_or' (p q : Semiformula L ξ n) :
  complexity (or p q) = max p.complexity q.complexity + 1 := rfl

@[simp] lemma complexity_all (p : Semiformula L ξ (n + 1)) :
  complexity (∀' p) = p.complexity + 1 := rfl

@[simp] lemma complexity_all' (p : Semiformula L ξ (n + 1)) :
  complexity (all p) = p.complexity + 1 := rfl

@[simp] lemma complexity_ex (p : Semiformula L ξ (n + 1)) :
  complexity (∃' p) = p.complexity + 1 := rfl

@[simp] lemma complexity_ex' (p : Semiformula L ξ (n + 1)) :
  complexity (ex p) = p.complexity + 1 := rfl

@[elab_as_elim]
def cases' {C : ∀ n, Semiformula L ξ n → Sort w}
    (hverum  : ∀ {n : ℕ}, C n ⊤)
    (hfalsum : ∀ {n : ℕ}, C n ⊥)
    (hrel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hnrel   : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hand    : ∀ {n : ℕ} (p q : Semiformula L ξ n), C n (p ⋏ q))
    (hor     : ∀ {n : ℕ} (p q : Semiformula L ξ n), C n (p ⋎ q))
    (hall    : ∀ {n : ℕ} (p : Semiformula L ξ (n + 1)), C n (∀' p))
    (hex     : ∀ {n : ℕ} (p : Semiformula L ξ (n + 1)), C n (∃' p)) :
    ∀ {n : ℕ} (p : Semiformula L ξ n), C n p
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and p q  => hand p q
  | _, or p q   => hor p q
  | _, all p    => hall p
  | _, ex p     => hex p

@[elab_as_elim]
def rec' {C : ∀ n, Semiformula L ξ n → Sort w}
    (hverum  : ∀ {n : ℕ}, C n ⊤)
    (hfalsum : ∀ {n : ℕ}, C n ⊥)
    (hrel    : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (rel r v))
    (hnrel   : ∀ {n k : ℕ} (r : L.Rel k) (v : Fin k → Semiterm L ξ n), C n (nrel r v))
    (hand    : ∀ {n : ℕ} (p q : Semiformula L ξ n), C n p → C n q → C n (p ⋏ q))
    (hor     : ∀ {n : ℕ} (p q : Semiformula L ξ n), C n p → C n q → C n (p ⋎ q))
    (hall    : ∀ {n : ℕ} (p : Semiformula L ξ (n + 1)), C (n + 1) p → C n (∀' p))
    (hex     : ∀ {n : ℕ} (p : Semiformula L ξ (n + 1)), C (n + 1) p → C n (∃' p)) :
    ∀ {n : ℕ} (p : Semiformula L ξ n), C n p
  | _, verum    => hverum
  | _, falsum   => hfalsum
  | _, rel r v  => hrel r v
  | _, nrel r v => hnrel r v
  | _, and p q  => hand p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p)
    (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, or p q   => hor p q (rec' hverum hfalsum hrel hnrel hand hor hall hex p)
    (rec' hverum hfalsum hrel hnrel hand hor hall hex q)
  | _, all p    => hall p (rec' hverum hfalsum hrel hnrel hand hor hall hex p)
  | _, ex p     => hex p (rec' hverum hfalsum hrel hnrel hand hor hall hex p)

@[simp] lemma complexity_neg (p : Semiformula L ξ n) : complexity (~p) = complexity p :=
  by induction p using rec' <;> simp[*]

section Decidable

variable [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)] [DecidableEq ξ]

def hasDecEq : {n : ℕ} → (p q : Semiformula L ξ n) → Decidable (p = q)
  | _, ⊤,        q => by cases q using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | _, ⊥,        q => by cases q using cases' <;>
      { simp; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | _, rel r v,  q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simp[h]; exact Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | _, nrel r v, q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hnrel k₁ k₂ r₂ v₂ =>
        by_cases e : k₁ = k₂
        · rcases e with rfl
          exact match decEq r r₂ with
          | isTrue h  => by simp[h]; exact Matrix.decVec _ _ (fun i => decEq (v i) (v₂ i))
          | isFalse h => isFalse (by simp[h])
        · exact isFalse (by simp[e])
  | _, p ⋏ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hand p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | _, p ⋎ q,    r => by
      cases r using cases' <;> try { simp; exact isFalse not_false }
      case hor p' q' =>
        exact match hasDecEq p p' with
        | isTrue hp =>
          match hasDecEq q q' with
          | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
          | isFalse hq => isFalse (by simp[hp, hq])
        | isFalse hp => isFalse (by simp[hp])
  | _, ∀' p,     q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hall p' => simp; exact hasDecEq p p'
  | _, ∃' p,     q => by
      cases q using cases' <;> try { simp; exact isFalse not_false }
      case hex p' => simp; exact hasDecEq p p'

instance : DecidableEq (Semiformula L ξ n) := hasDecEq

end Decidable

def fv [DecidableEq ξ] : {n : ℕ} → Semiformula L ξ n → Finset ξ
  | _, rel _ v  => .biUnion .univ fun i ↦ (v i).fv
  | _, nrel _ v => .biUnion .univ fun i ↦ (v i).fv
  | _, ⊤        => ∅
  | _, ⊥        => ∅
  | _, p ⋏ q    => fv p ∪ fv q
  | _, p ⋎ q    => fv p ∪ fv q
  | _, ∀' p     => fv p
  | _, ∃' p     => fv p

section fv

variable [DecidableEq ξ]

lemma fv_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (rel r v).fv = .biUnion .univ fun i ↦ (v i).fv := rfl

lemma fv_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) :
    (nrel r v).fv = .biUnion .univ fun i ↦ (v i).fv := rfl

@[simp] lemma fv_verum : (⊤ : Semiformula L ξ n).fv = ∅ := rfl

@[simp] lemma fv_falsum : (⊥ : Semiformula L ξ n).fv = ∅ := rfl

@[simp] lemma fv_and (p q : Semiformula L ξ n) : (p ⋏ q).fv = p.fv ∪ q.fv := rfl

@[simp] lemma fv_or (p q : Semiformula L ξ n) : (p ⋎ q).fv = p.fv ∪ q.fv := rfl

@[simp] lemma fv_all (p : Semiformula L ξ (n + 1)) : (∀' p).fv = p.fv := rfl

@[simp] lemma fv_ex (p : Semiformula L ξ (n + 1)) : (∃' p).fv = p.fv := rfl

@[simp] lemma fv_not (p : Semiformula L ξ n) : (~p).fv = p.fv := by
  induction p using rec' <;> simp [*, fv_rel, fv_nrel]

@[simp] lemma fv_imp (p q : Semiformula L ξ n) : (p ⟶ q).fv = p.fv ∪ q.fv := by simp [imp_eq]

end fv

end Semiformula

namespace Semiformula

variable {L : Language.{u}} {ξ : Type v} {n n₁ n₂ n₂ m m₁ m₂ m₃ : ℕ}

def qr : ∀ {n}, Semiformula L ξ n → ℕ
  | _, ⊤        => 0
  | _, ⊥        => 0
  | _, rel _ _  => 0
  | _, nrel _ _ => 0
  | _, p ⋏ q    => max p.qr q.qr
  | _, p ⋎ q    => max p.qr q.qr
  | _, ∀' p     => p.qr + 1
  | _, ∃' p     => p.qr + 1

@[simp] lemma qr_top : (⊤ : Semiformula L ξ n).qr = 0 := rfl

@[simp] lemma qr_bot : (⊥ : Semiformula L ξ n).qr = 0 := rfl

@[simp] lemma qr_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).qr = 0 := rfl

@[simp] lemma qr_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).qr = 0 := rfl

@[simp] lemma qr_and (p q : Semiformula L ξ n) : (p ⋏ q).qr = max p.qr q.qr := rfl

@[simp] lemma qr_or (p q : Semiformula L ξ n) : (p ⋎ q).qr = max p.qr q.qr := rfl

@[simp] lemma qr_all (p : Semiformula L ξ (n + 1)) : (∀' p).qr = p.qr + 1 := rfl

@[simp] lemma qr_ex (p : Semiformula L ξ (n + 1)) : (∃' p).qr = p.qr + 1 := rfl

@[simp] lemma qr_neg (p : Semiformula L ξ n) : (~p).qr = p.qr := by
  induction' p using rec' <;> simp[*]

@[simp] lemma qr_imply (p q : Semiformula L ξ n) : (p ⟶ q).qr = max p.qr q.qr :=
  by simp[imp_eq]

@[simp] lemma qr_iff (p q : Semiformula L ξ n) : (p ⟷ q).qr = max p.qr q.qr :=
  by simp[iff_eq, total_of]

def Open (p : Semiformula L ξ n) : Prop := p.qr = 0

@[simp] lemma open_top : (⊤ : Semiformula L ξ n).Open := rfl

@[simp] lemma open_bot : (⊥ : Semiformula L ξ n).Open := rfl

@[simp] lemma open_rel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (rel r v).Open := rfl

@[simp] lemma open_nrel {k} (r : L.Rel k) (v : Fin k → Semiterm L ξ n) : (nrel r v).Open := rfl

@[simp] lemma open_and {p q : Semiformula L ξ n} : (p ⋏ q).Open ↔ p.Open ∧ q.Open := by simp[Open]

@[simp] lemma open_or {p q : Semiformula L ξ n} : (p ⋎ q).Open ↔ p.Open ∧ q.Open := by simp[Open]

@[simp] lemma not_open_all {p : Semiformula L ξ (n + 1)} : ¬(∀' p).Open := by simp[Open]

@[simp] lemma not_open_ex {p : Semiformula L ξ (n + 1)} : ¬(∃' p).Open := by simp[Open]

@[simp] lemma open_neg {p : Semiformula L ξ n} : (~p).Open ↔ p.Open := by
  simp[Open]

@[simp] lemma open_imply {p q : Semiformula L ξ n} : (p ⟶ q).Open ↔ p.Open ∧ q.Open :=
  by simp[Open]

@[simp] lemma open_iff {p q : Semiformula L ξ n} : (p ⟷ q).Open ↔ p.Open ∧ q.Open :=
  by simp[Open]

def fvarList : {n : ℕ} → Semiformula L ξ n → List ξ
  | _, ⊤        => []
  | _, ⊥        => []
  | _, rel _ v  => List.join $ Matrix.toList (fun i => (v i).fvarList)
  | _, nrel _ v => List.join $ Matrix.toList (fun i => (v i).fvarList)
  | _, p ⋏ q    => p.fvarList ++ q.fvarList
  | _, p ⋎ q    => p.fvarList ++ q.fvarList
  | _, ∀' p     => p.fvarList
  | _, ∃' p     => p.fvarList

abbrev fvar? (p : Semiformula L ξ n) (x : ξ) : Prop := x ∈ p.fvarList

@[simp] lemma fvarList_top : fvarList (⊤ : Semiformula L ξ n) = [] := rfl

@[simp] lemma fvarList_bot : fvarList (⊥ : Semiformula L ξ n) = [] := rfl

@[simp] lemma fvarList_all (p : Semiformula L ξ (n + 1)) : fvarList (∀' p) = fvarList p := rfl

@[simp] lemma fvarList_ex (p : Semiformula L ξ (n + 1)) : fvarList (∃' p) = fvarList p := rfl

@[simp] lemma fvarList_neg (p : Semiformula L ξ n) : fvarList (~p) = fvarList p := by
  induction p using rec' <;> simp[*, fvarList, ← neg_eq]

@[simp] lemma fvarList_sentence {o : Type w} [IsEmpty o] (p : Semiformula L o n) :
    fvarList p = [] := by
  induction p using rec' <;> simp[*, fvarList, ← neg_eq]

def upper (p : SyntacticSemiformula L n) : ℕ := Finset.sup p.fvarList.toFinset id + 1

lemma not_fvar?_of_lt_upper (p : SyntacticSemiformula L n) (h : p.upper ≤ m) : ¬fvar? p m := by
  simp[upper, Nat.add_one_le_iff, fvar?] at h ⊢
  intro hm
  have : m ≤ Finset.sup p.fvarList.toFinset id :=
    Finset.le_sup (s := p.fvarList.toFinset) (b := m) (f := id) (by simpa using hm)
  exact irrefl_of _ _ $ lt_of_lt_of_le h this

@[simp] lemma not_fvar?_upper (p : SyntacticSemiformula L n) : ¬fvar? p p.upper :=
  not_fvar?_of_lt_upper p (by simp)

lemma ne_of_ne_complexity {p q : Semiformula L ξ n} (h : p.complexity ≠ q.complexity) : p ≠ q :=
  by rintro rfl; contradiction

@[simp] lemma ne_or_left (p q : Semiformula L ξ n) : p ≠ p ⋎ q := ne_of_ne_complexity (by simp)

@[simp] lemma ne_or_right (p q : Semiformula L ξ n) : q ≠ p ⋎ q := ne_of_ne_complexity (by simp)

variable {L : Language.{u}} {L₁ : Language.{u₁}} {L₂ : Language.{u₂}} {L₃ : Language.{u₃}}
  {ξ : Type v} {Φ : L₁ →ᵥ L₂}

def lMapAux (Φ : L₁ →ᵥ L₂) : ∀ {n}, Semiformula L₁ ξ n → Semiformula L₂ ξ n
  | _, ⊤        => ⊤
  | _, ⊥        => ⊥
  | _, rel r v  => rel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | _, nrel r v => nrel (Φ.rel r) (Semiterm.lMap Φ ∘ v)
  | _, p ⋏ q    => lMapAux Φ p ⋏ lMapAux Φ q
  | _, p ⋎ q    => lMapAux Φ p ⋎ lMapAux Φ q
  | _, ∀' p     => ∀' lMapAux Φ p
  | _, ∃' p     => ∃' lMapAux Φ p

lemma lMapAux_neg {n} (p : Semiformula L₁ ξ n) :
    (~p).lMapAux Φ = ~p.lMapAux Φ :=
  by induction p using Semiformula.rec' <;> simp[*, lMapAux, ← Semiformula.neg_eq]

def lMap (Φ : L₁ →ᵥ L₂) {n} : Semiformula L₁ ξ n →L Semiformula L₂ ξ n where
  toTr := lMapAux Φ
  map_top' := by simp[lMapAux]
  map_bot' := by simp[lMapAux]
  map_and' := by simp[lMapAux]
  map_or'  := by simp[lMapAux]
  map_neg' := by simp[lMapAux_neg]
  map_imply' := by simp[Semiformula.imp_eq, lMapAux_neg, ← Semiformula.neg_eq, lMapAux]

lemma lMap_rel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

@[simp] lemma lMap_rel₀ (r : L₁.Rel 0) (v : Fin 0 → Semiterm L₁ ξ n) :
    lMap Φ (rel r v) = rel (Φ.rel r) ![] := by simp[lMap_rel, Matrix.empty_eq]

@[simp] lemma lMap_rel₁ (r : L₁.Rel 1) (t : Semiterm L₁ ξ n) :
    lMap Φ (rel r ![t]) = rel (Φ.rel r) ![t.lMap Φ] := by
  simp[lMap_rel, Matrix.constant_eq_singleton]

@[simp] lemma lMap_rel₂ (r : L₁.Rel 2) (t₁ t₂ : Semiterm L₁ ξ n) :
    lMap Φ (rel r ![t₁, t₂]) = rel (Φ.rel r) ![t₁.lMap Φ, t₂.lMap Φ] := by
  simp[lMap_rel]; funext i; induction i using Fin.induction <;> simp

lemma lMap_nrel {k} (r : L₁.Rel k) (v : Fin k → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) (fun i => (v i).lMap Φ) := rfl

@[simp] lemma lMap_nrel₀ (r : L₁.Rel 0) (v : Fin 0 → Semiterm L₁ ξ n) :
    lMap Φ (nrel r v) = nrel (Φ.rel r) ![] := by
  simp[lMap_nrel, Matrix.empty_eq]

@[simp] lemma lMap_nrel₁ (r : L₁.Rel 1) (t : Semiterm L₁ ξ n) :
    lMap Φ (nrel r ![t]) = nrel (Φ.rel r) ![t.lMap Φ] := by
  simp[lMap_nrel, Matrix.constant_eq_singleton]

@[simp] lemma lMap_nrel₂ (r : L₁.Rel 2) (t₁ t₂ : Semiterm L₁ ξ n) :
    lMap Φ (nrel r ![t₁, t₂]) = nrel (Φ.rel r) ![t₁.lMap Φ, t₂.lMap Φ] := by
  simp[lMap_nrel]; funext i; induction i using Fin.induction <;> simp

@[simp] lemma lMap_all (p : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∀' p) = ∀' lMap Φ p := rfl

@[simp] lemma lMap_ex (p : Semiformula L₁ ξ (n + 1)) :
    lMap Φ (∃' p) = ∃' lMap Φ p := rfl

section fvListing

variable [DecidableEq ξ] [Inhabited ξ]

def fvEnum (p : Semiformula L ξ n) : ξ → ℕ := p.fvarList.indexOf

def fvEnumInv (p : Semiformula L ξ n) : ℕ → ξ :=
  fun i ↦ if hi : i < p.fvarList.length then p.fvarList.get ⟨i, hi⟩ else default

lemma fvEnumInv_fvEnum {p : Semiformula L ξ n} {x : ξ} (hx : x ∈ p.fvarList) :
    fvEnumInv p (fvEnum p x) = x := by
  simp [fvEnumInv, fvEnum]; intro h
  exact False.elim <| not_le.mpr (List.indexOf_lt_length.mpr $ hx) h

def fvListing (p : Semiformula L ξ n) : ξ → Fin (p.fvarList.length + 1) :=
  fun x ↦ ⟨p.fvarList.indexOf x, by simp [Nat.lt_succ, List.indexOf_le_length]⟩

def fvListingInv (p : Semiformula L ξ n) : Fin (p.fvarList.length + 1) → ξ :=
  fun i ↦ if hi : ↑i < p.fvarList.length then p.fvarList.get ⟨i, hi⟩ else default

lemma fvListingInv_fvListing {p : Semiformula L ξ n} {x : ξ} (hx : x ∈ p.fvarList) :
    fvListingInv p (fvListing p x) = x := by
  simp [fvListingInv, fvListing]; intro h
  exact False.elim <| not_le.mpr (List.indexOf_lt_length.mpr $ hx) h

end fvListing

end Semiformula

abbrev Theory (L : Language.{u}) := Set (Sentence L)

abbrev SyntacticTheory (L : Language.{u}) := Set (SyntacticFormula L)

def Theory.lMap (Φ : L₁ →ᵥ L₂) (T : Theory L₁) : Theory L₂ := Semiformula.lMap Φ '' T

namespace Theory

variable (T U : Theory L)

instance {L : Language} : Add (Theory L) := ⟨(· ∪ ·)⟩

lemma add_def : T + U = T ∪ U := rfl

end Theory

end FirstOrder

end ProofTheory
