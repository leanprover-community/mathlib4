/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Mathlib.Computability.SingleOracle.Constructions.Option
import Mathlib.Data.Nat.PSub

/-!
# Eval_Aux.lean

Auxiliary constructs for use in `Oracle.Single.Constructions.Eval`.

-/

open Nat
open Denumerable
open Encodable
open List

section rfindOpt
open Oracle.Single
namespace Oracle.Single.Code

theorem rfind'_eqv_rfind {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    (Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$>
        eval O c (Nat.pair a (n + m))).map (· + m)) (Nat.pair x 0) =
    (Nat.rfind fun n => (fun m => m = 0) <$> eval O c ⟪x, n⟫) := by
  simpa using by rfl

section rfind
/-- `[c_rfind c](x)=smallest n s.t. [c](x,n)=0.` -/
def c_rfind : Oracle.Single.Code→Oracle.Single.Code := fun c ↦ (rfind' c).comp (pair c_id zero)
/-- Given a code `c` -/
abbrev rfind (O : ℕ → ℕ) : Code → ℕ →. ℕ :=
  fun c ↦ fun a ↦ Nat.rfind fun n ↦ (fun m ↦ m = 0) <$> eval O c (Nat.pair a n)
theorem c_rfind_ev {O c a} : eval O (c_rfind c) a = rfind O c a := by
  unfold c_rfind
  unfold rfind
  rw [←rfind'_eqv_rfind]
  simp [eval,Seq.seq]
theorem c_rfind_ev' {O c a} :
    eval O (c_rfind c) a = (Nat.rfind (fun x => n2b' <$> eval O c (Nat.pair a x))) := by
  simp only [c_rfind_ev, ev_simps]
  simp only [rfind, Part.map_eq_map]
  unfold n2b'
  simp
theorem c_rfind_ev'' {O c} :
    eval O (c_rfind c) = fun a => (Nat.rfind (fun x => n2b' <$> eval O c (Nat.pair a x))) := by
  funext a
  exact c_rfind_ev'
theorem rfind_real {O f} (h : RecursiveIn O f) :
    RecursiveIn O (fun a =>
        Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)) := by
  rcases exists_code.mp h with ⟨c, hc⟩
  rw [← hc]
  apply exists_code.mpr
  use c_rfind c
  simp [c_rfind_ev'']
  congr
end rfind

def c_ppred := c_rfind (c_if_eq'.comp₂ left (succ.comp right))
@[simp, ev_simps] theorem c_ppred_ev {O y} : eval O c_ppred y = Nat.ppred y := by
  unfold c_ppred
  simp only [c_rfind_ev', ev_simps]
  simp? [Seq.seq] says
    simp only [Seq.seq, unpair_pair, Part.coe_some, Part.map_eq_map, Part.map_some,
      Part.bind_eq_bind, Part.bind_some, pair_l, pair_r]
  cases y with
  | zero =>
    have : ¬ ((Nat.rfind fun x ↦ Part.some (n2b' 1))).Dom := by
      simp [n2b']
    simpa using Part.eq_none_iff'.mpr this
  | succ n =>
    unfold n2b'
    aesop

def c_ofOption (c : Code) := c_ppred.comp c
theorem c_ofOption_ev {O : ℕ → ℕ} {c : Code} {x : ℕ} (hc1 : code_total O c) :
    eval O (c_ofOption c) x = ↑(n2o ((eval O c x).get (hc1 x))) := by
  unfold c_ofOption
  simp only [ev_simps]
  simp only [Part.Dom.bind (hc1 x), Part.bind_eq_bind, c_ppred_ev]
  cases (eval O c x).get (hc1 x) with
  | zero => simp;
  | succ n => simp;

def c_rfindOpt (c : Code) := (c_ofOption c).comp₂ c_id (c_rfind (c_isSome.comp (c)))
@[simp, ev_simps] theorem c_rfindOpt_ev {O : ℕ → ℕ} {c : Code} {x : ℕ} (hc1 : code_total O c) :
    eval O (c_rfindOpt c) x =
    Nat.rfindOpt (fun y => n2o <| (eval O c (Nat.pair x y)).get (hc1 (Nat.pair x y))) := by
  unfold c_rfindOpt
  simp only [c_rfind_ev', ev_simps]
  unfold rfindOpt
  simp? [n2b', b'2n] says
    simp only [Part.coe_some, Part.map_eq_map, Part.map_some, b'2n, Part.bind_eq_bind,
      Part.map_bind, PFun.coe_val, n2b', ite_eq_left_iff, Bool.not_eq_true,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none, one_ne_zero, imp_false, ite_not,
      Bool.if_true_right, Bool.or_false]
  have :
      (fun x_1 ↦ (eval O c (Nat.pair x x_1)).bind
        fun y ↦ Part.some !decide (n2o y = Option.none)) =
      (fun n ↦ Part.some (n2o ((eval O c ⟪x, n⟫).get (hc1 ⟪x, n⟫))).isSome) := by
    funext n
    simp only [Part.Dom.bind (hc1 ⟪x,n⟫), Part.some_inj, Bool.not_eq_eq_eq_not, Option.not_isSome]
    cases n2o ((eval O c ⟪x, n⟫).get (hc1 ⟪x, n⟫)) with
    | none => simp
    | some val => simp
  rw [this]
  if hh: (Nat.rfind fun n ↦ Part.some (n2o ((eval O c ⟪x, n⟫).get (hc1 ⟪x, n⟫))).isSome).Dom then
    simp [Part.Dom.bind hh]
    simp [Seq.seq]
    simp [c_ofOption_ev hc1]
    simp [Part.Dom.bind hh]
  else
    simp [Part.eq_none_iff'.mpr hh]
    simp [Seq.seq]
end Oracle.Single.Code
end rfindOpt
