/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Mathlib.Computability.SingleOracle.Oracle
import Mathlib.Computability.SingleOracle.Constructions.Eval_Aux
import Mathlib.Computability.RecursiveIn

/-!
# Reducibilities

In this file we relate Turing reducibility to other notions of reducibilities defined in Mathlib.

## Main declarations
- `SingleReducibleIff` : relates Turing reducibility to `Nat.RecursiveIn`.
-/

open Nat Part Encodable
section vars
variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]
nonrec theorem RecursiveIn.comp {O : Set (ℕ →. ℕ)} {f : β →. σ} {g : α → β}
    (hf : RecursiveIn O f) (hg : ComputableIn O g) :
    RecursiveIn O fun a => f (g a) :=
  (RecursiveIn.comp hf hg).of_eq fun n => by
    simp only [map_some, bind_eq_bind]
    rcases e : decode (α := α) n with - | a <;> simp [encodek]
theorem RecursiveIn.nat_iff {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} :
    _root_.RecursiveIn O f ↔ Nat.RecursiveIn O f := by
  simp [_root_.RecursiveIn, map_id']
theorem unpaired {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ →. α} :
    RecursiveIn O (Nat.unpaired f) ↔ RecursiveIn₂ O f :=
  ⟨fun h => by simpa using
    RecursiveIn.comp (g := fun p : ℕ × ℕ => (p.1, p.2)) h Primrec₂.pair.to_comp.computableIn,
    fun h => h.comp Primrec.unpair.to_comp.computableIn⟩
theorem RecursiveIn₂.unpaired' {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ →. ℕ} :
    Nat.RecursiveIn O (Nat.unpaired f) ↔ RecursiveIn₂ O f :=
  RecursiveIn.nat_iff.symm.trans unpaired
protected theorem Nat.RecursiveIn.some {O : Set (ℕ →. ℕ)} : Nat.RecursiveIn O some :=
  (Nat.Partrec.of_primrec Primrec.id).recursiveIn
protected theorem RecursiveIn.bind {O : Set (ℕ →. ℕ)} {f : α →. β} {g : α → β →. σ}
    (hf : RecursiveIn O f) (hg : RecursiveIn₂ O g) :
    RecursiveIn O fun a => (f a).bind (g a) :=
  (Nat.RecursiveIn.comp hg (Nat.RecursiveIn.some.pair hf)).of_eq fun n => by
    rcases e : decode (α := α) n <;> simp [Seq.seq, e, encodek]
theorem RecursiveIn.map {O : Set (ℕ →. ℕ)} {f : α →. β} {g : α → β → σ}
    (hf : RecursiveIn O f) (hg : ComputableIn₂ O g) :
    RecursiveIn O fun a => (f a).map (g a) := by
  simpa [bind_some_eq_map] using RecursiveIn.bind (g := fun a x => some (g a x)) hf hg
theorem rfind' {O f} (hf : Nat.RecursiveIn O f) :
    Nat.RecursiveIn O
      (Nat.unpaired fun a m =>
        (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m)) :=
  RecursiveIn₂.unpaired'.2 <| by
    refine
      RecursiveIn.map
        ((@RecursiveIn₂.unpaired' O fun a b : ℕ =>
              Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + b))).1
          ?_)
        (Primrec.nat_add.comp Primrec.snd <| Primrec.snd.comp Primrec.fst).to₂.computableIn₂
    have : Nat.RecursiveIn O (fun a => Nat.rfind (fun n => (fun m => decide (m = 0)) <$>
      Nat.unpaired (fun a b => f (Nat.pair (Nat.unpair a).1 (b + (Nat.unpair a).2)))
        (Nat.pair a n))) :=
        by
        apply Nat.RecursiveIn.rfind
        apply RecursiveIn₂.unpaired'.2
        apply RecursiveIn.comp (RecursiveIn.nat_iff.mpr hf)
        have a0 := (Primrec₂.pair.comp (Primrec.fst.comp <| Primrec.unpair.comp Primrec.fst)
                  (Primrec.nat_add.comp Primrec.snd
                    (Primrec.snd.comp <| Primrec.unpair.comp Primrec.fst))).to_comp
        exact Computable.computableIn a0
    simpa
end vars

open Oracle.Single
theorem SingleReducibleIff (O : ℕ → ℕ) (f : ℕ →. ℕ) :
    Oracle.Single.RecursiveIn O f ↔ Nat.RecursiveIn ({↑O} : (Set (ℕ →. ℕ))) f := by
  constructor
  · intro h
    induction h with
    | zero => exact Nat.RecursiveIn.zero
    | succ => exact Nat.RecursiveIn.succ
    | left => exact Nat.RecursiveIn.left
    | right => exact Nat.RecursiveIn.right
    | oracle => exact Nat.RecursiveIn.oracle (↑O) rfl
    | pair hf hh hf_ih hh_ih => exact Nat.RecursiveIn.pair hf_ih hh_ih
    | comp hf hh hf_ih hh_ih => exact Nat.RecursiveIn.comp hf_ih hh_ih
    | prec hf hh hf_ih hh_ih => exact Nat.RecursiveIn.prec hf_ih hh_ih
    | rfind hf ih => exact rfind' ih
  · intro h
    induction h with
    | zero => exact Oracle.Single.RecursiveIn.zero
    | succ => exact Oracle.Single.RecursiveIn.succ
    | left => exact Oracle.Single.RecursiveIn.left
    | right => exact Oracle.Single.RecursiveIn.right
    | oracle g hg =>
      have : g = O := by simp_all only [Set.mem_singleton_iff]
      rw [this]
      exact Oracle.Single.RecursiveIn.oracle
    | pair hf hh hf_ih hh_ih => exact Oracle.Single.RecursiveIn.pair hf_ih hh_ih
    | comp hf hh hf_ih hh_ih => exact Oracle.Single.RecursiveIn.comp hf_ih hh_ih
    | prec hf hh hf_ih hh_ih => exact Oracle.Single.RecursiveIn.prec hf_ih hh_ih
    | rfind hf ih => exact Code.rfind_real ih
