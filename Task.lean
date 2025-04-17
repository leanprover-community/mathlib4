import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Logic.Equiv.Fin.Rotate

#check Equiv.Perm
#check finRotate
#check Fin.cycleRange

open Equiv

def addNatEmb_1 {n : ℕ} (m : ℕ) : Fin n ↪ Fin (n + m) where
  toFun := (Fin.addNat · m)
  inj' a b := by simp [Fin.ext_iff]

def addNatEmb'' {n : ℕ} (m : ℕ) (hmn : n ≤ m): Fin n ↪ Fin (m) := by
  set g' : Fin (n + (m - n)) ≃ Fin (m) := by
    refine finCongr ?_
    exact Nat.add_sub_of_le hmn
  set g : Fin (n + (m - n)) ↪ Fin (m) := g'.toEmbedding
  set f : Fin n ↪ Fin (n + (m - n)) := Fin.addNatEmb (m - n)
  #check f.trans g
  sorry


def task {n m: ℕ} (i : Fin n) : Perm (Fin (n + m)) :=
  -- have : Fin n ≃ Set.range (Fin.addNatEmb (n := n) m) := (Fin.addNatEmb m).toEquivRange
  Equiv.Perm.extendDomain (Fin.cycleRange i) (Fin.addNatEmb m).toEquivRange


def task'' {n m: ℕ} (i : Fin n) (hmn : n ≤ m): Perm (Fin m) :=
  -- have : Fin n ≃ Set.range (Fin.addNatEmb (n := n) m) := (Fin.addNatEmb m).toEquivRange
  Equiv.Perm.extendDomain (Fin.cycleRange i) (addNatEmb'' m hmn).toEquivRange
