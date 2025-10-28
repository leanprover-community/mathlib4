/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Yaël Dillies
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Tooling to make copies of lattice structures

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/


open Order

universe u

variable {α : Type u}

/-- A function to create a provable equal copy of a top order
with possibly different definitional equalities. -/
def OrderTop.copy {h : LE α} {h' : LE α} (c : @OrderTop α h')
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (le_eq : ∀ x y : α, (@LE.le α h) x y ↔ x ≤ y) : @OrderTop α h :=
  @OrderTop.mk α h { top := top } fun _ ↦ by simp [eq_top, le_eq]

/-- A function to create a provable equal copy of a bottom order
with possibly different definitional equalities. -/
def OrderBot.copy {h : LE α} {h' : LE α} (c : @OrderBot α h')
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (le_eq : ∀ x y : α, (@LE.le α h) x y ↔ x ≤ y) : @OrderBot α h :=
  @OrderBot.mk α h { bot := bot } fun _ ↦ by simp [eq_bot, le_eq]

/-- A function to create a provable equal copy of a bounded order
with possibly different definitional equalities. -/
def BoundedOrder.copy {h : LE α} {h' : LE α} (c : @BoundedOrder α h')
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (le_eq : ∀ x y : α, (@LE.le α h) x y ↔ x ≤ y) : @BoundedOrder α h :=
  @BoundedOrder.mk α h (@OrderTop.mk α h { top := top } (fun _ ↦ by simp [eq_top, le_eq]))
    (@OrderBot.mk α h { bot := bot } (fun _ ↦ by simp [eq_bot, le_eq]))

/-- A function to create a provable equal copy of a lattice
with possibly different definitional equalities. -/
def Lattice.copy (c : Lattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min) : Lattice α where
  le := le
  sup := sup
  inf := inf
  lt := fun a b ↦ le a b ∧ ¬ le b a
  le_refl := by intros; simp [eq_le]
  le_trans := by intro _ _ _ hab hbc; rw [eq_le] at hab hbc ⊢; exact le_trans hab hbc
  le_antisymm := by intro _ _ hab hba; simp_rw [eq_le] at hab hba; exact le_antisymm hab hba
  le_sup_left := by intros; simp [eq_le, eq_sup]
  le_sup_right := by intros; simp [eq_le, eq_sup]
  sup_le := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_sup, hac, hbc]
  inf_le_left := by intros; simp [eq_le, eq_inf]
  inf_le_right := by intros; simp [eq_le, eq_inf]
  le_inf := by intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_inf, hac, hbc]

/-- A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities. -/
def DistribLattice.copy (c : DistribLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min) : DistribLattice α where
  toLattice := Lattice.copy (@DistribLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  le_sup_inf := by intros; simp [eq_le, eq_sup, eq_inf, le_sup_inf]

/-- A function to create a provable equal copy of a generalised heyting algebra
with possibly different definitional equalities. -/
def GeneralizedHeytingAlgebra.copy (c : GeneralizedHeytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp) :
    GeneralizedHeytingAlgebra α where
  __ := Lattice.copy (@GeneralizedHeytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderTop.copy (@GeneralizedHeytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ ↦ .rfl)
  himp := himp
  le_himp_iff _ _ _ := by simp [eq_le, eq_himp, eq_inf]

/-- A function to create a provable equal copy of a generalised co-Heyting algebra
with possibly different definitional equalities. -/
def GeneralizedCoheytingAlgebra.copy (c : GeneralizedCoheytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff) :
    GeneralizedCoheytingAlgebra α where
  __ := Lattice.copy (@GeneralizedCoheytingAlgebra.toLattice α c) le eq_le sup eq_sup inf eq_inf
  __ := OrderBot.copy (@GeneralizedCoheytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ ↦ .rfl)
  sdiff := sdiff
  sdiff_le_iff := by simp [eq_le, eq_sdiff, eq_sup]

/-- A function to create a provable equal copy of a heyting algebra
with possibly different definitional equalities. -/
def HeytingAlgebra.copy (c : HeytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α → α) (eq_compl : compl = (by infer_instance : HasCompl α).compl) :
    HeytingAlgebra α where
  toGeneralizedHeytingAlgebra := GeneralizedHeytingAlgebra.copy
    (@HeytingAlgebra.toGeneralizedHeytingAlgebra α c) le eq_le top eq_top sup eq_sup inf eq_inf himp
    eq_himp
  __ := OrderBot.copy (@HeytingAlgebra.toOrderBot α c) bot eq_bot
    (by rw [← eq_le]; exact fun _ _ ↦ .rfl)
  compl := compl
  himp_bot := by simp [eq_le, eq_himp, eq_bot, eq_compl]

/-- A function to create a provable equal copy of a co-Heyting algebra
with possibly different definitional equalities. -/
def CoheytingAlgebra.copy (c : CoheytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α → α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot) :
    CoheytingAlgebra α where
  toGeneralizedCoheytingAlgebra := GeneralizedCoheytingAlgebra.copy
    (@CoheytingAlgebra.toGeneralizedCoheytingAlgebra α c) le eq_le bot eq_bot sup eq_sup inf eq_inf
      sdiff eq_sdiff
  __ := OrderTop.copy (@CoheytingAlgebra.toOrderTop α c) top eq_top
    (by rw [← eq_le]; exact fun _ _ ↦ .rfl)
  hnot := hnot
  top_sdiff := by simp [eq_le, eq_sdiff, eq_top, eq_hnot]

/-- A function to create a provable equal copy of a bi-Heyting algebra
with possibly different definitional equalities. -/
def BiheytingAlgebra.copy (c : BiheytingAlgebra α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α → α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α → α) (eq_compl : compl = (by infer_instance : HasCompl α).compl) :
    BiheytingAlgebra α where
  toHeytingAlgebra := HeytingAlgebra.copy (@BiheytingAlgebra.toHeytingAlgebra α c) le eq_le top
    eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl
  __ := CoheytingAlgebra.copy (@BiheytingAlgebra.toCoheytingAlgebra α c) le eq_le top eq_top bot
    eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

/-- A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities. -/
def CompleteLattice.copy (c : CompleteLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    CompleteLattice α where
  toLattice := Lattice.copy (@CompleteLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf
  top := top
  bot := bot
  sSup := sSup
  sInf := sInf
  le_sSup := by intro _ _ h; simp [eq_le, eq_sSup, le_sSup _ _ h]
  sSup_le := by intro _ _ h; simpa [eq_le, eq_sSup] using h
  sInf_le := by intro _ _ h; simp [eq_le, eq_sInf, sInf_le _ _ h]
  le_sInf := by intro _ _ h; simpa [eq_le, eq_sInf] using h
  le_top := by intros; simp [eq_le, eq_top]
  bot_le := by intros; simp [eq_le, eq_bot]

/-- A function to create a provable equal copy of a frame with possibly different definitional
equalities. -/
def Frame.copy (c : Frame α) (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α → α) (eq_compl : compl = (by infer_instance : HasCompl α).compl)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) : Frame α where
  toCompleteLattice := CompleteLattice.copy (@Frame.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := HeytingAlgebra.copy (@Frame.toHeytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf himp eq_himp compl eq_compl

/-- A function to create a provable equal copy of a coframe with possibly different definitional
equalities. -/
def Coframe.copy (c : Coframe α) (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α → α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) : Coframe α where
  toCompleteLattice := CompleteLattice.copy (@Coframe.toCompleteLattice α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf
  __ := CoheytingAlgebra.copy (@Coframe.toCoheytingAlgebra α c)
    le eq_le top eq_top bot eq_bot sup eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot

/-- A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities. -/
def CompleteDistribLattice.copy (c : CompleteDistribLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sdiff : α → α → α) (eq_sdiff : sdiff = (by infer_instance : SDiff α).sdiff)
    (hnot : α → α) (eq_hnot : hnot = (by infer_instance : HNot α).hnot)
    (himp : α → α → α) (eq_himp : himp = (by infer_instance : HImp α).himp)
    (compl : α → α) (eq_compl : compl = (by infer_instance : HasCompl α).compl)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    CompleteDistribLattice α where
  toFrame := Frame.copy (@CompleteDistribLattice.toFrame α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf himp eq_himp compl eq_compl sSup eq_sSup sInf eq_sInf
  __ := Coframe.copy (@CompleteDistribLattice.toCoframe α c) le eq_le top eq_top bot eq_bot sup
    eq_sup inf eq_inf sdiff eq_sdiff hnot eq_hnot sSup eq_sSup sInf eq_sInf

/-- A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities. -/
def ConditionallyCompleteLattice.copy (c : ConditionallyCompleteLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Max α).max)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Min α).min)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    ConditionallyCompleteLattice α where
  toLattice := Lattice.copy (@ConditionallyCompleteLattice.toLattice α c)
    le eq_le sup eq_sup inf eq_inf
  sSup := sSup
  sInf := sInf
  le_csSup := by intro _ _ hb h; subst_vars; exact le_csSup _ _ hb h
  csSup_le := by intro _ _ hb h; subst_vars; exact csSup_le _ _ hb h
  csInf_le := by intro _ _ hb h; subst_vars; exact csInf_le _ _ hb h
  le_csInf := by intro _ _ hb h; subst_vars; exact le_csInf _ _ hb h
