/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Order.ConditionallyCompleteLattice.Basic

#align_import order.copy from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Tooling to make copies of lattice structures

Sometimes it is useful to make a copy of a lattice structure
where one replaces the data parts with provably equal definitions
that have better definitional properties.
-/


open Order

universe u

variable {α : Type u}

-- Porting note: mathlib3 proof uses `refine { top := top, bot := bot, .. }` but this does not work
-- anymore
/-- A function to create a provable equal copy of a bounded order
with possibly different definitional equalities. -/
def BoundedOrder.copy {h : LE α} {h' : LE α} (c : @BoundedOrder α h')
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (le_eq : ∀ x y : α, (@LE.le α h) x y ↔ x ≤ y) : @BoundedOrder α h :=
  @BoundedOrder.mk α h (@OrderTop.mk α h { top := top } (fun _ ↦ by simp [eq_top, le_eq]))
    (@OrderBot.mk α h { bot := bot } (fun _ ↦ by simp [eq_bot, le_eq]))
#align bounded_order.copy BoundedOrder.copy

-- Porting note: original proof uses
-- `all_goals { abstract { subst_vars, casesI c, simp_rw le_eq, assumption } }`
/-- A function to create a provable equal copy of a lattice
with possibly different definitional equalities. -/
def Lattice.copy (c : Lattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Sup α).sup)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Inf α).inf) : Lattice α := by
  refine' { le := le, sup := sup, inf := inf, lt := fun a b ↦ le a b ∧ ¬ le b a.. }
  · intros; simp [eq_le]
  · intro _ _ _ hab hbc; rw [eq_le] at hab hbc ⊢; exact le_trans hab hbc
  · intros; simp [eq_le]
  · intro _ _ hab hba; simp_rw [eq_le] at hab hba; exact le_antisymm hab hba
  · intros; simp [eq_le, eq_sup]
  · intros; simp [eq_le, eq_sup]
  · intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_sup, hac, hbc]
  · intros; simp [eq_le, eq_inf]
  · intros; simp [eq_le, eq_inf]
  · intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_inf, hac, hbc]
#align lattice.copy Lattice.copy

-- Porting note: original proof uses
-- `all_goals { abstract { subst_vars, casesI c, simp_rw le_eq, assumption } }`
/-- A function to create a provable equal copy of a distributive lattice
with possibly different definitional equalities. -/
def DistribLattice.copy (c : DistribLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Sup α).sup)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Inf α).inf) : DistribLattice α := by
  refine' { le := le, sup := sup, inf := inf, lt := fun a b ↦ le a b ∧ ¬ le b a.. }
  · intros; simp [eq_le]
  · intro _ _ _ hab hbc; rw [eq_le] at hab hbc ⊢; exact le_trans hab hbc
  · intros; simp [eq_le]
  · intro _ _ hab hba; simp_rw [eq_le] at hab hba; exact le_antisymm hab hba
  · intros; simp [eq_le, eq_sup]
  · intros; simp [eq_le, eq_sup]
  · intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_sup, hac, hbc]
  · intros; simp [eq_le, eq_inf]
  · intros; simp [eq_le, eq_inf]
  · intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_inf, hac, hbc]
  · intros; simp [eq_le, eq_inf, eq_sup, le_sup_inf]
#align distrib_lattice.copy DistribLattice.copy

-- Porting note: original proof uses
-- `all_goals { abstract { subst_vars, casesI c, simp_rw le_eq, assumption } }`
/-- A function to create a provable equal copy of a complete lattice
with possibly different definitional equalities. -/
def CompleteLattice.copy (c : CompleteLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Sup α).sup)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Inf α).inf)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    CompleteLattice α := by
  refine' { Lattice.copy (@CompleteLattice.toLattice α c) le eq_le sup eq_sup inf eq_inf with
    le := le, top := top, bot := bot, sup := sup, inf := inf, sSup := sSup, sInf := sInf.. }
  · intro _ _ h; simp [eq_le, eq_sSup, le_sSup _ _ h]
  · intro _ _ h; simpa [eq_le, eq_sSup] using h
  · intro _ _ h; simp [eq_le, eq_sInf, sInf_le _ _ h]
  · intro _ _ h; simpa [eq_le, eq_sInf] using h
  · intros; simp [eq_le, eq_top]
  · intros; simp [eq_le, eq_bot]
#align complete_lattice.copy CompleteLattice.copy

-- Porting note: original proof uses
-- `all_goals { abstract { subst_vars, casesI c, simp_rw le_eq, assumption } }`
/-- A function to create a provable equal copy of a frame with possibly different definitional
equalities. -/
def Frame.copy (c : Frame α) (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Sup α).sup)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Inf α).inf)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) : Frame α :=
  { CompleteLattice.copy (@Frame.toCompleteLattice α c) le eq_le top eq_top bot eq_bot
      sup eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf with
    inf_sSup_le_iSup_inf := fun a s => by
      simp [eq_le, eq_sup, eq_inf, eq_sSup, @Order.Frame.inf_sSup_le_iSup_inf α _ a s] }
#align frame.copy Frame.copy

-- Porting note: original proof uses
-- `all_goals { abstract { subst_vars, casesI c, simp_rw le_eq, assumption } }`
/-- A function to create a provable equal copy of a coframe with possibly different definitional
equalities. -/
def Coframe.copy (c : Coframe α) (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Sup α).sup)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Inf α).inf)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) : Coframe α :=
  { CompleteLattice.copy (@Coframe.toCompleteLattice α c) le eq_le top eq_top bot eq_bot sup
        eq_sup inf eq_inf sSup eq_sSup sInf eq_sInf with
    iInf_sup_le_sup_sInf := fun a s => by
      simp [eq_le, eq_sup, eq_inf, eq_sInf, @Order.Coframe.iInf_sup_le_sup_sInf α _ a s] }
#align coframe.copy Coframe.copy

/-- A function to create a provable equal copy of a complete distributive lattice
with possibly different definitional equalities. -/
def CompleteDistribLattice.copy (c : CompleteDistribLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (top : α) (eq_top : top = (by infer_instance : Top α).top)
    (bot : α) (eq_bot : bot = (by infer_instance : Bot α).bot)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Sup α).sup)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Inf α).inf)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    CompleteDistribLattice α :=
  { Frame.copy (@CompleteDistribLattice.toFrame α c) le eq_le top eq_top bot eq_bot sup eq_sup inf
      eq_inf sSup eq_sSup sInf eq_sInf,
    Coframe.copy (@CompleteDistribLattice.toCoframe α c) le eq_le top eq_top bot eq_bot sup eq_sup
      inf eq_inf sSup eq_sSup sInf eq_sInf with }
#align complete_distrib_lattice.copy CompleteDistribLattice.copy

-- Porting note: original proof uses
-- `all_goals { abstract { subst_vars, casesI c, simp_rw le_eq, assumption } }`
/-- A function to create a provable equal copy of a conditionally complete lattice
with possibly different definitional equalities. -/
def ConditionallyCompleteLattice.copy (c : ConditionallyCompleteLattice α)
    (le : α → α → Prop) (eq_le : le = (by infer_instance : LE α).le)
    (sup : α → α → α) (eq_sup : sup = (by infer_instance : Sup α).sup)
    (inf : α → α → α) (eq_inf : inf = (by infer_instance : Inf α).inf)
    (sSup : Set α → α) (eq_sSup : sSup = (by infer_instance : SupSet α).sSup)
    (sInf : Set α → α) (eq_sInf : sInf = (by infer_instance : InfSet α).sInf) :
    ConditionallyCompleteLattice α := by
  refine' { le := le, sup := sup, inf := inf, sSup := sSup, sInf := sInf.. }
  · intro a b; exact le a b ∧ ¬ le b a
  · intros; simp [eq_le]
  · intro _ _ _ hab hbc; rw [eq_le] at hab hbc ⊢; exact le_trans hab hbc
  · intros; simp [eq_le]
  · intro _ _ hab hba; simp_rw [eq_le] at hab hba; exact le_antisymm hab hba
  · intros; simp [eq_le, eq_sup]
  · intros; simp [eq_le, eq_sup]
  · intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_sup, hac, hbc]
  · intros; simp [eq_le, eq_inf]
  · intros; simp [eq_le, eq_inf]
  · intro _ _ _ hac hbc; simp_rw [eq_le] at hac hbc ⊢; simp [eq_inf, hac, hbc]
  · intro _ _ hb h; subst_vars; exact le_csSup _ _ hb h
  · intro _ _ hb h; subst_vars; exact csSup_le _ _ hb h
  · intro _ _ hb h; subst_vars; exact csInf_le _ _ hb h
  · intro _ _ hb h; subst_vars; exact le_csInf _ _ hb h
#align conditionally_complete_lattice.copy ConditionallyCompleteLattice.copy
