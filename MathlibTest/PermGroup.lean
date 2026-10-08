/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Tactic.PermGroup
import MathlibTest.PermGroupDefs
meta import MathlibTest.PermGroupDefs
meta import Lean

/-! Tests for the `perm_group` tactic. -/

public section

example : Nat.card (Subgroup.closure
    ({Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2} : Set _)) = 6 := by
  perm_group

-- The tactic needs only the conversions, without adding a group instance for Hex permutations.
run_elab do
  unless (← Lean.Meta.synthInstance? (← Lean.Meta.mkAppM ``_root_.Group
      #[← Lean.Meta.mkAppM ``Hex.Perm #[Lean.mkNatLit 3]])).isNone do
    throwError "importing perm_group introduced a group instance for Hex permutations"

-- Hex imports must preserve the default equality instances on core containers.
example : (inferInstance : DecidableEq (Array Nat)) = Array.instDecidableEq := rfl
example : (inferInstance : DecidableEq (Vector Nat 2)) = instDecidableEqVector := rfl

example : Nat.card PermGroupTest.subgroup = 6 := by perm_group
example : PermGroupTest.cycle ∈ PermGroupTest.subgroup := by perm_group

open Hex Hex.PermGroup

namespace Hex.PermGroup.Mathlib.TacticTests

@[expose] def cycle : Equiv.Perm (Fin 3) := permOfImages 3 [1, 2, 0]
@[expose] def swap : Equiv.Perm (Fin 3) := permOfImages 3 [1, 0, 2]
noncomputable def generators : Set (Equiv.Perm (Fin 3)) := {cycle, swap}
noncomputable def symmetric : Subgroup (Equiv.Perm (Fin 3)) := Subgroup.closure generators

theorem order : Nat.card symmetric = 6 := by perm_group
theorem member : cycle * swap ∈ symmetric := by perm_group
theorem nonmember : swap ∉ Subgroup.closure ({cycle} : Set _) := by perm_group
theorem full : symmetric = ⊤ := by perm_group

example : Nat.card (Subgroup.closure
    (↑({cycle, swap} : Finset (Equiv.Perm (Fin 3))) : Set (Equiv.Perm (Fin 3)))) = 6 := by
  perm_group
example : swap ∉ Subgroup.closure
    (↑({cycle} : Finset (Equiv.Perm (Fin 3))) : Set _) := by perm_group
example : Nat.card (Subgroup.closure
    (↑(∅ : Finset (Equiv.Perm (Fin 3))) : Set (Equiv.Perm (Fin 3)))) = 1 := by perm_group
example : cycle ∈ Subgroup.closure {p : Equiv.Perm (Fin 3) | p ∈ [cycle, swap]} := by
  perm_group
example : swap ∉ Subgroup.closure {p : Equiv.Perm (Fin 3) | p ∈ [cycle]} := by
  perm_group
example : Subgroup.closure {p : Equiv.Perm (Fin 3) | p ∈ [cycle, swap]} = ⊤ := by
  perm_group
example : Nat.card (Subgroup.closure
    ({permOfImages 3 [0, 0, 1]} : Set (Equiv.Perm (Fin 3)))) = 1 := by perm_group
example : Subgroup.closure (∅ : Set (Equiv.Perm (Fin 0))) = ⊤ := by perm_group
example : Subgroup.closure (∅ : Set (Equiv.Perm (Fin 1))) = ⊤ := by perm_group
example : Nat.card symmetric = 6 := by perm_group (maxChunkWork := 128)

noncomputable def m11 : Set (Equiv.Perm (Fin 11)) := {
  permOfImages 11 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0],
  permOfImages 11 [0, 1, 6, 9, 5, 3, 10, 2, 8, 4, 7]}

noncomputable def m11Finset : Finset (Equiv.Perm (Fin 11)) := {
  permOfImages 11 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0],
  permOfImages 11 [0, 1, 6, 9, 5, 3, 10, 2, 8, 4, 7]}

example : Nat.card (Subgroup.closure (↑m11Finset : Set (Equiv.Perm (Fin 11)))) = 7920 := by perm_group

theorem m11_order : Nat.card (Subgroup.closure m11) = 7920 := by perm_group
theorem m11_not_mem : permOfImages 11 [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10] ∉
    Subgroup.closure m11 := by perm_group

example : True := by
  fail_if_success have : Nat.card symmetric = 5 := by perm_group
  fail_if_success have : swap ∈ Subgroup.closure ({cycle} : Set _) := by perm_group
  fail_if_success have : cycle ∉ symmetric := by perm_group
  fail_if_success have : Subgroup.closure ({cycle} : Set _) = ⊤ := by perm_group
  trivial

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Mathlib.TacticTests.order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms order

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Mathlib.TacticTests.m11_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms m11_order

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Mathlib.TacticTests.m11_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms m11_not_mem

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Mathlib.TacticTests.member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms member

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Mathlib.TacticTests.full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms full

end Hex.PermGroup.Mathlib.TacticTests

-- Check that the printed certificate source parses and its proofs elaborate,
-- even when local declarations shadow the generated certificate's helpers.
namespace CertificateShadow

def order : Nat := 0
def pack : Nat := 0
def Perm : Nat := 0
def HasOrder : Nat := 0
def card_of_hasOrder : Nat := 0
def setOf_mem_cons : Nat := 0
def setOf_mem_singleton : Nat := 0
run_cmd do
  let source ← Lean.Elab.Command.liftTermElabM do
    let s ← `(term| (({permOfImages 3 [1, 2, 0], permOfImages 3 [1, 0, 2]} :
      Finset (Equiv.Perm (Fin 3))) : Set (Equiv.Perm (Fin 3))))
    let generators ← Lean.Elab.Term.elabTerm s none
    let some source ← Mathlib.Tactic.PermGroup.extension.certificate? "emitted" generators s
      | throwError "perm_group certificate generation did not recognize the literal"
    return source
  let input := Lean.Parser.mkInputContext source "<perm_group_certificate>"
  let mut state : Lean.Parser.ModuleParserState := {}
  repeat
    let (stx, next, errors) := Lean.Parser.parseCommand input
      { env := ← Lean.getEnv, options := ← Lean.getOptions } state {}
    if errors.hasErrors then throwError "the certificate source does not parse"
    if Lean.Parser.isTerminalCommand stx then break
    withReader (fun ctx => { ctx with fileName := input.fileName, fileMap := input.fileMap }) do
      Lean.Elab.Command.elabCommand stx
    state := next

end CertificateShadow

#guard_msgs (drop info) in
#perm_group_certificate swaps for
  ({Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2} : Set _)
