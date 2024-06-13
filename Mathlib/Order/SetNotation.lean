/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Data.Set.Defs
import Mathlib.Mathport.Notation

/-!
# Notation classes for set supremum and infimum

In this file we introduce notation for indexed suprema, infima, unions, and intersections.

## Main definitions

- `SupSet α`: typeclass introducing the operation `SupSet.sSup` (exported to the root namespace);
  `sSup s` is the supremum of the set `s`;
- `InfSet`: similar typeclass for infimum of a set;
- `iSup f`, `iInf f`: supremum and infimum of an indexed family of elements,
  defined as `sSup (Set.range f)` and `sInf (Set.range f)`, respectively;
- `Set.sUnion s`, `Set.sInter s`: same as `sSup s` and `sInf s`,
  but works only for sets of sets;
- `Set.iUnion s`, `Set.iInter s`: same as `iSup s` and `iInf s`,
  but works only for indexed families of sets.

## Notation

- `⨆ i, f i`, `⨅ i, f i`: supremum and infimum of an indexed family, respectively;
- `⋃₀ s`, `⋂₀ s`: union and intersection of a set of sets;
- `⋃ i, s i`, `⋂ i, s i`: union and intersection of an indexed family of sets.

-/

open Set

universe u v
variable {α : Type u} {ι : Sort v}

/-- Class for the `sSup` operator -/
class SupSet (α : Type*) where
  /-- Supremum of a set -/
  sSup : Set α → α
#align has_Sup SupSet
#align has_Sup.Sup SupSet.sSup


/-- Class for the `sInf` operator -/
class InfSet (α : Type*) where
  /-- Infimum of a set -/
  sInf : Set α → α
#align has_Inf InfSet
#align has_Inf.Inf InfSet.sInf


export SupSet (sSup)

export InfSet (sInf)

/-- Indexed supremum -/
def iSup [SupSet α] (s : ι → α) : α :=
  sSup (range s)
#align supr iSup

/-- Indexed infimum -/
def iInf [InfSet α] (s : ι → α) : α :=
  sInf (range s)
#align infi iInf

instance (priority := 50) infSet_to_nonempty (α) [InfSet α] : Nonempty α :=
  ⟨sInf ∅⟩
#align has_Inf_to_nonempty infSet_to_nonempty

instance (priority := 50) supSet_to_nonempty (α) [SupSet α] : Nonempty α :=
  ⟨sSup ∅⟩
#align has_Sup_to_nonempty supSet_to_nonempty

/-
Porting note: the code below could replace the `notation3` command
open Batteries.ExtendedBinder in
syntax "⨆ " extBinder ", " term:51 : term

macro_rules
  | `(⨆ $x:ident, $p) => `(iSup fun $x:ident ↦ $p)
  | `(⨆ $x:ident : $t, $p) => `(iSup fun $x:ident : $t ↦ $p)
  | `(⨆ $x:ident $b:binderPred, $p) =>
    `(iSup fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p) -/

/-- Indexed supremum. -/
notation3 "⨆ "(...)", "r:60:(scoped f => iSup f) => r

/-- Indexed infimum. -/
notation3 "⨅ "(...)", "r:60:(scoped f => iInf f) => r

section delaborators

open Lean Lean.PrettyPrinter.Delaborator

/-- Delaborator for indexed supremum. -/
@[delab app.iSup]
def iSup_delab : Delab := whenPPOption Lean.getPPNotation <| withOverApp 4 do
  let #[_, ι, _, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨆ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨆ ($x:ident : $dom), $body)
      else
        `(⨆ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨆ $x:ident, ⨆ (_ : $y:ident ∈ $s), $body)
    | `(⨆ ($x:ident : $_), ⨆ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⨆ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

/-- Delaborator for indexed infimum. -/
@[delab app.iInf]
def iInf_delab : Delab := whenPPOption Lean.getPPNotation <| withOverApp 4 do
  let #[_, ι, _, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨅ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨅ ($x:ident : $dom), $body)
      else
        `(⨅ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨅ $x:ident, ⨅ (_ : $y:ident ∈ $s), $body)
    | `(⨅ ($x:ident : $_), ⨅ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⨅ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx
end delaborators

namespace Set

instance : InfSet (Set α) :=
  ⟨fun s => { a | ∀ t ∈ s, a ∈ t }⟩

instance : SupSet (Set α) :=
  ⟨fun s => { a | ∃ t ∈ s, a ∈ t }⟩

/-- Intersection of a set of sets. -/
def sInter (S : Set (Set α)) : Set α :=
  sInf S
#align set.sInter Set.sInter

/-- Notation for `Set.sInter` Intersection of a set of sets. -/
prefix:110 "⋂₀ " => sInter

/-- Union of a set of sets. -/
def sUnion (S : Set (Set α)) : Set α :=
  sSup S
#align set.sUnion Set.sUnion

/-- Notation for `Set.sUnion`. Union of a set of sets. -/
prefix:110 "⋃₀ " => sUnion

@[simp]
theorem mem_sInter {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t :=
  Iff.rfl
#align set.mem_sInter Set.mem_sInter

@[simp]
theorem mem_sUnion {x : α} {S : Set (Set α)} : x ∈ ⋃₀ S ↔ ∃ t ∈ S, x ∈ t :=
  Iff.rfl
#align set.mem_sUnion Set.mem_sUnion

/-- Indexed union of a family of sets -/
def iUnion (s : ι → Set α) : Set α :=
  iSup s
#align set.Union Set.iUnion

/-- Indexed intersection of a family of sets -/
def iInter (s : ι → Set α) : Set α :=
  iInf s
#align set.Inter Set.iInter

/-- Notation for `Set.iUnion`. Indexed union of a family of sets -/
notation3 "⋃ "(...)", "r:60:(scoped f => iUnion f) => r

/-- Notation for `Set.iInter`. Indexed intersection of a family of sets -/
notation3 "⋂ "(...)", "r:60:(scoped f => iInter f) => r

section delaborators

open Lean Lean.PrettyPrinter.Delaborator

/-- Delaborator for indexed unions. -/
@[delab app.Set.iUnion]
def iUnion_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⋃ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⋃ ($x:ident : $dom), $body)
      else
        `(⋃ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⋃ $x:ident, ⋃ (_ : $y:ident ∈ $s), $body)
    | `(⋃ ($x:ident : $_), ⋃ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⋃ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

/-- Delaborator for indexed intersections. -/
@[delab app.Set.iInter]
def sInter_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⋂ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⋂ ($x:ident : $dom), $body)
      else
        `(⋂ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⋂ $x:ident, ⋂ (_ : $y:ident ∈ $s), $body)
    | `(⋂ ($x:ident : $_), ⋂ (_ : $y:ident ∈ $s), $body) =>
      if x == y then `(⋂ $x:ident ∈ $s, $body) else pure stx
    | _ => pure stx
  return stx

end delaborators

@[simp]
theorem mem_iUnion {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i :=
  ⟨fun ⟨_, ⟨⟨a, (t_eq : s a = _)⟩, (h : x ∈ _)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩
#align set.mem_Union Set.mem_iUnion

@[simp]
theorem mem_iInter {x : α} {s : ι → Set α} : (x ∈ ⋂ i, s i) ↔ ∀ i, x ∈ s i :=
  ⟨fun (h : ∀ a ∈ { a : Set α | ∃ i, s i = a }, x ∈ a) a => h (s a) ⟨a, rfl⟩,
    fun h _ ⟨a, (eq : s a = _)⟩ => eq ▸ h a⟩
#align set.mem_Inter Set.mem_iInter

@[simp]
theorem sSup_eq_sUnion (S : Set (Set α)) : sSup S = ⋃₀S :=
  rfl
#align set.Sup_eq_sUnion Set.sSup_eq_sUnion

@[simp]
theorem sInf_eq_sInter (S : Set (Set α)) : sInf S = ⋂₀ S :=
  rfl
#align set.Inf_eq_sInter Set.sInf_eq_sInter

@[simp]
theorem iSup_eq_iUnion (s : ι → Set α) : iSup s = iUnion s :=
  rfl
#align set.supr_eq_Union Set.iSup_eq_iUnion

@[simp]
theorem iInf_eq_iInter (s : ι → Set α) : iInf s = iInter s :=
  rfl
#align set.infi_eq_Inter Set.iInf_eq_iInter

end Set
