/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Yuyang Zhao
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Util.Notation3

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

@[expose] public section

open Set

universe u v
variable {α : Type u} {ι : Sort v}

/-- Class for the `sSup` operator -/
class SupSet (α : Type*) where
  /-- Supremum of a set -/
  sSup : Set α → α

/-- Class for the `sInf` operator -/
@[to_dual existing]
class InfSet (α : Type*) where
  /-- Infimum of a set -/
  sInf : Set α → α

export SupSet (sSup)

export InfSet (sInf)

/-- Indexed supremum -/
@[to_dual /-- Indexed infimum -/]
def iSup [SupSet α] (s : ι → α) : α :=
  sSup (range s)

@[to_dual]
instance (priority := 50) infSet_to_nonempty (α) [InfSet α] : Nonempty α :=
  ⟨sInf ∅⟩

/-- Indexed supremum. -/
notation3 "⨆ " (...)", " r:60:(scoped f => iSup f) => r

/-- Indexed infimum. -/
notation3 "⨅ " (...)", " r:60:(scoped f => iInf f) => r

section delaborators

open Lean Lean.PrettyPrinter.Delaborator

/-- Delaborator for indexed supremum. -/
@[app_delab iSup]
meta def iSup_delab : Delab := whenPPOption Lean.getPPNotation <| withOverApp 4 do
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
@[app_delab iInf]
meta def iInf_delab : Delab := whenPPOption Lean.getPPNotation <| withOverApp 4 do
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

section OrderSupSet

variable [LE α]

@[to_dual]
theorem subset_upperBounds_lowerBounds (s : Set α) : s ⊆ upperBounds (lowerBounds s) :=
  fun _ hx _ hy => hy hx

@[to_dual]
theorem IsGreatest.isLUB {s : Set α} {a : α} (h : IsGreatest s a) : IsLUB s a :=
  ⟨h.2, fun _ hb => hb h.1⟩

@[to_dual (attr := simp)]
theorem isLUB_lowerBounds {s : Set α} {a : α} : IsLUB (lowerBounds s) a ↔ IsGLB s a :=
  ⟨fun H => ⟨fun _ hx => H.2 <| subset_upperBounds_lowerBounds s hx, H.1⟩, IsGreatest.isLUB⟩

class OrderSupSet (α : Type*) [LE α] extends SupSet α where
  protected isLUB_sSup_of_isLUB s a : IsLUB s a → IsLUB s (sSup s)

@[to_dual existing]
class OrderInfSet (α : Type*) [LE α] extends InfSet α where
  protected isGLB_sInf_of_isGLB s a : IsGLB s a → IsGLB s (sInf s)

@[to_dual]
theorem isLUB_sSup_of_isLUB [OrderSupSet α] {s : Set α} {a : α} :
    IsLUB s a → IsLUB s (sSup s) :=
  OrderSupSet.isLUB_sSup_of_isLUB _ _

@[to_dual] protected alias IsLUB.isLUB_sSup := isLUB_sSup_of_isLUB

@[to_dual]
abbrev OrderInfSet.ofOrderSupSet [OrderSupSet α] :
    OrderInfSet α where
  sInf s := sSup (lowerBounds s)
  isGLB_sInf_of_isGLB _ _ h := isLUB_lowerBounds.mp (isLUB_sSup_of_isLUB h.isLUB)

open Classical in
@[to_dual]
noncomputable abbrev OrderSupSet.choose (d : α) :
    OrderSupSet α where
  sSup s := if h : ∃ x, IsLUB s x then h.choose else d
  isLUB_sSup_of_isLUB _ _ h := dif_pos (Exists.intro _ h) ▸ choose_spec _

@[to_dual]
theorem exists_isLUB_iff_isLUB_sSup [OrderSupSet α] {s : Set α} :
    (∃ a, IsLUB s a) ↔ IsLUB s (sSup s) :=
  ⟨fun ⟨_, h⟩ ↦ h.isLUB_sSup, fun h ↦ ⟨_, h⟩⟩

end OrderSupSet

namespace Set

instance : InfSet (Set α) :=
  ⟨fun s => { a | ∀ t ∈ s, a ∈ t }⟩

instance : SupSet (Set α) :=
  ⟨fun s => { a | ∃ t ∈ s, a ∈ t }⟩

/-- Intersection of a set of sets. -/
def sInter (S : Set (Set α)) : Set α :=
  sInf S

/-- Notation for `Set.sInter` Intersection of a set of sets. -/
prefix:110 "⋂₀ " => sInter

/-- Union of a set of sets. -/
def sUnion (S : Set (Set α)) : Set α :=
  sSup S

/-- Notation for `Set.sUnion`. Union of a set of sets. -/
prefix:110 "⋃₀ " => sUnion

@[simp, grind =, push]
theorem mem_sInter {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t :=
  Iff.rfl

@[simp, grind =, push]
theorem mem_sUnion {x : α} {S : Set (Set α)} : x ∈ ⋃₀ S ↔ ∃ t ∈ S, x ∈ t :=
  Iff.rfl

/-- Indexed union of a family of sets -/
def iUnion (s : ι → Set α) : Set α :=
  iSup s

/-- Indexed intersection of a family of sets -/
def iInter (s : ι → Set α) : Set α :=
  iInf s

/-- Notation for `Set.iUnion`. Indexed union of a family of sets -/
notation3 "⋃ " (...)", " r:60:(scoped f => iUnion f) => r

/-- Notation for `Set.iInter`. Indexed intersection of a family of sets -/
notation3 "⋂ " (...)", " r:60:(scoped f => iInter f) => r

section delaborators

open Lean Lean.PrettyPrinter.Delaborator

/-- Delaborator for indexed unions. -/
@[app_delab Set.iUnion]
meta def iUnion_delab : Delab := whenPPOption Lean.getPPNotation do
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
@[app_delab Set.iInter]
meta def sInter_delab : Delab := whenPPOption Lean.getPPNotation do
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

@[simp, push]
theorem mem_iUnion {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i :=
  ⟨fun ⟨_, ⟨⟨a, (t_eq : s a = _)⟩, (h : x ∈ _)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩

@[simp, push]
theorem mem_iInter {x : α} {s : ι → Set α} : (x ∈ ⋂ i, s i) ↔ ∀ i, x ∈ s i :=
  ⟨fun (h : ∀ a ∈ { a : Set α | ∃ i, s i = a }, x ∈ a) a => h (s a) ⟨a, rfl⟩,
    fun h _ ⟨a, (eq : s a = _)⟩ => eq ▸ h a⟩

@[simp]
theorem sSup_eq_sUnion (S : Set (Set α)) : sSup S = ⋃₀ S :=
  rfl

@[simp]
theorem sInf_eq_sInter (S : Set (Set α)) : sInf S = ⋂₀ S :=
  rfl

@[simp]
theorem iSup_eq_iUnion (s : ι → Set α) : iSup s = iUnion s :=
  rfl

@[simp]
theorem iInf_eq_iInter (s : ι → Set α) : iInf s = iInter s :=
  rfl

end Set
