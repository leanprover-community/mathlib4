/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Data.Rat.Cast.Defs

/-!
## `norm_num` plugin for scientific notation.
-/

set_option autoImplicit true

namespace Mathlib
open Lean hiding Rat mkRat
open Meta

namespace Meta.NormNum
open Qq

/-- Helper function to synthesize a typed `OfScientific α` expression given `DivisionRing α`. -/
def inferOfScientific (α : Q(Type u)) : MetaM Q(OfScientific $α) :=
  return ← synthInstanceQ (q(OfScientific $α) : Q(Type u)) <|>
    throwError "does not support scientific notation"

-- see note [norm_num lemma function equality]
theorem isRat_ofScientific_of_true [DivisionRing α] (σα : OfScientific α) :
    {m e : ℕ} → {n : ℤ} → {d : ℕ} →
    @OfScientific.ofScientific α σα = (fun m s e ↦ (Rat.ofScientific m s e : α)) →
    IsRat (mkRat m (10 ^ e) : α) n d → IsRat (@OfScientific.ofScientific α σα m true e) n d
  | _, _, _, _, σh, ⟨_, eq⟩ => ⟨_, by simp only [σh, Rat.ofScientific_true_def]; exact eq⟩

-- see note [norm_num lemma function equality]
theorem isNat_ofScientific_of_false [DivisionRing α] (σα : OfScientific α) : {m e nm ne n : ℕ} →
    @OfScientific.ofScientific α σα = (fun m s e ↦ (Rat.ofScientific m s e : α)) →
    IsNat m nm → IsNat e ne → n = Nat.mul nm ((10 : ℕ) ^ ne) →
    IsNat (@OfScientific.ofScientific α σα m false e : α) n
  | _, _, _, _, _, σh, ⟨rfl⟩, ⟨rfl⟩, h => ⟨by simp [σh, Rat.ofScientific_false_def, h]; norm_cast⟩

/-- The `norm_num` extension which identifies expressions in scientific notation, normalizing them
to rat casts if the scientific notation is inherited from the one for rationals. -/
@[norm_num OfScientific.ofScientific _ _ _] def evalOfScientific :
    NormNumExt where eval {u α} e := do
  let .app (.app (.app f (m : Q(ℕ))) (b : Q(Bool))) (exp : Q(ℕ)) ← whnfR e | failure
  let dα ← inferDivisionRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(OfScientific.ofScientific (α := $α))
  let σα ← inferOfScientific α
  assumeInstancesCommute
  haveI' : $e =Q OfScientific.ofScientific $m $b $exp := ⟨⟩
  haveI' lh : @OfScientific.ofScientific $α $σα =Q (fun m s e ↦ (Rat.ofScientific m s e : $α)) := ⟨⟩
  match b with
  | ~q(true) =>
    let rme ← derive (q(mkRat $m (10 ^ $exp)) : Q($α))
    let some ⟨q, n, d, p⟩ := rme.toRat' dα | failure
    return .isRat dα q n d q(isRat_ofScientific_of_true $σα $lh $p)
  | ~q(false) =>
    let ⟨nm, pm⟩ ← deriveNat m q(AddCommMonoidWithOne.toAddMonoidWithOne)
    let ⟨ne, pe⟩ ← deriveNat exp q(AddCommMonoidWithOne.toAddMonoidWithOne)
    have pm : Q(IsNat $m $nm) := pm
    have pe : Q(IsNat $exp $ne) := pe
    let m' := nm.natLit!
    let exp' := ne.natLit!
    let n' := Nat.mul m' (Nat.pow (10 : ℕ) exp')
    have n : Q(ℕ) := mkRawNatLit n'
    haveI : $n =Q Nat.mul $nm ((10 : ℕ) ^ $ne) := ⟨⟩
    return .isNat _ n q(isNat_ofScientific_of_false $σα $lh $pm $pe (.refl $n))
