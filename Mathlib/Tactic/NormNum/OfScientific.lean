/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Data.Rat.Cast.Lemmas

/-!
## `norm_num` plugin for scientific notation.
-/

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

variable {α : Type*}

-- see note [norm_num lemma function equality]
theorem isNNRat_ofScientific_of_true [DivisionRing α] :
    {m e : ℕ} → {n : ℕ} → {d : ℕ} →
    IsNNRat (mkRat m (10 ^ e) : α) n d → IsNNRat (OfScientific.ofScientific m true e : α) n d
  | _, _, _, _, ⟨_, eq⟩ => ⟨‹_›, by
    rwa [← Rat.cast_ofScientific, ← Rat.ofScientific_eq_ofScientific, Rat.ofScientific_true_def]⟩

-- see note [norm_num lemma function equality]
theorem isNat_ofScientific_of_false [DivisionRing α] : {m e nm ne n : ℕ} →
    IsNat m nm → IsNat e ne → n = Nat.mul nm ((10 : ℕ) ^ ne) →
    IsNat (OfScientific.ofScientific m false e : α) n
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => ⟨by
    rw [← Rat.cast_ofScientific, ← Rat.ofScientific_eq_ofScientific]
    simp only [Nat.cast_id, Rat.ofScientific_false_def, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, h, Nat.mul_eq]
    norm_cast⟩

/-- The `norm_num` extension which identifies expressions in scientific notation, normalizing them
to rat casts if the scientific notation is inherited from the one for rationals. -/
@[norm_num OfScientific.ofScientific _ _ _] def evalOfScientific :
    NormNumExt where eval {u α} e := do
  let .app (.app (.app f (m : Q(ℕ))) (b : Q(Bool))) (exp : Q(ℕ)) ← whnfR e | failure
  let dα ← inferDivisionRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(OfScientific.ofScientific (α := $α))
  assumeInstancesCommute
  haveI' : $e =Q OfScientific.ofScientific $m $b $exp := ⟨⟩
  match b with
  | ~q(true) =>
    let rme ← derive (q(mkRat $m (10 ^ $exp)) : Q($α))
    let some ⟨q, n, d, p⟩ := rme.toNNRat' q(DivisionRing.toDivisionSemiring) | failure
    return .isNNRat q(DivisionRing.toDivisionSemiring) q n d q(isNNRat_ofScientific_of_true $p)
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
    return .isNat _ n q(isNat_ofScientific_of_false $pm $pe (.refl $n))

end NormNum

end Meta

end Mathlib
