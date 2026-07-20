/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.RudimentaryCode

/-!
# A well-order on one definability step

Every member of `godelDef U` has a least rudimentary term representing it,
relative to a well-order of the generators `Option (ZFCarrier U)`.  Distinct
sets have distinct least terms because evaluating such a term recovers the
set.  Pulling the structural term order back along this injection therefore
well-orders `godelDef U`.
-/

@[expose] public section

universe u

namespace Constructible.Godel

open RudimentaryTerm

/-- The subtype of sets produced by one Gödel-definability step over `U`. -/
abbrev DefCarrier (U : ZFSet.{u}) :=
  {z : ZFSet.{u} // z ∈ godelDef U}

/-- The least rudimentary term representing an element of `godelDef U`. -/
noncomputable def leastTermMap (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    DefCarrier U → RudimentaryClosureTerm U :=
  fun z => leastRepresentingTerm U z.1 z.2 r

@[simp]
theorem eval_leastTermMap (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r]
    (z : DefCarrier U) :
    (leastTermMap U r z).eval = z.1 :=
  eval_leastRepresentingTerm U z.1 z.2 r

/-- Different sets in `godelDef U` have different least representing terms. -/
theorem leastTermMap_injective (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    Function.Injective (leastTermMap U r) := by
  intro x y hxy
  apply Subtype.ext
  have heval := congrArg RudimentaryClosureTerm.eval hxy
  simpa only [eval_leastTermMap] using heval

/-- Compare definable sets by their least rudimentary representations. -/
noncomputable def defCarrierRel (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    DefCarrier U → DefCarrier U → Prop :=
  InvImage (codeRel r) (leastTermMap U r)

/-- The least-term order well-orders the full Gödel-definability step. -/
theorem defCarrierRel_isWellOrder (U : ZFSet.{u})
    (r : Option (Constructible.ZFCarrier U) →
      Option (Constructible.ZFCarrier U) → Prop)
    [IsWellOrder (Option (Constructible.ZFCarrier U)) r] :
    IsWellOrder (DefCarrier U) (defCarrierRel U r) := by
  letI : IsWellOrder (RudimentaryClosureTerm U) (codeRel r) :=
    codeRel_isWellOrder r
  refine
    { wf := InvImage.wf (leastTermMap U r)
        (IsWellFounded.wf : WellFounded (codeRel r))
      trichotomous :=
        (InvImage.trichotomous (r := codeRel r)
          (leastTermMap_injective U r)).trichotomous }

end Constructible.Godel
