/-
Copyright (c) 2025 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jon Eugster, Emily Riehl
-/
import Mathlib.CategoryTheory.Enriched.Limits.HasConicalProducts
import Mathlib.CategoryTheory.Enriched.Limits.IsConicalTerminal

/-!
TODO: module docstring
-/

universe v₁ u₁ v₂ u₂ w v' v u u'

namespace CategoryTheory.Enriched

open Limits HasConicalLimit

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable (F : J ⥤ C)

variable [HasConicalLimit V F]

/-- A category has a conical terminal object
if it has a conical limit over the empty diagram. -/
abbrev HasConicalTerminal := HasConicalLimitsOfShape (Discrete.{0} PEmpty)

instance HasConicalTerminal_hasTerminal [hyp : HasConicalTerminal V C] : HasTerminal C :=
  inferInstance

namespace HasConicalTerminal

variable [HasConicalTerminal V C]

variable (C) in
/-- The conical terminal object which exists through `HasConicalTerminal V C` -/
noncomputable def conicalTerminal : C := conicalLimit V (Functor.empty.{0} C)

/-- assertion `conicalTerminal` is indeed the conical terminal object -/
noncomputable def conicalTerminalIsConicalTerminal :
    IsConicalTerminal V (conicalTerminal V C) :=
  conicalLimit.isConicalLimit V _ |>.ofIso <| Cones.ext (by rfl) (by simp)

/-- any terminal object is conical terminal -/
noncomputable def isTerminalIsConicalTerminal {T : C} (hT : IsTerminal T) :
    IsConicalTerminal V T := by
  let TT := conicalLimit V (Functor.empty.{0} C)
  let slim : IsConicalTerminal V TT := conicalTerminalIsConicalTerminal V
  let lim : IsTerminal TT := IsConicalTerminal.isTerminal V slim
  exact IsConicalTerminal.ofIso slim (hT.uniqueUpToIso lim).symm

-- note: `V` implicit because of how this is used in practise, see `Isofibrations.lean`
variable {V} in

/-- The terminal object is a conical terminal object. -/
noncomputable def terminalIsConicalTerminal : IsConicalTerminal V (⊤_ C) :=
  isTerminalIsConicalTerminal V terminalIsTerminal

end HasConicalTerminal

/-! ## Conical Products -/

namespace HasConicalProducts

instance hasConicalTerminal [hyp : HasConicalProducts.{0, v', v, u} V C] :
    HasConicalTerminal V C := by
      exact hyp.hasConicalLimitsOfShape PEmpty.{1}

instance hasConicalTerminal' [hyp : HasConicalProducts.{w, v', v, u} V C] :
    HasConicalTerminal V C := by
  have inst := hyp.hasConicalLimitsOfShape PEmpty
  exact HasConicalLimitsOfShape.of_equiv V (J := Discrete PEmpty.{w + 1}) emptyEquivalence

end HasConicalProducts

end CategoryTheory.Enriched
