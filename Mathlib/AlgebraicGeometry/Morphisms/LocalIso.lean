/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalClosure
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Sheaves.Init

/-!
# Local isomorphisms

A local isomorphism of schemes is a morphism that is source-locally an open immersion.
-/

@[expose] public section

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A local isomorphism of schemes is a morphism that is (Zariski-)source-locally an
open immersion. -/
@[mk_iff]
class IsLocalIso (f : X ⟶ Y) : Prop where
  exists_isOpenImmersion (x : X) : ∃ (U : X.Opens), x ∈ U ∧ IsOpenImmersion (U.ι ≫ f)

namespace IsLocalIso

variable (f : X ⟶ Y)

lemma eq_sourceLocalClosure_isOpenImmersion :
    @IsLocalIso = sourceLocalClosure IsOpenImmersion IsOpenImmersion := by
  ext
  rw [isLocalIso_iff, sourceLocalClosure.iff_forall_exists]

instance : IsZariskiLocalAtSource @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

instance : IsMultiplicative @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

instance : IsStableUnderBaseChange @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

/-- `IsLocalIso` is weaker than every source-Zariski-local property containing identities. -/
lemma le_of_isZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities]
    [IsZariskiLocalAtSource P] : @IsLocalIso ≤ P := by
  intro X Y f hf
  obtain ⟨𝒰, h⟩ := eq_sourceLocalClosure_isOpenImmersion ▸ hf
  rw [IsZariskiLocalAtSource.iff_of_openCover 𝒰 (P := P)]
  exact fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _

set_option backward.isDefEq.respectTransparency false in
/-- `IsLocalIso` is the weakest source-Zariski-local property containing identities. -/
lemma eq_iInf :
    @IsLocalIso = ⨅ (P : MorphismProperty Scheme.{u}) (_ : P.ContainsIdentities)
      (_ : IsZariskiLocalAtSource P), P := by
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    apply le_of_isZariskiLocalAtSource
  · refine iInf_le_of_le @IsLocalIso (iInf_le_of_le inferInstance (iInf_le _ ?_))
    infer_instance

end IsLocalIso

end AlgebraicGeometry
