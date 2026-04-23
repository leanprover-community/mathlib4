/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
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
# The 1-hypercover of a glue data

In this file, given `D : Scheme.GlueData`, we construct a 1-hypercover
`D.openHypercover` of the scheme `D.glued` in the big Zariski site.
We use this 1-hypercover in order to define a constructor `D.sheafValGluedMk`
for sections over `D.glued` of a sheaf of types over the big Zariski site.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

@[expose] public section

universe v u

open CategoryTheory Opposite Limits

namespace AlgebraicGeometry.Scheme.GlueData

variable (D : Scheme.GlueData.{u})

/-- The 1-hypercover of `D.glued` in the big Zariski site that is given by the
open cover `D.U` from the glue data `D`.
The "covering of the intersection of two such open subsets" is the trivial
covering given by `D.V`. -/
@[simps]
noncomputable def oneHypercover : Scheme.zariskiTopology.OneHypercover D.glued where
  I₀ := D.J
  X := D.U
  f := D.ι
  I₁ _ _ := PUnit
  Y i₁ i₂ _ := D.V (i₁, i₂)
  p₁ i₁ i₂ _ := D.f i₁ i₂
  p₂ i₁ i₂ _ := D.t i₁ i₂ ≫ D.f i₂ i₁
  w i₁ i₂ _ := by simp only [Category.assoc, Scheme.GlueData.glue_condition]
  mem₀ := by
    refine zariskiTopology.superset_covering ?_ D.openCover.mem_grothendieckTopology
    rw [Sieve.generate_le_iff]
    rintro W _ ⟨i⟩
    exact ⟨_, 𝟙 _, _, ⟨i⟩, by simp; rfl⟩
  mem₁ i₁ i₂ W p₁ p₂ fac := by
    refine zariskiTopology.superset_covering (fun T g _ ↦ ?_) (zariskiTopology.top_mem _)
    have ⟨φ, h₁, h₂⟩ := PullbackCone.IsLimit.lift' (D.vPullbackConeIsLimit i₁ i₂)
      (g ≫ p₁) (g ≫ p₂) (by simpa using g ≫= fac)
    exact ⟨⟨⟩, φ, h₁.symm, h₂.symm⟩

section

variable {F : Sheaf Scheme.zariskiTopology (Type v)}
  (s : ∀ (j : D.J), F.obj.obj (op (D.U j)))
  (h : ∀ (i j : D.J), F.obj.map (D.f i j).op (s i) =
    F.obj.map ((D.f j i).op ≫ (D.t i j).op) (s j))

/-- Constructor for sections over `D.glued` of a sheaf of types on the big Zariski site. -/
noncomputable def sheafValGluedMk : F.obj.obj (op D.glued) :=
  Multifork.IsLimit.sectionsEquiv (D.oneHypercover.isLimitMultifork F)
    { val := s
      property := fun _ ↦ h _ _ }

@[simp]
lemma sheafValGluedMk_val (j : D.J) : F.obj.map (D.ι j).op (D.sheafValGluedMk s h) = s j :=
  Multifork.IsLimit.sectionsEquiv_apply_val (D.oneHypercover.isLimitMultifork F) _ _

end

end AlgebraicGeometry.Scheme.GlueData
