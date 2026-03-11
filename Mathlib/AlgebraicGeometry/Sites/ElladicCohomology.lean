/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!

# `ℓ`-adic cohomology of a scheme

Let `X` be a scheme and `ℓ` be a prime number. In this file we define the sheaf
associated to the topological group `ℤ_[ℓ]` on the pro-étale site of `X`.
Its cohomology groups are the `ℓ`-adic cohomology groups of `X`.

## Main declarations

- `AlgebraicGeometry.Scheme.ellAdicSheaf`: The sheaf `U ↦ C(U, ℤ_[ℓ])`.
- `AlgebraicGeometry.Scheme.EllAdicCohomology`: The pro-étale cohomology groups `Hⁱ(X, ℤ_[ℓ])`.

## Notes

The `ℓ`-adic cohomology groups of `X : Scheme.{u}` are in `Type (u + 1)`, because
the pro-étale site of `X` has no essentially small subcategory with the same category of sheaves.
Eventually, we will be able to compare the `ℓ`-adic cohomology defined here with the classical
definition using étale cohomology. This will show that the groups defined here are indeed `u`-small.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

instance : IsGrothendieckAbelian.{u + 1} (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
  -- Without this, lean starts searching for `EssentiallySmall.{max (u + 1) ?v}` and fails.
  have : EssentiallySmall.{u + 1} X.ProEt := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (ProEt.topology X) Ab.{u + 1}

/--
The sheaf of continuous maps `U ↦ C(U, ℤ_[ℓ])` on the pro-étale site. This the coefficient
sheaf for `ℓ`-adic cohomology.
[Definition 6.8.1.][proetale2015]
-/
noncomputable def ellAdicSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    Sheaf (ProEt.topology X) Ab.{u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb (ℤ_[ℓ]), .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma isZero_ellAdicSheaf_of_isEmpty [IsEmpty X] : IsZero (X.ellAdicSheaf ℓ) :=
  (Sheaf.isTerminalOfEqTop (ProEt.topology_eq_top_of_isEmpty _) _).isZero

/-- `ℓ`-adic cohomology of a scheme in degree `n`. -/
def EllAdicCohomology (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) : Type (u + 1) :=
  ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj <| X.ellAdicSheaf ℓ).H n

noncomputable instance (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) : AddCommGroup (X.EllAdicCohomology ℓ n) :=
  inferInstanceAs <| AddCommGroup <|
    ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj <| X.ellAdicSheaf ℓ).H n

/-- `ℓ`-adic cohomology is trivial for the empty scheme. -/
instance [IsEmpty X] (n : ℕ) : Subsingleton (X.EllAdicCohomology ℓ n) := by
  apply Sheaf.subsingleton_H_of_isZero
  exact Functor.map_isZero _ (isZero_ellAdicSheaf_of_isEmpty _ _)

end AlgebraicGeometry.Scheme
