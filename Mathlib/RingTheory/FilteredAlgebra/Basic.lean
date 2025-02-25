/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.GradedMulAction
/-!
# The filtration on abelian groups and rings

In this file, we define the fitration on abelian groups,
and extend it to get the filtration on rings.

# Main definitions

* `IsFiltration` : For `σ` satisfying `SetLike σ A`, an increasing series of `F` in `σ`
  is a filtration if there is another series `F_lt` equal to the supremum of `F` with smaller index.

* `IsRingFiltration` : For `σ` satisfying `SetLike σ R` where `R` is a semiring,
  an increasing series `F` in `σ` is a ring filtration if `IsFiltration F F_lt` and
  the pointwise multiplication of `F i` and `F j` is in `F (i + j)`.

* `IsModuleFiltration` : For `F` satisfying `IsRingFiltration F F_lt` in a semiring `R` and `σM`
  satisfying `SetLike σ M` where `M` is a module over `R`, an increasing series `FM` in `σM` is
  a module filtration if `IsFiltration F F_lt` and the pointwise scalar multiplication of
  `F i` and `FM j` is in `F (i +ᵥ j)`.

-/

section GeneralFiltration

variable {ι A σ : Type*} [Preorder ι] [SetLike σ A]

/-- For `σ` satisfying `SetLike σ A`, an increasing series of `F` in `σ` is a filtration if
there is another series `F_lt` equal to the supremum of `F` with smaller index.

In fact `F_lt j = ⨆ i < j, F i`, the design of `F_lt` can handle different conditions in the
same structure, it avoid adding `CompleteLattice` to `σ`, also providing convenience when the index
is `ℤ`. -/
class IsFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) : Prop where
  mono : Monotone F
  is_le {i j} : i < j → F i ≤ F_lt j
  is_sup (B : σ) (j : ι) : (∀ i < j, F i ≤ B) → F_lt j ≤ B

/-- A special case of `IsFiltration` when index is integer. -/
lemma IsFiltration.mk_int (F : ℤ → σ) (mono : Monotone F) :
    IsFiltration F (fun n ↦ F (n - 1)) where
  mono := mono
  is_le lt := mono (Int.le_sub_one_of_lt lt)
  is_sup _ j hi := hi (j - 1) (sub_one_lt j)

end GeneralFiltration

section FilteredRing

variable {ι R σ : Type*} [OrderedAddCommMonoid ι] [Semiring R] [SetLike σ R]

/-- For `σ` satisfying `SetLike σ R` where `R` is a semiring, an increasing series `F` in `σ` is
a ring filtration if `IsFiltration F F_lt` and the pointwise multiplication of `F i` and `F j`
is in `F (i + j)`. -/
class IsRingFiltration (F : ι → σ) (F_lt : outParam <| ι → σ)
    extends IsFiltration F F_lt, SetLike.GradedMonoid F : Prop

/-- A special case of `IsRingFiltration` when index is integer. -/
lemma IsRingFiltration.mk_int (F : ℤ → σ) (mono : Monotone F) [SetLike.GradedMonoid F] :
    IsRingFiltration F (fun n ↦ F (n - 1)) where
  __ := IsFiltration.mk_int F mono

end FilteredRing


section FilteredModule

variable {ι ιM R M σ σM : Type*} [OrderedAddCommMonoid ι] [OrderedAddCommMonoid ιM]
variable [Semiring R] [SetLike σ R] [AddCommMonoid M] [Module R M] [VAdd ι ιM] [SetLike σM M]

/-- For `F` satisfying `IsRingFiltration F F_lt` in a semiring `R` and `σM` satisfying
`SetLike σ M` where `M` is a module over `R`, an increasing series `FM` in `σM` is
a module filtration if `IsFiltration F F_lt` and the pointwise scalar multiplication of
`F i` and `FM j` is in `F (i +ᵥ j)`.

The index set `ιM` for the module can be more general, however usually we take `ιM = ι`. -/
class IsModuleFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) [isfil : IsRingFiltration F F_lt]
    (F' : ιM → σM) (F'_lt : outParam <| ιM → σM)
    extends IsFiltration F' F'_lt, SetLike.GradedSMul F F' : Prop

/-- A special case of `IsModuleFiltration` when index is both integer. -/
lemma IsModuleFiltration.mk_int (F : ℤ → σ) (mono : Monotone F) [SetLike.GradedMonoid F]
    (F' : ℤ → σM) (mono' : Monotone F') [SetLike.GradedSMul F F']:
    IsModuleFiltration (isfil := IsRingFiltration.mk_int F mono)
      F (fun n ↦ F (n - 1)) F' (fun n ↦ F' (n - 1)) :=
  letI := IsRingFiltration.mk_int F mono
  { IsFiltration.mk_int F' mono' with }

end FilteredModule
