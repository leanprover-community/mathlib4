/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.GradedMonoid
import Mathlib.Algebra.Group.Submonoid.Defs
/-!
# The filtration on abelian group and ring

In this file, we defined the fitration on abelian group,
and extend it to get the filtration on ring.

# Main definitions

* `IsFiltration` : For `σ` satisfying `SetLike σ A`, an increasing series of `F` in `σ`
is filtration if there is another series `F_lt` equal to the supremum of `F` with smaller index

* `IsRingFiltration` : For `σ` satisfying `SetLike σ R` where `R` is a semiring,
an increasing series `F` in `σ` is ring filtration if `IsFiltration F F_lt` and
the pointwise multiplication of `F i` and `F j` is in `F (i + j)`

* `IsModuleFiltration` : For `F` satisfying `IsRingFiltration F F_lt` in a semiring `R` and `σM`
satisfying `SetLike σ M` where `M` is a module over `R`, an increasing series `FM` in `σM` is
module filtration if `IsFiltration F F_lt` and the pointwise scalar multiplication of
`F i` and `FM j` is in `F (i +ᵥ j)`

-/

section GeneralFiltration

variable {ι : Type*} [Preorder ι]

variable {A : Type*} {σ : Type*} [SetLike σ A]

/-- For `σ` satisfying `SetLike σ A`, an increasing series of `F` in `σ` is filtration if
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

variable {ι : Type*} [OrderedAddCommMonoid ι]

variable {R : Type*} [Semiring R] {σ : Type*} [SetLike σ R]

/-- For `σ` satisfying `SetLike σ R` where `R` is a semiring, an increasing series `F` in `σ` is
ring filtration if `IsFiltration F F_lt` and the pointwise multiplication of `F i` and `F j` is in
`F (i + j)`. -/
class IsRingFiltration (F : ι → σ) (F_lt : outParam <| ι → σ)
    extends IsFiltration F F_lt, SetLike.GradedMonoid F : Prop

/-- A special case of `IsRingFiltration` when index is integer. -/
lemma IsRingFiltration.mk_int (F : ℤ → σ) (mono : Monotone F) (one_mem : 1 ∈ F 0)
    (mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)) :
    IsRingFiltration F (fun n ↦ F (n - 1)) where
  __ := IsFiltration.mk_int F mono
  one_mem := one_mem
  mul_mem _ _ := mul_mem

end FilteredRing


section FilteredModule

variable {ι : Type*} [OrderedAddCommMonoid ι]

variable {R : Type*} [Semiring R] {σ : Type*} [SetLike σ R]

variable {M : Type*} [AddCommMonoid M] [Module R M] {ιM : Type*} [OrderedAddCommMonoid ιM]
  [VAdd ι ιM] {σM : Type*} [SetLike σM M]

/-- For `F` satisfying `IsRingFiltration F F_lt` in a semiring `R` and `σM` satisfying
 `SetLike σ M` where `M` is a module over `R`, an increasing series `FM` in `σM` is
module filtration if `IsFiltration F F_lt` and the pointwise scalar multiplication of
`F i` and `FM j` is in `F (i +ᵥ j)`.

The index set `ιM` for the module can be more general, however usually we take `ιM = ι`. -/
class IsModuleFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) [isfil : IsRingFiltration F F_lt]
    (F' : ιM → σM) (F'_lt : outParam <| ιM → σM) extends IsFiltration F' F'_lt : Prop where
  smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i +ᵥ j)

/-- A special case of `IsModuleFiltration` when index is both integer. -/
lemma IsModuleFiltration.mk_int (F : ℤ → σ) (mono : Monotone F) (one_mem : 1 ∈ F 0)
    (mul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j)) (F' : ℤ → σM)
    (mono' : Monotone F')
    (smul_mem : ∀ {i j x y}, x ∈ F i → y ∈ F' j → x • y ∈ F' (i + j)):
    IsModuleFiltration (isfil := IsRingFiltration.mk_int F mono one_mem mul_mem)
      F (fun n ↦ F (n - 1)) F' (fun n ↦ F' (n - 1)) :=
  letI := IsRingFiltration.mk_int F mono one_mem mul_mem
{ IsFiltration.mk_int F' mono' with
  smul_mem := smul_mem}

end FilteredModule
