/-
Copyright (c) 2026 Zhan Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhan Shi, Marco David
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Graded multilinear maps

This file defines graded multilinear maps of a fixed degree between externally graded modules,
i.e. families of modules `N : β → Type*` indexed by a type of degrees `β`.

A graded multilinear map `f` of degree `d` from the families `M k`, with indices `k : ι`,
to `N` consists of one multilinear map from `∀ k, M k (p k)` to `N q` for each choice of input
degrees `p : ι → β` and each output degree `q` with `(∑ k, p k) + d = q`.

## Main definitions

* `AInfinity.GradedMultilinearMap.Degrees ι d`: the input degrees `p : ι → β` together with
  an output degree `q` with `(∑ k, p k) + d = q`.
* `AInfinity.GradedMultilinearMap R M N d`: graded `R`-multilinear maps of degree `d` from
  the families `M k`, `k : ι`, to `N`.

## Main results

* `GradedMultilinearMap` is an additive commutative monoid (a group if `N` is), and a module over
  any semiring `S` whose action on each `N i` commutes with that of `R`.

## Implementation notes

Following `CochainComplex.HomComplex.Cochain` and `CochainComplex.HomComplex.Triplet`, a graded
multilinear map of degree `d` is a dependent function on the structure
`GradedMultilinearMap.Degrees ι d` of triples `⟨p, q, hpq⟩` with `hpq : (∑ k, p k) + d = q`.

Bundling the proof into this structure makes graded multilinear maps a `Pi` type, so their additive
group and module structures are inherited from the `Pi` instances.

`GradedMultilinearMap` needs `AddCommMonoid β` to sum the input degrees.
-/

@[expose] public section

namespace AInfinity

universe u v w₁ w₂

/-- A choice of degrees for a graded multilinear map of degree `d` with inputs indexed by `ι`:
input degrees `p : ι → β` and an output degree `q` with `(∑ k, p k) + d = q`. A graded
multilinear map of degree `d` has one component for each such choice. -/
structure GradedMultilinearMap.Degrees (ι : Type*) [Fintype ι] {β : Type v} [AddCommMonoid β]
    (d : β) where
  /-- The input degrees. -/
  p : ι → β
  /-- The output degree. -/
  q : β
  /-- The output degree is the total input degree shifted by `d`. -/
  hpq : (∑ k, p k) + d = q

/-- A graded `R`-multilinear map of degree `d` from the families `M k` (for `k : ι`) to `N`
consists of, for each choice of input degrees `p : ι → β` and each output degree `q` with
`(∑ k, p k) + d = q`, an `R`-multilinear map from `∀ k, M k (p k)` to `N q`. The possible choices
of valid input and output degrees are bundled in the tuples `T : GradedMultilinearMap.Degrees ι d`.
-/
def GradedMultilinearMap (R : Type u) [Semiring R] {ι : Type*} [Fintype ι]
    {β : Type v} [AddCommMonoid β] (M : ι → β → Type w₁) (N : β → Type w₂)
    [∀ k i, AddCommMonoid (M k i)] [∀ k i, Module R (M k i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] (d : β) :=
  ∀ T : GradedMultilinearMap.Degrees ι d, (Π k, M k (T.p k)) →ₘₗ[R] N T.q
deriving AddCommMonoid

namespace GradedMultilinearMap

variable {R : Type u} [Semiring R] {ι : Type*} [Fintype ι] {β : Type v} [AddCommMonoid β]
variable {M : ι → β → Type w₁} {N : β → Type w₂}
variable [∀ k i, AddCommMonoid (M k i)] [∀ k i, Module R (M k i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)] {d : β}

/-- The graded multilinear map with component `v p q hpq` for input degrees `p` and output
degree `q`, for each such choice with `(∑ k, p k) + d = q`. -/
def mk (v : ∀ (p : ι → β) (q : β), (∑ k, p k) + d = q →
    (Π k, M k (p k)) →ₘₗ[R] N q) : GradedMultilinearMap R M N d :=
  fun ⟨p, q, hpq⟩ ↦ v p q hpq

/-- The component of a graded multilinear map with input degrees `p` and output degree `q`,
where `(∑ k, p k) + d = q`. -/
def v (f : GradedMultilinearMap R M N d) (p : ι → β) (q : β) (hpq : (∑ k, p k) + d = q) :
    (Π k, M k (p k)) →ₘₗ[R] N q :=
  f ⟨p, q, hpq⟩

@[simp]
theorem mk_v (v : ∀ (p : ι → β) (q : β), (∑ k, p k) + d = q →
    (Π k, M k (p k)) →ₘₗ[R] N q) (p : ι → β) (q : β)
    (hpq : (∑ k, p k) + d = q) : (mk v).v p q hpq = v p q hpq :=
  rfl

theorem congr_v {f g : GradedMultilinearMap R M N d} (h : f = g) (p : ι → β) (q : β)
    (hpq : (∑ k, p k) + d = q) : f.v p q hpq = g.v p q hpq := by
  rw [h]

@[ext]
theorem ext {f g : GradedMultilinearMap R M N d}
    (h : ∀ p q hpq, f.v p q hpq = g.v p q hpq) : f = g := by
  funext ⟨p, q, hpq⟩
  exact h p q hpq

section AddCommMonoid

/-- Graded multilinear maps of degree `d` form a module over any semiring `S` acting on the
target, provided this action commutes with that of `R`. -/
instance {S : Type*} [Semiring S] [∀ i, Module S (N i)] [∀ i, SMulCommClass R S (N i)] :
    Module S (GradedMultilinearMap R M N d) :=
  inferInstanceAs <| Module S (∀ _, _)

@[simp]
theorem zero_v (p : ι → β) (q : β) (hpq : (∑ k, p k) + d = q) :
    (0 : GradedMultilinearMap R M N d).v p q hpq = 0 :=
  rfl

@[simp]
theorem add_v (f g : GradedMultilinearMap R M N d) (p : ι → β) (q : β)
    (hpq : (∑ k, p k) + d = q) : (f + g).v p q hpq = f.v p q hpq + g.v p q hpq :=
  rfl

@[simp]
theorem smul_v {S : Type*} [Semiring S] [∀ i, Module S (N i)] [∀ i, SMulCommClass R S (N i)]
    (c : S) (f : GradedMultilinearMap R M N d) (p : ι → β) (q : β)
    (hpq : (∑ k, p k) + d = q) : (c • f).v p q hpq = c • f.v p q hpq :=
  rfl

@[simp]
theorem nsmul_v (n : ℕ) (f : GradedMultilinearMap R M N d) (p : ι → β) (q : β)
    (hpq : (∑ k, p k) + d = q) : (n • f).v p q hpq = n • f.v p q hpq :=
  rfl

end AddCommMonoid

section AddCommGroup

variable {N : β → Type w₂} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- Graded multilinear maps of degree `d` into a family of additive groups form an additive
commutative group. -/
instance : AddCommGroup (GradedMultilinearMap R M N d) :=
  inferInstanceAs <| AddCommGroup (∀ _, _)

@[simp]
theorem neg_v (f : GradedMultilinearMap R M N d) (p : ι → β) (q : β)
    (hpq : (∑ k, p k) + d = q) : (-f).v p q hpq = -f.v p q hpq :=
  rfl

@[simp]
theorem sub_v (f g : GradedMultilinearMap R M N d) (p : ι → β) (q : β)
    (hpq : (∑ k, p k) + d = q) : (f - g).v p q hpq = f.v p q hpq - g.v p q hpq :=
  rfl

@[simp]
theorem zsmul_v (n : ℤ) (f : GradedMultilinearMap R M N d) (p : ι → β) (q : β)
    (hpq : (∑ k, p k) + d = q) : (n • f).v p q hpq = n • f.v p q hpq :=
  rfl

end AddCommGroup

end GradedMultilinearMap

end AInfinity
