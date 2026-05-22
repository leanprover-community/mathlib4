module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.RingTheory.GradedAlgebra.Map.auxiliary

@[expose] public section
/-
This file defines a type class assumption `AddSubmonoidClass.IsConcreteSSup σ M`, which asserts that
the `sSup` in some `SetLike` structure `σ` of `AddSubmonoid`s of some `AddCommMonoid` `M` is just
the `sSup` of submonoids (i.e. the span/additive closure of the union.)

Given `{σ M : Type*} [SetLike σ M]`, we have a map

  `coe : σ → Set M`

Given, in addition `[AddCommMonoid M] [AddSubmonoidClass σ M]`, this map factors through
`AddSubmonoid M`, so we have

  `σ → AddSubmonoid M → Set M`

(The first map in this factorization is called `AddSubmonoid.ofClass`, while the second is really a
special case of `coe`.)

Given, in addition `[CompleteLattice σ]`, we can make various assumptions about the behaviour of
these maps with respect to the complete lattice structures on each of `σ`, `AddSubmonoid M`, `Set
M`.

- Mathlib's `[IsConcreteLE σ M]` asserts that `coe` is order-preserving and also order-reflecting.
  (In functor language, `coe` *is* a functor, automatically faithful, and also full.)

- We have `[IsConcreteLE (AddSubmonoid M) M]`, so the second map `AddSubmonoid M → Set M` in the
  above factorization is order-preserving and order-reflecting.

  It also preserves arbitrary meets/infimas/limits = intersections, but not joins/supremas/
  colimits. (In functor language, it is a full and faithful functor that preserves limits. It is
  right adjoint to `AddSubmonoid.closure`.  Together, these functors define a  "GaloisInsertion",
  i.e. a Galois adjunction such that `closure ∘ coe = id`.)

- The assumption `[AddSubmonoidClass.IsConcreteSSup σ M]` defined here asserts that the
  factorization `ofClass : σ → AddSubmonoid M` preserves joins/supremas/colimits.

  This implies that the map is order-preserving, but we do not need this. It also implies that there
  is a right adjoint, but again, we do not need this. Note that this follows the general pattern in
  Mathlib, where sup-preserving maps are *defined* without an explicit assumption that they preserve
  order.

- In the cases where we currently want to apply `[AddSubmonoidClass.IsConcreteSSup σ M]`, the
  factorization `ofClass : σ → AddSubmonoid M` satisfies stronger properties. For examplve, for
  `σ = Submodules R M`, the map `ofClass : σ → AddSubmonoid M` is:

  - order-preserving and
  - limit-preserves and
  - colimit-preserving.

  Its left adjoint sends a submonoid `A` to the smallest R-submodule containing `A`, its right
  adjoint sends a submonoid `A` the largest R-submodule contained in `A`. (There is always some such
  R-submodule; in the worst case, it's the submodule {0}.) Precomposing either of these with
  `ofClass` is the identity on `σ`, so these two Galois adjunctions are a Galois insertion and a
  Galois coinsertion, respectively.
-/

section Mathlib.Algebra.Group.Submonoid.Defs
-- SubmoduleClass is defined at line 117, and the last mention is in line 156

/- Notes:
 - `AddSubmonoidClass.IsConcreteSSup`:
   Writing `(M : Type*)` rather than `(M : outParam Type*)` in accordance with the docstring of
   `Setlike` (Mathlib/Data/SetLike/Basic.lean, lines 96-103).  However, there is
   `(B : outParam Type*)` in the definition of `IsConcreteLE`, so I'm confused above this.

- `SetLike.iSup_toAddSubmonoid` is a SetLike generalization of `Submodule.iSup_toAddSubmonoid`.
-/

open Submonoid in
/-- A class to indicate that the canonical map `.ofClass` from a class `S` of submonoids
    of `M` to `Submonoid M` preserves suprema. -/
class SubmonoidClass.IsConcreteSSup (S : Type*) (M : outParam Type*) [Monoid M] [SetLike S M]
    [SubmonoidClass S M] [SupSet S] : Prop where
  sSup_toSubmonoid (S : Set S) : ofClass (sSup S) = sSup (ofClass '' S)

open AddSubmonoid in
/-- A class to indicate that the canonical map `.ofClass` from a class `S` of additive submonoids
    of `M` to `AddSubmonoid M` preserves suprema. -/
class AddSubmonoidClass.IsConcreteSSup (S : Type*) (M : outParam Type*) [AddMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] [SupSet S] : Prop where
  sSup_toAddSubmonoid (S : Set S) : ofClass (sSup S) = sSup (ofClass '' S)

attribute [to_additive existing] SubmonoidClass.IsConcreteSSup

namespace SubmonoidClass

open Submonoid

@[to_additive]
theorem iSup_toSubmonoid {σ : Type*} {M : Type*} [SetLike σ M] [Monoid M] [SubmonoidClass σ M]
    [SupSet σ] [IsConcreteSSup σ M]
    {ι : Sort*} (ℳ : ι → σ) :
    ofClass (⨆ i, ℳ i) = ⨆ i, ofClass (ℳ i) := by
  rw [iSup,IsConcreteSSup.sSup_toSubmonoid,←Set.range_comp]
  rfl

@[to_additive, simp]
theorem mem_iSup_iff_mem_iSup_Submonoid {σ : Type*} {M : Type*} [SetLike σ M] [Monoid M]
    [SubmonoidClass σ M] [SupSet σ] [IsConcreteSSup σ M] {ι : Sort*} (ℳ : ι → σ) (m : M) :
    m ∈ (⨆ i, ℳ i : σ) ↔ m ∈ (⨆ i, ofClass (ℳ i)) := by
  rw [← iSup_toSubmonoid ℳ]
  rfl

@[to_additive]
instance (M : Type*) [Monoid M] : IsConcreteSSup (Submonoid M) M where
  sSup_toSubmonoid S := by
    have : ofClass (sSup S) = sSup S := by rfl
    rw [this, Set.EqOn.image_eq_self (f := ofClass) (fun _ ↦ congrFun rfl)]

end SubmonoidClass

end Mathlib.Algebra.Group.Submonoid.Defs
/- --------------------------------------- -/

@[to_additive]
instance (M : Type*) [Group M] : SubmonoidClass.IsConcreteSSup (Subgroup M) M where
  sSup_toSubmonoid S := by
    have (N : Subgroup M) : Submonoid.ofClass N = N.toSubmonoid := by rfl
    simp [this, Subgroup.toSubmonoid_sSup]


instance (R : Type*) (M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    AddSubmonoidClass.IsConcreteSSup (Submodule R M) M where
  sSup_toAddSubmonoid S := by
    have (N : Submodule R M) : AddSubmonoid.ofClass N = N.toAddSubmonoid := by rfl
    simp only [this, Submodule.toAddSubmonoid_sSup]
