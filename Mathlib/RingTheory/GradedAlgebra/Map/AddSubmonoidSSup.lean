import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.GradedAlgebra.Map.auxiliary

/-
This file defines a type class assumption `AddSubmonoidSSup σ M`, which asserts that the `sSup` in
some `SetLike` structure `σ` of `AddSubmonoid`s of some `AddCommMonoid` `M` is just the `sSup` of
submonoids (i.e. the span/additive closure of the union.)

Given `{σ M : Type*} [SetLike σ M]`, we have a map

  `coe : σ → Set M`

Given, in addition `[AddCommMonoid M] [AddSubmonoidClass σ M]`, this map factors through
`AddSubmonoid M`, so we have

  `σ → AddSubmonoid M → Set M`

(The first map in this factorization is called `AddSubmonoid.ofClass`, while the second is really a
special case of `coe`.)

Given, in addition `[CompleteLattice σ]`, we can make various assumptions about the behaviour of
these maps with respect to the complete lattice structures on each of `σ`, `AddSubmonoid M`,
`Set M`.

- Mathlib's `[IsConcreteLE σ M]` asserts that `coe` is order-preserving and also order-reflecting.
  (In functor language, `coe` *is* a functor, automatically faithful, and also full.)
- The map `AddSubmonoid M → Set M` (a special case of `coe`) has the property `IsConcreteLE`. It
  moreover preserves arbitrary meets/infimas = intersections, but not joins/supremas. (In functor
  language, it is a full and faithful functor that preserves limits. It is right adjoint
  `AddSubmonoid.closure`.  Together, `coe` and the closure operatior define a "GaloisInsertion".)
- The assumption `[AddSubmonoidSSup σ M]` defined here asserts that the factorization
  `σ → AddSubmonoid M` preserves joins/supremas.  This implies that the map is order-preserving,
  but we do not need this. But perhaps there should be an additional typeclass for
  "order-preserving" anyway. (From the functorial viewpoint, we're asking for a functor to
  preserve colimits.)
-/


class AddSubmonoidSSup (σ : Type*) [CompleteLattice σ]
  (M : outParam Type*) [AddCommMonoid M]
  [SetLike σ M] [AddSubmonoidClass σ M]
  where
  sSup_toAddSubmonoid (S : Set σ) :
  AddSubmonoid.ofClass (sSup S) = sSup (AddSubmonoid.ofClass '' S)

/-- A SetLike generalization of `Submodule.iSup_toAddSubmonoid` -/
lemma SetLike.iSup_toAddSubmonoid {σ : Type*} [CompleteLattice σ]
  {M : Type*} [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]
  [AddSubmonoidSSup σ M] {ι : Sort*} (ℳ : ι → σ) :
  AddSubmonoid.ofClass (⨆ i, ℳ i) = ⨆ i, AddSubmonoid.ofClass (ℳ i)
  := by
  rw [iSup,AddSubmonoidSSup.sSup_toAddSubmonoid,←Set.range_comp]
  rfl

@[simp]
lemma SetLike.mem_iSup_iff_mem_iSup_AddSubmonoid {σ : Type*} [CompleteLattice σ]
  {M : Type*} [AddCommMonoid M] [SetLike σ M] [AddSubmonoidClass σ M]
  [AddSubmonoidSSup σ M] {ι : Sort*} (ℳ : ι → σ) (m : M) :
  m ∈ (⨆ i, ℳ i : σ) ↔ m ∈ (⨆ i, AddSubmonoid.ofClass (ℳ i))
  := by
  rw [← SetLike.iSup_toAddSubmonoid ℳ]
  rfl

instance (M : Type*) [AddCommMonoid M] :
  AddSubmonoidSSup (AddSubmonoid M) M where
  sSup_toAddSubmonoid S := by
    -- This is essentially `rfl`, but still 3 lines:
    have h₁ (N : AddSubmonoid M) : AddSubmonoid.ofClass N = N := rfl
    have h₂ (S : Set (AddSubmonoid M)) : AddSubmonoid.ofClass '' S = S :=
    Set.EqOn.image_eq_self fun ⦃x⦄ ↦ congrFun rfl
    rw [h₁,h₂]

instance (M : Type*) [AddCommGroup M] :
  AddSubmonoidSSup (AddSubgroup M) M where
  sSup_toAddSubmonoid S := by
    have (N : AddSubgroup M) : AddSubmonoid.ofClass N = N.toAddSubmonoid := by rfl
    simp [this, Subgroup.toAddSubmonoid_sSup]

instance (R : Type*) [Semiring R] (M : Type*) [AddCommMonoid M] [Module R M] :
  AddSubmonoidSSup (Submodule R M) M where
  sSup_toAddSubmonoid S := by
    have (N : Submodule R M) : AddSubmonoid.ofClass N = N.toAddSubmonoid := by rfl
    simp only [this, Submodule.toAddSubmonoid_sSup]
