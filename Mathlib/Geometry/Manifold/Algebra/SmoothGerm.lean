/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Order.Filter.Germ

/-! # Germs of smooth functions

Germs of smooth functions between manifolds.

## Main definitions and results
* `smoothGerm I I' N x`: the set of germs of smooth functions `f : M → N` at `x : M`
* `smoothGerm.toSubring` and friends: if `R` is a smooth ring,
the space of germs of smooth functions `M → R` is a subring of `Germ (𝓝 x) R`

## Tags
germ, smooth function, manifold

-/

noncomputable section

open Filter Set

open scoped Manifold Topology BigOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a smooth manifold `M` over the pair `(E, H)` with model `I`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- declare a smooth manifold `N` over the pair `(E', H')` with model `I'`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

-- Definition of germs of smooth maps, between any two manifolds.
section definition

variable (N) in
/-- The set of all germs of smooth functions `M → N` at `x : N`. -/
def smoothGerm (x : M) : Set (Germ (𝓝 x) N) :=
  { Filter.Germ.ofFun f | f : SmoothMap I I' M N }

instance (x : M) [ChartedSpace H' N] : Coe C^∞⟮I, M; I', N⟯ (smoothGerm I I' N x) :=
  ⟨fun f ↦ ⟨(f : M → N), ⟨f, rfl⟩⟩⟩

@[simp]
theorem smoothGerm.coe_coe (f : C^∞⟮I, M; I', N⟯) (x : M) :
    ((f : smoothGerm I I' N x) : (𝓝 x).Germ N) = (f : (𝓝 x).Germ N) :=
  rfl

@[simp]
theorem smoothGerm.coe_eq_coe (f g : C^∞⟮I, M; I', N⟯) {x : M} (h : ∀ᶠ y in 𝓝 x, f y = g y) :
    (f : smoothGerm I I' N x) = (g : smoothGerm I I' N x) := by
  ext
  exact Germ.coe_eq.mpr h

-- xxx: is this lemma useful?
lemma smoothGerm_iff_of_smoothFunction {x : M} (a : Germ (𝓝 x) N) :
    a ∈ smoothGerm I I' N x ↔ ∃ f : SmoothMap I I' M N, Germ.ofFun f = a := by
  rfl

end definition

-- If `R` has the appropriate structure, `smoothGerm I I' R x` is a subgroup etc.
-- All axioms are easy to prove by choosing explicit representatives.
section subring

-- for instance, HasZero resp. HasOne imply the space of smooth germs has one...
variable (I' : ModelWithCorners 𝕜 E' H')
  (R : Type*) [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]

/-- If `R` is a manifold with smooth multiplication,
`smoothGerm I I' R x` is a sub-semigroup of `Germ (𝓝 x) R`. -/
def smoothGerm.toSubsemigroup [SmoothMul I' R] (x : M) : Subsemigroup (Germ (𝓝 x) R) where
  carrier := smoothGerm I I' R x
  mul_mem' ha hb := by
    choose f hf using ha
    choose g hg using hb
    exact ⟨f * g, by rw [← hf, ← hg, SmoothMap.coe_mul, Germ.coe_mul]⟩

/-- If `R` is a manifold with smooth multiplication,
`smoothGerm I I' R x` is a submonoid of `Germ (𝓝 x) R`. -/
-- TODO: is this definition useful, given it has the same assumptions has `toSubsemigroup`??
def smoothGerm.toSubmonoid [SmoothMul I' R] (x : M) : Submonoid (Germ (𝓝 x) R) where
  toSubsemigroup := smoothGerm.toSubsemigroup I I' R x
  one_mem' := ⟨1, by rw [SmoothMap.coe_one, Germ.coe_one]⟩

/-- If `R` is a manifold with smooth addition,
`smoothGerm I I' R x` is an additive sub-semigroup of `Germ (𝓝 x) R`. -/
def smoothGerm.toAddSubsemigroup [SmoothAdd I' R] (x : M) : AddSubsemigroup (Germ (𝓝 x) R) where
  carrier := smoothGerm I I' R x
  add_mem' ha hb := by
    choose f hf using ha
    choose g hg using hb
    exact ⟨f + g, by rw [← hf, ← hg, SmoothMap.coe_add, Germ.coe_add]⟩

/-- If `G` is an additive Lie group, `smoothGerm I I' G x` is
  an additive subgroup of `Germ (𝓝 x) G`. -/
def smoothGerm.toAddSubgroup [LieAddGroup I' R] (x : M) : AddSubgroup (Germ (𝓝 x) R) where
  __ := smoothGerm.toAddSubsemigroup I I' R x
  zero_mem' := ⟨0, by rw [SmoothMap.coe_zero, Germ.coe_zero]⟩
  neg_mem' h := by
    choose f hf using h
    exact ⟨-f, by rw [← hf, SmoothMap.coe_neg, Germ.coe_neg]⟩

/-- If `R` is a smooth ring, `smoothGerm I I' R x` is a subring of `Germ (𝓝 x) R`. -/
def smoothGerm.toSubring [SmoothRing I' R] (x : M) : Subring (Germ (𝓝 x) R) where
  toSubmonoid := smoothGerm.toSubmonoid I I' R x
  -- xxx: how can I copy this from `toAddSubgroup`?
  zero_mem' := ⟨0, by rw [SmoothMap.coe_zero, Germ.coe_zero]⟩
  add_mem' ha hb := by
    choose f hf using ha
    choose g hg using hb
    exact ⟨f + g, by rw [← hf, ← hg, SmoothMap.coe_add, Germ.coe_add]⟩
  neg_mem' h := by
    choose f hf using h
    exact ⟨ -f, by rw [← hf, SmoothMap.coe_neg, Germ.coe_neg]⟩

-- xxx: is this lemma useful?
lemma smoothGerm.toSubring_mem_coe [SmoothRing I' R] {x : M} (a : Germ (𝓝 x) R) :
    a ∈ smoothGerm.toSubring I I' R x ↔ a ∈ smoothGerm I I' R x := by rfl

/-- The map `C^∞(M, R) → Germ (𝓝 x) R` as a ring homomorphism, for a smooth ring `R`. -/
def RingHom.germOfContMDiffMap (R : Type*) [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [SmoothRing I' R] (x : M) : C^∞⟮I, M; I', R⟯ →+* Germ (𝓝 x) R :=
  RingHom.comp (Germ.coeRingHom _) SmoothMap.coeFnRingHom

lemma toSubring_eq_range [SmoothRing I' R] (x : M) :
    smoothGerm.toSubring I I' R x = (RingHom.germOfContMDiffMap I I' R x).range := by
  rfl
