/-
Copyright (c) 2023 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Order.Filter.Germ

/-!
# Germs of smooth functions

Germs of smooth functions between smooth manifolds.

## Main definitions and results

* `smoothGerm I I' N x`: the set of germs of smooth functions `f : M → N` at `x : M`
* `smoothGerm.subring` and friends: if `R` is a smooth ring,
the space of germs of smooth functions `M → R` is a subring of `Germ (𝓝 x) R`.
There are analogous versions for additive and multiplicative monoids and groups.

## Tags

germ, smooth function, manifold
-/

noncomputable section

open Filter Set
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- Declare a smooth manifold `M` over the pair `(E, H)` with model `I`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [SmoothManifoldWithCorners I M]
  -- Declare a smooth manifold `N` over the pair `(E', H')` with model `I'`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

variable (N) in
/-- The set of all germs of smooth functions `M → N` at `x : N`. -/
def smoothGerm (x : M) : Set (Germ (𝓝 x) N) :=
  { Filter.Germ.ofFun f | f : SmoothMap I I' M N }

@[simp]
lemma mem_smoothGerm {x : M} (a : Germ (𝓝 x) N) :
    a ∈ smoothGerm I I' N x ↔ ∃ f : SmoothMap I I' M N, Germ.ofFun f = a := by
  rfl

namespace smoothGerm
instance (x : M) [ChartedSpace H' N] : Coe C^∞⟮I, M; I', N⟯ (smoothGerm I I' N x) :=
  ⟨fun f ↦ ⟨(f : M → N), ⟨f, rfl⟩⟩⟩

@[simp]
theorem coe_coe (f : C^∞⟮I, M; I', N⟯) (x : M) :
    ((f : smoothGerm I I' N x) : (𝓝 x).Germ N) = (f : (𝓝 x).Germ N) :=
  rfl

theorem coe_eq_coe (f g : C^∞⟮I, M; I', N⟯) {x : M} (h : ∀ᶠ y in 𝓝 x, f y = g y) :
    (f : smoothGerm I I' N x) = (g : smoothGerm I I' N x) := by
  ext
  rwa [Germ.coe_eq]

-- If `R` has the appropriate structure, `smoothGerm I I' R x` is a subgroup etc.
-- All respective axioms are easy to prove by choosing explicit representatives.
section subring

variable (I' : ModelWithCorners 𝕜 E' H')
  (R : Type*) [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]

/-- If `R` is a manifold with smooth multiplication,
`smoothGerm I I' R x` is a submonoid of `Germ (𝓝 x) R`. -/
def submonoid [SmoothMul I' R] (x : M) : Submonoid (Germ (𝓝 x) R) where
  carrier := smoothGerm I I' R x
  mul_mem' ha hb := by
    choose f hf using ha
    choose g hg using hb
    exact ⟨f * g, by rw [← hf, ← hg, SmoothMap.coe_mul, Germ.coe_mul]⟩
  one_mem' := ⟨1, by rw [SmoothMap.coe_one, Germ.coe_one]⟩

@[simp, norm_cast]
lemma coe_submonoid [SmoothMul I' R] (x : M) :
  smoothGerm.submonoid I I' R x = smoothGerm I I' R x := rfl

@[simp]
lemma mem_submonoid [SmoothMul I' R] {x : M} (a : Germ (𝓝 x) R) :
    a ∈ smoothGerm.submonoid I I' R x ↔ a ∈ smoothGerm I I' R x := Iff.rfl

/-- If `R` is a manifold with smooth addition,
`smoothGerm I I' R x` is an additive sub-semigroup of `Germ (𝓝 x) R`. -/
def addSubsemigroup [SmoothAdd I' R] (x : M) : AddSubsemigroup (Germ (𝓝 x) R) where
  carrier := smoothGerm I I' R x
  add_mem' ha hb := by
    choose f hf using ha
    choose g hg using hb
    exact ⟨f + g, by rw [← hf, ← hg, SmoothMap.coe_add, Germ.coe_add]⟩

@[simp, norm_cast]
lemma coe_addSubsemigroup [SmoothAdd I' R] (x : M) :
  smoothGerm.addSubsemigroup I I' R x = smoothGerm I I' R x := rfl

@[simp]
lemma mem_addSubsemigroup [SmoothAdd I' R] {x : M} (a : Germ (𝓝 x) R) :
    a ∈ smoothGerm.addSubsemigroup I I' R x ↔ a ∈ smoothGerm I I' R x := Iff.rfl

/-- If `G` is an additive Lie group, `smoothGerm I I' G x` is
an additive subgroup of `Germ (𝓝 x) G`. -/
def addSubgroup [LieAddGroup I' R] (x : M) : AddSubgroup (Germ (𝓝 x) R) where
  __ := smoothGerm.addSubsemigroup I I' R x
  zero_mem' := ⟨0, by rw [SmoothMap.coe_zero, Germ.coe_zero]⟩
  neg_mem' h := by
    choose f hf using h
    exact ⟨-f, by rw [← hf, SmoothMap.coe_neg, Germ.coe_neg]⟩

@[simp, norm_cast]
lemma coe_addSubgroup [LieAddGroup I' R] (x : M) :
  smoothGerm.addSubgroup I I' R x = smoothGerm I I' R x := rfl

@[simp]
lemma mem_addSubgroup [LieAddGroup I' R] {x : M} (a : Germ (𝓝 x) R) :
    a ∈ smoothGerm.addSubgroup I I' R x ↔ a ∈ smoothGerm I I' R x := Iff.rfl

/-- If `R` is a smooth ring, `smoothGerm I I' R x` is a subring of `Germ (𝓝 x) R`. -/
def subring [SmoothRing I' R] (x : M) : Subring (Germ (𝓝 x) R) where
  __ := smoothGerm.submonoid I I' R x
  __ := smoothGerm.addSubgroup I I' R x

@[simp, norm_cast]
lemma coe_toSubring [SmoothRing I' R] (x : M) : smoothGerm.subring I I' R x = smoothGerm I I' R x :=
  rfl

@[simp]
lemma mem_toSubring [SmoothRing I' R] {x : M} (a : Germ (𝓝 x) R) :
    a ∈ smoothGerm.subring I I' R x ↔ a ∈ smoothGerm I I' R x := Iff.rfl

/-- The map `C^∞(M, R) → Germ (𝓝 x) R` as a ring homomorphism, for a smooth ring `R`. -/
def germOfContMDiffMap (R : Type*) [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
    [SmoothRing I' R] (x : M) : C^∞⟮I, M; I', R⟯  →+* Germ (𝓝 x) R :=
  (Germ.coeRingHom _).comp SmoothMap.coeFnRingHom

lemma subring_eq_range [SmoothRing I' R] (x : M) :
    smoothGerm.subring I I' R x = (germOfContMDiffMap I I' R x).range := by
  rfl

def aux [SmoothRing I' R] (x : M) : R →+* (Germ (𝓝 x) R) :=
  sorry--Filter.Germ.coeRingHom (R := R) (α := M) (𝓝 x) --a--sorry
-- -- TODO complete this!
-- def xxxalgebra [SmoothRing I' R] (x : M) : Algebra R (Germ (𝓝 x) R) where
--   __ := aux I I' R x--toFun := sorry
-- --   commutes' := sorry
-- --   smul_def' := sorry

-- /-- The map `C^∞(M, R) → Germ (𝓝 x) R` as an `R`-algebra homomorphism, for a smooth ring `R`. -/
--  def germOfContMDiffMap2 (R : Type*) [CommRing R] [TopologicalSpace R] [ChartedSpace H' R]
--     [SmoothRing I' R] (x : M) : C^∞⟮I, M; I', R⟯  →ₐ Germ (𝓝 x) R := sorry


end subring

end smoothGerm
