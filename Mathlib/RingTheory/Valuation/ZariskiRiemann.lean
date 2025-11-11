/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Zariski–Riemann space

We show that the Zariski–Riemann space of a finitely generated extension K of
transcendence degree 1 over k (a function field of 1 variable) is proper scheme over k.
-/

variable (R k K : Type*) [CommSemiring R] [Field k] [Field K] [Algebra R K] [Algebra k K]

open IntermediateField AlgebraicGeometry TopologicalSpace

namespace Algebra

/-! ## Zariski–Riemann space -/

/-- If `K` is an `R`-algebra, `Place R K` is the collection of valuation subrings in `K`
that are `R`-subalgebras. It can be given a locally ringed space structure,
in which setting it is known as the Zariski--Riemann space. -/
@[ext] structure Place extends Subalgebra R K, ValuationSubring K

def genericPoint : Place R K where
  __ : Subalgebra R K := ⊤
  __ : ValuationSubring K := ⊤

instance : SetLike (Place R K) K where
  coe v := v.carrier
  coe_injective' _ _ := Place.ext

instance : SMulMemClass (Place R K) R K where
  smul_mem {v} r _ h := v.toSubalgebra.smul_mem h r

instance : SubringClass (Place R K) K := sorry

variable {k K} in
theorem Place.integralClosure_le (v : Place k K) : integralClosure k K ≤ v.toSubalgebra := by
  intro z hz
  by_contra hzv
  have : z⁻¹ ∈ v.toSubalgebra := (v.toValuationSubring.mem_or_inv_mem z).resolve_left hzv
  exact hzv (IsIntegral.mem_of_inv_mem hz this)

instance : TopologicalSpace (Place R K) :=
  -- subbasis consists of sets of all places containing a particular element
  .generateFrom {{v | f ∈ v} | f : K}
/- Later refactoring: consider define topology on `ValuationSubring K`
and take induced topology from there. -/

theorem closure_genericPoint : closure {genericPoint k K} = .univ := by
  sorry

variable {K} in
/- This is analogous to `D(f)` in Zariski topology because `f ∈ v ↔ f⁻¹ ∉ 𝔪ᵥ`.
But we no longer have `D(f * g) = D(f) ∩ D(g)`, so these form a subbasis, not a basis. -/
def basicOpen (f : K) : Opens (Place R K) where
  carrier := {v | f ∈ v}
  is_open' := by sorry

theorem basicOpen_eq_top_iff {f : K} : basicOpen k f = ⊤ ↔ IsAlgebraic k f := by
  sorry

/- should be true but not part of this project
instance : SpectralSpace (Place R K) := by
  sorry

instance : IrreducibleSpace (Place R K) := by
  sorry

-- show all sections are domains (easy)
-- mathlib doesn't have definition of integral scheme?
-/

def Place.locallyRingedSpace : LocallyRingedSpace where
  carrier := .of (Place R K)
  presheaf :=
  { -- sections over an open set is the intersection of all places in the set
    obj U := .of ↥(⨅ v : U.1, v.1.toValuationSubring.toSubring)
    map := sorry
    map_id := sorry, map_comp := sorry /- may be automatic -/ }
  IsSheaf := sorry
  isLocalRing := sorry

-- show every section has k-algebra structure
-- compute global sections = integral (algebraic) closure of k in K

end Algebra

/-! ## Basics of function fields -/

namespace Algebra

class Is1DFunctionField : Prop where
  trdeg_eq_one : Algebra.trdeg k K = 1
  fg : (⊤ : IntermediateField k K).FG

theorem Is1DFunctionField.iff_exists_transcendental_finiteDimensional :
    Is1DFunctionField k K ↔ ∃ x : K, Transcendental k x ∧ FiniteDimensional k⟮x⟯ K := by
  sorry

namespace Place

variable [Is1DFunctionField k K]

/- show all places other than the generic point are discrete valuation rings
(`IsDiscreteValuationRing`), see [Stichtenoth, Theorem 1.1.6]. -/

def scheme : Scheme where
  __ := Place.locallyRingedSpace k K
  local_affine := sorry
  /- Sketch: show `basicOpen k f` for transcendental `f` is isomorphic to Spec B,
    where B is the integral closure of k[f] in K, c.f. [Hartshorne, Lemma I.6.5].
    The map to Spec B can be constructed using Gamma-Spec adjunction. -/

section Scheme

universe u

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [Is1DFunctionField k K]

def structureMorphism : scheme k K ⟶ Spec (.of k) := sorry
-- use Gamma-Spec adjunction
-- the locallyRingedSpace version should also satisfy the valuative criterion

instance : QuasiCompact (structureMorphism k K) := by
  sorry

instance : QuasiSeparated (structureMorphism k K) := by
  sorry

instance : LocallyOfFiniteType (structureMorphism k K) := by
  sorry -- requires Krull–Akizuki, which we may assume.
  -- IsIntegralClosure.finite is a version with extra separability assumption

instance : IsProper (structureMorphism k K) := .of_valuativeCriterion _ <| by
  sorry

end Scheme

end Algebra
