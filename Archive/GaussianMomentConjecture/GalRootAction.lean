/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The transitive Galois action on the roots — the concrete instantiation of the orbit-product core

To instantiate the abstract orbit-product wrapper (`OrbitProductWrapper`) at an actual polynomial, we
need the Galois group `L ≃ₐ[K] L` acting on the roots of an irreducible `Φ ∈ K[X]` (splitting in a
normal `L`), **transitively**, with the root inclusion **equivariant**. Using the *direct* action
`σ • x = σ x` (rather than Mathlib's `galAction`, whose equivariance routes through the finicky
`rootsEquivRoots`), equivariance is tautological, and transitivity comes from `IsConjRoot`: any two
roots of the same irreducible are conjugate, so `IsConjRoot.exists_algEquiv` supplies the
automorphism.
-/

open Polynomial

namespace GMC2.GalRootAction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An automorphism `σ` fixing `K` sends a root of `Φ ∈ K[X]` to a root. -/
theorem mem_rootSet_smul (Φ : K[X]) (σ : L ≃ₐ[K] L) {x : L} (hx : x ∈ Φ.rootSet L) :
    σ x ∈ Φ.rootSet L := by
  rw [mem_rootSet] at hx ⊢
  refine ⟨hx.1, ?_⟩
  rw [show (σ x) = σ.toAlgHom x from rfl, aeval_algHom_apply, hx.2, map_zero]

/-- The Galois group acts on the roots of `Φ` (direct action `σ • x = σ x`). -/
instance rootAction (Φ : K[X]) : MulAction (L ≃ₐ[K] L) (Φ.rootSet L) where
  smul σ x := ⟨σ x, mem_rootSet_smul Φ σ x.2⟩
  one_smul x := by ext; simp
  mul_smul σ τ x := by ext; simp

/-- The action is by the honest field action: `↑(σ • x) = σ ↑x` — tautological equivariance. -/
@[simp] theorem coe_smul (Φ : K[X]) (σ : L ≃ₐ[K] L) (x : Φ.rootSet L) :
    ((σ • x : Φ.rootSet L) : L) = σ (x : L) := rfl

/-- **Transitivity.**  For an irreducible `Φ` over a normal extension `L`, the Galois group acts
transitively on the roots — any two roots are conjugate (`IsConjRoot`), so an automorphism carries
one to the other. -/
theorem isPretransitive_rootAction [Normal K L] (Φ : K[X]) (hΦ : Irreducible Φ) :
    MulAction.IsPretransitive (L ≃ₐ[K] L) (Φ.rootSet L) := by
  refine ⟨fun x y => ?_⟩            -- goal: `∃ g, g • x = y`
  have hxr : (aeval (x : L)) Φ = 0 := (mem_rootSet.mp x.2).2
  have hyr : (aeval (y : L)) Φ = 0 := (mem_rootSet.mp y.2).2
  have hΦ0 : Φ ≠ 0 := hΦ.ne_zero
  have halgy : IsAlgebraic K (y : L) := ⟨Φ, hΦ0, hyr⟩
  have hinty : IsIntegral K (y : L) := halgy.isIntegral
  -- `Φ = minpoly K y * c` with `c` a unit; so `aeval x (minpoly K y) = 0`
  obtain ⟨c, hc⟩ := minpoly.dvd K (y : L) hyr
  have hcu : IsUnit c := (hΦ.isUnit_or_isUnit hc).resolve_left (minpoly.not_isUnit K (y : L))
  have hcx : aeval (x : L) c ≠ 0 := by
    obtain ⟨a, ha, hac⟩ := Polynomial.isUnit_iff.mp hcu
    rw [← hac, aeval_C]
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective K L)).mpr ha.ne_zero
  have haex : aeval (x : L) (minpoly K (y : L)) = 0 := by
    have hmul : aeval (x : L) (minpoly K (y : L)) * aeval (x : L) c = 0 := by
      rw [← map_mul, ← hc]; exact hxr
    exact (mul_eq_zero.mp hmul).resolve_right hcx
  -- `IsConjRoot K y x` ⟹ an automorphism with `σ x = y`
  have hconj : IsConjRoot K (y : L) (x : L) :=
    (isConjRoot_iff_aeval_eq_zero hinty).mpr haex
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  exact ⟨σ, Subtype.ext (by rw [coe_smul]; exact hσ)⟩

end GMC2.GalRootAction

