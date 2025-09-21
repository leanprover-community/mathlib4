/-
Copyright (c) 2025 Uni Marx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uni Marx
-/
import Mathlib.RepresentationTheory.FDRep

/-!
# Representations of commutative monoids

This file introduces facts on representations of monoids that only holds for commutative monoids.

A key result shown in `finrank_eq_one_simple_of_commMonoid` is that for a commutative monoid, the
simple finite dimensional representations over algebraically closed fields are all one-dimensional.

-/

universe u
open CategoryTheory LinearMap Representation Module

namespace FDRep
variable {k G : Type u} [Field k] [CommMonoid G]

/-- If `G` is a commutative monoid and `k` is algebraically closed, any finite dimensional
simple representation of `G` has dimension 1. -/
theorem finrank_eq_one_simple_of_commMonoid [IsAlgClosed k]
    {V : FDRep k G} [Simple V] : finrank k V = 1 := by
  -- exclude the case of dim 0 representations
  have finrank_pos : 0 < finrank k V := FDRep.finrank_pos_of_simple V
  rw[finrank_pos_iff_exists_ne_zero] at finrank_pos
  obtain ⟨x, x_nonzero⟩ := finrank_pos
  -- We show that for any nonzero `x : V`, the span of `x` is a subrepresentation.
  -- We have to explicitly show it is a representation since the relationship
  -- between `FDRep` and `Rep` is not developed well enough yet.
  -- TODO: fix this when made possible
  let W := Submodule.span k {x}
  -- This is true since `G` is abelian, such that each `V.ρ g` is a representation morphism, ...
  let rho_endo (g : G) : V ⟶ V := ⟨FGModuleCat.ofHom <| V.ρ g, by
    intro h
    ext a
    change (V.ρ g * V.ρ h) a = (V.ρ h * V.ρ g) a
    rw[← map_mul, ← map_mul, mul_comm]⟩
  have invariant (g y) (hy : y ∈ Submodule.span k {x}) : (V.ρ g) y ∈ Submodule.span k {x} := by
    change (rho_endo g) y ∈ Submodule.span k {x}
  -- ...hence by Schur's lemma, it acts as a scalar and every subspace is invariant.
    obtain ⟨c, eq⟩ := endomorphism_simple_eq_smul_id k <| rho_endo g
    rw[← eq]
    exact (Submodule.span k {x}).smul_mem c hy
  -- So the span of `x` can be turned into a representation with `V.ρ`.
  let w_rho : G →* W →ₗ[k] W := ⟨⟨fun g => (V.ρ g).restrict <| invariant g,
      by ext a; simp⟩,
    by intro g h; ext a; aesop⟩
  let WMod := FDRep.of w_rho
  -- This subrepresentation induces a monomorphism into `V`, which must be iso since `V` is simple.
  let incl : WMod ⟶ V := ⟨FGModuleCat.ofHom <| Submodule.subtype _, fun _ => rfl⟩
  have mono_incl : Mono incl :=
    (forget (FDRep k G)).reflectsMonomorphisms_of_faithful.reflects incl (by
      rw[CategoryTheory.mono_iff_injective]
      rintro ⟨a,ha⟩ ⟨b,hb⟩ rfl
      rfl)
  have incl_nz : incl ≠ 0 := by
    intro h
    have mem : x ∈ Submodule.span k {x} := Submodule.mem_span_singleton_self x
    have wrong : incl ⟨x,mem⟩ = (0 : WMod ⟶ V) ⟨x,mem⟩ := by rw[h]
    exact x_nonzero wrong
  have := isIso_of_mono_of_nonzero incl_nz
  let incl' := (forget₂ (FGModuleCat k) (ModuleCat k)).mapIso <|
    (forget₂ _ (FGModuleCat k)).mapIso <| asIso incl
  -- Hence `V` must be equal to the span of `x`, hence 1-dimensional.
  let incl_equiv : WMod ≃ₗ[k] V.V := CategoryTheory.Iso.toLinearEquiv <| incl'
  rw[← LinearEquiv.finrank_eq incl_equiv]
  apply finrank_span_singleton x_nonzero

end FDRep
