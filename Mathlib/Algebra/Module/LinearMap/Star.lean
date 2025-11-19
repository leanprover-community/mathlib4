/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Star.Basic

/-!
# Notation for star-linear maps

This is in a separate file as a it is not needed until much later,
and avoids importing the theory of star operations unnecessarily early.
-/

@[expose] public section

/-- `M →ₗ⋆[R] N` is the type of `R`-conjugate-linear maps from `M` to `N`. -/
notation:25 M " →ₗ⋆[" R:25 "] " M₂:0 => LinearMap (starRingEnd R) M M₂

/-- The notation `M ≃ₗ⋆[R] M₂` denotes the type of star-linear equivalences between `M` and `M₂`
over the `⋆` endomorphism of the underlying starred ring `R`. -/
notation:50 M " ≃ₗ⋆[" R "] " M₂ => LinearEquiv (starRingEnd R) M M₂
