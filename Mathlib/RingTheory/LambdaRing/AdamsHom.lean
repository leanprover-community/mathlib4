/-
Copyright (c) 2026 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
module

public import Mathlib.RingTheory.LambdaRing.AdamsOperations

/-!
# Homomorphisms of Adams-operations rings (λ-ring homomorphisms)

A homomorphism of λ-rings is a ring homomorphism compatible with the `λⁿ`.
Rationally which is the case of concern throughout, this is equivalent to
an `R`-algebra homomorphism that commutes with every Adams operation `ψⁿ`. -/

/-- A homomorphism of Adams-operations rings: an `R`-algebra homomorphism `A →ₐ[R] B` commuting
with every Adams operation `ψⁿ`, `n ≥ 1`. -/
public structure AdamsHom (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [AdamsOperations R A] [AdamsOperations R B] extends A →ₐ[R] B where
  /-- The defining compatibility with the Adams operations, `n ≥ 1`. -/
  map_psi : ∀ n, 0 < n → toAlgHom.comp (AdamsOperations.ψ (R := R) n)
      = (AdamsOperations.ψ (R := R) n).comp toAlgHom

namespace AdamsHom

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]
  [AdamsOperations R A] [AdamsOperations R B] [AdamsOperations R C]

public instance : FunLike (AdamsHom R A B) A B where
  coe f := f.toAlgHom
  coe_injective := by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    congr 1
    exact DFunLike.coe_injective h

/--
Simplify `f x` which is just using it as an algebra homomorphism
and not needing that it has a proof of preserving `ψ^n` structure.
-/
@[simp] public theorem toAlgHom_apply (f : AdamsHom R A B) (x : A) : f.toAlgHom x = f x := rfl

/-- Extensional Equality of `AdamsHom` -/
@[ext] public theorem ext {f g : AdamsHom R A B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- The identity Adams-ring homomorphism. -/
@[expose] public def id : AdamsHom R A A where
  __ := AlgHom.id R A
  map_psi _ _ := by rw [AlgHom.id_comp, AlgHom.comp_id]

/-- Composition of Adams-ring homomorphisms. -/
@[expose] public def comp (g : AdamsHom R B C) (f : AdamsHom R A B) : AdamsHom R A C where
  __ := g.toAlgHom.comp f.toAlgHom
  map_psi n hn := by
    show (g.toAlgHom.comp f.toAlgHom).comp (AdamsOperations.ψ (R := R) n)
        = (AdamsOperations.ψ (R := R) n).comp (g.toAlgHom.comp f.toAlgHom)
    rw [AlgHom.comp_assoc, f.map_psi n hn, ← AlgHom.comp_assoc, g.map_psi n hn, AlgHom.comp_assoc]

/-- Composing `AdamsHom` and then applying to an `x` also does
not need that each has a proof of preserving `ψ^n` structure.
-/
@[simp] public theorem comp_apply (g : AdamsHom R B C) (f : AdamsHom R A B) (x : A) :
    g.comp f x = g (f x) := rfl

end AdamsHom

/-- Adams operations restrict to any `ψ`-invariant subalgebra.

This requires `[Algebra ℚ R]` because `ψ_prime_congr` on `S` is
built fresh via `isUnit_natCast_of_algebra_rat` rather than
transferred from `A`'s own which requires more structure on the inclusion. -/
@[instance_reducible] public noncomputable def AdamsOperations.restrict {R A : Type*} [CommRing R]
    [Algebra ℚ R] [CommRing A] [Algebra R A] [AdamsOperations R A] (S : Subalgebra R A)
    (hS : ∀ n, ∀ x ∈ S, AdamsOperations.ψ (R := R) n x ∈ S) :
    AdamsOperations R S where
  ψ n := ((AdamsOperations.ψ (R := R) n).comp S.val).codRestrict S
    (fun x => by rw [AlgHom.comp_apply]; exact hS n x.1 x.2)
  ψ_prime_congr p hp _ := (isUnit_natCast_of_algebra_rat (R := R) (A := S) hp.pos.ne').dvd
  ψ_one := by
    ext x
    rw [AlgHom.coe_codRestrict, AlgHom.comp_apply, AdamsOperations.ψ_one]
    rfl
  ψ_mul hm hn := by
    ext x
    rw [AlgHom.coe_codRestrict, AlgHom.comp_apply, AdamsOperations.ψ_mul hm hn]
    rfl

/-- The inclusion of a `ψ`-invariant subalgebra into `A`
as an Adams-ring homomorphism -/
@[expose] public def AdamsHom.ofRestrict
  {R A : Type*} [CommRing R] [Algebra ℚ R]
  [CommRing A] [Algebra R A]
  [AdamsOperations R A] (S : Subalgebra R A)
  (hS : ∀ n, ∀ x ∈ S, AdamsOperations.ψ (R := R) n x ∈ S) :
    letI := AdamsOperations.restrict S hS
    AdamsHom R S A :=
  letI := AdamsOperations.restrict S hS
  { toAlgHom := S.val
    map_psi := fun _ _ => by ext x; rfl }

/-- `SymmFun.act a : Λ →ₐ[R] A` is an Adams-ring homomorphism sending `p₁ ↦ a`. -/
public noncomputable def SymmFun.actAdamsHom {R : Type*} [CommRing R] [Algebra ℚ R]
    {A : Type*} [CommRing A] [Algebra R A] [AdamsOperations R A] (a : A) :
    AdamsHom R (SymmFun R) A where
  __ := SymmFun.act a
  map_psi n hn := AlgHom.ext fun g => SymmFun.act_psi a n hn g
