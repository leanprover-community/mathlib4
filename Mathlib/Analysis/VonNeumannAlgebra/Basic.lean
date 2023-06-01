/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module analysis.von_neumann_algebra.basic
! leanprover-community/mathlib commit 46b633fd842bef9469441c0209906f6dddd2b4f5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Subalgebra

/-!
# Von Neumann algebras

We give the "abstract" and "concrete" definitions of a von Neumann algebra.
We still have a major project ahead of us to show the equivalence between these definitions!

An abstract von Neumann algebra `wstar_algebra M` is a C^* algebra with a Banach space predual,
per Sakai (1971).

A concrete von Neumann algebra `von_neumann_algebra H` (where `H` is a Hilbert space)
is a *-closed subalgebra of bounded operators on `H` which is equal to its double commutant.

We'll also need to prove the von Neumann double commutant theorem,
that the concrete definition is equivalent to a *-closed subalgebra which is weakly closed.
-/


universe u v

/-- Sakai's definition of a von Neumann algebra as a C^* algebra with a Banach space predual.

So that we can unambiguously talk about these "abstract" von Neumann algebras
in parallel with the "concrete" ones (weakly closed *-subalgebras of B(H)),
we name this definition `wstar_algebra`.

Note that for now we only assert the mere existence of predual, rather than picking one.
This may later prove problematic, and need to be revisited.
Picking one may cause problems with definitional unification of different instances.
One the other hand, not picking one means that the weak-* topology
(which depends on a choice of predual) must be defined using the choice,
and we may be unhappy with the resulting opaqueness of the definition.
-/
class WstarAlgebra (M : Type u) [NormedRing M] [StarRing M] [CstarRing M] [Module ℂ M]
    [NormedAlgebra ℂ M] [StarModule ℂ M] where
  exists_predual :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X) (_ : CompleteSpace X),
      Nonempty (NormedSpace.Dual ℂ X ≃ₗᵢ⋆[ℂ] M)
#align wstar_algebra WstarAlgebra

-- TODO: Without this, `von_neumann_algebra` times out. Why?
/-- The double commutant definition of a von Neumann algebra,
as a *-closed subalgebra of bounded operators on a Hilbert space,
which is equal to its double commutant.

Note that this definition is parameterised by the Hilbert space
on which the algebra faithfully acts, as is standard in the literature.
See `wstar_algebra` for the abstract notion (a C^*-algebra with Banach space predual).

Note this is a bundled structure, parameterised by the Hilbert space `H`,
rather than a typeclass on the type of elements.
Thus we can't say that the bounded operators `H →L[ℂ] H` form a `von_neumann_algebra`
(although we will later construct the instance `wstar_algebra (H →L[ℂ] H)`),
and instead will use `⊤ : von_neumann_algebra H`.
-/
@[nolint has_nonempty_instance]
structure VonNeumannAlgebra (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] extends StarSubalgebra ℂ (H →L[ℂ] H) where
  centralizer_centralizer' : Set.centralizer (Set.centralizer carrier) = carrier
#align von_neumann_algebra VonNeumannAlgebra

/-- Consider a von Neumann algebra acting on a Hilbert space `H` as a *-subalgebra of `H →L[ℂ] H`.
(That is, we forget that it is equal to its double commutant
or equivalently that it is closed in the weak and strong operator topologies.)
-/
add_decl_doc VonNeumannAlgebra.toStarSubalgebra

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance : SetLike (VonNeumannAlgebra H) (H →L[ℂ] H) :=
  ⟨VonNeumannAlgebra.carrier, fun S T h => by cases S <;> cases T <;> congr⟩

instance : StarMemClass (VonNeumannAlgebra H) (H →L[ℂ] H) where star_mem s a := s.star_mem'

instance : SubringClass (VonNeumannAlgebra H) (H →L[ℂ] H) where
  add_mem := add_mem'
  mul_mem := mul_mem'
  one_mem := one_mem'
  zero_mem := zero_mem'
  neg_mem s a ha := show -a ∈ s.toStarSubalgebra from neg_mem ha

@[simp]
theorem mem_carrier {S : VonNeumannAlgebra H} {x : H →L[ℂ] H} :
    x ∈ S.carrier ↔ x ∈ (S : Set (H →L[ℂ] H)) :=
  Iff.rfl
#align von_neumann_algebra.mem_carrier VonNeumannAlgebra.mem_carrier

@[ext]
theorem ext {S T : VonNeumannAlgebra H} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align von_neumann_algebra.ext VonNeumannAlgebra.ext

@[simp]
theorem centralizer_centralizer (S : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S :=
  S.centralizer_centralizer'
#align von_neumann_algebra.centralizer_centralizer VonNeumannAlgebra.centralizer_centralizer

/-- The centralizer of a `von_neumann_algebra`, as a `von_neumann_algebra`.-/
def commutant (S : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  {
    StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H)) fun a (ha : a ∈ S) =>
      (star_mem ha : _) with
    carrier := Set.centralizer (S : Set (H →L[ℂ] H))
    centralizer_centralizer' := by rw [S.centralizer_centralizer] }
#align von_neumann_algebra.commutant VonNeumannAlgebra.commutant

@[simp]
theorem coe_commutant (S : VonNeumannAlgebra H) :
    ↑S.commutant = Set.centralizer (S : Set (H →L[ℂ] H)) :=
  rfl
#align von_neumann_algebra.coe_commutant VonNeumannAlgebra.coe_commutant

@[simp]
theorem mem_commutant_iff {S : VonNeumannAlgebra H} {z : H →L[ℂ] H} :
    z ∈ S.commutant ↔ ∀ g ∈ S, g * z = z * g :=
  Iff.rfl
#align von_neumann_algebra.mem_commutant_iff VonNeumannAlgebra.mem_commutant_iff

@[simp]
theorem commutant_commutant (S : VonNeumannAlgebra H) : S.commutant.commutant = S :=
  SetLike.coe_injective S.centralizer_centralizer'
#align von_neumann_algebra.commutant_commutant VonNeumannAlgebra.commutant_commutant

end VonNeumannAlgebra

