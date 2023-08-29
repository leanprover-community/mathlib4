/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Subalgebra

#align_import analysis.von_neumann_algebra.basic from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Von Neumann algebras

We give the "abstract" and "concrete" definitions of a von Neumann algebra.
We still have a major project ahead of us to show the equivalence between these definitions!

An abstract von Neumann algebra `WStarAlgebra M` is a C^* algebra with a Banach space predual,
per Sakai (1971).

A concrete von Neumann algebra `VonNeumannAlgebra H` (where `H` is a Hilbert space)
is a *-closed subalgebra of bounded operators on `H` which is equal to its double commutant.

We'll also need to prove the von Neumann double commutant theorem,
that the concrete definition is equivalent to a *-closed subalgebra which is weakly closed.
-/


universe u v

/-- Sakai's definition of a von Neumann algebra as a C^* algebra with a Banach space predual.

So that we can unambiguously talk about these "abstract" von Neumann algebras
in parallel with the "concrete" ones (weakly closed *-subalgebras of B(H)),
we name this definition `WStarAlgebra`.

Note that for now we only assert the mere existence of predual, rather than picking one.
This may later prove problematic, and need to be revisited.
Picking one may cause problems with definitional unification of different instances.
One the other hand, not picking one means that the weak-* topology
(which depends on a choice of predual) must be defined using the choice,
and we may be unhappy with the resulting opaqueness of the definition.
-/
class WStarAlgebra (M : Type u) [NormedRing M] [StarRing M] [CstarRing M] [Module ℂ M]
    [NormedAlgebra ℂ M] [StarModule ℂ M] : Prop where
  /-- There is a Banach space `X` whose dual is isometrically (conjugate-linearly) isomorphic
  to the `WStarAlgebra`. -/
  exists_predual :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℂ X) (_ : CompleteSpace X),
      Nonempty (NormedSpace.Dual ℂ X ≃ₗᵢ⋆[ℂ] M)
#align wstar_algebra WStarAlgebra

-- TODO: Without this, `VonNeumannAlgebra` times out. Why?
/-- The double commutant definition of a von Neumann algebra,
as a *-closed subalgebra of bounded operators on a Hilbert space,
which is equal to its double commutant.

Note that this definition is parameterised by the Hilbert space
on which the algebra faithfully acts, as is standard in the literature.
See `WStarAlgebra` for the abstract notion (a C^*-algebra with Banach space predual).

Note this is a bundled structure, parameterised by the Hilbert space `H`,
rather than a typeclass on the type of elements.
Thus we can't say that the bounded operators `H →L[ℂ] H` form a `VonNeumannAlgebra`
(although we will later construct the instance `WStarAlgebra (H →L[ℂ] H)`),
and instead will use `⊤ : VonNeumannAlgebra H`.
-/
-- porting note: I don't think the nonempty instance linter exists yet
structure VonNeumannAlgebra (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] extends StarSubalgebra ℂ (H →L[ℂ] H) where
  /-- The double commutant (a.k.a. centralizer) of a `VonNeumannAlgebra` is itself. -/
  centralizer_centralizer' : Set.centralizer (Set.centralizer carrier) = carrier
#align von_neumann_algebra VonNeumannAlgebra

/-- Consider a von Neumann algebra acting on a Hilbert space `H` as a *-subalgebra of `H →L[ℂ] H`.
(That is, we forget that it is equal to its double commutant
or equivalently that it is closed in the weak and strong operator topologies.)
-/
add_decl_doc VonNeumannAlgebra.toStarSubalgebra

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance instSetLike : SetLike (VonNeumannAlgebra H) (H →L[ℂ] H) where
  coe S := S.carrier
  coe_injective' S T h := by obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := S; cases T; congr
                             -- ⊢ { toStarSubalgebra := { toSubalgebra := { toSubsemiring := { toSubmonoid :=  …
                                                                          -- ⊢ { toStarSubalgebra := { toSubalgebra := { toSubsemiring := { toSubmonoid :=  …
                                                                                   -- 🎉 no goals

-- porting note: `StarMemClass` should be in `Prop`?
noncomputable instance instStarMemClass : StarMemClass (VonNeumannAlgebra H) (H →L[ℂ] H) where
  star_mem {s} := s.star_mem'

instance instSubringClass : SubringClass (VonNeumannAlgebra H) (H →L[ℂ] H) where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  one_mem {s} := s.one_mem'
  zero_mem {s} := s.zero_mem'
  neg_mem {s} a ha := show -a ∈ s.toStarSubalgebra from neg_mem ha

@[simp]
theorem mem_carrier {S : VonNeumannAlgebra H} {x : H →L[ℂ] H} :
    x ∈ S.toStarSubalgebra ↔ x ∈ (S : Set (H →L[ℂ] H)) :=
  Iff.rfl
#align von_neumann_algebra.mem_carrier VonNeumannAlgebra.mem_carrierₓ
-- porting note: changed the declaration because `simpNF` indicated the LHS simplifies to this.

@[simp]
theorem coe_toStarSubalgebra (S : VonNeumannAlgebra H) :
    (S.toStarSubalgebra : Set (H →L[ℂ] H)) = S :=
  rfl

@[simp]
theorem coe_mk (S : StarSubalgebra ℂ (H →L[ℂ] H)) (h) :
    ((⟨S, h⟩ : VonNeumannAlgebra H) : Set (H →L[ℂ] H)) = S :=
  rfl

@[ext]
theorem ext {S T : VonNeumannAlgebra H} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align von_neumann_algebra.ext VonNeumannAlgebra.ext

@[simp]
theorem centralizer_centralizer (S : VonNeumannAlgebra H) :
    Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S :=
  S.centralizer_centralizer'
#align von_neumann_algebra.centralizer_centralizer VonNeumannAlgebra.centralizer_centralizer

/-- The centralizer of a `VonNeumannAlgebra`, as a `VonNeumannAlgebra`.-/
def commutant (S : VonNeumannAlgebra H) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (S : Set (H →L[ℂ] H))
  centralizer_centralizer' := by simp
                                 -- 🎉 no goals
#align von_neumann_algebra.commutant VonNeumannAlgebra.commutant

@[simp]
theorem coe_commutant (S : VonNeumannAlgebra H) :
    ↑S.commutant = Set.centralizer (S : Set (H →L[ℂ] H)) := by
  simp [commutant]
  -- 🎉 no goals

#align von_neumann_algebra.coe_commutant VonNeumannAlgebra.coe_commutant

@[simp]
theorem mem_commutant_iff {S : VonNeumannAlgebra H} {z : H →L[ℂ] H} :
    z ∈ S.commutant ↔ ∀ g ∈ S, g * z = z * g := by
  rw [←SetLike.mem_coe, coe_commutant]
  -- ⊢ z ∈ Set.centralizer ↑S ↔ ∀ (g : H →L[ℂ] H), g ∈ S → g * z = z * g
  rfl
  -- 🎉 no goals
#align von_neumann_algebra.mem_commutant_iff VonNeumannAlgebra.mem_commutant_iff

@[simp]
theorem commutant_commutant (S : VonNeumannAlgebra H) : S.commutant.commutant = S :=
  SetLike.coe_injective <| by simp
                              -- 🎉 no goals
#align von_neumann_algebra.commutant_commutant VonNeumannAlgebra.commutant_commutant

end VonNeumannAlgebra
