/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Extension

/-!
# Extensions of Lie algebras

Copy group extension API from GroupTheory.GroupExtension.Defs

We use a type alias for the product, so that we can produce instances depending on the
cocycle. We should add reducible equivalences.

Also, need a `make an abelian Lie algebra` class?

-/

namespace LieAlgebra

variable {R L M N V : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M] (S : Extension R N M)

instance : LieRing S.L := S.instLieRing
instance : LieAlgebra R S.L := S.instLieAlgebra

/-- An extension is central if the image of the left map commutes with the whole Lie algebra. -/
def IsCentral : Prop :=
  LieModule.IsTrivial S.L S.proj.ker

/-- `Extension`s are equivalent iff there is a homomorphism making a commuting diagram. -/
structure Equiv {L' : Type*} [LieRing L'] [LieAlgebra R L'] (S' : Extension R N M) where
  /-- The homomorphism -/
  toLieHom : S.L ≃ₗ⁅R⁆ S'.L
  /-- The left-hand side of the diagram commutes. -/
  incl_comm : toLieHom.comp S.incl = S'.incl
  /-- The right-hand side of the diagram commutes. -/
  proj_comm : S'.proj.comp toLieHom = S.proj

/-- `Splitting` of a Lie extension is a section homomorphism. -/
structure Splitting where
  /-- A section homomorphism -/
  sectionHom : M →ₗ⁅R⁆ S.L
  /-- The section is a left inverse of the projection map. -/
  proj_comp_sectionHom : S.proj.comp sectionHom = LieHom.id

instance : FunLike (Splitting S) M S.L where
  coe s := s.sectionHom
  coe_injective' := by
    intro ⟨_, _⟩ ⟨_, _⟩ h
    congr
    exact DFunLike.coe_injective h

instance : LinearMapClass (Splitting S) R M S.L where
  map_add f := f.sectionHom.map_add'
  map_smulₛₗ f := f.sectionHom.map_smul'

section TwoCocycleTriv

variable [AddCommGroup V] [Module R V] (c : twoCocycleTriv R L V)

lemma isCentral_ofTwoCocycleTriv :
    IsCentral (Extension.ofTwoCocycleTriv c) := by
  dsimp only [IsCentral]
  rw [LieModule.trivial_iff_le_maximal_trivial]
  intro x hx
  simp_all only [LieHom.mem_ker, LieModule.mem_maxTrivSubmodule, Extension.ofTwoCocycleTriv]
  intro y
  simp_all only [IsExtension.extension_L, IsExtension.extension_instLieRing,
    IsExtension.extension_instLieAlgebra, IsExtension.extension_proj, bracket_ofTwoCocycleTriv]
  rw [show x = (x.1, x.2) by rfl, twoCocycleTrivProj] at hx
  simp [show x.1 = 0 by exact hx, Prod.mk_zero_zero]

end TwoCocycleTriv

end LieAlgebra
