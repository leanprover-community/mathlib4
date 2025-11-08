/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Module.Submodule.Invariant
import Mathlib.RepresentationTheory.Basic

/-!
# Invariant submodules of a group representation

-/

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

namespace Representation

/-- Given a representation `ρ` of a group, `ρ.invtSubmodule` is the sublattice of all
`ρ`-invariant submodules. -/
def invtSubmodule : Sublattice (Submodule k V) :=
  ⨅ g, Module.End.invtSubmodule (ρ g)

lemma mem_invtSubmodule {p : Submodule k V} :
    p ∈ ρ.invtSubmodule ↔ ∀ g, p ∈ Module.End.invtSubmodule (ρ g) := by
  rw [invtSubmodule, Sublattice.mem_iInf]

namespace invtSubmodule

@[simp] protected lemma top_mem : ⊤ ∈ ρ.invtSubmodule := by simp [invtSubmodule]

@[simp] protected lemma bot_mem : ⊥ ∈ ρ.invtSubmodule := by simp [invtSubmodule]

instance : BoundedOrder ρ.invtSubmodule where
  top := ⟨⊤, invtSubmodule.top_mem ρ⟩
  bot := ⟨⊥, invtSubmodule.bot_mem ρ⟩
  le_top := fun ⟨p, hp⟩ ↦ by simp
  bot_le := fun ⟨p, hp⟩ ↦ by simp

@[simp] protected lemma coe_top : (↑(⊤ : ρ.invtSubmodule) : Submodule k V) = ⊤ := rfl

@[simp] protected lemma coe_bot : (↑(⊥ : ρ.invtSubmodule) : Submodule k V) = ⊥ := rfl

protected lemma nontrivial_iff : Nontrivial ρ.invtSubmodule ↔ Nontrivial V := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    infer_instance
  · refine ⟨⊥, ⊤, ?_⟩
    rw [← Subtype.coe_ne_coe, invtSubmodule.coe_top, invtSubmodule.coe_bot]
    exact bot_ne_top

instance [Nontrivial V] : Nontrivial ρ.invtSubmodule :=
  (invtSubmodule.nontrivial_iff ρ).mpr inferInstance

end invtSubmodule

lemma asAlgebraHom_mem_of_forall_mem (p : Submodule k V) (hp : ∀ g, ∀ v ∈ p, ρ g v ∈ p)
    (v : V) (hv : v ∈ p) (x : MonoidAlgebra k G) :
    ρ.asAlgebraHom x v ∈ p := by
  apply x.induction_on <;> aesop

/-- The natural order isomorphism between the two ways to represent invariant submodules. -/
noncomputable def mapSubmodule :
    ρ.invtSubmodule ≃o Submodule (MonoidAlgebra k G) ρ.asModule where
  toFun p :=
    { toAddSubmonoid := (p : Submodule k V).toAddSubmonoid.map ρ.asModuleEquiv.symm
      smul_mem' := by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        refine fun x v hv ↦ ⟨ρ.asModuleEquiv (x • ρ.asModuleEquiv.symm v), ?_, rfl⟩
        simpa using ρ.asAlgebraHom_mem_of_forall_mem p (ρ.mem_invtSubmodule.mp p.property) v hv x }
  invFun q := ⟨(Submodule.orderIsoMapComap ρ.asModuleEquiv.symm).symm (q.restrictScalars k), by
    rw [invtSubmodule, Sublattice.mem_iInf]
    intro g v hv
    simp only [Submodule.orderIsoMapComap_symm_apply, Submodule.mem_comap] at hv ⊢
    convert q.smul_mem (MonoidAlgebra.of k G g) hv using 1
    rw [← asModuleEquiv_symm_map_rho]⟩
  left_inv p := by ext; simp
  right_inv q := by ext; aesop
  map_rel_iff' {p q} :=
    ⟨fun h x hx ↦ by
      suffices ρ.asModuleEquiv.symm x ∈
        (q : Submodule k V).toAddSubmonoid.map ρ.asModuleEquiv.symm by simpa using this
      exact h <| by simpa using hx,
    fun h x hx ↦ by aesop⟩

end Representation
