/-
Copyright (c) 2026 Jiaxi Mo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiaxi Mo
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-!
# Hecke Modules

This file defines `HeckeModule` of a representation `ρ` as `Hom_G(k[G ⧸ H], ρ)` and identifies it
with the space of `H`-invariants.

-/

@[expose] public section

namespace Representation

variable {k : Type*} [CommRing k]
variable {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable (H : Subgroup G) (ρ : Representation k G V)

/-- The intertwining space `Hom_G(k[G ⧸ H], ρ)`, which can be viewed as a module over the standard
Hecke algebra `End_G(k[G ⧸ H])ᵒᵖ`. -/
abbrev HeckeModule := (ofMulAction k G (G ⧸ H)).IntertwiningMap ρ

section heckeModule

open MonoidAlgebra

variable (k) {H} in
/-- The basis vector in `k[G ⧸ H]` of a left coset. -/
noncomputable abbrev cosetVector (x : G ⧸ H) : k[G ⧸ H] := .single x 1

@[simp]
lemma cosetVector_mem_eq (h : H) :
    cosetVector k h = cosetVector k ((1 : G) : G ⧸ H) := by
  congr 1
  simp [QuotientGroup.eq]

@[ext]
lemma HeckeModule.ext {H : Subgroup G} (f g : HeckeModule H ρ)
    (h : f (cosetVector k (1 : G)) = g (cosetVector k (1 : G))) : f = g := by
  ext x
  simpa [← IntertwiningMap.isIntertwining] using congrArg (ρ x.out) h

/-- Evaluation at the trivial coset gives a linear equivalence between the `H`-invariants of `ρ` and
the Hecke module `Hom_G(k[G ⧸ H], ρ)`. -/
@[simps! symm_apply]
noncomputable def HeckeModule.invariantsEquiv :
    invariants (ρ.comp H.subtype) ≃ₗ[k] HeckeModule H ρ where
  toLinearMap :=
    { toFun v :=
        ⟨ Finsupp.lift V k (G ⧸ H)
          ( fun x => Quotient.liftOn x (fun x => ρ x v) (fun a b hab => by
              have : ρ (a⁻¹ * b) v = v := by simpa using v.2 ⟨_, QuotientGroup.leftRel_apply.mp hab⟩
              nth_rw 1 [← this]
              simp)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap,
          by
            intro g
            ext z
            simpa using Quotient.inductionOn z (by simp [MulAction.Quotient.smul_mk])⟩
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp}
  invFun f := ⟨f (cosetVector k (1 : G)), by simp [← IntertwiningMap.isIntertwining]⟩
  left_inv _ := by simp
  right_inv _ := by ext; simp

@[simp]
lemma HeckeModule.invariantsEquiv_apply (g : G) (v : invariants (ρ.comp H.subtype)) :
    invariantsEquiv H ρ v (cosetVector k (g : G)) = ρ g v := by
  simp [invariantsEquiv]

end heckeModule

end Representation
