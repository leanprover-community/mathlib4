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

variable {k : Type*} [CommRing k] {G : Type*} [Group G] (H : Subgroup G)
variable {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- The intertwining space `Hom_G(k[G ⧸ H], ρ)`, which can be viewed as a module over the standard
Hecke algebra `End_G(k[G ⧸ H])ᵒᵖ`. -/
abbrev HeckeModule := (ofMulAction k G (G ⧸ H)).IntertwiningMap ρ

section heckeModule

open MonoidAlgebra

variable (k) {H} in
/-- The basis vector in `k[G ⧸ H]` of a left coset. -/
noncomputable def cosetVector (x : G ⧸ H) : k[G ⧸ H] := single x 1

@[simp]
lemma ofMulAction_apply_cosetVector (g : G) (x : G ⧸ H) :
    ofMulAction k G (G ⧸ H) g (cosetVector k x)  =  cosetVector k (g • x) := by
  simp [cosetVector]

@[simp]
lemma cosetVector_mem (h : H) :
    cosetVector k h = cosetVector k ((1 : G) : G ⧸ H) := by
  congr 1
  simp [QuotientGroup.eq]

@[simp]
lemma coeff_cosetVector (x : G ⧸ H) :
    (cosetVector k x).coeff = Finsupp.single x (1 : k) := rfl

@[ext]
lemma HeckeModule.ext {H : Subgroup G} (f g : HeckeModule H ρ)
    (h : f (cosetVector k (1 : G)) = g (cosetVector k (1 : G))) : f = g := by
  ext x
  simpa [← IntertwiningMap.isIntertwining, cosetVector] using congrArg (ρ x.out) h

/-- Evaluation at the trivial coset gives a linear equivalence between the `H`-invariants of `ρ` and
the Hecke module `Hom_G(k[G ⧸ H], ρ)`. -/
@[simps symm_apply]
noncomputable def HeckeModule.invariantsEquiv :
    invariants (ρ.comp H.subtype) ≃ₗ[k] HeckeModule H ρ :=
  let invariantsMk (v :invariants (ρ.comp H.subtype)) : HeckeModule H ρ :=
    ⟨ Finsupp.linearCombination k (Quotient.lift (fun x => ρ x v) (fun a b hab => by
        nth_rw 1 [← v.2 ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩]
        simp)) ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap,
      fun _ => by ext z; simpa using Quotient.inductionOn z (by simp)⟩
  have invariantsMk_apply (v : invariants (ρ.comp H.subtype)) :
      invariantsMk v (cosetVector k (1 : G)) = v := by
    simp [invariantsMk]
  { toLinearMap :=
    { toFun := invariantsMk
      map_add' _ _ := by ext; simp [invariantsMk_apply]
      map_smul' _ _ := by ext; simp [invariantsMk_apply]}
    invFun f := ⟨f (cosetVector k (1 : G)), by simp [← IntertwiningMap.isIntertwining]⟩
    left_inv _ := Subtype.ext (invariantsMk_apply _)
    right_inv _ := by ext; exact invariantsMk_apply _}

@[simp]
lemma HeckeModule.invariantsEquiv_apply (g : G) (v : invariants (ρ.comp H.subtype)) :
    invariantsEquiv H ρ v (cosetVector k g) = ρ g v := by
  simp [invariantsEquiv]

end heckeModule

end Representation
