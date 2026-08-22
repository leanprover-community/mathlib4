/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# ...

-/

@[expose] public section

universe u

namespace groupCohomology

open CategoryTheory Representation Rep Limits

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep.{u} k H} {B : Rep.{u} k G} (f : G →* H) (φ : res f A ⟶ B)

lemma map_eq_zero (n : ℕ) [NeZero n] (hf : f = 1) : map f φ n = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  let a : G →* PUnit.{u + 1} := 1
  let b : PUnit.{u + 1} →* H := 1
  let C := Rep.trivial k PUnit.{u + 1} B.ρ.invariants
  let β : res a C ⟶ B :=
    Rep.ofHom
      { toLinearMap := B.ρ.invariants.subtype
        isIntertwining' g := by ext x; exact (x.property g).symm }
  let α : res b A ⟶ Rep.trivial k PUnit.{u + 1} C :=
    Rep.ofHom
      { toLinearMap :=
          LinearMap.codRestrict B.ρ.invariants φ.hom.toLinearMap (fun a g ↦ by
            simpa [hf] using ((φ.hom.isIntertwining) g a).symm)
        isIntertwining' g := by aesop }
  obtain rfl : f = b.comp a := by aesop
  rw [show φ = (resFunctor a).map α ≫ β from rfl]
  have : map a β (n + 1) = 0 :=
    (isZero_groupCohomology_succ_of_subsingleton _ _).eq_of_src ..
  rw [map_comp, this, comp_zero]

end groupCohomology
