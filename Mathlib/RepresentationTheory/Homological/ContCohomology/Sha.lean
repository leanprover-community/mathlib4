/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, David Kurniadi Angdinata
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# The Tate-Shafarevich group of a continuous representation

This file defines a general notion of a Tate--Shafarevich group for a continuous representation `A`
over a field `K`, as the intersection of the kernels of the maps `Hⁿ(K, A) → Hⁿ(Kᵥ, Aᵥ)`.

Here `Kᵥ` is a `K`-algebra for each place `v` in an arbitrary indexing set `V`,
which induces maps between absolute Galois groups and hence maps between cohomology groups.

When `V` is the set of places of a global field `K`, `A` is the set of rational points of an abelian
variety over K, and `n = 1`, this recovers the classical definition of the Tate-Shafarevich group.

## Reference

* [Wikipedia, *Tate–Shafarevich group*](https://en.wikipedia.org/wiki/Tate%E2%80%93Shafarevich_group)

-/

@[expose] public section

universe u v

variable {K : Type u} {V : Type v} [Field K] (f : V → Type u) [∀ v, Field (f v)]
  [∀ v, Algebra K (f v)] (A : TopRep ℤ (Field.absoluteGaloisGroup K)) (n : ℕ)

open CategoryTheory

namespace ContinuousCohomology

/-- The Tate-Shafarevich group of a continuous representation. -/
@[simps!]
noncomputable def tateSha : AddSubgroup (continuousCohomology n A) :=
  ⨅ v, (map (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker

lemma tateSha_eq_iInf :
    tateSha f A n = ⨅ v : V, (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker := rfl

lemma tateSha_eq_ker_pi :
    tateSha f A n = (AddMonoidHom.pi fun v : V ↦ (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom).ker := by
  ext; simp [tateSha_eq_iInf, funext_iff]

@[simp]
lemma mem_tateSha (x : continuousCohomology n A) : x ∈ tateSha f A n ↔
    ∀ v : V, x ∈ (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.ker := by
  simp [tateSha_eq_iInf]

end ContinuousCohomology
