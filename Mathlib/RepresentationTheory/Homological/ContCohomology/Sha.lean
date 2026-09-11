/-
Copyright (c) 2026 Edison Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie, David Kurniadi Angdinata
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# The Tate–Shafarevich group of a Galois module

This file defines a general notion of a *Tate–Shafarevich group* of a Galois module (i.e. an abelian
group `A` equipped with a continuous action of the absolute Galois group `G_K` of a field `K`), as
the intersection of the kernels of the maps `Hⁿ(K, A) → Hⁿ(Kᵥ, A)`, induced by the map `G_Kᵥ → G_K`,
where `Kᵥ` is a field extension of `K` for each `v` in an arbitrary indexing set `V`.

## Main definitions

* `ContinuousCohomology.tateShafarevich`: the Tate–Shafarevich group of a Galois module.

## TODOs

* Add a notation for `ContinuousCohomology.tateShafarevich`.
* Prove that `ContinuousCohomology.tateShafarevich` of a discrete Galois module is torsion.
* Define the classical Tate–Shafarevich group in `Mathlib/AlgebraicGeometry/EllipticCurve`.

## Implementation notes

The generality of this definition will be useful to define the Tate–Shafarevich groups occurring in
Poitou–Tate duality. When `K` is a global field, `V` is the set of places of `K`, `A` is the group
of rational points of an abelian variety over the separable closure `Kˢ` of `K`, and `n = 1`, this
recovers the classical definition of the Tate–Shafarevich group of an abelian variety, since
`Hⁿ(Kᵥ, A(Kˢ)) ≅ Hⁿ(Kᵥ, A(Kᵥˢ))` by the Greenberg approximation theorem.

## References

* [Milne, *Arithmetic Duality Theorems*](https://www.jmilne.org/math/Books/ADTnot.pdf)
* [Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*](https://link.springer.com/book/10.1007/978-3-540-37889-1)
-/

@[expose] public section

universe u v

variable {K : Type u} {V : Type v} [Field K] (f : V → Type u) [∀ v, Field (f v)]
  [∀ v, Algebra K (f v)] (A : TopRep ℤ (Field.absoluteGaloisGroup K)) (n : ℕ)

open CategoryTheory

namespace ContinuousCohomology

/-- The Tate–Shafarevich group of a Galois module. -/
@[simps!]
noncomputable def tateShafarevich : AddSubgroup (continuousCohomology n A) :=
  ⨅ v, (map (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker

lemma tateShafarevich_eq_iInf : tateShafarevich f A n =
    ⨅ v : V, (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom.ker := rfl

lemma tateShafarevich_eq_ker_pi : tateShafarevich f A n =
    (AddMonoidHom.pi fun v : V ↦ (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom.toAddMonoidHom).ker := by
  ext; simp [tateShafarevich_eq_iInf, funext_iff]

@[simp]
lemma mem_tateShafarevich (x : continuousCohomology n A) : x ∈ tateShafarevich f A n ↔
    ∀ v : V, (ContinuousCohomology.map
      (Field.absoluteGaloisGroup.map (algebraMap K (f v))) (𝟙 _) n).hom x = 0 := by
  simp [tateShafarevich_eq_iInf]

end ContinuousCohomology
