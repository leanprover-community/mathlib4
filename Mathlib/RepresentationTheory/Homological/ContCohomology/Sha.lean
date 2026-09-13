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

Mathematicians seem to use "Tate–Shafarevich group" in at least two distinct contexts. They have in
common the set-up that `K` is a global field, `A` is a discrete `G_K`-module, `V` is the set of
places of `K`, and `Kᵥ` is the completion of `K` at a place `v` in `V`.

The first context is when `A` is finite. This is used, for example, in the statement of global
Poitou-Tate duality. In this theorem, the Tate–Shafarevich group is defined exactly as in this file.
It agrees with Definition 8.6.2 of [Neukirch–Schmidt–Wingberg].

The second context is when `A` is the `Kˢ`-valued points of a group scheme `A` such as an abelian
variety. Then the Tate–Shafarevich group is usually defined as the intersection of the kernels of
the maps `H¹(K, A(Kˢ)) → H¹(Kᵥ, A(Kᵥˢ))`. Note that in particular the module changes as well as the
group, so technically this is not quite what is happening in this definition. However the inclusion
`H¹(Kᵥ, A(Kᵥˢ)) → H¹(Kᵥ, A(Kˢ))` is an isomorphism by the Greenberg approximation theorem, so the
definition in this file is still mathematically correct. See Remark I.3.10 of [Milne].

This definition is different but related to the "Tate–Shafarevich group" in the context of `p`-adic
representations, where `A` is the quotient of a `p`-adic `G_K`-module by a `G_K`-invariant lattice.
See Section 1 of [Flach]. For instance, when `A` is the quotient of the `p`-adic rational Tate
module of an abelian variety by its integral sublattice, its associated Tate–Shafarevich group will
be a quotient of the one in this file by its divisible part, which will be finite by definition.

## References

* [Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*](https://link.springer.com/book/10.1007/978-3-540-37889-1)
* [Milne, *Arithmetic Duality Theorems*](https://www.jmilne.org/math/Books/ADTnot.pdf)
* [Flach, *A finiteness theorem for the symmetric square of an elliptic curve*](https://link.springer.com/article/10.1007/BF01232029)
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
