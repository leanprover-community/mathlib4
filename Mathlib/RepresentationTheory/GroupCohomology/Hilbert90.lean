/-
Copyright (c) 2023 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.FieldTheory.Galois
import Mathlib.RepresentationTheory.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.LinearIndependent

/-!
# Hilbert's Theorem 90

Let `L/K` be a finite extension of fields. Then this file proves Noether's generalization of
Hilbert's Theorem 90: that the 1st group cohomology $H^1(Aut_K(L), Lˣ)$ is trivial. We state it
both in terms of $H^1$ and in terms of cocycles being coboundaries.

Hilbert's original statement was that if $L/K$ is Galois, and $Gal(L/K)$ is cyclic, generated
by an element `σ`, then for every `x : L` such that $N_{L/K}(x) = 1,$ there exists `y : L` such
that $x = y/σ(y).$ This can be deduced from the fact that the function $Gal(L/K) → L^\times$
sending $σ^i \mapsto xσ(x)σ^2(x)...σ^{i-1}(x)$ is a 1-cocycle. Alternatively, we can derive it by
analyzing the cohomology of finite cyclic groups in general.

Noether's generalization also holds for infinite Galois extensions.

## Main statements

* `hilbert90`: for all $f: Aut_K(L) \to L^\times$ satisfying the 1-cocycle condition, there exists
`β : Lˣ` such that $f(g)g(β) = β$ for all `g : Aut_K(L)`.
* `groupCohomology.hilbert90`: $H^1(Aut_K(L), L^\times)$ is trivial.

## Implementation notes

Given a commutative ring `k` and a group `G`, group cohomology is developed in terms of `k`-linear
`G`-representations on `k`-modules. Thus stating Noether's generalization of Hilbert 90 in terms
of `H¹` requires us to turn the natural action of `Aut_K(L)` on `Lˣ` into a morphism
`Aut_K(L) →* (Additive Lˣ →ₗ[ℤ] Additive Lˣ)`. Thus we provide the non-`H¹` version too, as its
statement is clearer.

## TODO

* The original Hilbert's Theorem 90, deduced from the cohomology of general finite cyclic groups.
* Develop Galois cohomology to extend Noether's result to infinite Galois extensions.
* "Additive Hilbert 90": let `L/K` be a finite Galois extension. Then $H^n(Gal(L/K), L)$ is trivial
for all $1 ≤ n.$

-/

open BigOperators
namespace Hilbert90

variable (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Given `f : Aut_K(L) → Lˣ`, the sum `∑ f(φ) • φ` for `φ ∈ Aut_K(L)`, as a function `L → L`. -/
noncomputable def aux (f : (L ≃ₐ[K] L) → Lˣ) : L → L :=
  Finsupp.total (L ≃ₐ[K] L) (L → L) L (fun φ => φ)
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))

theorem aux_ne_zero (f : (L ≃ₐ[K] L) → Lˣ) : aux K L f ≠ 0 :=
/- the set `Aut_K(L)` is linearly independent in the `L`-vector space `L → L`, by Dedekind's
linear independence of characters -/
  have : LinearIndependent L (fun (f : L ≃ₐ[K] L) => (f : L → L)) :=
    LinearIndependent.comp (ι' := L ≃ₐ[K] L)
      (linearIndependent_monoidHom L L) (fun f => f)
      (fun x y h => by ext; exact DFunLike.ext_iff.1 h _)
  have h := linearIndependent_iff.1 this
    (Finsupp.equivFunOnFinite.symm (fun φ => (f φ : L)))
  fun H => Units.ne_zero (f 1) (DFunLike.ext_iff.1 (h H) 1)

end Hilbert90
section
open Hilbert90
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem hilbert90 (f : (L ≃ₐ[K] L) → Lˣ)
    (hf : ∀ (g h : (L ≃ₐ[K] L)), f (g * h) = g (f h) * f g) :
    ∃ β : Lˣ, ∀ g : (L ≃ₐ[K] L), f g * Units.map g β = β := by
/- Let `z : L` be such that `∑ f(h) * h(z) ≠ 0`, for `h ∈ Aut_K(L)` -/
  obtain ⟨z, hz⟩ : ∃ z, aux K L f z ≠ 0 :=
    not_forall.1 (fun H => aux_ne_zero K L f <| funext fun x => H x)
  have : aux K L f z = ∑ h, f h * h z := by simp [aux, Finsupp.total, Finsupp.sum_fintype]
/- Let `β = ∑ f(h) * h(z).` -/
  use Units.mk0 (aux K L f z) hz
  intro g
/- Then the equality follows from the hypothesis `hf` (that `f` is a 1-cocycle). -/
  simp_rw [Units.ext_iff, this, Units.val_mul, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe,
    map_sum, map_mul, Finset.mul_sum, ← mul_assoc, mul_comm (f _ : L), ← hf, mul_comm (f _ : L)]
  exact Fintype.sum_bijective (fun i => g * i) (Group.mulLeft_bijective g) _ _ (fun i => rfl)

end
namespace groupCohomology
variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Given a finite extension of fields `L/K`, the first group cohomology `H¹(Aut_K(L), Lˣ)` is
trivial. -/
noncomputable instance hilbert90 : Unique (H1 (Rep.ofAlgebraAutOnUnits K L)) where
  default := 0
  uniq := fun a => Quotient.inductionOn' a fun x => (Submodule.Quotient.mk_eq_zero _).2 <| by
    rcases _root_.hilbert90 (Additive.toMul ∘ x.1) (fun g h => Units.ext_iff.1
      ((mem_oneCocycles_iff x.1).1 x.2 g h)) with ⟨β, hβ⟩
    use Additive.ofMul (β⁻¹ : Lˣ)
    ext g
    refine' Additive.toMul.bijective.1 _
    show Units.map g β⁻¹ / β⁻¹ = Additive.toMul (x.1 g)
    rw [map_inv, div_inv_eq_mul, mul_comm]
    apply mul_inv_eq_iff_eq_mul.2 (hβ g).symm

end groupCohomology
