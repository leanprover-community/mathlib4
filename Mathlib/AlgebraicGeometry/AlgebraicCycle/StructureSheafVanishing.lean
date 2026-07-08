/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.RiemannRochStructureSheaf

/-!
# Vanishing of the higher cohomology of the structure sheaf, given a flasque resolution

This file proves that if the divisorial structure sheaf `𝒪ₓ = 𝒪ₓ(0)` admits a two-step flasque
resolution `0 ⟶ 𝒪ₓ ⟶ 𝒦 ⟶ Q ⟶ 0` (a short exact sequence of sheaves of modules whose second
and third terms are flasque), then `Hⁿ(X, 𝒪ₓ)` vanishes for `n ≥ 2` — that is, the vanishing
hypothesis `hb₀` of `riemann_roch_of_structureSheaf` holds with `N = 1`.

## The intended resolution (TODO)

On an integral curve the classical resolution takes `𝒦` to be the constant sheaf of rational
functions and `Q = 𝒦/𝒪ₓ` the sheaf of principal parts. In this development:

* `𝒦 := functionFieldSheaf X` (`SheafViaSubmodule`), the skyscraper at the generic point
  valued in `k(X)`. It is **already known to be flasque**: the instance
  `TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf _).obj (skyscraperSheafOfModules p R M))`
  from `SkyscraperTopos` applies at `p := genericPoint X`.
* `𝒪ₓ ⟶ 𝒦` is the submodule inclusion `(divisorSubmodule 0).ι` (a monomorphism with the
  correct kernel by construction).
* `Q` should be constructed as the sheaf of **principal parts**: sections over `U` are
  finitely-supported families `(f_p)_{p ∈ U, coheight p = 1}` with `f_p ∈ L_p := k(X)/𝒪ₚ(0)`
  (the quotient of the function field by the nonnegative-order submodule `ordSubmodule hp 0`
  of `ExactSequenceViaSubmodule`). Since `X` is Noetherian, opens are quasi-compact and local
  finiteness of supports is just finiteness, so the presheaf is a sheaf; restriction maps are
  literal restrictions of families, hence surjective — `Q` is flasque by extension by zero.
  The map `𝒦 ⟶ Q` sends a rational function to its family of classes; it is stalkwise
  surjective (at `p` the component map `k(X) → k(X)/𝒪ₚ` is already surjective), and its
  kernel is exactly `𝒪ₓ(0)` because membership in `𝒪ₓ(0)(U)` is by definition the pointwise
  order condition `0 ≤ ord f p` for all codimension-one `p ∈ U`.

Constructing `Q` and the short exact sequence is the remaining work for the vanishing input;
the finiteness input `hf₀` additionally requires properness (classically via a finite map to
`ℙ¹` or the adèlic argument) and is a separate project.
-/

universe u

open AlgebraicGeometry Scheme Order CategoryTheory Opposite

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

variable {X : Scheme.{u}} (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))]
    [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]

include k in
/--
If the structure sheaf admits a two-step flasque resolution `0 ⟶ 𝒪ₓ ⟶ 𝒦 ⟶ Q ⟶ 0`, then its
cohomology vanishes in degrees `n ≥ 2`: in the long exact sequence, `Hⁿ(𝒪ₓ)` is trapped
between `Hⁿ⁻¹(Q)` and `Hⁿ(𝒦)`, both of which vanish by flasqueness. Together with
`subsingleton_H_sheaf_of_structureSheaf` this gives the vanishing hypothesis of
`riemann_roch_of_structureSheaf` with `N = 1`.
-/
lemma subsingleton_H_structureSheaf_of_flasque_ses
    (o : ShortComplex X.Modules) (hS : (o.map (Modules.toSheafAb X)).ShortExact)
    (h1 : o.X₁ = sheaf (0 : AlgebraicCycle X ℤ))
    (h2 : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj o.X₂))
    (h3 : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj o.X₃))
    {n : ℕ} (hn : 1 < n) :
    Subsingleton ((sheaf (0 : AlgebraicCycle X ℤ)).H n) := by
  rw [← h1]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  haveI := h2
  haveI := h3
  exact subsingleton_H_first_succ k o hS (m + 1)
    (inferInstanceAs
      (Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj o.X₃).H (m + 1))))
    (inferInstanceAs
      (Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj o.X₂).H (m + 2))))

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
