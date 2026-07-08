/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperEulerCharViaSubmodule
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Degree
import Mathlib.AlgebraicGeometry.AlgebraicCycle.LocallyFinsupp
import Mathlib.AlgebraicGeometry.AlgebraicCycle.KrullDimLE

/-!
# Riemann–Roch for curves assuming cohomological finiteness and vanishing

In this file we prove the following (weak) variant of Riemann–Roch for the
submodule-based divisorial sheaves of `SheafViaSubmodule`. Let `X` be a scheme over a field
`k` with Krull dimension at most one such that for any Weil divisor `D`, `𝒪ₓ(D)` has finite
cohomology groups which eventually vanish. Then for any Weil divisor `D`, we have
`χ(𝒪ₓ(D)) = deg(D) + χ(𝒪ₓ)`. It remains to be shown that these cohomological assumptions are
satisfied precisely when `X` is proper over `k`.

The induction on `D` adds and removes codimension-one points one at a time; each step is the
additivity of `χ` on the short exact sequence `0 ⟶ 𝒪ₓ(D - p) ⟶ 𝒪ₓ(D) ⟶ Q_p(D) ⟶ 0` of
`ExactSequenceViaSubmodule` together with `χ(Q_p(D)) = dim_k κ(p)` from
`SkyscraperEulerCharViaSubmodule`. In contrast to the presentation via a uniformizer-dependent
skyscraper map, no choice of uniformizer appears anywhere in this file: the third term of the
sequence is the canonical cokernel, and its Euler characteristic is computed once and for all
behind the isomorphism-invariance of `χ`.
-/

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

open AlgebraicGeometry Order CategoryTheory Limits
open Function.locallyFinsuppWithin

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k]
    (D : AlgebraicCycle X ℤ) [X.Over (Spec (CommRingCat.of k))]
    [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]

/-- Additivity of `χ` on a short exact sequence whose third term is the canonical cokernel
`Q_p(E)`: the middle Euler characteristic exceeds the first by `dim_k κ(p)`. -/
lemma eulerChar_step {N : ℕ}
    {p : X} (hp : coheight p = 1)
    (E : AlgebraicCycle X ℤ) (o : ShortComplex X.Modules) (ho : o.ShortExact)
    (hf : ∀ n, Module.Finite k (o.X₁.H n)) (hf' : ∀ n, Module.Finite k (o.X₂.H n))
    (hf₃ : ∀ n, Module.Finite k ((residueLineSheaf hp E).H n))
    (hb : ∀ n, N < n → Subsingleton (o.X₁.H n)) (hb' : ∀ n, N < n → Subsingleton (o.X₂.H n))
    (hC : o.X₃ = residueLineSheaf hp E) :
    o.X₂.eulerChar k = o.X₁.eulerChar k + Module.finrank k (X.residueField p) := by
  have hf₃' : ∀ n, Module.Finite k (o.X₃.H n) := fun n => hC ▸ hf₃ n
  have hb₃ : ∀ n, N < n → Subsingleton (o.X₃.H n) :=
    fun n hn => hC ▸ subsingleton_H_residueLineSheaf_of_pos hp E (by omega)
  rw [eulerChar_additive k o ho hf hf' hf₃' hb hb' hb₃, hC, eulerChar_residueLineSheaf k hp E]

open Classical in
/-- Adding a codimension-one point `p` to `E` raises `χ(𝒪ₓ(E))` by `finrank k κ(p)`. -/
lemma eulerChar_add_step {N : ℕ}
    (hf₁ : ∀ (E : AlgebraicCycle X ℤ) (n : ℕ), Module.Finite k ((sheaf E).H n))
    (hb₁ : ∀ (E : AlgebraicCycle X ℤ) (n : ℕ), N < n → Subsingleton ((sheaf E).H n))
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    (E : AlgebraicCycle X ℤ) (hE : E.support ⊆ {x | coheight x = 1})
    {p : X} (hp : coheight p = 1) :
    (sheaf (E + single p 1)).eulerChar k =
      (sheaf E).eulerChar k + Module.finrank k (X.residueField p) :=
  eulerChar_step k hp (E + single p 1)
    (twistedClosedSubschemeComplex₂ (D := E) (D' := E + single p 1) hp (by simp))
    (twistedClosedSubschemeComplex₂_shortExact hE hp (by simp) (hX p hp))
    (hf₁ E) (hf₁ (E + single p 1))
    (fun n => finite_H_residueLineSheaf k hp (E + single p 1) hf₁ (hX p hp) n)
    (hb₁ E) (hb₁ (E + single p 1)) rfl

open Classical in
/-- Subtracting a codimension-one point `p` from `E` lowers `χ(𝒪ₓ(E))` by `finrank k κ(p)`. -/
lemma eulerChar_sub_step {N : ℕ}
    (hf₁ : ∀ (E : AlgebraicCycle X ℤ) (n : ℕ), Module.Finite k ((sheaf E).H n))
    (hb₁ : ∀ (E : AlgebraicCycle X ℤ) (n : ℕ), N < n → Subsingleton ((sheaf E).H n))
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    (E : AlgebraicCycle X ℤ) (hE : E.support ⊆ {x | coheight x = 1})
    {p : X} (hp : coheight p = 1) :
    (sheaf (E - single p 1)).eulerChar k =
      (sheaf E).eulerChar k - Module.finrank k (X.residueField p) := by
  have hkey : (sheaf E).eulerChar k =
      (sheaf (E - single p 1)).eulerChar k + Module.finrank k (X.residueField p) :=
    eulerChar_step k hp E
      (twistedClosedSubschemeComplex₁ (D := E) (D' := E - single p 1) hp (by simp))
      (twistedClosedSubschemeComplex₁_shortExact hE hp (by simp) (hX p hp))
      (hf₁ (E - single p 1)) (hf₁ E)
      (fun n => finite_H_residueLineSheaf k hp E hf₁ (hX p hp) n)
      (hb₁ (E - single p 1)) (hb₁ E) rfl
  lia

/--
**Weak Riemann–Roch.** If `X` is a curve (in the sense that `Order.KrullDimLE 1 X`) over a
field `k`, and every `𝒪ₓ(D)` has finite-dimensional cohomology that vanishes above a fixed
degree `N`, then for any Weil divisor `D`, `χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.
-/
theorem riemann_roch {N : ℕ}
    (hf₁ : ∀ (E : AlgebraicCycle X ℤ) (n : ℕ), Module.Finite k ((sheaf E).H n))
    (hb₁ : ∀ (E : AlgebraicCycle X ℤ) (n : ℕ), N < n → Subsingleton ((sheaf E).H n))
    (hD : D.support ⊆ {x | coheight x = 1}) [Order.KrullDimLE 1 X] :
    (sheaf D).eulerChar k =
      D.degree k + (sheaf (0 : AlgebraicCycle X ℤ)).eulerChar k := by
  classical
  have hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x := fun x hx y hy =>
    have hmin : IsMin x :=
      Order.KrullDimLE.isMin_of_le_coheight (n := 1) (by simpa using hx.ge)
    ((Scheme.le_iff_specializes.mp (hmin hy)).antisymm (Scheme.le_iff_specializes.mp hy)).eq
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => simp [degree]
  | add E hE ih p hp => simp [eulerChar_add_step k hf₁ hb₁ hX E hE hp, ih]; ring
  | minus E hE ih p hp => simp [eulerChar_sub_step k hf₁ hb₁ hX E hE hp, ih]; ring

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
