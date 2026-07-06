import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.SkyscraperEulerChar
import Mathlib.AlgebraicGeometry.AlgebraicCycle.ExactSequence
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Degree
import Mathlib.AlgebraicGeometry.AlgebraicCycle.LocallyFinsupp
import Mathlib.AlgebraicGeometry.AlgebraicCycle.KrullDimLE

/-!
# Riemann-Roch for curves assuming cohomological finiteness and vanishing

In this file we prove the following (weak) variant of Riemann-Roch. Let `X` be a scheme over
a field `k` with krull dimension less than or equal to one such that for any Weil divisor `D`,
`𝒪ₓ(D)` has finite cohomology groups which eventually vanish. Then for any Weil divisor `D`,
we have that `χ(𝒪ₓ(D)) = deg(D) + χ(𝒪ₓ)`. It remains to be shown that these cohomological
assumptions are satisfied precisely when `X` is proper over `k`.
-/

namespace AlgebraicGeometry.AlgebraicCycle

open AlgebraicGeometry Order CategoryTheory Limits
open AlgebraicCycle.Sheaf Function.locallyFinsuppWithin

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k]
    (D : AlgebraicCycle X ℤ) [X.Over (Spec (CommRingCat.of k))]
    [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]

lemma eulerChar_step {N : ℕ}
    (hf₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, Module.Finite k (D.sheaf.H n))
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    {p : X} (hp : coheight p = 1) (o : ShortComplex X.Modules) (ho : o.ShortExact)
    (hf : ∀ n, Module.Finite k (o.X₁.H n)) (hf' : ∀ n, Module.Finite k (o.X₂.H n))
    (hb : ∀ n, N < n → Subsingleton (o.X₁.H n)) (hb' : ∀ n, N < n → Subsingleton (o.X₂.H n))
    (hC : o.X₃ = skyscraperSheafOfModules p X.ringCatSheaf (X.residueField p)) :
    o.X₂.eulerChar k = o.X₁.eulerChar k + Module.finrank k (X.residueField p) := by
  have hf₃ : ∀ n, Module.Finite k (o.X₃.H n) :=
    fun n => hC ▸ finite_H_skyscraper k hf₁ hX hp n
  have hb₃ : ∀ n, N < n → Subsingleton (o.X₃.H n) :=
    fun n hn => hC ▸ subsingleton_H_skyscraper_of_pos p (by omega)
  rw [eulerChar_additive k o ho hf hf' hf₃ hb hb' hb₃, hC, eulerChar_skyscraper k p]

open Classical in
/-- Adding a codimension-one point `p` to `E` raises `χ(𝒪ₓ(E))` by `finrank k κ(p)`. -/
lemma eulerChar_add_step {N : ℕ}
    (hf₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, Module.Finite k (D.sheaf.H n))
    (hb₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, N < n → Subsingleton (D.sheaf.H n))
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    (E : AlgebraicCycle X ℤ) (hE : E.support ⊆ {x | coheight x = 1})
    {p : X} (hp : coheight p = 1) :
    (E + single p 1).sheaf.eulerChar k =
      E.sheaf.eulerChar k + Module.finrank k (X.residueField p) := by
  have : IsDiscreteValuationRing (X.presheaf.stalk p) := IsRegularInCodimensionOne.stalk_dvr p hp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p)
  let o := twistedClosedSubschemeComplex₂ p hE ϖ hϖ hp
    (by simp : (E + single p 1) - E = single p 1)
  exact eulerChar_step k hf₁ hX hp o
    (twistedClosedSubschemeComplex₂_shortExact _ _ _ _ _ _ (hX p hp))
    (hf₁ E) (hf₁ (E + single p 1)) (hb₁ E) (hb₁ (E + single p 1)) rfl

open Classical in
/-- Subtracting a codimension-one point `p` from `E` lowers `χ(𝒪ₓ(E))` by `finrank k κ(p)`. -/
lemma eulerChar_sub_step {N : ℕ}
    (hf₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, Module.Finite k (D.sheaf.H n))
    (hb₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, N < n → Subsingleton (D.sheaf.H n))
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    (E : AlgebraicCycle X ℤ) (hE : E.support ⊆ {x | coheight x = 1})
    {p : X} (hp : coheight p = 1) :
    (E - single p 1).sheaf.eulerChar k =
      E.sheaf.eulerChar k - Module.finrank k (X.residueField p) := by
  have : IsDiscreteValuationRing (X.presheaf.stalk p) := IsRegularInCodimensionOne.stalk_dvr p hp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p)
  let o := twistedClosedSubschemeComplex₁ p hE ϖ hϖ hp
    (by simp : E - (E - single p 1) = single p 1)
  have hkey : E.sheaf.eulerChar k =
      (E - single p 1).sheaf.eulerChar k + Module.finrank k (X.residueField p) :=
    eulerChar_step k hf₁ hX hp o
      (twistedClosedSubschemeComplex₁_shortExact _ _ _ _ _ _ (hX p hp))
      (hf₁ (E - single p 1)) (hf₁ E) (hb₁ (E - single p 1)) (hb₁ E) rfl
  lia

/--
**Weak Riemann–Roch** If `X` is a curve (in the sense that
`Order.KrullDimLE 1 X`) over a field `k`, and every `𝒪ₓ(D)` has finite-dimensional cohomology that
vanishes above a fixed degree `N`, then for any Weil divisor `D`,
`χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.
-/
theorem riemann_roch {N : ℕ}
    (hf₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, Module.Finite k (D.sheaf.H n))
    (hb₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, N < n → Subsingleton (D.sheaf.H n))
    (hD : D.support ⊆ {x | coheight x = 1}) [Order.KrullDimLE 1 X] : D.sheaf.eulerChar k =
    D.degree k + (0 : AlgebraicCycle X ℤ).sheaf.eulerChar k := by
  classical
  -- On a curve (`KrullDimLE 1`), codimension-one points are minimal in the specialization
  -- preorder, hence closed: minimality upgrades to equality since schemes are `T0`.
  have hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x := fun x hx y hy =>
    have hmin : IsMin x :=
      Order.KrullDimLE.isMin_of_le_coheight (n := 1) (by simpa using hx.ge)
    ((Scheme.le_iff_specializes.mp (hmin hy)).antisymm (Scheme.le_iff_specializes.mp hy)).eq
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => simp [degree]
  | add E hE ih p hp => simp [eulerChar_add_step k hf₁ hb₁ hX E hE hp, ih]; ring
  | minus E hE ih p hp => simp [eulerChar_sub_step k hf₁ hb₁ hX E hE hp, ih]; ring

end AlgebraicGeometry.AlgebraicCycle
