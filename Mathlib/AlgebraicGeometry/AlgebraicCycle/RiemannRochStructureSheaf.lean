/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.RiemannRochViaSubmodule

/-!
# Riemann–Roch from cohomological finiteness of the structure sheaf alone

The weak Riemann–Roch theorem `riemann_roch` assumes finiteness and eventual vanishing of the
cohomology of `𝒪ₓ(D)` for *every* Weil divisor `D`. In this file we reduce those hypotheses to
the structure sheaf alone: because the canonical cokernel `Q_p` of `𝒪ₓ(D - p) ⟶ 𝒪ₓ(D)` is
flasque with `H⁰(Q_p) ≅ κ(p)`, the long exact sequence shows that adding or removing a single
codimension-one point changes cohomology only in degrees `0` and `1`, and by at most
`dim_k κ(p)`. This is the cohomological form of the classical bound
`ℓ(D) ≤ ℓ(D') + deg(D - D')` used in older treatments of Riemann–Roch to control the sizes of
the relevant spaces.

Main results:

* `finite_H_sheaf_of_structureSheaf`: if every `Hⁿ(X, 𝒪ₓ)` is finite dimensional and residue
  fields at codimension-one points are finite over `k`, then every `Hⁿ(X, 𝒪ₓ(D))` is finite
  dimensional (for `D` supported in codimension one);
* `subsingleton_H_sheaf_of_structureSheaf`: if `Hⁿ(X, 𝒪ₓ)` vanishes for `n > N`, then
  `Hⁿ(X, 𝒪ₓ(D))` vanishes for `n > max N 1`;
* `riemann_roch_of_structureSheaf`: **Riemann–Roch** for a curve over `k` assuming only that
  `Hⁿ(X, 𝒪ₓ)` is finite dimensional for all `n` and vanishes for large `n` (together with
  finiteness of the residue fields, which also makes `degree` meaningful).

For `X` proper over `k` the remaining hypotheses are known theorems that are not yet in
Mathlib, and they concern only the single sheaf `𝒪ₓ`:

* finite dimensionality of `Hⁿ(X, 𝒪ₓ)` is the finiteness theorem for coherent cohomology of
  proper schemes (EGA III 3.2.1; for `X` projective this is Serre's finiteness theorem, provable
  by Čech methods against `𝒪_{ℙⁿ}(d)`);
* vanishing for `n > N` follows from Grothendieck's vanishing theorem (`Hⁿ = 0` for
  `n > dim X`, so `N = 1` works for a curve);
* finiteness of `κ(p)/k` at points of codimension one holds because a curve proper over `k` is
  of finite type and its codimension-one points are closed.

TODO: formalize these three inputs; each is independent of the divisor machinery in this
development.
-/

universe u

open AlgebraicGeometry Scheme Order CategoryTheory Limits Opposite TopologicalSpace
open Function.locallyFinsupp Function.locallyFinsuppWithin

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

/-- A module trapped in an exact sequence between two subsingleton modules is subsingleton. -/
lemma subsingleton_of_range_eq_ker {R M N P : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : LinearMap.range f = LinearMap.ker g)
    [Subsingleton M] [Subsingleton P] : Subsingleton N := by
  have key : ∀ y : N, y = 0 := by
    intro y
    have hy : y ∈ LinearMap.ker g := LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
    obtain ⟨x, hx⟩ := h.ge hy
    rw [← hx, Subsingleton.elim x 0, map_zero]
  exact ⟨fun a b => (key a).trans (key b).symm⟩

variable {X : Scheme.{u}} (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))]
    [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X]

/-!
### Transfer of finiteness and vanishing along the long exact sequence

Given a short exact sequence of sheaves of modules, the long exact sequence traps each term of
cohomology between its neighbours. We record the two windows we need: the middle term of the
sequence in each degree, and the first term in each positive degree.
-/

section Transfer

variable (o : ShortComplex X.Modules) (hS : (o.map (Modules.toSheafAb X)).ShortExact)

omit [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X] in
include hS in
/-- In the long exact sequence, `Hⁿ(X₂)` is trapped between `Hⁿ(X₁)` and `Hⁿ(X₃)`. -/
lemma finite_H_middle (n : ℕ) (h1 : Module.Finite k (o.X₁.H n))
    (h3 : Module.Finite k (o.X₃.H n)) : Module.Finite k (o.X₂.H n) := by
  have hex := dAux_exact (CommRingCat.of k) o hS n 0
  haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o n 0) :=
    IsNoetherian.iff_fg.mpr h1
  haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o n 2) :=
    IsNoetherian.iff_fg.mpr h3
  haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o n 1) :=
    isNoetherian_of_range_eq_ker _ _ hex.moduleCat_range_eq_ker
  exact IsNoetherian.iff_fg.mp ‹_›

omit [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X] in
include hS in
/-- In the long exact sequence, `Hⁿ⁺¹(X₁)` is trapped between `Hⁿ(X₃)` and `Hⁿ⁺¹(X₂)`. -/
lemma finite_H_first_succ (n : ℕ) (h3 : Module.Finite k (o.X₃.H n))
    (h2 : Module.Finite k (o.X₂.H (n + 1))) : Module.Finite k (o.X₁.H (n + 1)) := by
  have hex := dAux_exact (CommRingCat.of k) o hS n 2
  haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o n 2) :=
    IsNoetherian.iff_fg.mpr h3
  haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o n 4) :=
    IsNoetherian.iff_fg.mpr h2
  haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o n 3) :=
    isNoetherian_of_range_eq_ker _ _ hex.moduleCat_range_eq_ker
  exact IsNoetherian.iff_fg.mp ‹_›

omit [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X] in
include k hS in
/-- Subsingleton version of `finite_H_middle`. -/
lemma subsingleton_H_middle (n : ℕ) (h1 : Subsingleton (o.X₁.H n))
    (h3 : Subsingleton (o.X₃.H n)) : Subsingleton (o.X₂.H n) := by
  have hex := dAux_exact (CommRingCat.of k) o hS n 0
  haveI : Subsingleton (lesXAux (CommRingCat.of k) o n 0) := h1
  haveI : Subsingleton (lesXAux (CommRingCat.of k) o n 2) := h3
  exact subsingleton_of_range_eq_ker _ _ hex.moduleCat_range_eq_ker

omit [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X] in
include k hS in
/-- Subsingleton version of `finite_H_first_succ`. -/
lemma subsingleton_H_first_succ (n : ℕ) (h3 : Subsingleton (o.X₃.H n))
    (h2 : Subsingleton (o.X₂.H (n + 1))) : Subsingleton (o.X₁.H (n + 1)) := by
  have hex := dAux_exact (CommRingCat.of k) o hS n 2
  haveI : Subsingleton (lesXAux (CommRingCat.of k) o n 2) := h3
  haveI : Subsingleton (lesXAux (CommRingCat.of k) o n 4) := h2
  exact subsingleton_of_range_eq_ker _ _ hex.moduleCat_range_eq_ker

end Transfer

/-!
### Degree-zero cohomology of a smaller divisor

`H⁰` is left exact: the inclusion `𝒪ₓ(D₁) ⟶ 𝒪ₓ(D₂)` for `D₁ ≤ D₂` is injective on global
sections, hence on `H⁰` via `H.equiv₀`. This handles the one degree the long exact sequence
windows above do not reach.
-/

/-- The inclusion of divisorial sheaves is injective on sections. -/
lemma extendLe_app_injective {D₁ D₂ : AlgebraicCycle X ℤ} (hle : D₁ ≤ D₂)
    (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) :
    Function.Injective ((extendLe hle).app U) := by
  intro a b hab
  have h1 := congrArg Subtype.val hab
  exact Subtype.ext h1

omit [IsIntegral X] [IsNoetherian X] [IsRegularInCodimensionOne X] in
/-- A morphism of sheaves of modules which is injective on global sections is injective on
`H⁰`, by naturality of `H.equiv₀`. -/
lemma hMapₗ_zero_injective {F G : X.Modules} (ψ : F ⟶ G)
    (hinj : Function.Injective
      ((((SheafOfModules.toSheaf X.ringCatSheaf).map ψ).hom.app (op ⊤)))) :
    Function.Injective ⇑(HMapₗ (R := CommRingCat.of k) ψ 0) := by
  intro x y hxy
  apply (CategoryTheory.Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj F)
      isTerminalTop).injective
  apply hinj
  rw [CategoryTheory.Sheaf.H.equiv₀_naturality
      (f := (SheafOfModules.toSheaf X.ringCatSheaf).map ψ) (hT := isTerminalTop) x,
    CategoryTheory.Sheaf.H.equiv₀_naturality
      (f := (SheafOfModules.toSheaf X.ringCatSheaf).map ψ) (hT := isTerminalTop) y]
  exact congrArg (CategoryTheory.Sheaf.H.equiv₀ _ isTerminalTop) hxy

/-- `H⁰(𝒪ₓ(D₁))` is finite dimensional whenever `H⁰(𝒪ₓ(D₂))` is, for `D₁ ≤ D₂`. -/
lemma finite_H_zero_of_le {D₁ D₂ : AlgebraicCycle X ℤ} (hle : D₁ ≤ D₂)
    (h : Module.Finite k ((sheaf D₂).H 0)) : Module.Finite k ((sheaf D₁).H 0) := by
  haveI := h
  exact Module.Finite.of_injective (HMapₗ (R := CommRingCat.of k) (extendLeSheaf hle) 0)
    (hMapₗ_zero_injective k (extendLeSheaf hle) fun _ _ hab =>
      extendLe_app_injective hle (op ⊤) hab)

/-!
### Reduction of the Riemann–Roch hypotheses to the structure sheaf
-/

open Classical in
/-- If every `Hⁿ(X, 𝒪ₓ)` is finite dimensional over `k` and the residue fields at
codimension-one points are finite over `k`, then every `Hⁿ(X, 𝒪ₓ(D))` is finite dimensional,
for `D` supported in codimension one. -/
lemma finite_H_sheaf_of_structureSheaf
    (hκ : ∀ q : X, coheight q = 1 → Module.Finite k (X.residueField q))
    (hf₀ : ∀ n, Module.Finite k ((sheaf (0 : AlgebraicCycle X ℤ)).H n))
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    {D : AlgebraicCycle X ℤ} (hD : D.support ⊆ {x | coheight x = 1}) :
    ∀ n, Module.Finite k ((sheaf D).H n) := by
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => exact hf₀
  | add E hE ih p hp =>
    intro n
    have hS := shortExact_map_toSheaf (twistedClosedSubschemeComplex₂_shortExact
      (D := E) (D' := E + single p 1) hE hp (by simp) (hX p hp))
    exact finite_H_middle k _ hS n (ih n)
      (finite_H_residueLineSheaf_of_finite_residueField k hp (E + single p 1) (hκ p hp) n)
  | minus E hE ih p hp =>
    intro n
    have hS := shortExact_map_toSheaf (twistedClosedSubschemeComplex₁_shortExact
      (D := E) (D' := E - single p 1) hE hp (by simp) (hX p hp))
    rcases n with _ | m
    · exact finite_H_zero_of_le k (sub_single_le E) (ih 0)
    · exact finite_H_first_succ k _ hS m
        (finite_H_residueLineSheaf_of_finite_residueField k hp E (hκ p hp) m) (ih (m + 1))

open Classical in
include k in
/-- If `Hⁿ(X, 𝒪ₓ)` vanishes for `n > N`, then `Hⁿ(X, 𝒪ₓ(D))` vanishes for `n > max N 1`,
for `D` supported in codimension one: the canonical cokernels are flasque, so twisting by a
divisor can only change cohomology in degrees `0` and `1`. -/
lemma subsingleton_H_sheaf_of_structureSheaf {N : ℕ}
    (hb₀ : ∀ n, N < n → Subsingleton ((sheaf (0 : AlgebraicCycle X ℤ)).H n))
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    {D : AlgebraicCycle X ℤ} (hD : D.support ⊆ {x | coheight x = 1}) :
    ∀ n, max N 1 < n → Subsingleton ((sheaf D).H n) := by
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => exact fun n hn => hb₀ n (lt_of_le_of_lt (le_max_left N 1) hn)
  | add E hE ih p hp =>
    intro n hn
    have hS := shortExact_map_toSheaf (twistedClosedSubschemeComplex₂_shortExact
      (D := E) (D' := E + single p 1) hE hp (by simp) (hX p hp))
    exact subsingleton_H_middle k _ hS n (ih n hn)
      (subsingleton_H_residueLineSheaf_of_pos hp (E + single p 1)
        (by omega : 0 < n))
  | minus E hE ih p hp =>
    intro n hn
    have hS := shortExact_map_toSheaf (twistedClosedSubschemeComplex₁_shortExact
      (D := E) (D' := E - single p 1) hE hp (by simp) (hX p hp))
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact subsingleton_H_first_succ k _ hS m
      (subsingleton_H_residueLineSheaf_of_pos hp E (by omega : 0 < m)) (ih (m + 1) hn)

open Classical in
/--
**Riemann–Roch from the structure sheaf.** Let `X` be a curve over `k` (integral, Noetherian,
regular in codimension one, of Krull dimension at most one) whose codimension-one residue
fields are finite over `k`. If `Hⁿ(X, 𝒪ₓ)` is finite dimensional for every `n` and vanishes
for `n > N`, then for every Weil divisor `D`,
`χ(𝒪ₓ(D)) = deg D + χ(𝒪ₓ)`.

For `X` proper over `k` the three hypotheses hold by the finiteness theorem for coherent
cohomology (EGA III 3.2.1), Grothendieck vanishing, and finiteness of residue fields at closed
points of schemes of finite type; none of these is yet available in Mathlib.
-/
theorem riemann_roch_of_structureSheaf {N : ℕ}
    (hκ : ∀ q : X, coheight q = 1 → Module.Finite k (X.residueField q))
    (hf₀ : ∀ n, Module.Finite k ((sheaf (0 : AlgebraicCycle X ℤ)).H n))
    (hb₀ : ∀ n, N < n → Subsingleton ((sheaf (0 : AlgebraicCycle X ℤ)).H n))
    {D : AlgebraicCycle X ℤ} (hD : D.support ⊆ {x | coheight x = 1})
    [Order.KrullDimLE 1 X] :
    (sheaf D).eulerChar k =
      D.degree k + (sheaf (0 : AlgebraicCycle X ℤ)).eulerChar k := by
  have hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x := fun x hx y hy =>
    have hmin : IsMin x :=
      Order.KrullDimLE.isMin_of_le_coheight (n := 1) (by simpa using hx.ge)
    ((Scheme.le_iff_specializes.mp (hmin hy)).antisymm (Scheme.le_iff_specializes.mp hy)).eq
  have hf : ∀ E : AlgebraicCycle X ℤ, E.support ⊆ {x | coheight x = 1} →
      ∀ n, Module.Finite k ((sheaf E).H n) :=
    fun E hE => finite_H_sheaf_of_structureSheaf k hκ hf₀ hX hE
  have hb : ∀ E : AlgebraicCycle X ℤ, E.support ⊆ {x | coheight x = 1} →
      ∀ n, max N 1 < n → Subsingleton ((sheaf E).H n) :=
    fun E hE => subsingleton_H_sheaf_of_structureSheaf k hb₀ hX hE
  induction D, hD using Function.locallyFinsupp.inductionOn with
  | zero => simp [degree]
  | add E hE ih p hp =>
    have hE' := support_add_single_subset hE hp
    have step : (sheaf (E + single p 1)).eulerChar k =
        (sheaf E).eulerChar k + Module.finrank k (X.residueField p) :=
      eulerChar_step (N := max N 1) k hp (E + single p 1)
      (twistedClosedSubschemeComplex₂ (D := E) (D' := E + single p 1) hp (by simp))
      (twistedClosedSubschemeComplex₂_shortExact hE hp (by simp) (hX p hp))
      (hf E hE) (hf (E + single p 1) hE')
      (fun n => finite_H_residueLineSheaf_of_finite_residueField k hp (E + single p 1)
        (hκ p hp) n)
      (hb E hE) (hb (E + single p 1) hE') rfl
    simp [step, ih]
    ring
  | minus E hE ih p hp =>
    have hE' := support_sub_single_subset hE hp
    have hkey : (sheaf E).eulerChar k =
        (sheaf (E - single p 1)).eulerChar k + Module.finrank k (X.residueField p) :=
      eulerChar_step (N := max N 1) k hp E
      (twistedClosedSubschemeComplex₁ (D := E) (D' := E - single p 1) hp (by simp))
      (twistedClosedSubschemeComplex₁_shortExact hE hp (by simp) (hX p hp))
      (hf (E - single p 1) hE') (hf E hE)
      (fun n => finite_H_residueLineSheaf_of_finite_residueField k hp E (hκ p hp) n)
      (hb (E - single p 1) hE') (hb E hE) rfl
    have step : (sheaf (E - single p 1)).eulerChar k =
        (sheaf E).eulerChar k - Module.finrank k (X.residueField p) := by lia
    simp [step, ih]
    ring

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
