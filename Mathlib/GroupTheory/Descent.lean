/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Order.Northcott

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Descent Theorem

We provide a proof of the following result.

Let `G` be a group and `f : G →* G` an endomorphism of `G` that maps every
subgroup of `G` into itself (e.g., `f = fun g ↦ g ^ n` when `G` is commutative).

If there is a finite subset `s : Set G` and there exists a "height" function `h : G → ℝ`
and constants `a, b, c : ℝ` such that
* `s` surjects onto the quotient `G ⧸ f(G)`,
* for all `g ∈ s` and `x : G`, `h x ≤ a * h (g * x) + c`,
* for all `x : G`, `h (f x) ≥ b * h x - c`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`, and
* `0 ≤ a < b`,

then `G` is finitely generated. See `Group.fg_of_descent` / `AddGroup.fg_of_descent`.

We use this to deduce a more specific version when `G` is commutative and `f` is the `n`th power
endomorphism and finally an even more specific version with `n = 2`, replacing the upper
and lower bound for the height function by the "approximate parallelogram law"
`∀ x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| ≤ C`.
See `CommGroup.fg_of_descent` / `AddCommGroup.fg_of_descent` and
`CommGroup.fg_of_descent'` / `AddCommGroup.fg_of_descent'`.

This last version is one of the main ingredients of the standard proof of the
**Mordell-Weil Theorem**. It allows to reduce the statement to showing that `G / 2 • G` is finite
(where `G` is the Mordell-Weil group).

We also provide versions that prove that the torsion subgroup is finite under weaker assumptions.

### Implementation note

Replacing `ℝ` by an ordered field (`{R : Type*} [LinearOrder R] [Field R] [IsOrderedRing R]`)
works, but makes the type check quite slow (and `to_additive` needs some  help...).
As the application(s) work with `ℝ`-valued height functions, we think that generalizing
is not really worth the trouble.
-/

public section

open scoped Pointwise

open Subgroup in
/-- If `G` is a group and `f : G →* G` is an endomorphism sending subgroups into themselves,
and if there is a "height function" `h : G → ℝ` with respect to `f` and a finite subset `s`
of `G`, then `G` is finitely generated. -/
@[to_additive /-- If `G` is an additive group and `f : G →+ G` is an endomorphism sending
subgroups into themselves, and if there is a "height function" `h : G → ℝ` with respect
to `f` and a finite subset `s` of `G`, then `G` is finitely generated. -/]
theorem Group.fg_of_descent {G : Type*} [Group G] {f : G →* G} (hf : ∀ U : Subgroup G, U.map f ≤ U)
    {s : Set G} {h : G → ℝ} {a b c : ℝ} (ha : 0 ≤ a) (H₀ : a < b) (hs : s.Finite)
    (H₁ : s * f.range = .univ) (H₂ : ∀ g ∈ s, ∀ x, h x ≤ a * h (g * x) + c)
    (H₃ : ∀ x, b * h x - c ≤ h (f x)) [Northcott h] :
    FG G := by
  set q := QuotientGroup.mk (s := map f ⊤)
  -- Main proof idea: `s` together with elements of sufficiently small "height" `h` generates `G`.
  let S : Set G := s ∪ {x : G | h x ≤ 2 * c / (b - a)}
  let U := closure S
  suffices U = ⊤ from Group.fg_iff.mpr ⟨S, this, hs.union <| Northcott.finite_le _⟩
  by_contra! H -- Assume for contradiction that these elements generate a proper subgroup `U`.
  rw [← SetLike.coe_ne_coe, coe_top, ← Set.nonempty_compl] at H
  -- Then we can find an element `x : G` not in `U` and of minimal height.
  obtain ⟨x, hx₁, hx₂⟩ := Northcott.exists_min_image h Uᶜ H
  -- Now we construct an element `y` of smaller height and not in `U`.
  obtain ⟨g, hg, z, ⟨y, rfl⟩, rfl⟩ := Set.mem_mul.mp <| H₁ ▸ Set.mem_univ x
  have H' : h y < h (g * f y) := by
    suffices a * h (g * f y) + 2 * c < b * h (g * f y) by nlinarith [H₂ g hg (f y), H₃ y]
    suffices 2 * c / (b - a) < h (g * f y) by field_simp [sub_pos.mpr H₀] at this; grind
    suffices g * f y ∉ S by grind
    exact notMem_of_notMem_closure hx₁
  -- To obtain a contradiction, we do cases on whether `y ∈ U`.
  by_cases hy : y ∈ U
  · exact hx₁ <| U.mul_mem (mem_closure_of_mem <| .inl hg) <| hf U <| mem_map_of_mem f hy
  · exact H'.not_ge <| hx₂ y hy

open Subgroup QuotientGroup in
/--
If `G` is a commutative group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / G ^ n` is finite,
* for all `g x : G`, `h x ≤ a * h (g * x) + c g`,
* for all `x : G`, `h (x ^ n) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

where `0 ≤ a < b` and `c₀` are real numbers, `c : G → ℝ`, then `G` is finitely generated.
-/
@[to_additive /-- If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / n • G` is finite,
* for all `g x : G`, `h x ≤ a * h (g + x) + c g`,
* for all `x : G`, `h (n • x) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

where `0 ≤ a < b` and `c₀` are real numbers, `c : G → ℝ`, then `G` is finitely generated. -/]
theorem CommGroup.fg_of_descent {G : Type*} [CommGroup G] {n : ℕ} {h : G → ℝ} {a b c₀ : ℝ}
    {c : G → ℝ} (ha : 0 ≤ a) (H₀ : a < b) (H₁ : (powMonoidHom (α := G) n).range.FiniteIndex)
    (H₂ : ∀ g x, h x ≤ a * h (g * x) + c g) (H₃ : ∀ x, b * h x - c₀ ≤ h (x ^ n)) [Northcott h] :
    Group.FG G := by
  let f : G →* G := powMonoidHom n
  let q := QuotientGroup.mk (s := f.range)
  let qi : G ⧸ f.range → G := Function.surjInv mk_surjective
  let s : Set G := Set.range qi
  obtain ⟨g, hg₁, hg₂⟩ := s.exists_max_image c s.toFinite <| Set.range_nonempty qi
  have H₁' : s * f.range = .univ := by
    refine Set.eq_univ_iff_forall.mpr fun x ↦ Set.mem_mul.mpr ⟨qi (q x), by simp [s], ?_⟩
    conv => enter [1, y]; rw [eq_comm, ← div_eq_iff_eq_mul', SetLike.mem_coe]
    simp only [↓existsAndEq, and_true]
    exact eq_iff_div_mem.mp (Function.surjInv_eq mk_surjective _).symm
  let c' : ℝ := max c₀ (c g)
  have H₃' x : b * h x - c' ≤ h (f x) := by grind [powMonoidHom_apply]
  refine Group.fg_of_descent (fun U u hu ↦ ?_) ha H₀ s.toFinite H₁' (fun g' hg' x ↦ ?_) H₃'
  · obtain ⟨u', hu₁, rfl⟩ := mem_map.mp hu
    exact U.pow_mem hu₁ n
  · grind

/--
If `G` is a commutative group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / G ^ 2` is finite,
* `0 ≤ h x` for all `x : G`,
* there is `C : ℝ` such that for all `x y : G`, `|h (x * y) + h(x / y) - 2 * (h x + h y)| ≤ C`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

then `G` is finitely generated.
-/
@[to_additive /-- If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* `G / 2 • G` is finite,
* `0 ≤ h x` for all `x : G`,
* there is `C : ℝ` such that for all `x y : G`, `|h (x + y) + h(x - y) - 2 * (h x + h y)| ≤ C`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

then `G` is finitely generated. -/]
theorem CommGroup.fg_of_descent' {G : Type*} [CommGroup G] {h : G → ℝ} {C : ℝ}
    (H₁ : (powMonoidHom (α := G) 2).range.FiniteIndex) (H₂ : ∀ x, 0 ≤ h x)
    (H₃ : ∀ x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| ≤ C) [Northcott h] :
    Group.FG G := by
  have H₃' x : 4 * h x - (h 1 + C) ≤ h (x ^ 2) := by grind [pow_two, div_self']
  have H₂' g x : h x ≤ 2 * h (g * x) + (2 * h g⁻¹ + C) := by grind [mul_inv_cancel_comm]
  exact fg_of_descent (b := 4) (by norm_num) (by norm_num) H₁ H₂' H₃'

/--
If `M` is a monoid and `n : ℕ`, `h : M → ℝ` satisfy
* for all `M : G`, `h (x ^ n) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : M` such that `h x ≤ B`,

where `1 < b` and `c₀` are real numbers, then the set of elements of finite order in `M` is finite.
-/
@[to_additive /-- If `M` is an additive monoid and `n : ℕ`, `h : M → ℝ` satisfy
* for all `x : M`, `h (n • x) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : M` such that `h x ≤ B`,

where `1 < b` and `c₀` are real numbers, then the set of elements of finite order in `M`
is finite. -/]
theorem Monoid.finite_set_isOfFiniteOrder_of_descent {M : Type*} [Monoid M] {n : ℕ} {h : M → ℝ}
    {b c₀ : ℝ} (hb : 1 < b) (H : ∀ x, b * h x - c₀ ≤ h (x ^ n)) [Northcott h] :
    Finite { x : M | IsOfFinOrder x } := by
  refine (Northcott.finite_le (h := h) (c₀ / (b - 1))).subset fun t ht ↦ ?_
  have : Finite ↥(Submonoid.powers t) := ht.finite_powers
  let C : ℝ := ⨆ g : Submonoid.powers t, h g
  have hC : ∀ g ∈ Submonoid.powers t, h g ≤ C :=
    fun g hg ↦ Finite.le_ciSup (fun g : Submonoid.powers t ↦ h g) ⟨g, hg⟩
  refine (hC t (Submonoid.mem_powers t)).trans ?_
  obtain ⟨t₀, ht₀⟩ : ∃ g : Submonoid.powers t, h g = C := exists_eq_ciSup_of_finite
  rw [le_div_iff₀' (by grind)]
  grind [Submonoid.pow_mem]

/--
If `G` is a commutative group and `n : ℕ`, `h : G → ℝ` satisfy
* for all `x : G`, `h (x ^ n) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

where `1 < b` and `c₀` are real numbers, then the torsion subgroup of `G` is finite.
-/
@[to_additive /-- If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* for all `x : G`, `h (n • x) ≥ b * h x - c₀`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

where `1 < b` and `c₀` are real numbers, then the torsion subgroup of `G` is finite. -/]
theorem CommGroup.finite_torsion_of_descent {G : Type*} [CommGroup G] {n : ℕ} {h : G → ℝ}
    {b c₀ : ℝ} (hb : 1 < b) (H : ∀ x, b * h x - c₀ ≤ h (x ^ n)) [Northcott h] :
    Finite (torsion G) :=
  Monoid.finite_set_isOfFiniteOrder_of_descent hb H

/--
If `G` is a commutative group and `n : ℕ`, `h : G → ℝ` satisfy
* there is `C : ℝ` such that for all `x y : G`, `|h (x * y) + h(x / y) - 2 * (h x + h y)| ≤ C`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

then the torsion subgroup of `G` is finite.
-/
@[to_additive /-- If `G` is a commutative additive group and `n : ℕ`, `h : G → ℝ` satisfy
* there is `C : ℝ` such that for all `x y : G`, `|h (x + y) + h(x - y) - 2 * (h x + h y)| ≤ C`,
* for all `B : ℝ`, there are only finitely many `x : G` such that `h x ≤ B`,

then the torsion subgroup of `G` is finite. -/]
theorem CommGroup.finite_torsion_of_descent' {G : Type*} [CommGroup G] {h : G → ℝ} {C : ℝ}
    (H : ∀ x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| ≤ C) [Northcott h] :
    Finite (torsion G) := by
  have H' x : 4 * h x - (h 1 + C) ≤ h (x ^ 2) := by grind [pow_two, div_self']
  exact finite_torsion_of_descent (b := 4) (by norm_num) H'

end
