/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

#align_import linear_algebra.clifford_algebra.grading from "leanprover-community/mathlib"@"34020e531ebc4e8aac6d449d9eecbcd1508ea8d0"

/-!
# Results about the grading structure of the clifford algebra

The main result is `CliffordAlgebra.gradedAlgebra`, which says that the clifford algebra is a
ℤ₂-graded algebra (or "superalgebra").
-/


namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

open scoped DirectSum

variable (Q)

/-- The even or odd submodule, defined as the supremum of the even or odd powers of
`(ι Q).range`. `evenOdd 0` is the even submodule, and `evenOdd 1` is the odd submodule. -/
def evenOdd (i : ZMod 2) : Submodule R (CliffordAlgebra Q) :=
  ⨆ j : { n : ℕ // ↑n = i }, LinearMap.range (ι Q) ^ (j : ℕ)
#align clifford_algebra.even_odd CliffordAlgebra.evenOdd

theorem one_le_evenOdd_zero : 1 ≤ evenOdd Q 0 := by
  refine' le_trans _ (le_iSup _ ⟨0, Nat.cast_zero⟩)
  exact (pow_zero _).ge
#align clifford_algebra.one_le_even_odd_zero CliffordAlgebra.one_le_evenOdd_zero

theorem range_ι_le_evenOdd_one : LinearMap.range (ι Q) ≤ evenOdd Q 1 := by
  refine' le_trans _ (le_iSup _ ⟨1, Nat.cast_one⟩)
  exact (pow_one _).ge
#align clifford_algebra.range_ι_le_even_odd_one CliffordAlgebra.range_ι_le_evenOdd_one

theorem ι_mem_evenOdd_one (m : M) : ι Q m ∈ evenOdd Q 1 :=
  range_ι_le_evenOdd_one Q <| LinearMap.mem_range_self _ m
#align clifford_algebra.ι_mem_even_odd_one CliffordAlgebra.ι_mem_evenOdd_one

theorem ι_mul_ι_mem_evenOdd_zero (m₁ m₂ : M) : ι Q m₁ * ι Q m₂ ∈ evenOdd Q 0 :=
  Submodule.mem_iSup_of_mem ⟨2, rfl⟩
    (by
      rw [Subtype.coe_mk, pow_two]
      exact
        Submodule.mul_mem_mul (LinearMap.mem_range_self (ι Q) m₁)
          (LinearMap.mem_range_self (ι Q) m₂))
#align clifford_algebra.ι_mul_ι_mem_even_odd_zero CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero

theorem evenOdd_mul_le (i j : ZMod 2) : evenOdd Q i * evenOdd Q j ≤ evenOdd Q (i + j) := by
  simp_rw [evenOdd, Submodule.iSup_eq_span, Submodule.span_mul_span]
  apply Submodule.span_mono
  intro z hz
  obtain ⟨x, y, hx, hy, rfl⟩ := hz
  obtain ⟨xi, hx'⟩ := Set.mem_iUnion.mp hx
  obtain ⟨yi, hy'⟩ := Set.mem_iUnion.mp hy
  refine' Set.mem_iUnion.mpr ⟨⟨xi + yi, by simp only [Nat.cast_add, xi.prop, yi.prop]⟩, _⟩
  simp only [Subtype.coe_mk, Nat.cast_add, pow_add]
  exact Submodule.mul_mem_mul hx' hy'
#align clifford_algebra.even_odd_mul_le CliffordAlgebra.evenOdd_mul_le

instance evenOdd.gradedMonoid : SetLike.GradedMonoid (evenOdd Q) where
  one_mem := Submodule.one_le.mp (one_le_evenOdd_zero Q)
  mul_mem _i _j _p _q hp hq := Submodule.mul_le.mp (evenOdd_mul_le Q _ _) _ hp _ hq
#align clifford_algebra.even_odd.graded_monoid CliffordAlgebra.evenOdd.gradedMonoid

/-- A version of `CliffordAlgebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `CliffordAlgebra.gradedAlgebra`. -/
-- porting note: added `protected`
protected def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ZMod 2, evenOdd Q i :=
  DirectSum.lof R (ZMod 2) (fun i => ↥(evenOdd Q i)) 1 ∘ₗ (ι Q).codRestrict _ (ι_mem_evenOdd_one Q)
#align clifford_algebra.graded_algebra.ι CliffordAlgebra.GradedAlgebra.ι

theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι Q m = DirectSum.of (fun i => ↥(evenOdd Q i)) 1 ⟨ι Q m, ι_mem_evenOdd_one Q m⟩ :=
  rfl
#align clifford_algebra.graded_algebra.ι_apply CliffordAlgebra.GradedAlgebra.ι_apply

nonrec theorem GradedAlgebra.ι_sq_scalar (m : M) :
    GradedAlgebra.ι Q m * GradedAlgebra.ι Q m = algebraMap R _ (Q m) := by
  rw [GradedAlgebra.ι_apply Q, DirectSum.of_mul_of, DirectSum.algebraMap_apply]
  refine' DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext rfl <| ι_sq_scalar _ _)
#align clifford_algebra.graded_algebra.ι_sq_scalar CliffordAlgebra.GradedAlgebra.ι_sq_scalar

theorem GradedAlgebra.lift_ι_eq (i' : ZMod 2) (x' : evenOdd Q i') :
    -- porting note: added a second `by apply`
    lift Q ⟨by apply GradedAlgebra.ι Q, by apply GradedAlgebra.ι_sq_scalar Q⟩ x' =
      DirectSum.of (fun i => evenOdd Q i) i' x' := by
  cases' x' with x' hx'
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx' using Submodule.iSup_induction' with
  | hp i x hx =>
    obtain ⟨i, rfl⟩ := i
    -- porting note: `dsimp only [Subtype.coe_mk] at hx` doesn't work, use `change` instead
    change x ∈ LinearMap.range (ι Q) ^ i at hx
    induction hx using Submodule.pow_induction_on_left' with
    | hr r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | hadd x y i hx hy ihx ihy =>
      rw [AlgHom.map_add, ihx, ihy, ← map_add]
      rfl
    | hmul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [AlgHom.map_mul, ih, lift_ι_apply, GradedAlgebra.ι_apply Q, DirectSum.of_mul_of]
      refine' DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext _ _) <;>
        dsimp only [GradedMonoid.mk, Subtype.coe_mk]
      · rw [Nat.succ_eq_add_one, add_comm, Nat.cast_add, Nat.cast_one]
      rfl
  | h0 =>
    rw [AlgHom.map_zero]
    apply Eq.symm
    apply DFinsupp.single_eq_zero.mpr; rfl
  | hadd x y hx hy ihx ihy =>
    rw [AlgHom.map_add, ihx, ihy, ← map_add]; rfl
#align clifford_algebra.graded_algebra.lift_ι_eq CliffordAlgebra.GradedAlgebra.lift_ι_eq

/-- The clifford algebra is graded by the even and odd parts. -/
instance gradedAlgebra : GradedAlgebra (evenOdd Q) :=
  GradedAlgebra.ofAlgHom (evenOdd Q)
    -- while not necessary, the `by apply` makes this elaborate faster
    (lift Q ⟨by apply GradedAlgebra.ι Q, by apply GradedAlgebra.ι_sq_scalar Q⟩)
    -- the proof from here onward is mostly similar to the `TensorAlgebra` case, with some extra
    -- handling for the `iSup` in `evenOdd`.
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [lift_ι_apply, GradedAlgebra.ι_apply Q, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    (by apply GradedAlgebra.lift_ι_eq Q)
#align clifford_algebra.graded_algebra CliffordAlgebra.gradedAlgebra

theorem iSup_ι_range_eq_top : ⨆ i : ℕ, LinearMap.range (ι Q) ^ i = ⊤ := by
  rw [← (DirectSum.Decomposition.isInternal (evenOdd Q)).submodule_iSup_eq_top, eq_comm]
  calc
    -- porting note: needs extra annotations, no longer unifies against the goal in the face of
    -- ambiguity
    ⨆ (i : ZMod 2) (j : { n : ℕ // ↑n = i }), LinearMap.range (ι Q) ^ (j : ℕ) =
        ⨆ i : Σ i : ZMod 2, { n : ℕ // ↑n = i }, LinearMap.range (ι Q) ^ (i.2 : ℕ) :=
      by rw [iSup_sigma]
    _ = ⨆ i : ℕ, LinearMap.range (ι Q) ^ i :=
      Function.Surjective.iSup_congr (fun i => i.2) (fun i => ⟨⟨_, i, rfl⟩, rfl⟩) fun _ => rfl
#align clifford_algebra.supr_ι_range_eq_top CliffordAlgebra.iSup_ι_range_eq_top

theorem evenOdd_isCompl : IsCompl (evenOdd Q 0) (evenOdd Q 1) :=
  (DirectSum.Decomposition.isInternal (evenOdd Q)).isCompl zero_ne_one <| by
    have : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl
    simpa using congr_arg ((↑) : Finset (ZMod 2) → Set (ZMod 2)) this
#align clifford_algebra.even_odd_is_compl CliffordAlgebra.evenOdd_isCompl

/-- To show a property is true on the even or odd part, it suffices to show it is true on the
scalars or vectors (respectively), closed under addition, and under left-multiplication by a pair
of vectors. -/
@[elab_as_elim]
theorem evenOdd_induction (n : ZMod 2) {P : ∀ x, x ∈ evenOdd Q n → Prop}
    (hr :
      ∀ (v) (h : v ∈ LinearMap.range (ι Q) ^ n.val),
        P v (Submodule.mem_iSup_of_mem ⟨n.val, n.nat_cast_zmod_val⟩ h))
    (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (hιι_mul :
      ∀ (m₁ m₂) {x hx},
        P x hx →
          P (ι Q m₁ * ι Q m₂ * x)
            (zero_add n ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x ∈ evenOdd Q n) : P x hx := by
  apply Submodule.iSup_induction' (C := P) _ (hr 0 (Submodule.zero_mem _)) @hadd
  refine' Subtype.rec _
  -- porting note: was `simp_rw [Subtype.coe_mk, ZMod.nat_coe_zmod_eq_iff, add_comm n.val]`
  -- leanprover/lean4#1926 is to blame.
  dsimp only [Subtype.coe_mk]
  let hlean1926 : ∀ val : ℕ, ↑val = n ↔ ∃ k, val = 2 * k + ZMod.val n := by
    intro val
    simp_rw [ZMod.nat_coe_zmod_eq_iff, add_comm n.val]
  have := fun val : ℕ => forall_prop_congr'
    (q := fun property => ∀ x (hx : x ∈ LinearMap.range (ι Q) ^ val),
      P x (Submodule.mem_iSup_of_mem { val := val, property := property } hx))
    (hq := fun property => Iff.rfl) (hp := hlean1926 val)
  simp_rw [this]; clear this
  -- end porting note
  rintro n' ⟨k, rfl⟩ xv
  -- porting note: was `simp_rw [pow_add, pow_mul]`
  -- leanprover/lean4#1926 is to blame.
  refine (forall_prop_congr' (hq := fun property => Iff.rfl) (
    show xv ∈ LinearMap.range (ι Q) ^ (2 * k + ZMod.val n)
        ↔ xv ∈ (LinearMap.range (ι Q) ^ 2) ^ k * LinearMap.range (ι Q) ^ ZMod.val n by
      simp_rw [pow_add, pow_mul])).mpr ?_
  -- end porting note
  intro hxv
  induction hxv using Submodule.mul_induction_on' with
  | hm a ha b hb =>
    induction ha using Submodule.pow_induction_on_left' with
    | hr r =>
      simp_rw [← Algebra.smul_def]
      exact hr _ (Submodule.smul_mem _ _ hb)
    | hadd x y n hx hy ihx ihy =>
      simp_rw [add_mul]
      apply hadd ihx ihy
    | hmul x hx n'' y hy ihy =>
      revert hx
      -- porting note: was `simp_rw [pow_two]`
      -- leanprover/lean4#1926 is to blame.
      let hlean1926'' : x ∈ LinearMap.range (ι Q) ^ 2
          ↔ x ∈ LinearMap.range (ι Q) * LinearMap.range (ι Q) := by
        rw [pow_two]
      refine (forall_prop_congr' (hq := fun property => Iff.rfl) hlean1926'').mpr ?_
      -- end porting note
      intro hx2
      induction hx2 using Submodule.mul_induction_on' with
      | hm m hm n hn =>
        simp_rw [LinearMap.mem_range] at hm hn
        obtain ⟨m₁, rfl⟩ := hm; obtain ⟨m₂, rfl⟩ := hn
        simp_rw [mul_assoc _ y b]
        refine' hιι_mul _ _ ihy
      | ha x hx y hy ihx ihy =>
        simp_rw [add_mul]
        apply hadd ihx ihy
  | ha x y hx hy ihx ihy =>
    apply hadd ihx ihy
#align clifford_algebra.even_odd_induction CliffordAlgebra.evenOdd_induction

/-- To show a property is true on the even parts, it suffices to show it is true on the
scalars, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_elim]
theorem even_induction {P : ∀ x, x ∈ evenOdd Q 0 → Prop}
    (hr : ∀ r : R, P (algebraMap _ _ r) (SetLike.algebraMap_mem_graded _ _))
    (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (hιι_mul :
      ∀ (m₁ m₂) {x hx},
        P x hx →
          P (ι Q m₁ * ι Q m₂ * x)
            (zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x ∈ evenOdd Q 0) : P x hx := by
  refine' evenOdd_induction Q 0 (fun rx => _) (@hadd) hιι_mul x hx
  rintro ⟨r, rfl⟩
  exact hr r
#align clifford_algebra.even_induction CliffordAlgebra.even_induction

/-- To show a property is true on the odd parts, it suffices to show it is true on the
vectors, closed under addition, and under left-multiplication by a pair of vectors. -/
@[elab_as_elim]
theorem odd_induction {P : ∀ x, x ∈ evenOdd Q 1 → Prop}
    (hι : ∀ v, P (ι Q v) (ι_mem_evenOdd_one _ _))
    (hadd : ∀ {x y hx hy}, P x hx → P y hy → P (x + y) (Submodule.add_mem _ hx hy))
    (hιι_mul :
      ∀ (m₁ m₂) {x hx},
        P x hx →
          P (ι Q m₁ * ι Q m₂ * x)
            (zero_add (1 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx))
    (x : CliffordAlgebra Q) (hx : x ∈ evenOdd Q 1) : P x hx := by
  refine' evenOdd_induction Q 1 (fun ιv => _) (@hadd) hιι_mul x hx
  -- porting note: was `simp_rw [ZMod.val_one, pow_one]`, lean4#1926
  intro h; rw [ZMod.val_one, pow_one] at h; revert h
  rintro ⟨v, rfl⟩
  exact hι v
#align clifford_algebra.odd_induction CliffordAlgebra.odd_induction

end CliffordAlgebra
