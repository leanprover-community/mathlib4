/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Algebra.Squarefree
import Mathlib.Data.Polynomial.Expand
import Mathlib.Data.Polynomial.Splits
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.PowerBasis

#align_import field_theory.separable from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!

# Separable polynomials

We define a polynomial to be separable if it is coprime with its derivative. We prove basic
properties about separable polynomials here.

## Main definitions

* `Polynomial.Separable f`: a polynomial `f` is separable iff it is coprime with its derivative.

-/


universe u v w

open Classical BigOperators Polynomial Finset

namespace Polynomial

section CommSemiring

variable {R : Type u} [CommSemiring R] {S : Type v} [CommSemiring S]

/-- A polynomial is separable iff it is coprime with its derivative. -/
def Separable (f : R[X]) : Prop :=
  IsCoprime f (derivative f)
#align polynomial.separable Polynomial.Separable

theorem separable_def (f : R[X]) : f.Separable ↔ IsCoprime f (derivative f) :=
  Iff.rfl
#align polynomial.separable_def Polynomial.separable_def

theorem separable_def' (f : R[X]) : f.Separable ↔ ∃ a b : R[X], a * f + b * (derivative f) = 1 :=
  Iff.rfl
#align polynomial.separable_def' Polynomial.separable_def'

theorem not_separable_zero [Nontrivial R] : ¬Separable (0 : R[X]) := by
  rintro ⟨x, y, h⟩
  -- ⊢ False
  simp only [derivative_zero, mul_zero, add_zero, zero_ne_one] at h
  -- 🎉 no goals
#align polynomial.not_separable_zero Polynomial.not_separable_zero

theorem separable_one : (1 : R[X]).Separable :=
  isCoprime_one_left
#align polynomial.separable_one Polynomial.separable_one

@[nontriviality]
theorem separable_of_subsingleton [Subsingleton R] (f : R[X]) : f.Separable := by
  simp [Separable, IsCoprime]
  -- 🎉 no goals
#align polynomial.separable_of_subsingleton Polynomial.separable_of_subsingleton

theorem separable_X_add_C (a : R) : (X + C a).Separable := by
  rw [separable_def, derivative_add, derivative_X, derivative_C, add_zero]
  -- ⊢ IsCoprime (X + ↑C a) 1
  exact isCoprime_one_right
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.separable_X_add_C Polynomial.separable_X_add_C

theorem separable_X : (X : R[X]).Separable := by
  rw [separable_def, derivative_X]
  -- ⊢ IsCoprime X 1
  exact isCoprime_one_right
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.separable_X Polynomial.separable_X

theorem separable_C (r : R) : (C r).Separable ↔ IsUnit r := by
  rw [separable_def, derivative_C, isCoprime_zero_right, isUnit_C]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.separable_C Polynomial.separable_C

theorem Separable.of_mul_left {f g : R[X]} (h : (f * g).Separable) : f.Separable := by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  -- ⊢ Separable f
                              -- ⊢ Separable f
  exact IsCoprime.of_mul_right_left (IsCoprime.of_add_mul_left_right this)
  -- 🎉 no goals
#align polynomial.separable.of_mul_left Polynomial.Separable.of_mul_left

theorem Separable.of_mul_right {f g : R[X]} (h : (f * g).Separable) : g.Separable := by
  rw [mul_comm] at h
  -- ⊢ Separable g
  exact h.of_mul_left
  -- 🎉 no goals
#align polynomial.separable.of_mul_right Polynomial.Separable.of_mul_right

theorem Separable.of_dvd {f g : R[X]} (hf : f.Separable) (hfg : g ∣ f) : g.Separable := by
  rcases hfg with ⟨f', rfl⟩
  -- ⊢ Separable g
  exact Separable.of_mul_left hf
  -- 🎉 no goals
#align polynomial.separable.of_dvd Polynomial.Separable.of_dvd

theorem separable_gcd_left {F : Type*} [Field F] {f : F[X]} (hf : f.Separable) (g : F[X]) :
    (EuclideanDomain.gcd f g).Separable :=
  Separable.of_dvd hf (EuclideanDomain.gcd_dvd_left f g)
#align polynomial.separable_gcd_left Polynomial.separable_gcd_left

theorem separable_gcd_right {F : Type*} [Field F] {g : F[X]} (f : F[X]) (hg : g.Separable) :
    (EuclideanDomain.gcd f g).Separable :=
  Separable.of_dvd hg (EuclideanDomain.gcd_dvd_right f g)
#align polynomial.separable_gcd_right Polynomial.separable_gcd_right

theorem Separable.isCoprime {f g : R[X]} (h : (f * g).Separable) : IsCoprime f g := by
  have := h.of_mul_left_left; rw [derivative_mul] at this
  -- ⊢ IsCoprime f g
                              -- ⊢ IsCoprime f g
  exact IsCoprime.of_mul_right_right (IsCoprime.of_add_mul_left_right this)
  -- 🎉 no goals
#align polynomial.separable.is_coprime Polynomial.Separable.isCoprime

theorem Separable.of_pow' {f : R[X]} :
    ∀ {n : ℕ} (_h : (f ^ n).Separable), IsUnit f ∨ f.Separable ∧ n = 1 ∨ n = 0
  | 0 => fun _h => Or.inr <| Or.inr rfl
  | 1 => fun h => Or.inr <| Or.inl ⟨pow_one f ▸ h, rfl⟩
  | n + 2 => fun h => by
    rw [pow_succ, pow_succ] at h
    -- ⊢ IsUnit f ∨ Separable f ∧ n + 2 = 1 ∨ n + 2 = 0
    exact Or.inl (isCoprime_self.1 h.isCoprime.of_mul_right_left)
    -- 🎉 no goals
#align polynomial.separable.of_pow' Polynomial.Separable.of_pow'

theorem Separable.of_pow {f : R[X]} (hf : ¬IsUnit f) {n : ℕ} (hn : n ≠ 0)
    (hfs : (f ^ n).Separable) : f.Separable ∧ n = 1 :=
  (hfs.of_pow'.resolve_left hf).resolve_right hn
#align polynomial.separable.of_pow Polynomial.Separable.of_pow

theorem Separable.map {p : R[X]} (h : p.Separable) {f : R →+* S} : (p.map f).Separable :=
  let ⟨a, b, H⟩ := h
  ⟨a.map f, b.map f, by
    rw [derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, H,
      Polynomial.map_one]⟩
#align polynomial.separable.map Polynomial.Separable.map

variable (p q : ℕ)

theorem isUnit_of_self_mul_dvd_separable {p q : R[X]} (hp : p.Separable) (hq : q * q ∣ p) :
    IsUnit q := by
  obtain ⟨p, rfl⟩ := hq
  -- ⊢ IsUnit q
  apply isCoprime_self.mp
  -- ⊢ IsCoprime q q
  have : IsCoprime (q * (q * p))
      (q * (derivative q * p + derivative q * p + q * derivative p)) := by
    simp only [← mul_assoc, mul_add]
    dsimp only [Separable] at hp
    convert hp using 1
    rw [derivative_mul, derivative_mul]
    ring
  exact IsCoprime.of_mul_right_left (IsCoprime.of_mul_left_left this)
  -- 🎉 no goals
#align polynomial.is_unit_of_self_mul_dvd_separable Polynomial.isUnit_of_self_mul_dvd_separable

theorem multiplicity_le_one_of_separable {p q : R[X]} (hq : ¬IsUnit q) (hsep : Separable p) :
    multiplicity q p ≤ 1 := by
  contrapose! hq
  -- ⊢ IsUnit q
  apply isUnit_of_self_mul_dvd_separable hsep
  -- ⊢ q * q ∣ p
  rw [← sq]
  -- ⊢ q ^ 2 ∣ p
  apply multiplicity.pow_dvd_of_le_multiplicity
  -- ⊢ ↑2 ≤ multiplicity q p
  have h : ⟨Part.Dom 1 ∧ Part.Dom 1, fun _ ↦ 2⟩ ≤ multiplicity q p := PartENat.add_one_le_of_lt hq
  -- ⊢ ↑2 ≤ multiplicity q p
  rw [and_self] at h
  -- ⊢ ↑2 ≤ multiplicity q p
  exact h
  -- 🎉 no goals
#align polynomial.multiplicity_le_one_of_separable Polynomial.multiplicity_le_one_of_separable

theorem Separable.squarefree {p : R[X]} (hsep : Separable p) : Squarefree p := by
  rw [multiplicity.squarefree_iff_multiplicity_le_one p]
  -- ⊢ ∀ (x : R[X]), multiplicity x p ≤ 1 ∨ IsUnit x
  exact fun f => or_iff_not_imp_right.mpr fun hunit => multiplicity_le_one_of_separable hunit hsep
  -- 🎉 no goals
#align polynomial.separable.squarefree Polynomial.Separable.squarefree

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

theorem separable_X_sub_C {x : R} : Separable (X - C x) := by
  simpa only [sub_eq_add_neg, C_neg] using separable_X_add_C (-x)
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.separable_X_sub_C Polynomial.separable_X_sub_C

theorem Separable.mul {f g : R[X]} (hf : f.Separable) (hg : g.Separable) (h : IsCoprime f g) :
    (f * g).Separable := by
  rw [separable_def, derivative_mul]
  -- ⊢ IsCoprime (f * g) (↑derivative f * g + f * ↑derivative g)
  exact
    ((hf.mul_right h).add_mul_left_right _).mul_left ((h.symm.mul_right hg).mul_add_right_right _)
#align polynomial.separable.mul Polynomial.Separable.mul

theorem separable_prod' {ι : Sort _} {f : ι → R[X]} {s : Finset ι} :
    (∀ x ∈ s, ∀ y ∈ s, x ≠ y → IsCoprime (f x) (f y)) →
      (∀ x ∈ s, (f x).Separable) → (∏ x in s, f x).Separable :=
  Finset.induction_on s (fun _ _ => separable_one) fun a s has ih h1 h2 => by
    simp_rw [Finset.forall_mem_insert, forall_and] at h1 h2; rw [prod_insert has]
    -- ⊢ Separable (∏ x in insert a s, f x)
                                                             -- ⊢ Separable (f a * ∏ x in s, f x)
    exact
      h2.1.mul (ih h1.2.2 h2.2)
        (IsCoprime.prod_right fun i his => h1.1.2 i his <| Ne.symm <| ne_of_mem_of_not_mem his has)
#align polynomial.separable_prod' Polynomial.separable_prod'

theorem separable_prod {ι : Sort _} [Fintype ι] {f : ι → R[X]} (h1 : Pairwise (IsCoprime on f))
    (h2 : ∀ x, (f x).Separable) : (∏ x, f x).Separable :=
  separable_prod' (fun _x _hx _y _hy hxy => h1 hxy) fun x _hx => h2 x
#align polynomial.separable_prod Polynomial.separable_prod

theorem Separable.inj_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} {f : ι → R} {s : Finset ι}
    (hfs : (∏ i in s, (X - C (f i))).Separable) {x y : ι} (hx : x ∈ s) (hy : y ∈ s)
    (hfxy : f x = f y) : x = y := by
  by_contra hxy
  -- ⊢ False
  rw [← insert_erase hx, prod_insert (not_mem_erase _ _), ←
    insert_erase (mem_erase_of_ne_of_mem (Ne.symm hxy) hy), prod_insert (not_mem_erase _ _), ←
    mul_assoc, hfxy, ← sq] at hfs
  cases (hfs.of_mul_left.of_pow (not_isUnit_X_sub_C _) two_ne_zero).2
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.separable.inj_of_prod_X_sub_C Polynomial.Separable.inj_of_prod_X_sub_C

theorem Separable.injective_of_prod_X_sub_C [Nontrivial R] {ι : Sort _} [Fintype ι] {f : ι → R}
    (hfs : (∏ i, (X - C (f i))).Separable) : Function.Injective f := fun _x _y hfxy =>
  hfs.inj_of_prod_X_sub_C (mem_univ _) (mem_univ _) hfxy
set_option linter.uppercaseLean3 false in
#align polynomial.separable.injective_of_prod_X_sub_C Polynomial.Separable.injective_of_prod_X_sub_C

theorem nodup_of_separable_prod [Nontrivial R] {s : Multiset R}
    (hs : Separable (Multiset.map (fun a => X - C a) s).prod) : s.Nodup := by
  rw [Multiset.nodup_iff_ne_cons_cons]
  -- ⊢ ∀ (a : R) (t : Multiset R), s ≠ a ::ₘ a ::ₘ t
  rintro a t rfl
  -- ⊢ False
  refine' not_isUnit_X_sub_C a (isUnit_of_self_mul_dvd_separable hs _)
  -- ⊢ (X - ↑C a) * (X - ↑C a) ∣ Multiset.prod (Multiset.map (fun a => X - ↑C a) (a …
  simpa only [Multiset.map_cons, Multiset.prod_cons] using mul_dvd_mul_left _ (dvd_mul_right _ _)
  -- 🎉 no goals
#align polynomial.nodup_of_separable_prod Polynomial.nodup_of_separable_prod

/-- If `IsUnit n` in a `CommRing R`, then `X ^ n - u` is separable for any unit `u`. -/
theorem separable_X_pow_sub_C_unit {n : ℕ} (u : Rˣ) (hn : IsUnit (n : R)) :
    Separable (X ^ n - C (u : R)) := by
  nontriviality R
  -- ⊢ Separable (X ^ n - ↑C ↑u)
  rcases n.eq_zero_or_pos with (rfl | hpos)
  -- ⊢ Separable (X ^ 0 - ↑C ↑u)
  · simp at hn
    -- 🎉 no goals
  apply (separable_def' (X ^ n - C (u : R))).2
  -- ⊢ ∃ a b, a * (X ^ n - ↑C ↑u) + b * ↑derivative (X ^ n - ↑C ↑u) = 1
  obtain ⟨n', hn'⟩ := hn.exists_left_inv
  -- ⊢ ∃ a b, a * (X ^ n - ↑C ↑u) + b * ↑derivative (X ^ n - ↑C ↑u) = 1
  refine' ⟨-C ↑u⁻¹, C (↑u⁻¹ : R) * C n' * X, _⟩
  -- ⊢ -↑C ↑u⁻¹ * (X ^ n - ↑C ↑u) + ↑C ↑u⁻¹ * ↑C n' * X * ↑derivative (X ^ n - ↑C ↑ …
  rw [derivative_sub, derivative_C, sub_zero, derivative_pow X n, derivative_X, mul_one]
  -- ⊢ -↑C ↑u⁻¹ * (X ^ n - ↑C ↑u) + ↑C ↑u⁻¹ * ↑C n' * X * (↑C ↑n * X ^ (n - 1)) = 1
  calc
    -C ↑u⁻¹ * (X ^ n - C ↑u) + C ↑u⁻¹ * C n' * X * (↑n * X ^ (n - 1)) =
        C (↑u⁻¹ * ↑u) - C ↑u⁻¹ * X ^ n + C ↑u⁻¹ * C (n' * ↑n) * (X * X ^ (n - 1)) := by
      simp only [C.map_mul, C_eq_nat_cast]
      ring
    _ = 1 := by
      simp only [Units.inv_mul, hn', C.map_one, mul_one, ← pow_succ,
        Nat.sub_add_cancel (show 1 ≤ n from hpos), sub_add_cancel]
set_option linter.uppercaseLean3 false in
#align polynomial.separable_X_pow_sub_C_unit Polynomial.separable_X_pow_sub_C_unit

theorem rootMultiplicity_le_one_of_separable [Nontrivial R] {p : R[X]} (hsep : Separable p)
    (x : R) : rootMultiplicity x p ≤ 1 := by
  by_cases hp : p = 0
  -- ⊢ rootMultiplicity x p ≤ 1
  · simp [hp]
    -- 🎉 no goals
  rw [rootMultiplicity_eq_multiplicity, dif_neg hp, ← PartENat.coe_le_coe, PartENat.natCast_get,
    Nat.cast_one]
  exact multiplicity_le_one_of_separable (not_isUnit_X_sub_C _) hsep
  -- 🎉 no goals
#align polynomial.root_multiplicity_le_one_of_separable Polynomial.rootMultiplicity_le_one_of_separable

end CommRing

section IsDomain

variable {R : Type u} [CommRing R] [IsDomain R]

theorem count_roots_le_one {p : R[X]} (hsep : Separable p) (x : R) : p.roots.count x ≤ 1 := by
  rw [count_roots p]
  -- ⊢ rootMultiplicity x p ≤ 1
  exact rootMultiplicity_le_one_of_separable hsep x
  -- 🎉 no goals
#align polynomial.count_roots_le_one Polynomial.count_roots_le_one

theorem nodup_roots {p : R[X]} (hsep : Separable p) : p.roots.Nodup :=
  Multiset.nodup_iff_count_le_one.mpr (count_roots_le_one hsep)
#align polynomial.nodup_roots Polynomial.nodup_roots

end IsDomain

section Field

variable {F : Type u} [Field F] {K : Type v} [Field K]

theorem separable_iff_derivative_ne_zero {f : F[X]} (hf : Irreducible f) :
    f.Separable ↔ derivative f ≠ 0 :=
  ⟨fun h1 h2 => hf.not_unit <| isCoprime_zero_right.1 <| h2 ▸ h1, fun h =>
    EuclideanDomain.isCoprime_of_dvd (mt And.right h) fun g hg1 _hg2 ⟨p, hg3⟩ hg4 =>
      let ⟨u, hu⟩ := (hf.isUnit_or_isUnit hg3).resolve_left hg1
      have : f ∣ derivative f := by
        conv_lhs => rw [hg3, ← hu]
        -- ⊢ g * ↑u ∣ ↑derivative f
        rwa [Units.mul_right_dvd]
        -- 🎉 no goals
      not_lt_of_le (natDegree_le_of_dvd this h) <|
        natDegree_derivative_lt <| mt derivative_of_natDegree_zero h⟩
#align polynomial.separable_iff_derivative_ne_zero Polynomial.separable_iff_derivative_ne_zero

theorem separable_map (f : F →+* K) {p : F[X]} :
    (p.map f).Separable ↔ p.Separable := by
  simp_rw [separable_def, derivative_map, isCoprime_map]
  -- 🎉 no goals
#align polynomial.separable_map Polynomial.separable_map

theorem separable_prod_X_sub_C_iff' {ι : Sort _} {f : ι → F} {s : Finset ι} :
    (∏ i in s, (X - C (f i))).Separable ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  ⟨fun hfs x hx y hy hfxy => hfs.inj_of_prod_X_sub_C hx hy hfxy, fun H => by
    rw [← prod_attach]
    -- ⊢ Separable (∏ x in attach s, (X - ↑C (f ↑x)))
    exact
      separable_prod'
        (fun x _hx y _hy hxy =>
          @pairwise_coprime_X_sub_C _ _ { x // x ∈ s } (fun x => f x)
            (fun x y hxy => Subtype.eq <| H x.1 x.2 y.1 y.2 hxy) _ _ hxy)
        fun _ _ => separable_X_sub_C⟩
set_option linter.uppercaseLean3 false in
#align polynomial.separable_prod_X_sub_C_iff' Polynomial.separable_prod_X_sub_C_iff'

theorem separable_prod_X_sub_C_iff {ι : Sort _} [Fintype ι] {f : ι → F} :
    (∏ i, (X - C (f i))).Separable ↔ Function.Injective f :=
  separable_prod_X_sub_C_iff'.trans <| by simp_rw [mem_univ, true_imp_iff, Function.Injective]
                                          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.separable_prod_X_sub_C_iff Polynomial.separable_prod_X_sub_C_iff

section CharP

variable (p : ℕ) [HF : CharP F p]

theorem separable_or {f : F[X]} (hf : Irreducible f) :
    f.Separable ∨ ¬f.Separable ∧ ∃ g : F[X], Irreducible g ∧ expand F p g = f :=
  if H : derivative f = 0 then by
    rcases p.eq_zero_or_pos with (rfl | hp)
    -- ⊢ Separable f ∨ ¬Separable f ∧ ∃ g, Irreducible g ∧ ↑(expand F 0) g = f
    · haveI := CharP.charP_to_charZero F
      -- ⊢ Separable f ∨ ¬Separable f ∧ ∃ g, Irreducible g ∧ ↑(expand F 0) g = f
      have := natDegree_eq_zero_of_derivative_eq_zero H
      -- ⊢ Separable f ∨ ¬Separable f ∧ ∃ g, Irreducible g ∧ ↑(expand F 0) g = f
      have := (natDegree_pos_iff_degree_pos.mpr <| degree_pos_of_irreducible hf).ne'
      -- ⊢ Separable f ∨ ¬Separable f ∧ ∃ g, Irreducible g ∧ ↑(expand F 0) g = f
      contradiction
      -- 🎉 no goals
    haveI := isLocalRingHom_expand F hp
    -- ⊢ Separable f ∨ ¬Separable f ∧ ∃ g, Irreducible g ∧ ↑(expand F p) g = f
    exact
      Or.inr
        ⟨by rw [separable_iff_derivative_ne_zero hf, Classical.not_not, H], contract p f,
          of_irreducible_map (expand F p : F[X] →+* F[X])
            (by rwa [← expand_contract p H hp.ne'] at hf),
          expand_contract p H hp.ne'⟩
  else Or.inl <| (separable_iff_derivative_ne_zero hf).2 H
#align polynomial.separable_or Polynomial.separable_or

theorem exists_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : p ≠ 0) :
    ∃ (n : ℕ) (g : F[X]), g.Separable ∧ expand F (p ^ n) g = f := by
  replace hp : p.Prime := (CharP.char_is_prime_or_zero F p).resolve_right hp
  -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
  induction' hn : f.natDegree using Nat.strong_induction_on with N ih generalizing f
  -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
  rcases separable_or p hf with (h | ⟨h1, g, hg, hgf⟩)
  -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
  · refine' ⟨0, f, h, _⟩
    -- ⊢ ↑(expand F (p ^ 0)) f = f
    rw [pow_zero, expand_one]
    -- 🎉 no goals
  · cases' N with N
    -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
    · rw [natDegree_eq_zero_iff_degree_le_zero, degree_le_zero_iff] at hn
      -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
      rw [hn, separable_C, isUnit_iff_ne_zero, Classical.not_not] at h1
      -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
      have hf0 : f ≠ 0 := hf.ne_zero
      -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
      rw [h1, C_0] at hn
      -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
      exact absurd hn hf0
      -- 🎉 no goals
    have hg1 : g.natDegree * p = N.succ := by rwa [← natDegree_expand, hgf]
    -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
    have hg2 : g.natDegree ≠ 0 := by
      intro this
      rw [this, zero_mul] at hg1
      cases hg1
    have hg3 : g.natDegree < N.succ := by
      rw [← mul_one g.natDegree, ← hg1]
      exact Nat.mul_lt_mul_of_pos_left hp.one_lt hg2.bot_lt
    rcases ih _ hg3 hg rfl with ⟨n, g, hg4, rfl⟩
    -- ⊢ ∃ n g, Separable g ∧ ↑(expand F (p ^ n)) g = f
    refine' ⟨n + 1, g, hg4, _⟩
    -- ⊢ ↑(expand F (p ^ (n + 1))) g = f
    rw [← hgf, expand_expand, pow_succ]
    -- 🎉 no goals
#align polynomial.exists_separable_of_irreducible Polynomial.exists_separable_of_irreducible

theorem isUnit_or_eq_zero_of_separable_expand {f : F[X]} (n : ℕ) (hp : 0 < p)
    (hf : (expand F (p ^ n) f).Separable) : IsUnit f ∨ n = 0 := by
  rw [or_iff_not_imp_right]
  -- ⊢ ¬n = 0 → IsUnit f
  rintro hn : n ≠ 0
  -- ⊢ IsUnit f
  have hf2 : derivative (expand F (p ^ n) f) = 0 := by
    rw [derivative_expand, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hn.bot_lt,
      zero_mul, mul_zero]
  rw [separable_def, hf2, isCoprime_zero_right, isUnit_iff] at hf
  -- ⊢ IsUnit f
  rcases hf with ⟨r, hr, hrf⟩
  -- ⊢ IsUnit f
  rw [eq_comm, expand_eq_C (pow_pos hp _)] at hrf
  -- ⊢ IsUnit f
  rwa [hrf, isUnit_C]
  -- 🎉 no goals
#align polynomial.is_unit_or_eq_zero_of_separable_expand Polynomial.isUnit_or_eq_zero_of_separable_expand

theorem unique_separable_of_irreducible {f : F[X]} (hf : Irreducible f) (hp : 0 < p) (n₁ : ℕ)
    (g₁ : F[X]) (hg₁ : g₁.Separable) (hgf₁ : expand F (p ^ n₁) g₁ = f) (n₂ : ℕ) (g₂ : F[X])
    (hg₂ : g₂.Separable) (hgf₂ : expand F (p ^ n₂) g₂ = f) : n₁ = n₂ ∧ g₁ = g₂ := by
  revert g₁ g₂
  -- ⊢ ∀ (g₁ : F[X]), Separable g₁ → ↑(expand F (p ^ n₁)) g₁ = f → ∀ (g₂ : F[X]), S …
  -- Porting note: the variable `K` affects the `wlog` tactic.
  clear! K
  -- ⊢ ∀ (g₁ : F[X]), Separable g₁ → ↑(expand F (p ^ n₁)) g₁ = f → ∀ (g₂ : F[X]), S …
  wlog hn : n₁ ≤ n₂
  -- ⊢ ∀ (g₁ : F[X]), Separable g₁ → ↑(expand F (p ^ n₁)) g₁ = f → ∀ (g₂ : F[X]), S …
  · intro g₁ hg₁ Hg₁ g₂ hg₂ Hg₂
    -- ⊢ n₁ = n₂ ∧ g₁ = g₂
    simpa only [eq_comm] using this p hf hp n₂ n₁ (le_of_not_le hn) g₂ hg₂ Hg₂ g₁ hg₁ Hg₁
    -- 🎉 no goals
  have hf0 : f ≠ 0 := hf.ne_zero
  -- ⊢ ∀ (g₁ : F[X]), Separable g₁ → ↑(expand F (p ^ n₁)) g₁ = f → ∀ (g₂ : F[X]), S …
  intros g₁ hg₁ hgf₁ g₂ hg₂ hgf₂
  -- ⊢ n₁ = n₂ ∧ g₁ = g₂
  rw [le_iff_exists_add] at hn
  -- ⊢ n₁ = n₂ ∧ g₁ = g₂
  rcases hn with ⟨k, rfl⟩
  -- ⊢ n₁ = n₁ + k ∧ g₁ = g₂
  rw [← hgf₁, pow_add, expand_mul, expand_inj (pow_pos hp n₁)] at hgf₂
  -- ⊢ n₁ = n₁ + k ∧ g₁ = g₂
  subst hgf₂
  -- ⊢ n₁ = n₁ + k ∧ ↑(expand F (p ^ k)) g₂ = g₂
  subst hgf₁
  -- ⊢ n₁ = n₁ + k ∧ ↑(expand F (p ^ k)) g₂ = g₂
  rcases isUnit_or_eq_zero_of_separable_expand p k hp hg₁ with (h | rfl)
  -- ⊢ n₁ = n₁ + k ∧ ↑(expand F (p ^ k)) g₂ = g₂
  · rw [isUnit_iff] at h
    -- ⊢ n₁ = n₁ + k ∧ ↑(expand F (p ^ k)) g₂ = g₂
    rcases h with ⟨r, hr, rfl⟩
    -- ⊢ n₁ = n₁ + k ∧ ↑(expand F (p ^ k)) (↑C r) = ↑C r
    simp_rw [expand_C] at hf
    -- ⊢ n₁ = n₁ + k ∧ ↑(expand F (p ^ k)) (↑C r) = ↑C r
    exact absurd (isUnit_C.2 hr) hf.1
    -- 🎉 no goals
  · rw [add_zero, pow_zero, expand_one]
    -- ⊢ n₁ = n₁ ∧ g₂ = g₂
    constructor <;> rfl
    -- ⊢ n₁ = n₁
                    -- 🎉 no goals
                    -- 🎉 no goals
#align polynomial.unique_separable_of_irreducible Polynomial.unique_separable_of_irreducible

end CharP

/-- If `n ≠ 0` in `F`, then ` X ^ n - a` is separable for any `a ≠ 0`. -/
theorem separable_X_pow_sub_C {n : ℕ} (a : F) (hn : (n : F) ≠ 0) (ha : a ≠ 0) :
    Separable (X ^ n - C a) :=
  separable_X_pow_sub_C_unit (Units.mk0 a ha) (IsUnit.mk0 (n : F) hn)
set_option linter.uppercaseLean3 false in
#align polynomial.separable_X_pow_sub_C Polynomial.separable_X_pow_sub_C

-- this can possibly be strengthened to making `separable_X_pow_sub_C_unit` a
-- bi-implication, but it is nontrivial!
/-- In a field `F`, `X ^ n - 1` is separable iff `↑n ≠ 0`. -/
theorem X_pow_sub_one_separable_iff {n : ℕ} : (X ^ n - 1 : F[X]).Separable ↔ (n : F) ≠ 0 := by
  refine' ⟨_, fun h => separable_X_pow_sub_C_unit 1 (IsUnit.mk0 (↑n) h)⟩
  -- ⊢ Separable (X ^ n - 1) → ↑n ≠ 0
  rw [separable_def', derivative_sub, derivative_X_pow, derivative_one, sub_zero]
  -- ⊢ (∃ a b, a * (X ^ n - 1) + b * (↑C ↑n * X ^ (n - 1)) = 1) → ↑n ≠ 0
  -- Suppose `(n : F) = 0`, then the derivative is `0`, so `X ^ n - 1` is a unit, contradiction.
  rintro (h : IsCoprime _ _) hn'
  -- ⊢ False
  rw [hn', C_0, zero_mul, isCoprime_zero_right] at h
  -- ⊢ False
  exact not_isUnit_X_pow_sub_one F n h
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.X_pow_sub_one_separable_iff Polynomial.X_pow_sub_one_separable_iff

section Splits

theorem card_rootSet_eq_natDegree [Algebra F K] {p : F[X]} (hsep : p.Separable)
    (hsplit : Splits (algebraMap F K) p) : Fintype.card (p.rootSet K) = p.natDegree := by
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  -- ⊢ card (Multiset.toFinset (roots (map (algebraMap F K) p))) = natDegree p
  rw [Multiset.toFinset_card_of_nodup, ← natDegree_eq_card_roots hsplit]
  -- ⊢ Multiset.Nodup (roots (map (algebraMap F K) p))
  exact nodup_roots hsep.map
  -- 🎉 no goals
#align polynomial.card_root_set_eq_nat_degree Polynomial.card_rootSet_eq_natDegree

variable {i : F →+* K}

theorem eq_X_sub_C_of_separable_of_root_eq {x : F} {h : F[X]} (h_sep : h.Separable)
    (h_root : h.eval x = 0) (h_splits : Splits i h) (h_roots : ∀ y ∈ (h.map i).roots, y = i x) :
    h = C (leadingCoeff h) * (X - C x) := by
  have h_ne_zero : h ≠ 0 := by
    rintro rfl
    exact not_separable_zero h_sep
  apply Polynomial.eq_X_sub_C_of_splits_of_single_root i h_splits
  -- ⊢ roots (map i h) = {↑i x}
  apply Finset.mk.inj
  · change _ = {i x}
    -- ⊢ { val := roots (map i h), nodup := ?nodup } = {↑i x}
    rw [Finset.eq_singleton_iff_unique_mem]
    -- ⊢ ↑i x ∈ { val := roots (map i h), nodup := ?nodup } ∧ ∀ (x_1 : K), x_1 ∈ { va …
    constructor
    · apply Finset.mem_mk.mpr
      -- ⊢ ↑i x ∈ roots (map i h)
      · rw [mem_roots (show h.map i ≠ 0 from map_ne_zero h_ne_zero)]
        -- ⊢ IsRoot (map i h) (↑i x)
        rw [IsRoot.def, ← eval₂_eq_eval_map, eval₂_hom, h_root]
        -- ⊢ ↑i 0 = 0
        exact RingHom.map_zero i
        -- 🎉 no goals
      · exact nodup_roots (Separable.map h_sep)
        -- 🎉 no goals
    · exact h_roots
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.eq_X_sub_C_of_separable_of_root_eq Polynomial.eq_X_sub_C_of_separable_of_root_eq

theorem exists_finset_of_splits (i : F →+* K) {f : F[X]} (sep : Separable f) (sp : Splits i f) :
    ∃ s : Finset K, f.map i = C (i f.leadingCoeff) * s.prod fun a : K => X - C a := by
  obtain ⟨s, h⟩ := (splits_iff_exists_multiset _).1 sp
  -- ⊢ ∃ s, map i f = ↑C (↑i (leadingCoeff f)) * ∏ a in s, (X - ↑C a)
  use s.toFinset
  -- ⊢ map i f = ↑C (↑i (leadingCoeff f)) * ∏ a in Multiset.toFinset s, (X - ↑C a)
  rw [h, Finset.prod_eq_multiset_prod, ← Multiset.toFinset_eq]
  -- ⊢ Multiset.Nodup s
  apply nodup_of_separable_prod
  -- ⊢ Separable (Multiset.prod (Multiset.map (fun a => X - ↑C a) s))
  apply Separable.of_mul_right
  -- ⊢ Separable (?h.hs.f * Multiset.prod (Multiset.map (fun a => X - ↑C a) s))
  rw [← h]
  -- ⊢ Separable (map i f)
  exact sep.map
  -- 🎉 no goals
#align polynomial.exists_finset_of_splits Polynomial.exists_finset_of_splits

end Splits

theorem _root_.Irreducible.separable [CharZero F] {f : F[X]} (hf : Irreducible f) :
    f.Separable := by
  rw [separable_iff_derivative_ne_zero hf, Ne, ← degree_eq_bot, degree_derivative_eq]
  -- ⊢ ¬↑(natDegree f - 1) = ⊥
  · rintro ⟨⟩
    -- 🎉 no goals
  rw [pos_iff_ne_zero, Ne, natDegree_eq_zero_iff_degree_le_zero, degree_le_zero_iff]
  -- ⊢ ¬f = ↑C (coeff f 0)
  refine' fun hf1 => hf.not_unit _
  -- ⊢ IsUnit f
  rw [hf1, isUnit_C, isUnit_iff_ne_zero]
  -- ⊢ coeff f 0 ≠ 0
  intro hf2
  -- ⊢ False
  rw [hf2, C_0] at hf1
  -- ⊢ False
  exact absurd hf1 hf.ne_zero
  -- 🎉 no goals
#align irreducible.separable Irreducible.separable

end Field

end Polynomial

open Polynomial

section CommRing

variable (F K : Type*) [CommRing F] [Ring K] [Algebra F K]

-- TODO: refactor to allow transcendental extensions?
-- See: https://en.wikipedia.org/wiki/Separable_extension#Separability_of_transcendental_extensions
-- Note that right now a Galois extension (class `IsGalois`) is defined to be an extension which
-- is separable and normal, so if the definition of separable changes here at some point
-- to allow non-algebraic extensions, then the definition of `IsGalois` must also be changed.
/-- Typeclass for separable field extension: `K` is a separable field extension of `F` iff
the minimal polynomial of every `x : K` is separable.

We define this for general (commutative) rings and only assume `F` and `K` are fields if this
is needed for a proof.
-/
class IsSeparable : Prop where
  isIntegral' (x : K) : IsIntegral F x
  separable' (x : K) : (minpoly F x).Separable
#align is_separable IsSeparable

variable (F : Type*) {K : Type*} [CommRing F] [Ring K] [Algebra F K]

theorem IsSeparable.isIntegral [IsSeparable F K] : ∀ x : K, IsIntegral F x :=
  IsSeparable.isIntegral'
#align is_separable.is_integral IsSeparable.isIntegral

theorem IsSeparable.separable [IsSeparable F K] : ∀ x : K, (minpoly F x).Separable :=
  IsSeparable.separable'
#align is_separable.separable IsSeparable.separable

variable {F K : Type*} [CommRing F] [Ring K] [Algebra F K]

theorem isSeparable_iff : IsSeparable F K ↔ ∀ x : K, IsIntegral F x ∧ (minpoly F x).Separable :=
  ⟨fun _ x => ⟨IsSeparable.isIntegral F x, IsSeparable.separable F x⟩, fun h =>
    ⟨fun x => (h x).1, fun x => (h x).2⟩⟩
#align is_separable_iff isSeparable_iff

end CommRing

instance isSeparable_self (F : Type*) [Field F] : IsSeparable F F :=
  ⟨fun x => isIntegral_algebraMap,
   fun x => by
    rw [minpoly.eq_X_sub_C']
    -- ⊢ Separable (X - ↑C x)
    exact separable_X_sub_C⟩
    -- 🎉 no goals
#align is_separable_self isSeparable_self

-- See note [lower instance priority]
/-- A finite field extension in characteristic 0 is separable. -/
instance (priority := 100) IsSeparable.of_finite (F K : Type*) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [CharZero F] : IsSeparable F K :=
  have : ∀ x : K, IsIntegral F x := fun _x => Algebra.isIntegral_of_finite _ _ _
  ⟨this, fun x => (minpoly.irreducible (this x)).separable⟩
#align is_separable.of_finite IsSeparable.of_finite

section IsSeparableTower

variable (F K E : Type*) [Field F] [Field K] [Field E] [Algebra F K] [Algebra F E] [Algebra K E]
  [IsScalarTower F K E]

theorem isSeparable_tower_top_of_isSeparable [IsSeparable F E] : IsSeparable K E :=
  ⟨fun x => isIntegral_of_isScalarTower (IsSeparable.isIntegral F x), fun x =>
    (IsSeparable.separable F x).map.of_dvd (minpoly.dvd_map_of_isScalarTower _ _ _)⟩
#align is_separable_tower_top_of_is_separable isSeparable_tower_top_of_isSeparable

theorem isSeparable_tower_bot_of_isSeparable [h : IsSeparable F E] : IsSeparable F K :=
  isSeparable_iff.2 fun x => by
    refine'
      (isSeparable_iff.1 h (algebraMap K E x)).imp isIntegral_tower_bot_of_isIntegral_field
        fun hs => _
    obtain ⟨q, hq⟩ :=
      minpoly.dvd F x
        ((aeval_algebraMap_eq_zero_iff _ _ _).mp (minpoly.aeval F ((algebraMap K E) x)))
    rw [hq] at hs
    -- ⊢ Separable (minpoly F x)
    exact hs.of_mul_left
    -- 🎉 no goals
#align is_separable_tower_bot_of_is_separable isSeparable_tower_bot_of_isSeparable

variable {E}

theorem IsSeparable.of_algHom (E' : Type*) [Field E'] [Algebra F E'] (f : E →ₐ[F] E')
    [IsSeparable F E'] : IsSeparable F E := by
  letI : Algebra E E' := RingHom.toAlgebra f.toRingHom
  -- ⊢ IsSeparable F E
  haveI : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  -- ⊢ IsSeparable F E
  exact isSeparable_tower_bot_of_isSeparable F E E'
  -- 🎉 no goals
#align is_separable.of_alg_hom IsSeparable.of_algHom

end IsSeparableTower

section CardAlgHom

variable {R S T : Type*} [CommRing S]

variable {K L F : Type*} [Field K] [Field L] [Field F]

variable [Algebra K S] [Algebra K L]

theorem AlgHom.card_of_powerBasis (pb : PowerBasis K S) (h_sep : (minpoly K pb.gen).Separable)
    (h_splits : (minpoly K pb.gen).Splits (algebraMap K L)) :
    @Fintype.card (S →ₐ[K] L) (PowerBasis.AlgHom.fintype pb) = pb.dim := by
  let s := ((minpoly K pb.gen).map (algebraMap K L)).roots.toFinset
  -- ⊢ Fintype.card (S →ₐ[K] L) = pb.dim
  let _ := (PowerBasis.AlgHom.fintype pb : Fintype (S →ₐ[K] L))
  -- ⊢ Fintype.card (S →ₐ[K] L) = pb.dim
  rw [Fintype.card_congr pb.liftEquiv', Fintype.card_of_subtype s (fun x => Multiset.mem_toFinset),
    ← pb.natDegree_minpoly, natDegree_eq_card_roots h_splits, Multiset.toFinset_card_of_nodup]
  exact nodup_roots ((separable_map (algebraMap K L)).mpr h_sep)
  -- 🎉 no goals
#align alg_hom.card_of_power_basis AlgHom.card_of_powerBasis

end CardAlgHom
