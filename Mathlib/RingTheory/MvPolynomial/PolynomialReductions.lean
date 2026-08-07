/-
Copyright (c) 2026 Sanghyeok Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sanghyeok Park
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ScopedNS
public import Mathlib.Logic.Relation.NormalForm

/-!
# Polynomial reductions

This file defines one-step polynomial reduction with respect to a monomial
order and a set of multivariate polynomials. It proves termination of
reduction using the colexicographic order on supports, basic translation
lemmas, and local confluence results for singleton reductions.

## References

* [Becker and Weispfenning, *Gröbner bases*][Becker-Weispfenning1993]
-/

@[expose] public section

namespace Reduction
end Reduction

namespace Finset.Colex

open scoped symmDiff

variable {α : Type*}

/--
The characteristic finitely supported function of a finite set.

It sends elements of `s` to `1` and all other elements to `0`.
-/
private noncomputable abbrev char (s : Finset α) : α →₀ ℕ :=
  Finsupp.indicator s fun _ _ => (1 : ℕ)

private theorem mem_iff_of_not_mem_symmDiff
    {s t : Finset α} {a : α} [DecidableEq α]
    (ha : a ∉ s ∆ t) :
    a ∈ s ↔ a ∈ t := by
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t
  · exact ⟨fun _ => ht, fun _ => hs⟩
  · exfalso
    exact ha (by simp [Finset.mem_symmDiff, hs, ht])
  · exfalso
    exact ha (by simp [Finset.mem_symmDiff, hs, ht])
  · exact ⟨fun h => False.elim (hs h), fun h => False.elim (ht h)⟩

/--
If `s < t` in finite-set colex order, then the characteristic functions of
`s` and `t` are ordered by the corresponding finitely supported lex order
from larger indices to smaller indices.
-/
private theorem finsuppLex_of_toColex_lt_toColex
    {s t : Finset α} [LinearOrder α]
    (h : toColex s < toColex t) :
    Finsupp.Lex
      (fun x y : α => x > y)
      ((· < ·) : ℕ → ℕ → Prop)
      (char s)
      (char t) := by
  rcases (toColex_lt_toColex_iff_max'_mem).1 h with ⟨hst, hmax_mem_t⟩
  let a := (s ∆ t).max' (symmDiff_nonempty.2 hst)
  have haD : a ∈ s ∆ t := by
    exact Finset.max'_mem (s ∆ t) (symmDiff_nonempty.2 hst)
  have hat : a ∈ t := by
    exact hmax_mem_t
  have has : a ∉ s := by
    have hD := haD
    simpa only [mem_symmDiff, hat, not_true_eq_false, and_false, true_and, false_or] using hD
  rw [Finsupp.lex_def]
  refine ⟨a, ?_, ?_⟩
  · intro d hd
    have hd_notD : d ∉ s ∆ t := by
      intro hdD
      have hd_le_a : d ≤ a := by
        exact Finset.le_max' (s ∆ t) d hdD
      exact (not_lt_of_ge hd_le_a) hd
    have hdiff : d ∈ s ↔ d ∈ t :=
      mem_iff_of_not_mem_symmDiff hd_notD
    by_cases hds : d ∈ s
    · have hdt : d ∈ t := hdiff.mp hds
      simp only [char, Finsupp.indicator_apply, hds, ↓reduceDIte, hdt]
    · have hdt : d ∉ t := by
        intro hdt
        exact hds (hdiff.mpr hdt)
      simp only [char, Finsupp.indicator_apply, hds, ↓reduceDIte, hdt]
  · simp only [char, Finsupp.indicator_apply, has, ↓reduceDIte, hat, Order.lt_one_iff]

/--
The colexicographic order on finite subsets of a well-ordered type is
well-founded.
-/
theorem wellFounded
    {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    WellFounded ((· < ·) : Colex (Finset α) → Colex (Finset α) → Prop) := by
  haveI : Std.Trichotomous (fun x y : α => x > y) :=
    { trichotomous := by
        intro a b hab hba
        exact le_antisymm (le_of_not_gt hab) (le_of_not_gt hba) }
  have hlex :
      WellFounded
        (Finsupp.Lex
          (fun x y : α => x > y)
          ((· < ·) : ℕ → ℕ → Prop) :
            (α →₀ ℕ) → (α →₀ ℕ) → Prop) := by
    refine Finsupp.Lex.wellFounded'
      (r := fun x y : α => x > y)
      (s := ((· < ·) : ℕ → ℕ → Prop))
      ?hbot
      ?hs
      ?hr
    · intro n
      exact Nat.not_lt_zero n
    · exact (inferInstance : WellFoundedLT ℕ).wf
    · change WellFounded ((· < ·) : α → α → Prop)
      exact (inferInstance : WellFoundedLT α).wf
  exact
    (InvImage.wf
      (fun s : Colex (Finset α) => char (ofColex s))
      hlex).mono
      (by
        intro s t hst
        change
          Finsupp.Lex
            (fun x y : α => x > y)
            ((· < ·) : ℕ → ℕ → Prop)
            (char (ofColex s))
            (char (ofColex t))
        exact finsuppLex_of_toColex_lt_toColex
          (s := ofColex s)
          (t := ofColex t)
          (by simpa only [toColex_ofColex] using hst))

end Finset.Colex

namespace MonomialOrder

open MvPolynomial
open scoped MonomialOrder Reduction

variable {σ : Type*} (m : MonomialOrder σ)

section CommRing

variable {R : Type*} [CommRing R]

/--
Reduction of `f` by a polynomial `p` at the term `t`.

This means that `t` occurs in `f` and is divisible by the leading monomial of
`p`. More precisely, there is a monomial `s` such that
`s + m.degree p = t`, and a coefficient `c` such that the leading term of
`monomial s c * p` has the same coefficient as the term `t` of `f`.

The resulting polynomial `g` is obtained from `f` by subtracting this multiple
of `p`, so that the term `t` is eliminated.
-/
def ReducesToBy
    (p f g : MvPolynomial σ R) (t : σ →₀ ℕ) : Prop :=
  p ≠ 0 ∧
    t ∈ f.support ∧
      ∃ s : σ →₀ ℕ,
        s + m.degree p = t ∧
          ∃ c : R,
            c * m.leadingCoeff p = f.coeff t ∧
              g = f - monomial s c * p

/-- One-step reduction modulo a single polynomial `p`. -/
def ReducesToPoly (p f g : MvPolynomial σ R) : Prop :=
  ∃ t : σ →₀ ℕ, m.ReducesToBy p f g t

/-- One-step reduction modulo a set `P`. -/
def ReducesToSet (P : Set (MvPolynomial σ R)) (f g : MvPolynomial σ R) : Prop :=
  ∃ p ∈ P, m.ReducesToPoly p f g

/-- Reducibility modulo a single polynomial. -/
def Reducible (p f : MvPolynomial σ R) : Prop :=
  ∃ g, m.ReducesToPoly p f g

/-- Reducibility modulo a set. -/
def ReducibleSet (P : Set (MvPolynomial σ R)) (f : MvPolynomial σ R) : Prop :=
  ∃ g, m.ReducesToSet P f g

/--
One-step reduction modulo a set `P`.

The notation `f ⟶[m, P] g` means that `f` reduces to `g` in one step
modulo the set of polynomials `P`, with respect to the monomial order `m`.
-/
scoped[Reduction] notation:50 f:51 " ⟶[" m ", " P "] " g:51 =>
  MonomialOrder.ReducesToSet m P f g

/--
Finite reduction modulo a set `P`.

This is the reflexive-transitive closure of one-step reduction modulo `P`.
-/
scoped[Reduction] notation:50 f:51 " ⟶*[" m ", " P "] " g:51 =>
  Relation.ReflTransGen (MonomialOrder.ReducesToSet m P) f g

/--
Symmetric one-step reduction modulo a set `P`.
-/
scoped[Reduction] notation:50 f:51 " ⟷[" m ", " P "] " g:51 =>
  Relation.SymmGen (MonomialOrder.ReducesToSet m P) f g

/--
Equivalence closure generated by reduction modulo a set `P`.
-/
scoped[Reduction] notation:50 f:51 " ⟷*[" m ", " P "] " g:51 =>
  Relation.EqvGen (MonomialOrder.ReducesToSet m P) f g

/--
Joinability modulo a set `P`.

The notation `f ↓[m, P] g` means that `f` and `g` reduce to a common
polynomial by finite reductions modulo `P`.
-/
scoped[Reduction] notation:50 f:51 " ↓[" m ", " P "] " g:51 =>
  Relation.Join (Relation.ReflTransGen (MonomialOrder.ReducesToSet m P)) f g

namespace ReducesToPoly

/-- Normal form modulo a single polynomial. -/
abbrev NormalForm (p f : MvPolynomial σ R) : Prop :=
  Relation.IsNormalForm (m.ReducesToPoly p) f

/--
A polynomial is reducible modulo `p` exactly when `p` is nonzero and some
support exponent `t` satisfies `m.degree p ≤ t`, while `m.leadingCoeff p`
divides the corresponding coefficient `f.coeff t`.
-/
theorem reducible_iff_exists_degree_le_and_leadingCoeff_dvd
    (p f : MvPolynomial σ R) :
    m.Reducible p f ↔
      p ≠ 0 ∧
        ∃ t ∈ f.support,
          m.degree p ≤ t ∧
            m.leadingCoeff p ∣ f.coeff t := by
  constructor
  · rintro ⟨g, t, hp, ht, s, hs, c, hc, hg⟩
    refine ⟨hp, t, ht, ?_, ?_⟩
    · rw [← hs]
      exact self_le_add_left _ _
    · exact ⟨c, by simpa only [mul_comm] using hc.symm⟩
  · rintro ⟨hp, t, ht, hp_le_t, hp_dvd⟩
    rcases le_iff_exists_add.mp hp_le_t with ⟨s, hs⟩
    rcases hp_dvd with ⟨c, hc⟩
    have hs' : s + m.degree p = t := by
      simpa only [add_comm] using hs.symm
    refine ⟨f - monomial s c * p, t, hp, ht, s, hs', c, ?_, rfl⟩
    simpa only [mul_comm] using hc.symm

/--
Lemma 5.20(i), unit-leading-coefficient version.

If the leading coefficient of `p` is a unit, then reducibility modulo `p`
is equivalent to divisibility of some term of `f` by the leading monomial
of `p`.
-/
theorem reducible_iff_exists_degree_le_of_isUnit
    (p f : MvPolynomial σ R)
    (hLC : IsUnit (m.leadingCoeff p)) :
    m.Reducible p f ↔
      p ≠ 0 ∧
        ∃ t ∈ f.support,
          m.degree p ≤ t := by
  constructor
  · intro h
    rcases
      (MonomialOrder.ReducesToPoly.reducible_iff_exists_degree_le_and_leadingCoeff_dvd
        m p f).1 h with ⟨hp, t, ht, hp_le_t, _hp_dvd⟩
    exact ⟨hp, t, ht, hp_le_t⟩
  · rintro ⟨hp, t, ht, hp_le_t⟩
    exact
      (MonomialOrder.ReducesToPoly.reducible_iff_exists_degree_le_and_leadingCoeff_dvd
        m p f).2 ⟨hp, t, ht, hp_le_t, hLC.dvd⟩

end ReducesToPoly

private lemma isUnit_leadingCoeff_of_mem_ne
    {P : Set (MvPolynomial σ R)}
    (hP₀ : ∀ p ∈ P, IsUnit (m.leadingCoeff p) ∨ p = 0)
    {p : MvPolynomial σ R}
    (hpP : p ∈ P)
    (hp : p ≠ 0) :
    IsUnit (m.leadingCoeff p) :=
  (hP₀ p hpP).resolve_right hp

namespace ReducesToSet

/-- Reflexive-transitive closure of one-step reduction modulo `P`. -/
abbrev ReflTransGen (P : Set (MvPolynomial σ R)) :
    MvPolynomial σ R → MvPolynomial σ R → Prop :=
  fun f g => f ⟶*[m, P] g

/-- Equivalence closure generated by one-step reduction modulo `P`. -/
abbrev EqvGen (P : Set (MvPolynomial σ R)) :
    MvPolynomial σ R → MvPolynomial σ R → Prop :=
  fun f g => f ⟷*[m, P] g

/-- Joinability modulo `P`. -/
abbrev Join (P : Set (MvPolynomial σ R)) :
    MvPolynomial σ R → MvPolynomial σ R → Prop :=
  fun f g => f ↓[m, P] g

/-- Normal form modulo a set `P`. -/
abbrev NormalForm (P : Set (MvPolynomial σ R)) (f : MvPolynomial σ R) : Prop :=
  Relation.IsNormalForm (m.ReducesToSet P) f

/--
Without assumptions on leading coefficients, a polynomial is in normal form
exactly when there is no support exponent `t` and nonzero reducer `p` such that
`m.degree p ≤ t` and `m.leadingCoeff p ∣ f.coeff t`.
-/
theorem normalForm_iff_forall_not_degree_le_and_dvd
    (P : Set (MvPolynomial σ R))
    {f : MvPolynomial σ R} :
    Relation.IsNormalForm (m.ReducesToSet P) f ↔
      ∀ t ∈ f.support, ∀ p ∈ P, p ≠ 0 →
        ¬ (m.degree p ≤ t ∧ m.leadingCoeff p ∣ f.coeff t) := by
  constructor
  · intro hnf t ht p hpP hp_ne ⟨hp_le_t, hp_dvd⟩
    rcases le_iff_exists_add.mp hp_le_t with ⟨s, hs⟩
    rcases hp_dvd with ⟨c, hc⟩
    have hs' : s + m.degree p = t := by
      simpa only [add_comm] using hs.symm
    apply hnf (f - monomial s c * p)
    refine ⟨p, hpP, t, hp_ne, ht, s, hs', c, ?_, rfl⟩
    simpa only [mul_comm] using hc.symm
  · intro hsupport g hfg
    rcases hfg with ⟨p, hpP, t, hp_ne, ht, s, hs, c, hc, _hg⟩
    apply hsupport t ht p hpP hp_ne
    constructor
    · rw [← hs]
      exact self_le_add_left _ _
    · exact ⟨c, by simpa only [mul_comm] using hc.symm⟩

/--
If every nonzero reducer has unit leading coefficient, normal forms are exactly
the polynomials whose support terms are not divisible by the leading monomial
of any nonzero reducer.

This is the unit-leading-coefficient specialization of
`normalForm_iff_forall_not_degree_le_and_dvd`.
-/
theorem normalForm_iff_forall_not_degree_le
    (P : Set (MvPolynomial σ R))
    (hP₀ : ∀ p ∈ P, IsUnit (m.leadingCoeff p) ∨ p = 0)
    {f : MvPolynomial σ R} :
    Relation.IsNormalForm (m.ReducesToSet P) f ↔
      ∀ t ∈ f.support, ∀ p ∈ P, p ≠ 0 → ¬ m.degree p ≤ t := by
  rw [normalForm_iff_forall_not_degree_le_and_dvd]
  constructor
  · intro hnf t ht p hpP hp_ne hp_le_t
    have hp_unit : IsUnit (m.leadingCoeff p) :=
      isUnit_leadingCoeff_of_mem_ne m hP₀ hpP hp_ne
    exact hnf t ht p hpP hp_ne ⟨hp_le_t, hp_unit.dvd⟩
  · intro hsupport t ht p hpP hp_ne hred
    exact hsupport t ht p hpP hp_ne hred.1

end ReducesToSet

/--
The strict order on polynomials induced from the colex order on finite supports.

The support of a polynomial is transported to the synonym type `m.syn` using
the monomial order equivalence `m.toSyn`, and then compared by the colex
order on finite subsets.
-/
def supportColexLt (f g : MvPolynomial σ R) : Prop :=
  letI : LinearOrder m.syn := m.linearOrderSyn
  toColex (f.support.image m.toSyn) < toColex (g.support.image m.toSyn)

/--
The support-colex order on polynomials is well-founded.
-/
theorem supportColexLt_wellFounded :
    WellFounded
      (m.supportColexLt : MvPolynomial σ R → MvPolynomial σ R → Prop) := by
  letI : LinearOrder m.syn := m.linearOrderSyn
  haveI : WellFoundedLT m.syn := m.wellFoundedLT_syn
  exact
    InvImage.wf
      (fun f : MvPolynomial σ R => toColex (f.support.image m.toSyn))
      (Finset.Colex.wellFounded (α := m.syn))

namespace ReducesToPoly

/--
In a one-step reduction eliminating the term `t`, the coefficient of `t`
in the reduced polynomial is zero.
-/
lemma coeff_eq_zero_of_reducesToBy
    {p f g : MvPolynomial σ R} {t s : σ →₀ ℕ} {c : R}
    (_hp : p ≠ 0)
    (_ht : t ∈ f.support)
    (hs : s + m.degree p = t)
    (hc : c * m.leadingCoeff p = f.coeff t)
    (hg : g = f - monomial s c * p) :
    g.coeff t = 0 := by
  rw [hg, coeff_sub]
  have hcoeff :
      (monomial s c * p).coeff t = f.coeff t := by
    rw [← hs]
    simp only [coeff_monomial_mul]
    rw [← hs] at hc
    simpa only [leadingCoeff] using hc
  rw [hcoeff, sub_self]

/--
If `d` is strictly larger than the term `t` being reduced, then its
coefficient is unchanged by the one-step reduction.
-/
lemma coeff_eq_of_reduced_term_lt
    {p f g : MvPolynomial σ R} {t s d : σ →₀ ℕ} {c : R}
    (_hp : p ≠ 0)
    (hs : s + m.degree p = t)
    (hg : g = f - monomial s c * p)
    (hd : m.toSyn t < m.toSyn d) :
    g.coeff d = f.coeff d := by
  rw [hg, coeff_sub]
  suffices hzero : (monomial s c * p).coeff d = 0 by
    rw [hzero, sub_zero]
  rw [← notMem_support_iff]
  intro hdprod
  have hd_le_prod :
      m.toSyn d ≤ m.toSyn (m.degree (monomial s c * p)) :=
    m.le_degree hdprod
  have hmul :
      m.toSyn (m.degree (monomial s c * p)) ≤
        m.toSyn (m.degree (monomial s c) + m.degree p) :=
    m.degree_mul_le
  have hmon :
      m.toSyn (m.degree (monomial s c)) ≤ m.toSyn s :=
    m.degree_monomial_le c
  have hmon_add :
      m.toSyn (m.degree (monomial s c) + m.degree p) ≤
        m.toSyn (s + m.degree p) := by
    simp only [map_add]
    exact add_le_add_left hmon (m.toSyn (m.degree p))
  have hd_le_t : m.toSyn d ≤ m.toSyn t := by
    exact le_trans hd_le_prod (le_trans hmul (by simpa only [map_add, hs] using hmon_add))
  exact not_lt_of_ge hd_le_t hd

/--
Lemma 5.20(iv), single-polynomial form.

Every one-step reduction modulo a single polynomial strictly decreases the
support-colex order.
-/
theorem supportColexLt
    {p f g : MvPolynomial σ R}
    (h : m.ReducesToPoly p f g) :
    m.supportColexLt g f := by
  rcases h with ⟨t, hp, ht, s, hs, c, hc, hg⟩
  unfold MonomialOrder.supportColexLt
  letI : LinearOrder m.syn := m.linearOrderSyn
  rw [Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt]
  refine ⟨m.toSyn t, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  · intro ht_in_g
    rcases Finset.mem_image.mp ht_in_g with ⟨d, hdg, hdt⟩
    have hdt' : d = t :=
      m.toSyn.injective hdt
    subst d
    have hcoeff0 : g.coeff t = 0 :=
      coeff_eq_zero_of_reducesToBy m hp ht hs hc hg
    exact (MvPolynomial.mem_support_iff.mp hdg) hcoeff0
  · intro b hb_g hb_not_f
    rcases Finset.mem_image.mp hb_g with ⟨d, hdg, rfl⟩
    have hd_not_f : d ∉ f.support := by
      intro hdf
      exact hb_not_f (Finset.mem_image.mpr ⟨d, hdf, rfl⟩)
    have hnot_gt : ¬ m.toSyn t < m.toSyn d := by
      intro htd
      have hcoeff : g.coeff d = f.coeff d :=
        coeff_eq_of_reduced_term_lt m hp hs hg htd
      have hdf : d ∈ f.support := by
        rw [MvPolynomial.mem_support_iff]
        rw [← hcoeff]
        exact MvPolynomial.mem_support_iff.mp hdg
      exact hd_not_f hdf
    have hne : m.toSyn d ≠ m.toSyn t := by
      intro hdt
      have hdt' : d = t :=
        m.toSyn.injective hdt
      subst d
      exact hb_not_f (Finset.mem_image.mpr ⟨t, ht, rfl⟩)
    exact lt_of_le_of_ne (le_of_not_gt hnot_gt) hne

end ReducesToPoly

namespace ReducesToSet

theorem supportColexLt
    (P : Set (MvPolynomial σ R))
    {f g : MvPolynomial σ R}
    (h : f ⟶[m, P] g) :
    m.supportColexLt g f := by
  rcases h with ⟨p, _hpP, hpfg⟩
  exact ReducesToPoly.supportColexLt m hpfg

theorem wellFounded
    (P : Set (MvPolynomial σ R)) :
    WellFounded (flip (m.ReducesToSet P)) :=
  m.supportColexLt_wellFounded.mono
    (by
      intro f g h
      exact supportColexLt m P h)

theorem asymm
    (P : Set (MvPolynomial σ R)) :
    Std.Asymm (m.ReducesToSet P) :=
  ⟨fun a b hab hba => (wellFounded m P).asymmetric a b hba hab⟩

end ReducesToSet

/--
Lemma 5.24(ii), single-polynomial version.

If `f` reduces to `g` modulo a single polynomial `p`, then multiplying both
sides by a monomial preserves the one-step reduction.
-/
theorem monomial_mul_reducesToPoly
    (u : σ →₀ ℕ) {p f g : MvPolynomial σ R}
    (h : m.ReducesToPoly p f g) :
    m.ReducesToPoly p
      (monomial u (1 : R) * f)
      (monomial u (1 : R) * g) := by
  rcases h with ⟨t, hp, ht, s, hs, c, hc, hg⟩
  refine ⟨u + t, hp, ?_, u + s, ?_, c, ?_, ?_⟩
  · rw [MvPolynomial.mem_support_iff] at ht ⊢
    simpa only [coeff_monomial_mul, one_mul] using ht
  · rw [add_assoc, hs]
  · have hcoeff :
        (monomial u (1 : R) * f).coeff (u + t) = f.coeff t := by
      rw [coeff_monomial_mul, one_mul]
    simpa only [hcoeff] using hc
  · calc
      monomial u (1 : R) * g
          = monomial u (1 : R) *
              (f - monomial s c * p) := by
                rw [hg]
      _ = monomial u (1 : R) * f
            - (monomial u (1 : R) * monomial s c) * p := by
                ring
      _ = monomial u (1 : R) * f
            - monomial (u + s) c * p := by
                rw [monomial_mul, one_mul]

/--
If a polynomial has degree zero, then deleting its leading term gives zero.
-/
lemma subLTerm_eq_zero_of_degree_eq_zero
    {h : MvPolynomial σ R}
    (hdeg : m.degree h = 0) :
    m.subLTerm h = 0 := by
  rw [MonomialOrder.subLTerm, sub_eq_zero]
  nth_rewrite 1 [eq_C_of_degree_eq_zero hdeg, hdeg]
  rw [monomial_zero']

section RegularLeadingCoeff

/--
A product `h * f` reduces in one step to `(m.subLTerm h) * f`
modulo `P`, provided `f ∈ P`, `h ≠ 0`, and the leading coefficient
of `f` is a non-zero-divisor.
-/
lemma mul_mem_reducesTo_subLTerm_mul
    (P : Set (MvPolynomial σ R))
    {f h : MvPolynomial σ R}
    (hfP : f ∈ P)
    (hLCf : m.leadingCoeff f ∈ nonZeroDivisors R)
    (hh : h ≠ 0) :
    (h * f) ⟶[m, P] m.subLTerm h * f := by
  have hlch : m.leadingCoeff h ≠ 0 := by
    simpa only [ne_eq, leadingCoeff_eq_zero_iff] using hh
  have hf : f ≠ 0 := by
    intro hf0
    have hLCf0 : m.leadingCoeff f = 0 := by
      simpa only [leadingCoeff_eq_zero_iff] using hf0
    have hzero : m.leadingCoeff f * m.leadingCoeff h = 0 := by
      rw [hLCf0, zero_mul]
    have hlch0 : m.leadingCoeff h = 0 :=
      (mul_left_mem_nonZeroDivisors_eq_zero_iff hLCf).1 hzero
    exact hlch hlch0
  refine
    ⟨f, hfP, m.degree h + m.degree f, hf, ?_,
      m.degree h, rfl, m.leadingCoeff h, ?_, ?_⟩
  · -- Show that the chosen term occurs in `(h * f).support`.
    rw [MvPolynomial.mem_support_iff]
    have hcoeff :
        (h * f).coeff (m.degree h + m.degree f)
          = m.leadingCoeff h * m.leadingCoeff f := by
      rw [coeff_mul_of_degree_add (m := m)]
    rw [hcoeff]
    intro hzero
    have hzero' : m.leadingCoeff f * m.leadingCoeff h = 0 := by
      simpa only [mul_comm] using hzero
    have hlch0 : m.leadingCoeff h = 0 :=
      (mul_left_mem_nonZeroDivisors_eq_zero_iff hLCf).1 hzero'
    exact hlch hlch0
  · -- Coefficient divisibility condition.
    rw [coeff_mul_of_degree_add (m := m)]
  · -- The resulting polynomial is exactly `m.subLTerm h * f`.
    rw [subLTerm]
    ring

/--
Lemma 5.24(i), regular-leading-coefficient version.

If `f ∈ P` and the leading coefficient of `f` is a non-zero-divisor whenever
`f` is nonzero, then every polynomial multiple of `f` reduces to zero modulo `P`.
-/
theorem mul_mem_reflTransGen_zero
    (P : Set (MvPolynomial σ R))
    {f h : MvPolynomial σ R}
    (hfP : f ∈ P)
    (hLCf : f ≠ 0 →
      m.leadingCoeff f ∈ nonZeroDivisors R) :
  (h * f) ⟶*[m, P] 0 := by
  by_cases hf : f = 0
  · subst f
    simpa only [mul_zero] using (Relation.ReflTransGen.refl : (0 : MvPolynomial σ R) ⟶*[m, P] 0)
  let r : MvPolynomial σ R → MvPolynomial σ R → Prop :=
    fun a b => m.degree a ≺[m] m.degree b
  have hrwf : WellFounded r := by
    unfold r
    exact InvImage.wf
      (fun h : MvPolynomial σ R => m.toSyn (m.degree h))
      m.wellFoundedLT_syn.wf
  revert h
  intro h
  refine hrwf.induction
    (C := fun h : MvPolynomial σ R => h * f ⟶*[m, P] 0)
    h
    ?_
  intro h ih
  by_cases hh : h = 0
  · subst h
    simpa only [zero_mul] using (Relation.ReflTransGen.refl : (0 : MvPolynomial σ R) ⟶*[m, P] 0)
  have hstep : (h * f) ⟶[m, P] m.subLTerm h * f :=
    mul_mem_reducesTo_subLTerm_mul m P hfP (hLCf hf) hh
  by_cases hdeg : m.degree h = 0
  · have hsub : m.subLTerm h = 0 :=
      subLTerm_eq_zero_of_degree_eq_zero m hdeg
    simpa only [hsub, zero_mul] using Relation.ReflTransGen.single hstep
  · have hlt : r (m.subLTerm h) h := by
      unfold r
      exact m.degree_sub_LTerm_lt hdeg
    exact (Relation.ReflTransGen.single hstep).trans
      (ih (m.subLTerm h) hlt)

end RegularLeadingCoeff

section UnitLeadingCoeffTranslation

/-- Helper for the Translation Lemma: single-step translation. -/
private lemma translation_step
    (P : Set (MvPolynomial σ R))
    (hP₀ : ∀ p ∈ P, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (f g h h₁ : MvPolynomial σ R)
    (hfgh : f - g = h)
    (hh₁ : h ⟶[m, P] h₁) :
    ∃ f₁ g₁ : MvPolynomial σ R,
      f₁ - g₁ = h₁ ∧
      f ⟶*[m, P] f₁ ∧
      g ⟶*[m, P] g₁ := by
  obtain ⟨p, hpP, t, hp_ne, _ht_supp, s, hs, c, hc, hh₁_eq⟩ := hh₁
  have hp_unit : IsUnit (m.leadingCoeff p) :=
    isUnit_leadingCoeff_of_mem_ne m hP₀ hpP hp_ne
  rcases hp_unit with ⟨u, hu⟩
  let c₁ : R := ((u⁻¹ : Rˣ) : R) * f.coeff t
  let c₂ : R := ((u⁻¹ : Rˣ) : R) * g.coeff t
  have unit_inv_mul_lc (a : R) :
      (((u⁻¹ : Rˣ) : R) * a) * m.leadingCoeff p = a := by
    rw [← hu]
    calc
      (((u⁻¹ : Rˣ) : R) * a) * (u : R)
          = (((u⁻¹ : Rˣ) : R) * (u : R)) * a := by
              ring
      _ = a := by
              rw [Units.inv_mul, one_mul]
  have hc₁ : c₁ * m.leadingCoeff p = f.coeff t := by
    unfold c₁
    exact unit_inv_mul_lc (f.coeff t)
  have hc₂ : c₂ * m.leadingCoeff p = g.coeff t := by
    unfold c₂
    exact unit_inv_mul_lc (g.coeff t)
  have hc_diff : f.coeff t - g.coeff t = h.coeff t := by
    rw [← hfgh, MvPolynomial.coeff_sub]
  have hc_eq : c₁ - c₂ = c := by
    have hc' : c = ((u⁻¹ : Rˣ) : R) * h.coeff t := by
      rw [← hc, ← hu]
      rw [mul_comm, mul_assoc, Units.mul_inv, mul_one]
    rw [hc']
    unfold c₁ c₂
    rw [← hc_diff]
    ring
  refine
    ⟨f - monomial s c₁ * p,
      g - monomial s c₂ * p,
      ?_, ?_, ?_⟩
  · have hmono :
        (monomial s c₁ - monomial s c₂ : MvPolynomial σ R)
          = monomial s c := by
      rw [← map_sub, hc_eq]
    rw [hh₁_eq]
    linear_combination hfgh - p * hmono
  · by_cases hc₁0 : f.coeff t = 0
    · have hzero : (monomial s c₁ : MvPolynomial σ R) = 0 := by
        unfold c₁
        rw [hc₁0, mul_zero, monomial_zero]
      rw [hzero, zero_mul, sub_zero]
    · apply Relation.ReflTransGen.single
      exact
        ⟨p, hpP, t, hp_ne,
          MvPolynomial.mem_support_iff.mpr hc₁0,
          s, hs, c₁, hc₁, rfl⟩
  · by_cases hc₂0 : g.coeff t = 0
    · have hzero : (monomial s c₂ : MvPolynomial σ R) = 0 := by
        unfold c₂
        rw [hc₂0, mul_zero, monomial_zero]
      rw [hzero, zero_mul, sub_zero]
    · apply Relation.ReflTransGen.single
      exact
        ⟨p, hpP, t, hp_ne,
          MvPolynomial.mem_support_iff.mpr hc₂0,
          s, hs, c₂, hc₂, rfl⟩

/-- Translation Lemma, part (i). -/
theorem translation_reflTransGen
    (P : Set (MvPolynomial σ R))
    (hP₀ : ∀ p ∈ P, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (f g h h₁ : MvPolynomial σ R)
    (hfgh : f - g = h)
    (hh₁ : h ⟶*[m, P] h₁) :
    ∃ f₁ g₁ : MvPolynomial σ R,
      f₁ - g₁ = h₁ ∧
      f ⟶*[m, P] f₁ ∧
      g ⟶*[m, P] g₁ := by
  induction hh₁ with
  | refl =>
      exact ⟨f, g, hfgh, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _hstep hlast ih =>
      obtain ⟨f₂, g₂, hsub₂, hf₂, hg₂⟩ := ih
      obtain ⟨f₁, g₁, hsub₁, hf₂f₁, hg₂g₁⟩ :=
        m.translation_step P hP₀ f₂ g₂ _ _ hsub₂ hlast
      exact ⟨f₁, g₁, hsub₁, hf₂.trans hf₂f₁, hg₂.trans hg₂g₁⟩

/-- Translation Lemma, part (ii): joinability. -/
theorem join_of_sub_reflTransGen_zero
    (P : Set (MvPolynomial σ R))
    (hP₀ : ∀ p ∈ P, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (f g : MvPolynomial σ R)
    (hfg : f - g ⟶*[m, P] 0) :
    f ↓[m, P] g := by
  obtain ⟨f₁, g₁, hsub, hf, hg⟩ :=
    m.translation_reflTransGen P hP₀ f g (f - g) 0 rfl hfg
  refine ⟨f₁, hf, ?_⟩
  have hgf : g₁ = f₁ := (sub_eq_zero.mp hsub).symm
  rw [hgf] at hg
  exact hg

/-- Translation Lemma, part (ii): equivalence closure. -/
theorem eqvGen_of_sub_reflTransGen_zero
    (P : Set (MvPolynomial σ R))
    (hP₀ : ∀ p ∈ P, IsUnit (m.leadingCoeff p) ∨ p = 0)
    (f g : MvPolynomial σ R)
    (hfg : f - g ⟶*[m, P] 0) :
    f ⟷*[m, P] g := by
  exact Relation.Join.to_eqvGen
    (m.join_of_sub_reflTransGen_zero P hP₀ f g hfg)

end UnitLeadingCoeffTranslation

/-- One-step reduction does not increase degree. -/
theorem degree_le_of_reducesToSet
    (B : Set (MvPolynomial σ R))
    {f g : MvPolynomial σ R}
    (h : f ⟶[m, B] g) :
    m.degree g ≼[m] m.degree f := by
  rcases h with ⟨p, _hpB, t, _hp_ne, ht, s, hs, c, _hc, hg⟩
  have ht_le_f : m.toSyn t ≤ m.toSyn (m.degree f) :=
    m.le_degree ht
  have hmon_le : m.toSyn (m.degree (monomial s c : MvPolynomial σ R)) ≤ m.toSyn s :=
    m.degree_monomial_le c
  have hprod_le_t :
      m.toSyn (m.degree (monomial s c * p)) ≤ m.toSyn t := by
    have hmul :
        m.toSyn (m.degree (monomial s c * p)) ≤
          m.toSyn (m.degree (monomial s c : MvPolynomial σ R) + m.degree p) :=
      m.degree_mul_le
    have hmon_add :
        m.toSyn (m.degree (monomial s c : MvPolynomial σ R) + m.degree p) ≤
          m.toSyn (s + m.degree p) := by
      simp only [map_add]
      exact add_le_add_left hmon_le (m.toSyn (m.degree p))
    exact le_trans hmul (by simpa only [map_add, hs] using hmon_add)
  have hprod_le_f :
      m.toSyn (m.degree (monomial s c * p)) ≤ m.toSyn (m.degree f) :=
    le_trans hprod_le_t ht_le_f
  have hsub :
      m.toSyn (m.degree g) ≤
        m.toSyn (m.degree f) ⊔ m.toSyn (m.degree (monomial s c * p)) := by
    simpa only [hg, le_sup_iff] using (m.degree_sub_le (f := f) (g := monomial s c * p))
  exact le_trans hsub (sup_le le_rfl hprod_le_f)

/-- Finite reduction does not increase degree. -/
theorem degree_le_of_reflTransGen
    (B : Set (MvPolynomial σ R))
    {f r : MvPolynomial σ R}
    (h : f ⟶*[m, B] r) :
    m.degree r ≼[m] m.degree f := by
  induction h with
  | refl =>
      exact le_rfl
  | tail _hfg hstep ih =>
      exact le_trans (degree_le_of_reducesToSet m B hstep) ih

/--
One-step reduction gives an explicit one-term quotient representation.

This is the first bridge from the relation-theoretic reduction API to the
remainder-style statement used by the division theorem: if `f` reduces to `g`
modulo `B`, then `f` is a finite linear combination of elements of `B`, plus
`g`.
-/
theorem exists_linearCombination_of_reducesToSet
    (B : Set (MvPolynomial σ R))
    {f g : MvPolynomial σ R}
    (h : f ⟶[m, B] g) :
    ∃ q : B →₀ MvPolynomial σ R,
      f =
        Finsupp.linearCombination
          (MvPolynomial σ R)
          (fun b : B => (b : MvPolynomial σ R))
          q + g := by
  rcases h with ⟨p, hpB, _t, _hp_ne, _ht, s, _hs, c, _hc, hg⟩
  refine ⟨Finsupp.single ⟨p, hpB⟩ (monomial s c), ?_⟩
  rw [Finsupp.linearCombination_single]
  rw [hg]
  ring

/--
One-step reduction gives a quotient representation satisfying the product
degree bound used by `MonomialOrder.div_set`.
-/
theorem exists_linearCombination_of_reducesToSet_with_degree_bound
    (B : Set (MvPolynomial σ R))
    {f g : MvPolynomial σ R}
    (h : f ⟶[m, B] g) :
    ∃ q : B →₀ MvPolynomial σ R,
      f =
        Finsupp.linearCombination
          (MvPolynomial σ R)
          (fun b : B => (b : MvPolynomial σ R))
          q + g ∧
        ∀ b : B, m.degree ((b : MvPolynomial σ R) * q b) ≼[m] m.degree f := by
  rcases h with ⟨p, hpB, t, _hp_ne, ht, s, hs, c, _hc, hg⟩
  let b₀ : B := ⟨p, hpB⟩
  let q : B →₀ MvPolynomial σ R := Finsupp.single b₀ (monomial s c)
  refine ⟨q, ?_, ?_⟩
  · unfold q b₀
    rw [Finsupp.linearCombination_single]
    rw [hg]
    ring
  · intro b
    by_cases hb : b = b₀
    · subst b
      have ht_le_f : m.toSyn t ≤ m.toSyn (m.degree f) :=
        m.le_degree ht
      have hmon_le : m.toSyn (m.degree (monomial s c : MvPolynomial σ R)) ≤ m.toSyn s :=
        m.degree_monomial_le c
      have hprod_le_t :
          m.toSyn (m.degree ((p : MvPolynomial σ R) * monomial s c)) ≤ m.toSyn t := by
        have hmul :
            m.toSyn (m.degree ((p : MvPolynomial σ R) * monomial s c)) ≤
              m.toSyn (m.degree p + m.degree (monomial s c : MvPolynomial σ R)) :=
          m.degree_mul_le
        have hmon_add :
            m.toSyn (m.degree p + m.degree (monomial s c : MvPolynomial σ R)) ≤
              m.toSyn (m.degree p + s) := by
          simp only [map_add]
          exact add_le_add_right hmon_le (m.toSyn (m.degree p))
        exact le_trans hmul (by simpa only [map_add, add_comm, hs] using hmon_add)
      simpa only [Finsupp.single_eq_same, q] using le_trans hprod_le_t ht_le_f
    · have hzero :
          ((b : MvPolynomial σ R) * q b) = 0 := by
        simp only [ne_eq, hb, not_false_eq_true, Finsupp.single_eq_of_ne, mul_zero, q]
      rw [hzero, m.degree_zero]
      simpa only [map_zero] using MonomialOrder.zero_le m (m.toSyn (m.degree f))

/--
Finite reduction gives an explicit quotient representation.

If `f ⟶*[m, B] r`, then `f` is a finite linear combination of elements of
`B`, plus the final reduct `r`.
-/
theorem exists_linearCombination_of_reflTransGen
    (B : Set (MvPolynomial σ R))
    {f r : MvPolynomial σ R}
    (h : f ⟶*[m, B] r) :
    ∃ q : B →₀ MvPolynomial σ R,
      f =
        Finsupp.linearCombination
          (MvPolynomial σ R)
          (fun b : B => (b : MvPolynomial σ R))
          q + r := by
  induction h with
  | refl =>
      refine ⟨0, ?_⟩
      rw [map_zero, zero_add]
  | tail _hfg hstep ih =>
      rcases ih with ⟨q₁, hq₁⟩
      rcases exists_linearCombination_of_reducesToSet m B hstep with
        ⟨q₂, hq₂⟩
      refine ⟨q₁ + q₂, ?_⟩
      rw [hq₁, hq₂, map_add]
      ring

/--
Finite reduction gives a quotient representation satisfying the product
degree bound used by `MonomialOrder.div_set`.
-/
theorem exists_linearCombination_of_reflTransGen_with_degree_bound
    (B : Set (MvPolynomial σ R))
    {f r : MvPolynomial σ R}
    (h : f ⟶*[m, B] r) :
    ∃ q : B →₀ MvPolynomial σ R,
      f =
        Finsupp.linearCombination
          (MvPolynomial σ R)
          (fun b : B => (b : MvPolynomial σ R))
          q + r ∧
        ∀ b : B, m.degree ((b : MvPolynomial σ R) * q b) ≼[m] m.degree f := by
  induction h with
  | refl =>
      refine ⟨0, ?_, ?_⟩
      · rw [map_zero, zero_add]
      · intro b
        rw [Finsupp.coe_zero, Pi.zero_apply, mul_zero, m.degree_zero]
        simpa only [map_zero] using MonomialOrder.zero_le m (m.toSyn (m.degree f))
  | tail hfg hstep ih =>
      rcases ih with ⟨q₁, hq₁, hdeg₁⟩
      rcases exists_linearCombination_of_reducesToSet_with_degree_bound m B hstep with
        ⟨q₂, hq₂, hdeg₂⟩
      refine ⟨q₁ + q₂, ?_, ?_⟩
      · rw [hq₁, hq₂, map_add]
        ring
      · intro b
        rw [Finsupp.coe_add, Pi.add_apply, mul_add]
        apply le_trans m.degree_add_le
        apply sup_le
        · exact hdeg₁ b
        · exact le_trans (hdeg₂ b) (degree_le_of_reflTransGen m B hfg)

/--
If `f` reduces to `g` in one step modulo `P`, then `f - g` belongs to
the ideal generated by `P`.
-/
theorem sub_mem_span_of_reducesToSet
    (P : Set (MvPolynomial σ R))
    {f g : MvPolynomial σ R}
    (h : f ⟶[m, P] g) :
    f - g ∈ Ideal.span P := by
  rcases h with ⟨p, hpP, t, hp_ne, ht, s, hs, c, hc, hg⟩
  have hpSpan : p ∈ Ideal.span P :=
    Ideal.subset_span hpP
  rw [hg]
  have hsub :
      f - (f - monomial s c * p) = monomial s c * p := by
    ring
  rw [hsub]
  exact Ideal.mul_mem_left (Ideal.span P) (monomial s c) hpSpan

theorem sub_mem_span_of_reflTransGen
    (P : Set (MvPolynomial σ R))
    {f g : MvPolynomial σ R}
    (h : f ⟶*[m, P] g) :
    f - g ∈ Ideal.span P := by
  induction h with
  | refl =>
      simp only [sub_self, zero_mem]
  | tail hfg hstep ih =>
      have hstep' :
          _ - _ ∈ Ideal.span P :=
        sub_mem_span_of_reducesToSet m P hstep
      have hadd :
          (_ - _) + (_ - _) ∈ Ideal.span P :=
        Ideal.add_mem (Ideal.span P) ih hstep'
      rw [sub_add_sub_cancel] at hadd
      exact hadd

theorem sub_mem_span_of_eqvGen
    (P : Set (MvPolynomial σ R))
    {f g : MvPolynomial σ R}
    (h : f ⟷*[m, P] g) :
    f - g ∈ Ideal.span P := by
  induction h with
  | refl x =>
      simp
  | rel x y hxy =>
      exact sub_mem_span_of_reducesToSet m P hxy
  | symm x y hxy ih =>
      have hneg : -(x - y) ∈ Ideal.span P := by
        rw [Ideal.neg_mem_iff]
        exact ih
      simpa only [neg_sub] using hneg
  | trans x y z hxy hyz ihxy ihyz =>
      have hadd : (x - y) + (y - z) ∈ Ideal.span P :=
        Ideal.add_mem (Ideal.span P) ihxy ihyz
      have hsum : (x - y) + (y - z) = x - z := by
        ring
      simpa only [hsum] using hadd

theorem mem_span_of_reflTransGen_zero
    (P : Set (MvPolynomial σ R))
    {f : MvPolynomial σ R}
    (h : f ⟶*[m, P] 0) :
    f ∈ Ideal.span P := by
  have hsub : f - 0 ∈ Ideal.span P :=
    sub_mem_span_of_reflTransGen m P h
  simpa only [sub_zero] using hsub

section UnitLeadingCoeffIdealEquivalence

/--
A polynomial multiple of an element of `P` can be removed up to the
equivalence closure generated by reduction modulo `P`.
-/
theorem eqvGen_add_mul_mem
    (P : Set (MvPolynomial σ R))
    (hP₀ : ∀ p ∈ P, IsUnit (m.leadingCoeff p) ∨ p = 0)
    {f h p : MvPolynomial σ R}
    (hpP : p ∈ P) :
    f + h * p ⟷*[m, P] f := by
  have hred : h * p ⟶*[m, P] 0 :=
    mul_mem_reflTransGen_zero m P hpP
      (fun hp_ne =>
        (isUnit_leadingCoeff_of_mem_ne m hP₀ hpP hp_ne).mem_nonZeroDivisors)
  have hsub : (f + h * p) - f ⟶*[m, P] 0 := by
    convert hred using 1
    ring
  exact m.eqvGen_of_sub_reflTransGen_zero P hP₀ (f + h * p) f hsub

/--
Lemma 5.26.

Two polynomials are equivalent modulo the ideal generated by `P` iff they
are equivalent under the equivalence closure of reduction modulo `P`.
-/
theorem eqvGen_iff_sub_mem_span
    (P : Set (MvPolynomial σ R))
    (hP₀ : ∀ p ∈ P, IsUnit (m.leadingCoeff p) ∨ p = 0)
    {f g : MvPolynomial σ R} :
    f ⟷*[m, P] g ↔ f - g ∈ Ideal.span P := by
  constructor
  · intro h
    exact sub_mem_span_of_eqvGen m P h
  · intro hfg
    let Q : MvPolynomial σ R → Prop :=
      fun x => ∀ h f : MvPolynomial σ R, f + h * x ⟷*[m, P] f
    have hQ : Q (f - g) := by
      refine Submodule.span_induction
        (R := MvPolynomial σ R)
        (s := P)
        (p := fun x _hx => Q x)
        ?hPgen
        ?h0
        ?hadd
        ?hsmul
        hfg
      · intro p hpP h f
        exact eqvGen_add_mul_mem m P hP₀ (f := f) (h := h) (p := p) hpP
      · intro h f
        simpa only [mul_zero, add_zero] using (Relation.EqvGen.refl f : f ⟷*[m, P] f)
      · intro x y hx hy hxQ hyQ h f
        have hy' :
            f + h * x + h * y ⟷*[m, P] f + h * x :=
          hyQ h (f + h * x)
        have hx' :
            f + h * x ⟷*[m, P] f :=
          hxQ h f
        have hleft :
            f + h * (x + y) = f + h * x + h * y := by
          ring
        rw [hleft]
        exact Relation.EqvGen.trans _ _ _ hy' hx'
      · intro a x hx hxQ h f
        have hx' :
            f + (h * a) * x ⟷*[m, P] f :=
          hxQ (h * a) f
        simpa only [smul_eq_mul, mul_assoc] using hx'
    have hmain :
        g + 1 * (f - g) ⟷*[m, P] g :=
      hQ 1 g
    have hleft :
        g + 1 * (f - g) = f := by
      ring
    simpa only [one_mul, add_sub_cancel] using hmain

end UnitLeadingCoeffIdealEquivalence

namespace ReducesToSet

theorem singleton_iff
    {p f g : MvPolynomial σ R} :
    m.ReducesToSet ({p} : Set (MvPolynomial σ R)) f g ↔
      m.ReducesToPoly p f g := by
  constructor
  · intro h
    rcases h with ⟨q, hq, hqfg⟩
    rw [Set.mem_singleton_iff] at hq
    subst q
    exact hqfg
  · intro h
    exact ⟨p, by simp only [Set.mem_singleton_iff], h⟩

/--
Finite reduction modulo the singleton set `{p}` gives finite reduction
modulo the single polynomial `p`.
-/
theorem reflTransGen_singleton_to_reducesToPoly
    {p f g : MvPolynomial σ R}
    (h : f ⟶*[m, ({p} : Set (MvPolynomial σ R))] g) :
    Relation.ReflTransGen (m.ReducesToPoly p) f g := by
  exact
    (Relation.ReflTransGen.mono
      (r := m.ReducesToSet ({p} : Set (MvPolynomial σ R)))
      (p := m.ReducesToPoly p)
      (fun x y hxy => (ReducesToSet.singleton_iff m).1 hxy)) f g h

/--
Finite reduction modulo the single polynomial `p` gives finite reduction
modulo the singleton set `{p}`.
-/
theorem reflTransGen_reducesToPoly_to_singleton
    {p f g : MvPolynomial σ R}
    (h : Relation.ReflTransGen (m.ReducesToPoly p) f g) :
    f ⟶*[m, ({p} : Set (MvPolynomial σ R))] g := by
  exact
    (Relation.ReflTransGen.mono
      (r := m.ReducesToPoly p)
      (p := m.ReducesToSet ({p} : Set (MvPolynomial σ R)))
      (fun x y hxy => (ReducesToSet.singleton_iff m).2 hxy)) f g h

/--
If `Q ⊆ P`, then finite reductions modulo `Q` are finite reductions modulo `P`.
-/
theorem reflTransGen_mono
    {P Q : Set (MvPolynomial σ R)}
    (hQP : Q ⊆ P)
    {f g : MvPolynomial σ R}
    (h : f ⟶*[m, Q] g) :
    f ⟶*[m, P] g := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hfg hstep ih =>
      exact ih.tail
        (by
          rcases hstep with ⟨q, hqQ, hqfg⟩
          exact ⟨q, hQP hqQ, hqfg⟩)

end ReducesToSet

section UnitLeadingCoeffConfluence

private lemma leadingCoeff_unit_or_zero_singleton
    {p : MvPolynomial σ R}
    (hpLC : IsUnit (m.leadingCoeff p)) :
    ∀ q ∈ ({p} : Set (MvPolynomial σ R)),
      IsUnit (m.leadingCoeff q) ∨ q = 0 := by
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst q
  exact Or.inl hpLC

namespace ReducesToSet

/--
Proposition 5.33, singleton-set version.

If `p` has unit leading coefficient, then reduction modulo `{p}` is locally
confluent.
-/
theorem locallyConfluent_singleton
    {p : MvPolynomial σ R}
    (hpLC : IsUnit (m.leadingCoeff p)) :
    Relation.LocallyConfluent
      (m.ReducesToSet ({p} : Set (MvPolynomial σ R))) := by
  intro f f₁ f₂ hf₁ hf₂
  rcases hf₁ with ⟨q₁, hq₁P, t₁, hq₁_ne, ht₁, s₁, hs₁, c₁, hc₁, hf₁_eq⟩
  rcases hf₂ with ⟨q₂, hq₂P, t₂, hq₂_ne, ht₂, s₂, hs₂, c₂, hc₂, hf₂_eq⟩
  rw [Set.mem_singleton_iff] at hq₁P hq₂P
  subst q₁
  subst q₂
  let m₁ : MvPolynomial σ R := monomial s₁ c₁
  let m₂ : MvPolynomial σ R := monomial s₂ c₂
  have hdiff :
      f₁ - f₂ = (m₂ - m₁) * p := by
    rw [hf₁_eq, hf₂_eq]
    ring
  have hP₀_single :
      ∀ q ∈ ({p} : Set (MvPolynomial σ R)),
        IsUnit (m.leadingCoeff q) ∨ q = 0 :=
    leadingCoeff_unit_or_zero_singleton m hpLC
  have hred : (f₁ - f₂) ⟶*[m, ({p} : Set (MvPolynomial σ R))] 0 := by
    rw [hdiff]
    exact
      mul_mem_reflTransGen_zero m
      ({p} : Set (MvPolynomial σ R))
      (f := p)
      (h := m₂ - m₁)
      (by rw [Set.mem_singleton_iff])
      (fun _ => hpLC.mem_nonZeroDivisors)
  exact m.join_of_sub_reflTransGen_zero
    ({p} : Set (MvPolynomial σ R))
    hP₀_single
    f₁ f₂ hred

end ReducesToSet

namespace ReducesToPoly

/--
Proposition 5.33.

If `p` has unit leading coefficient, then reduction modulo the single
polynomial `p` is locally confluent.
-/
theorem locallyConfluent
    {p : MvPolynomial σ R}
    (hpLC : IsUnit (m.leadingCoeff p)) :
    Relation.LocallyConfluent (m.ReducesToPoly p) := by
  intro f f₁ f₂ hf₁ hf₂
  have hset :
      Relation.Join
        (Relation.ReflTransGen
          (m.ReducesToSet ({p} : Set (MvPolynomial σ R))))
        f₁ f₂ :=
    ReducesToSet.locallyConfluent_singleton m hpLC
      ((ReducesToSet.singleton_iff m).2 hf₁)
      ((ReducesToSet.singleton_iff m).2 hf₂)
  rcases hset with ⟨d, hf₁d, hf₂d⟩
  exact ⟨d,
    ReducesToSet.reflTransGen_singleton_to_reducesToPoly m hf₁d,
    ReducesToSet.reflTransGen_singleton_to_reducesToPoly m hf₂d⟩

end ReducesToPoly

namespace ReducesToSet

/--
Corollary 5.34.

If `Ideal.span P = Ideal.span {p}` for some nonzero `p ∈ P`, and all
nonzero elements of `P` have unit leading coefficient, then reduction
modulo `P` is locally confluent.
-/
theorem locallyConfluent_of_span_eq_singleton
    (P : Set (MvPolynomial σ R))
    (hP₀ : ∀ q ∈ P, IsUnit (m.leadingCoeff q) ∨ q = 0)
    {p : MvPolynomial σ R}
    (hpP : p ∈ P)
    (hp : p ≠ 0)
    (hspan : Ideal.span P = Ideal.span ({p} : Set (MvPolynomial σ R))) :
    Relation.LocallyConfluent (m.ReducesToSet P) := by
  intro f f₁ f₂ hf₁ hf₂
  have hpLC : IsUnit (m.leadingCoeff p) :=
    isUnit_leadingCoeff_of_mem_ne m hP₀ hpP hp
  have hP₀_single :
      ∀ q ∈ ({p} : Set (MvPolynomial σ R)),
        IsUnit (m.leadingCoeff q) ∨ q = 0 :=
    leadingCoeff_unit_or_zero_singleton m hpLC
  have hEqvP : f₁ ⟷*[m, P] f₂ := by
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hf₁))
      (Relation.EqvGen.rel _ _ hf₂)
  have hsubP : f₁ - f₂ ∈ Ideal.span P :=
    (eqvGen_iff_sub_mem_span m P hP₀).1 hEqvP
  have hsubSingleton :
      f₁ - f₂ ∈ Ideal.span ({p} : Set (MvPolynomial σ R)) := by
    simpa only [hspan] using hsubP
  have hEqvSingleton :
      f₁ ⟷*[m, ({p} : Set (MvPolynomial σ R))] f₂ :=
    (eqvGen_iff_sub_mem_span m
      ({p} : Set (MvPolynomial σ R))
      hP₀_single).2 hsubSingleton
  have hChurchSingleton :
      Relation.ChurchRosser
        (m.ReducesToSet ({p} : Set (MvPolynomial σ R))) := by
    have hloc :
        Relation.LocallyConfluent
          (m.ReducesToSet ({p} : Set (MvPolynomial σ R))) :=
      locallyConfluent_singleton m hpLC
    have hwf_single :
        WellFounded
          (flip (m.ReducesToSet ({p} : Set (MvPolynomial σ R)))) :=
      ReducesToSet.wellFounded m ({p} : Set (MvPolynomial σ R))
    have hconf :
        Relation.Confluent
          (m.ReducesToSet ({p} : Set (MvPolynomial σ R))) :=
      Relation.confluent_of_wellFounded_flip_of_locallyConfluent
        hwf_single hloc
    intro a b hab
    exact Relation.Confluent.churchRosser hconf hab
  rcases hChurchSingleton hEqvSingleton with ⟨d, hf₁d, hf₂d⟩
  refine ⟨d, ?_, ?_⟩
  · exact reflTransGen_mono m
      (P := P)
      (Q := ({p} : Set (MvPolynomial σ R)))
      (Set.singleton_subset_iff.mpr hpP)
      hf₁d
  · exact reflTransGen_mono m
      (P := P)
      (Q := ({p} : Set (MvPolynomial σ R)))
      (Set.singleton_subset_iff.mpr hpP)
      hf₂d

end ReducesToSet

end UnitLeadingCoeffConfluence

end CommRing

end MonomialOrder
