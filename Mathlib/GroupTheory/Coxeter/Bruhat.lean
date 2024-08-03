import Mathlib.GroupTheory.Coxeter.inversion
import Mathlib.Order.Interval.Basic

/-!
# The Bruhat Order of Coxeter group

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system. The Bruhat order is defined on `CoxeterSystem.Group`,
not directly defined on the group W.

## Bruhat Order

Given two elements $u, v \in cs.Group$, we say `lt_adj cs u v` (.resp `lt_adj' cs u v`) if
$\exists t \in cs.Group$, s.t.` cs.isReflection t` and
$$ut = v\wedge \ell (u) < \ell (v)$$ (.resp $tu = v\wedge \ell (u) < \ell (v)$)
Then we define  `· < ·` and `· ≤ ·` using `Relation.TransGen` and `Relation.ReflTransGen`.
This means if $u < v$, there exists a chain $u_0, u_1, \cdots, u_n$ satisfies :
$$
u = u_0 \wedge u_n = v \wedge \exists t_i \in T, u_it = u_{i+1}\quad \text{where} \quad 0 \leq i < n
$$
$u \le v$ means $u < v$ or $u = v$

Symmetrically, we have `Bruhat.lt'` and `Bruhat.le`, where their equivalence is
provided by `lt_iff_lt'` and `le_iff_le'`.

## Main definitions

* `Bruhat.lt_adj`
* `Bruhat.lt`
* `Bruhat.le`

## Notation

* `<`, `≤` are used as notation for `Bruhat.lt`, `Bruhat.le`
* `<ₗ`, `≤ₗ` are used as notation for `Bruhat.lt'`, `Bruhat.le'`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

open CoxeterSystem Relation
open Classical (choice choose choose_spec)

variable {B : Type*}
variable {W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simple
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length

abbrev CoxeterSystem.Group (_ : CoxeterSystem M W) := W

namespace Bruhat

variable {u v : cs.Group}

def lt_adj  : W → W → Prop := fun u v =>
  (∃ t, cs.IsReflection t ∧ v = u * t) ∧ ℓ u < ℓ v

def lt_adj' : W → W → Prop := fun u v =>
  (∃ t, cs.IsReflection t ∧ v = t * u) ∧ ℓ u < ℓ v

/-- `lt` is the transitive closure of `lt_adj` -/
def lt := Relation.TransGen <| lt_adj (cs := cs)

/-- `lt'` is the transitive closure of `lt_adj'` -/
def lt' := Relation.TransGen <| lt_adj' (cs := cs)

/-- The left Bruhat order is equivalent to the right Bruhat order since `lt_adj` is
  equivalent to ` lt_adj' `-/
lemma lt_adj_iff_lt_adj' : lt_adj cs u v ↔ lt_adj' cs u v := by
  constructor <;> rintro ⟨⟨t, vut⟩, llt⟩
  · have : cs.IsReflection (u * t * u⁻¹):=
      IsReflection.conj vut.1 u
    exact ⟨⟨u * t * u⁻¹, by simpa⟩, llt⟩
  · have subt : cs.IsReflection (u⁻¹ * t * u) := by
      have := IsReflection.conj vut.1 u⁻¹
      simp at this
      assumption
    exact ⟨⟨u⁻¹ * t * u, ⟨subt, by group; exact vut.2⟩⟩, llt⟩

/-- `le` is the reflexive transitive closure of `lt_adj ` -/
def le := Relation.ReflTransGen <| lt_adj cs

/-- `le'` is the reflexive transitive closure of `lt_adj' ` -/
def le' := Relation.ReflTransGen <| lt_adj' cs

lemma length_lt_of_lt (hlt : lt cs u v) : ℓ u < ℓ v :=
  Relation.TransGen.trans_induction_on hlt (fun h => h.2) (fun _ _ h1 h2 => h1.trans h2)

lemma length_le_of_le (hle : le cs u v) : ℓ u ≤ ℓ v := by
  induction hle with
  | refl           => rfl
  | tail _ bltv ih => exact le_of_lt (lt_of_le_of_lt ih bltv.2)

lemma le_of_lt (h : lt cs u v) : le cs u v := reflTransGen_iff_eq_or_transGen.2 (Or.inr h)

lemma eq_of_le_of_length_ge (hle : le cs u v) (lle : ℓ v ≤ ℓ u) : u = v := by
    have : ¬Relation.TransGen (lt_adj cs) u v := by
      contrapose! lle; exact length_lt_of_lt cs lle
    exact ((or_iff_left this).1 (Relation.reflTransGen_iff_eq_or_transGen.1 hle)).symm

/-- The Bruhat order is the partial order on Coxeter group. -/
instance : PartialOrder cs.Group where
  lt               := lt cs
  le               := le cs
  le_refl          := fun _             => id Relation.ReflTransGen.refl
  le_trans         := fun _ _ _ ha hb  => Relation.ReflTransGen.trans ha hb
  le_antisymm      := fun a b ha hb => eq_of_le_of_length_ge cs ha (length_le_of_le cs hb)
  lt_iff_le_not_le := by
    intro a b;
    constructor <;> intro h
    · exact ⟨TransGen.to_reflTransGen h, fun hh => by
        linarith [length_le_of_le cs hh, length_lt_of_lt cs h]⟩
    · exact Or.elim (reflTransGen_iff_eq_or_transGen.1 h.1) (right := fun a ↦ a)
        (fun hh => (False.elim <| h.2 <| reflTransGen_iff_eq_or_transGen.2 <| (Or.inl hh.symm)))

local infix : 100 "<ₗ" => lt' cs
local infix : 100 "≤ₗ" => le' cs

/-- Bruhat.lt is equivalent to Bruhat.lt' -/
lemma lt_iff_lt' : u < v ↔ u <ₗ v := by
  constructor <;> intro h
  · exact TransGen.mono (fun _ _ => (lt_adj_iff_lt_adj' cs).1) h
  · exact TransGen.mono (fun _ _ => (lt_adj_iff_lt_adj' cs).2) h

lemma le'_iff_lt'_or_eq : u ≤ₗ v ↔ u <ₗ v ∨ u = v := by
  have := @reflTransGen_iff_eq_or_transGen _ (lt_adj' cs) u v
  tauto

/-- Bruhat.le is equivalent to Bruhat.le' -/
lemma le_iff_le' : u ≤ v ↔ u ≤ₗ v := by
  constructor <;> intro h
  · have := le_iff_lt_or_eq.1 h
    rw [le'_iff_lt'_or_eq]
    exact Or.elim this (fun h1 => Or.inl <| (lt_iff_lt' cs).1 h1) (fun h2 => Or.inr h2)
  · exact Or.elim ((le'_iff_lt'_or_eq cs).1 h) (fun h1 => (le_of_lt cs) <| (lt_iff_lt' cs).2 h1)
      (fun h2 => reflTransGen_iff_eq_or_transGen.2 (Or.inl h2.symm))

lemma lt_of_le_of_length_lt : u ≤ v → ℓ u < ℓ v → u < v := fun h1 h2 =>
  (or_iff_right (by contrapose! h2; rw [h2])).1 <| reflTransGen_iff_eq_or_transGen.1 h1

/--If $t$ is the reflection of $W$, then $u < ut$ iff $\ell (u) < \ell (ut) $ -/
lemma lt_reflection_mul_iff_length_lt {t : W} (ht : cs.IsReflection t) :
  u < u * t ↔ ℓ u < ℓ (u * t) := by
    constructor <;> intro h
    · exact length_lt_of_lt cs h
    · exact (Relation.transGen_iff (lt_adj cs) u (u * t)).2 (Or.inl ⟨⟨t, ⟨ht, rfl⟩⟩, h⟩)

lemma mul_lt_of_IsRightInversion {t : W} (ht : cs.IsRightInversion u t) : u * t < u :=
  TransGen.single ⟨⟨t, ⟨ht.1, by rw [mul_assoc, IsReflection.mul_self ht.1, mul_one]⟩⟩, ht.2⟩

lemma mul_lt'_of_IsLeftInversion {t : W} (ht : cs.IsLeftInversion u t) : (t * u) <ₗ u :=
  TransGen.single ⟨⟨t, ⟨ht.1, by rw [←mul_assoc, IsReflection.mul_self ht.1, one_mul]⟩⟩, ht.2⟩

/-- $\forall u \in W$, if $ u \ne 1$, then $1 < u$ -/
lemma one_lt_of_ne_one (h : u ≠ 1) : 1 < u := by
  generalize h1 : ℓ u = n
  revert u
  induction' n with n ih
  · intro u h hu
    exact False.elim <| h <| cs.length_eq_zero_iff.1 <| hu
  · intro u h hu
    by_cases hh : n = 0
    · rw [hh] at hu
      obtain ⟨i, hi⟩ := (cs.length_eq_one_iff).1 hu
      exact TransGen.single ⟨ ⟨s i, ⟨cs.isReflection_simple i, by rw [hi,one_mul]⟩ ⟩,
      by simp;linarith⟩
    · obtain ⟨i, hi⟩ := exists_rightDescent_of_ne_one cs h
      have h1  : ℓ (u * s i) = n := by linarith [cs.isRightDescent_iff.1 hi]
      have ne1 : u * s i ≠ 1 := by
        have := cs.length_mul_ge_length_sub_length u (s i)
        simp only [length_simple] at this
        apply (Iff.not cs.length_eq_zero_iff).1
        intro h
        rw [h1] at h
        tauto
      have := mul_lt_of_IsRightInversion cs
        ((cs.isRightInversion_simple_iff_isRightDescent u i).2 hi)
      exact (ih ne1 h1).trans this

/-- $\forall u \in W, 1 \leq u$  -/
lemma one_le : 1 ≤ u := by
  by_cases h : u = 1
  · rw [h]
  · exact le_of_lt cs (one_lt_of_ne_one cs h)

end Bruhat
