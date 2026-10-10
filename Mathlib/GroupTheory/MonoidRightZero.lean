/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Card

/-!
# Right zeros in finite monoids

An element `p` of a monoid `M` is a *right zero* if `u * p = p` for every `u : M`.

## Main results

* `Monoid.exists_forall_mul_eq_self_of_finite`: a finite monoid in which any two
  principal right ideals meet, and which has no nontrivial morphism to a group, has a
  right zero.
* `Monoid.exists_forall_mul_eq_self_iff_of_finite`: for a finite monoid the two
  conditions together are equivalent to having a right zero.

Neither of the two conditions can be dropped. A nontrivial finite group satisfies the
first and has no right zero. The monoid `{1, a, b}` with `a`, `b` left zeros
(`x * y = x` for `x ≠ 1`) satisfies the second and has no right zero.

## Proof sketch

Finiteness and the meeting condition give `p` lying in every principal right ideal
`u * M`. Then `E = p * M` satisfies `E ⊆ u * E` for every `u`, hence `E = u * E`
since `E` is finite, so left multiplication defines a monoid morphism
`M →* Equiv.Perm E`. It is trivial by hypothesis, so `u * p = p`.

## References

The statement is Proposition 1 of an unpublished manuscript of A. Grothendieck
(Université de Montpellier, fonds Grothendieck, cote 158, pp. 44–46).
-/

public section

universe u

namespace Monoid

variable {M : Type u} [Monoid M]

/-- In a finite monoid in which any two principal right ideals meet, some element lies
in every principal right ideal. -/
theorem exists_forall_exists_eq_mul_of_finite [Finite M]
    (h : ∀ u v : M, ∃ u' v' : M, u * u' = v * v') :
    ∃ p : M, ∀ u : M, ∃ v : M, p = u * v := by
  classical
  have key : ∀ s : Finset M, ∃ p : M, ∀ u ∈ s, ∃ v : M, p = u * v := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp⟩
    | insert a s _ ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨p', v', e⟩ := h p a
      refine ⟨p * p', fun u hu => ?_⟩
      rcases Finset.mem_insert.1 hu with rfl | hu
      · exact ⟨v', e⟩
      · obtain ⟨v, hv⟩ := hp u hu
        exact ⟨v * p', by rw [hv, mul_assoc]⟩
  have := Fintype.ofFinite M
  obtain ⟨p, hp⟩ := key Finset.univ
  exact ⟨p, fun u => hp u (Finset.mem_univ u)⟩

/-- A finite monoid in which any two principal right ideals meet, and which has no
nontrivial morphism to a group, has a right zero. -/
theorem exists_forall_mul_eq_self_of_finite [Finite M]
    (h : ∀ u v : M, ∃ u' v' : M, u * u' = v * v')
    (hG : ∀ (G : Type u) [Group G] (f : M →* G), f = 1) :
    ∃ p : M, ∀ u : M, u * p = p := by
  obtain ⟨p, hp⟩ := exists_forall_exists_eq_mul_of_finite h
  let E : Set M := Set.range (p * ·)
  have hsub : ∀ u : M, E ⊆ (u * ·) '' E := by
    rintro u x ⟨y, rfl⟩
    obtain ⟨v, hv⟩ := hp (u * p)
    refine ⟨p * (v * y), ⟨v * y, rfl⟩, ?_⟩
    change u * (p * (v * y)) = p * y
    conv_rhs => rw [hv]
    simp only [mul_assoc]
  have heq : ∀ u : M, (u * ·) '' E = E := fun u =>
    (Set.eq_of_subset_of_ncard_le (hsub u) (Set.ncard_image_le (Set.toFinite _))
      (Set.toFinite _)).symm
  let f : M → E → E := fun u x => ⟨u * x, (heq u).subset ⟨x, x.2, rfl⟩⟩
  have hbij : ∀ u : M, Function.Bijective (f u) := fun u =>
    Finite.surjective_iff_bijective.1 fun y => by
      obtain ⟨x, hx, e⟩ := (heq u).symm.subset y.2
      exact ⟨⟨x, hx⟩, Subtype.ext e⟩
  let φ : M →* Equiv.Perm E :=
    { toFun := fun u => Equiv.ofBijective (f u) (hbij u)
      map_one' := by ext x; simp [f]
      map_mul' := fun a b => by ext x; simp [f, mul_assoc] }
  refine ⟨p, fun u => ?_⟩
  have h1 : φ u = 1 := by rw [hG _ φ]; rfl
  simpa [φ, f] using congrArg (fun σ : Equiv.Perm E => (σ ⟨p, 1, mul_one p⟩ : M)) h1

/-- A monoid with a right zero has no nontrivial morphism to a group. -/
theorem monoidHom_eq_one_of_forall_mul_eq_self {G : Type*} [Group G] {p : M}
    (hp : ∀ u : M, u * p = p) (f : M →* G) : f = 1 := by
  ext u
  simpa using congrArg f (hp u)

/-- A finite monoid has a right zero if and only if any two of its principal right
ideals meet and it has no nontrivial morphism to a group. -/
theorem exists_forall_mul_eq_self_iff_of_finite [Finite M] :
    (∃ p : M, ∀ u : M, u * p = p) ↔
      (∀ u v : M, ∃ u' v' : M, u * u' = v * v') ∧
        ∀ (G : Type u) [Group G] (f : M →* G), f = 1 := by
  refine ⟨fun ⟨p, hp⟩ => ⟨fun u v => ⟨p, p, by rw [hp, hp]⟩,
    fun G _ f => monoidHom_eq_one_of_forall_mul_eq_self hp f⟩, fun ⟨h, hG⟩ => ?_⟩
  exact exists_forall_mul_eq_self_of_finite h hG

end Monoid
