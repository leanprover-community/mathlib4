/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexInduction
public import Mathlib.Algebra.Homology.Homotopy

/-!
# K-injective cochain complexes

We define the notion of K-injective cochain complex in an abelian category,
and show that bounded below complexes of injective objects are K-injective.

## TODO (@joelriou)
* Show that a cochain complex is K-injective iff its image in the homotopy
category belongs to the right orthogonal of the triangulated subcategory
of acyclic complexes
* Deduce that we can compute morphisms to a K-injective complex in the
derived category as homotopy classes of morphisms
* Provide an API for computing `Ext`-groups using an injective resolution
* Dualize everything

## References
* [N. Spaltenstein, *Resolutions of unbounded complexes*][spaltenstein1998]

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits HomComplex Preadditive

variable {C : Type*} [Category C] [Abelian C]

-- TODO (@joelriou): show that this definition is equivalent to the
-- original definition by Spaltenstein saying that whenever `K`
-- is acyclic, then `HomComplex K L` is acyclic. (The condition below
-- is equivalent to the acyclicity of `HomComplex K L` in degree
-- `0`, and the general case follows by shifting `K`.)
/-- A cochain complex `L` is K-injective if any morphism `K ⟶ L`
with `K` acyclic is homotopic to zero. -/
class IsKInjective (L : CochainComplex C ℤ) : Prop where
  nonempty_homotopy_zero {K : CochainComplex C ℤ} (f : K ⟶ L) :
    K.Acyclic → Nonempty (Homotopy f 0)

lemma isKInjective_of_injective_aux {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (α : Cochain K L (-1)) (n m : ℤ) (hnm : n + 1 = m)
    (hK : K.ExactAt m) [Injective (L.X m)]
    (hα : (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) n) :
    ∃ (h : K.X (n + 2) ⟶ L.X (n + 1)),
      (δ (-1) 0 (α + Cochain.single h (-1))).EqUpTo (Cochain.ofHom f) m := by
  subst hnm
  let u := f.f (n + 1) - α.v (n + 1) n (by cutsat) ≫ L.d n (n + 1) -
    K.d (n + 1) (n + 2) ≫ α.v (n + 2) (n + 1) (by cutsat)
  have hu : K.d n (n+1) ≫ u = 0 := by
    have eq := hα n n (add_zero n) (by rfl)
    simp only [δ_v (-1) 0 (neg_add_cancel 1) α n n (add_zero _) (n - 1) (n + 1)
      (by cutsat) (by cutsat), Int.negOnePow_zero, one_smul, Cochain.ofHom_v] at eq
    simp only [u, comp_sub, HomologicalComplex.d_comp_d_assoc, zero_comp,
      ← f.comm, ← eq, add_comp, Category.assoc, L.d_comp_d, comp_zero, zero_add, sub_self]
  rw [K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; cutsat)] at hK
  obtain ⟨β, hβ⟩ : ∃ (β : K.X (n + 2) ⟶ L.X (n + 1)), K.d (n + 1) (n + 2) ≫ β = u :=
    ⟨hK.descToInjective _ hu, hK.comp_descToInjective _ _⟩
  refine ⟨β, ?_⟩
  intro p q hpq hp
  obtain rfl : p = q := by cutsat
  obtain hp | rfl := hp.lt_or_eq
  · rw [δ_add, Cochain.add_v, hα p p (by cutsat) (by cutsat), add_eq_left,
      δ_v (-1) 0 (neg_add_cancel 1) _ p p hpq (p - 1) (p + 1) rfl rfl,
      Cochain.single_v_eq_zero _ _ _ _ _ (by cutsat),
      Cochain.single_v_eq_zero _ _ _ _ _ (by cutsat)]
    simp
  · rw [δ_v (-1) 0 (neg_add_cancel 1) _ (n + 1) (n + 1) (by cutsat) n (n + 2)
      (by cutsat) (by cutsat), Cochain.add_v,
      Cochain.single_v_eq_zero _ _ _ _ _ (by cutsat)]
    simp [hβ, u]

open Cochain.InductionUp in
lemma isKInjective_of_injective (L : CochainComplex C ℤ) (d : ℤ)
    [L.IsStrictlyGE d] [∀ (n : ℤ), Injective (L.X n)] :
    L.IsKInjective where
  nonempty_homotopy_zero {K} f hK := by
    /- The strategy of the proof is express the `0`-cocycle in `Cochain K L 0`
    corresponding to `f` as the coboundary of a `-1`-cochain. An approximate
    solution for some `n : ℕ` is an element in the subset `X n` consisting
    of the `-1`-cochains such that `δ (-1) 0 α` coincide with `Cochain.ofHom f`
    up to the degree `n + d - 1`. The assumption on `L` implies that
    the zero `-1`-cochain belongs to `X 0`, and we use the lemma
    `isKInjective_of_injective_aux` in order to get better approximations,
    and we pass to the limit. -/
    let X (n : ℕ) : Set (Cochain K L (-1)) :=
      setOf (fun α => (δ (-1) 0 α).EqUpTo (Cochain.ofHom f) (n + d - 1))
    let x₀ : X 0 := ⟨0, fun p q hpq hp ↦
      IsZero.eq_of_tgt (L.isZero_of_isStrictlyGE d _ (by cutsat)) _ _⟩
    let φ (n : ℕ) (α : X n) : X (n + 1) :=
      ⟨_, (isKInjective_of_injective_aux f α.1 (n + d - 1) ((n + 1 : ℕ) + d - 1)
        (by cutsat) (hK _) α.2).choose_spec⟩
    have hφ (k : ℕ) (x : X k) : (φ k x).1.EqUpTo x.1 (d + k) := fun p q hpq hp => by
      dsimp [φ]
      rw [add_eq_left, Cochain.single_v_eq_zero _ _ _ _ _ (by cutsat)]
    refine ⟨(Cochain.equivHomotopy f 0).symm ⟨limitSequence φ hφ x₀, ?_⟩⟩
    rw [Cochain.ofHom_zero, add_zero]
    ext n
    let k₀ := (n - d + 1).toNat
    rw [← (sequence φ x₀ k₀).2 n n (add_zero n) (by cutsat),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by cutsat) (n - 1) (n + 1) rfl (by cutsat),
      δ_v (-1) 0 (neg_add_cancel 1) _ n n (by cutsat) (n - 1) (n + 1) rfl (by cutsat),
      limitSequence_eqUpTo φ hφ x₀ k₀ n (n - 1) (by cutsat) (by cutsat),
      limitSequence_eqUpTo φ hφ x₀ k₀ (n + 1) n (by cutsat) (by cutsat)]

end CochainComplex
