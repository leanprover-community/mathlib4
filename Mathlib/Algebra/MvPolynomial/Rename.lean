/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Renaming variables of polynomials

This file establishes the `rename` operation on multivariate polynomials,
which modifies the set of variables.

## Main declarations

* `MvPolynomial.rename`
* `MvPolynomial.renameEquiv`

## Notation

As in other polynomial files, we typically use the notation:

+ `σ τ α : Type*` (indexing the variables)

+ `R S : Type*` `[CommSemiring R]` `[CommSemiring S]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `MvPolynomial σ R` which mathematicians might call `X^s`

+ `r : R` elements of the coefficient ring

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : MvPolynomial σ α`

-/


noncomputable section

open Set Function Finsupp AddMonoidAlgebra

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

namespace MvPolynomial

section Rename

/-- Rename all the variables in a multivariable polynomial. -/
def rename (f : σ → τ) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval (X ∘ f)

theorem rename_C (f : σ → τ) (r : R) : rename f (C r) = C r :=
  eval₂_C _ _ _

@[simp]
theorem rename_X (f : σ → τ) (i : σ) : rename f (X i : MvPolynomial σ R) = X (f i) :=
  eval₂_X _ _ _

theorem map_rename (f : R →+* S) (g : σ → τ) (p : MvPolynomial σ R) :
    map f (rename g p) = rename g (map f p) := by
  apply MvPolynomial.induction_on p
    (fun a => by simp only [map_C, rename_C])
    (fun p q hp hq => by simp only [hp, hq, map_add]) fun p n hp => by
    simp only [hp, rename_X, map_X, map_mul]

lemma map_comp_rename (f : R →+* S) (g : σ → τ) :
    (map f).comp (rename g).toRingHom = (rename g).toRingHom.comp (map f) :=
  RingHom.ext fun p ↦ map_rename f g p

@[simp]
theorem rename_rename (f : σ → τ) (g : τ → α) (p : MvPolynomial σ R) :
    rename g (rename f p) = rename (g ∘ f) p := by
  nth_rw 2 [rename]
  simp_rw [aeval_def, algebraMap_eq, rename, aeval_eq_eval₂Hom]
  rw [eval₂_comp_left (eval₂Hom (algebraMap R (MvPolynomial α R)) (X ∘ g)) C (X ∘ f) p]
  simp only [comp_def, eval₂Hom_X']
  refine eval₂Hom_congr ?_ rfl rfl
  ext1; simp only [comp_apply, RingHom.coe_comp, eval₂Hom_C]

lemma rename_comp_rename (f : σ → τ) (g : τ → α) :
    (rename (R := R) g).comp (rename f) = rename (g ∘ f) :=
  AlgHom.ext fun p ↦ rename_rename f g p

@[simp]
theorem rename_id : rename id = AlgHom.id R (MvPolynomial σ R) :=
  AlgHom.ext fun p ↦ eval₂_eta p

lemma rename_id_apply (p : MvPolynomial σ R) : rename id p = p := by
  simp

theorem rename_monomial (f : σ → τ) (d : σ →₀ ℕ) (r : R) :
    rename f (monomial d r) = monomial (d.mapDomain f) r := by
  rw [rename, aeval_monomial, monomial_eq (s := Finsupp.mapDomain f d),
    Finsupp.prod_mapDomain_index, algebraMap_eq]
  · simp_rw [Function.comp_apply]
  · exact fun n => pow_zero _
  · exact fun n i₁ i₂ => pow_add _ _ _

theorem rename_eq (f : σ → τ) (p : MvPolynomial σ R) :
    rename f p = Finsupp.mapDomain (Finsupp.mapDomain f) p := by
  simp_rw [rename, aeval_def, eval₂, Finsupp.mapDomain, algebraMap_eq, comp_apply,
    X_pow_eq_monomial, ← monomial_finsupp_sum_index, ← single_eq_monomial]

theorem rename_injective (f : σ → τ) (hf : Function.Injective f) :
    Function.Injective (rename f : MvPolynomial σ R → MvPolynomial τ R) := by
  have :
    (rename f : MvPolynomial σ R → MvPolynomial τ R) = Finsupp.mapDomain (Finsupp.mapDomain f) :=
    funext (rename_eq f)
  rw [this]
  exact Finsupp.mapDomain_injective (Finsupp.mapDomain_injective hf)

theorem rename_leftInverse {f : σ → τ} {g : τ → σ} (hf : Function.LeftInverse f g) :
    Function.LeftInverse (rename f : MvPolynomial σ R → MvPolynomial τ R) (rename g) := by
  intro x
  simp [hf.comp_eq_id]

theorem rename_rightInverse {f : σ → τ} {g : τ → σ} (hf : Function.RightInverse f g) :
    Function.RightInverse (rename f : MvPolynomial σ R → MvPolynomial τ R) (rename g) :=
  rename_leftInverse hf

theorem rename_surjective (f : σ → τ) (hf : Function.Surjective f) :
    Function.Surjective (rename f : MvPolynomial σ R → MvPolynomial τ R) :=
  let ⟨_, hf⟩ := hf.hasRightInverse; rename_rightInverse hf |>.surjective

section

variable {f : σ → τ} (hf : Function.Injective f)

open Classical in
/-- Given a function between sets of variables `f : σ → τ` that is injective with proof `hf`,
  `MvPolynomial.killCompl hf` is the `AlgHom` from `R[τ]` to `R[σ]` that is left inverse to
  `rename f : R[σ] → R[τ]` and sends the variables in the complement of the range of `f` to `0`. -/
def killCompl : MvPolynomial τ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => if h : i ∈ Set.range f then X <| (Equiv.ofInjective f hf).symm ⟨i, h⟩ else 0

theorem killCompl_C (r : R) : killCompl hf (C r) = C r := algHom_C _ _

theorem killCompl_comp_rename : (killCompl hf).comp (rename f) = AlgHom.id R _ :=
  algHom_ext fun i => by
    dsimp
    rw [rename, killCompl, aeval_X, comp_apply, aeval_X, dif_pos ⟨i, rfl⟩,
      Equiv.ofInjective_symm_apply]

@[simp]
theorem killCompl_rename_app (p : MvPolynomial σ R) : killCompl hf (rename f p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename hf) p

end

section

variable (R)

/-- `MvPolynomial.rename e` is an equivalence when `e` is. -/
@[simps apply]
def renameEquiv (f : σ ≃ τ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R :=
  { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id_apply]
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id_apply] }

@[simp]
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl :=
  AlgEquiv.ext (by simp)

@[simp]
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm :=
  rfl

@[simp]
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ α) :
    (renameEquiv R e).trans (renameEquiv R f) = renameEquiv R (e.trans f) :=
  AlgEquiv.ext (rename_rename e f)

end

section

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

theorem eval₂_rename : (rename k p).eval₂ f g = p.eval₂ f (g ∘ k) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

theorem eval_rename (g : τ → R) (p : MvPolynomial σ R) : eval g (rename k p) = eval (g ∘ k) p :=
  eval₂_rename _ _ _ _

theorem eval₂Hom_rename : eval₂Hom f g (rename k p) = eval₂Hom f (g ∘ k) p :=
  eval₂_rename _ _ _ _

theorem aeval_rename [Algebra R S] : aeval g (rename k p) = aeval (g ∘ k) p :=
  eval₂Hom_rename _ _ _ _

lemma aeval_comp_rename [Algebra R S] :
    (aeval (R := R) g).comp (rename k) = MvPolynomial.aeval (g ∘ k) :=
  AlgHom.ext fun p ↦ aeval_rename k g p

theorem rename_eval₂ (g : τ → MvPolynomial σ R) :
    rename k (p.eval₂ C (g ∘ k)) = (rename k p).eval₂ C (rename k ∘ g) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

theorem rename_prod_mk_eval₂ (j : τ) (g : σ → MvPolynomial σ R) :
    rename (Prod.mk j) (p.eval₂ C g) = p.eval₂ C fun x => rename (Prod.mk j) (g x) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

theorem eval₂_rename_prod_mk (g : σ × τ → S) (i : σ) (p : MvPolynomial τ R) :
    (rename (Prod.mk i) p).eval₂ f g = eval₂ f (fun j => g (i, j)) p := by
  apply MvPolynomial.induction_on p <;>
    · intros
      simp [*]

theorem eval_rename_prod_mk (g : σ × τ → R) (i : σ) (p : MvPolynomial τ R) :
    eval g (rename (Prod.mk i) p) = eval (fun j => g (i, j)) p :=
  eval₂_rename_prod_mk (RingHom.id _) _ _ _

end

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_finset_rename (p : MvPolynomial σ R) :
    ∃ (s : Finset σ) (q : MvPolynomial { x // x ∈ s } R), p = rename (↑) q := by
  classical
  apply induction_on p
  · intro r
    exact ⟨∅, C r, by rw [rename_C]⟩
  · rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩
    refine ⟨s ∪ t, ⟨?_, ?_⟩⟩
    · refine rename (Subtype.map id ?_) p + rename (Subtype.map id ?_) q <;>
        simp +contextual only [id, true_or, or_true,
          Finset.mem_union, forall_true_iff]
    · simp only [rename_rename, map_add]
      rfl
  · rintro p n ⟨s, p, rfl⟩
    refine ⟨insert n s, ⟨?_, ?_⟩⟩
    · refine rename (Subtype.map id ?_) p * X ⟨n, s.mem_insert_self n⟩
      simp +contextual only [id, or_true, Finset.mem_insert, forall_true_iff]
    · simp only [rename_rename, rename_X, map_mul]
      rfl

/-- `exists_finset_rename` for two polynomials at once: for any two polynomials `p₁`, `p₂` in a
  polynomial semiring `R[σ]` of possibly infinitely many variables, `exists_finset_rename₂` yields
  a finite subset `s` of `σ` such that both `p₁` and `p₂` are contained in the polynomial semiring
  `R[s]` of finitely many variables. -/
theorem exists_finset_rename₂ (p₁ p₂ : MvPolynomial σ R) :
    ∃ (s : Finset σ) (q₁ q₂ : MvPolynomial s R), p₁ = rename (↑) q₁ ∧ p₂ = rename (↑) q₂ := by
  obtain ⟨s₁, q₁, rfl⟩ := exists_finset_rename p₁
  obtain ⟨s₂, q₂, rfl⟩ := exists_finset_rename p₂
  classical
    use s₁ ∪ s₂
    use rename (Set.inclusion s₁.subset_union_left) q₁
    use rename (Set.inclusion s₁.subset_union_right) q₂
    constructor <;> simp [Function.comp_def]

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_fin_rename (p : MvPolynomial σ R) :
    ∃ (n : ℕ) (f : Fin n → σ) (_hf : Injective f) (q : MvPolynomial (Fin n) R), p = rename f q := by
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  let n := Fintype.card { x // x ∈ s }
  let e := Fintype.equivFin { x // x ∈ s }
  refine ⟨n, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective, rename e q, ?_⟩
  rw [← rename_rename, rename_rename e]
  simp only [Function.comp_def, Equiv.symm_apply_apply, rename_rename]

end Rename

theorem eval₂_cast_comp (f : σ → τ) (c : ℤ →+* R) (g : τ → R) (p : MvPolynomial σ ℤ) :
    eval₂ c (g ∘ f) p = eval₂ c g (rename f p) := (eval₂_rename c f g p).symm

section Coeff

@[simp]
theorem coeff_rename_mapDomain (f : σ → τ) (hf : Injective f) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (rename f φ).coeff (d.mapDomain f) = φ.coeff d := by
  classical
  apply φ.induction_on' (P := fun ψ => coeff (Finsupp.mapDomain f d) ((rename f) ψ) = coeff d ψ)
  -- Lean could no longer infer the motive
  · intro u r
    rw [rename_monomial, coeff_monomial, coeff_monomial]
    simp only [(Finsupp.mapDomain_injective hf).eq_iff]
  · intros
    simp only [*, map_add, coeff_add]

@[simp]
theorem coeff_rename_embDomain (f : σ ↪ τ) (φ : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (rename f φ).coeff (d.embDomain f) = φ.coeff d := by
  rw [Finsupp.embDomain_eq_mapDomain f, coeff_rename_mapDomain f f.injective]

theorem coeff_rename_eq_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
    (h : ∀ u : σ →₀ ℕ, u.mapDomain f = d → φ.coeff u = 0) : (rename f φ).coeff d = 0 := by
  classical
  rw [rename_eq, ← notMem_support_iff]
  intro H
  replace H := mapDomain_support H
  rw [Finset.mem_image] at H
  obtain ⟨u, hu, rfl⟩ := H
  specialize h u rfl
  rw [Finsupp.mem_support_iff] at hu
  contradiction

theorem coeff_rename_ne_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
    (h : (rename f φ).coeff d ≠ 0) : ∃ u : σ →₀ ℕ, u.mapDomain f = d ∧ φ.coeff u ≠ 0 := by
  contrapose! h
  apply coeff_rename_eq_zero _ _ _ h

@[simp]
theorem constantCoeff_rename {τ : Type*} (f : σ → τ) (φ : MvPolynomial σ R) :
    constantCoeff (rename f φ) = constantCoeff φ := by
  apply φ.induction_on
  · intro a
    simp only [constantCoeff_C, rename_C]
  · intro p q hp hq
    simp only [hp, hq, map_add]
  · intro p n hp
    simp only [hp, rename_X, constantCoeff_X, map_mul]

end Coeff

section Support

theorem support_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} [DecidableEq τ]
    (h : Function.Injective f) :
    (rename f p).support = Finset.image (Finsupp.mapDomain f) p.support := by
  rw [rename_eq]
  exact Finsupp.mapDomain_support_of_injective (Finsupp.mapDomain_injective h) _

end Support

end MvPolynomial
