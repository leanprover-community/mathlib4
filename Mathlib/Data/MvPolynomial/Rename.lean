/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
import Mathlib.Data.MvPolynomial.Basic

#align_import data.mv_polynomial.rename from "leanprover-community/mathlib"@"2f5b500a507264de86d666a5f87ddb976e2d8de4"

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

open BigOperators

open Set Function Finsupp AddMonoidAlgebra

open BigOperators

variable {σ τ α R S : Type*} [CommSemiring R] [CommSemiring S]

namespace MvPolynomial

section Rename

/-- Rename all the variables in a multivariable polynomial. -/
def rename (f : σ → τ) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval (X ∘ f)
#align mv_polynomial.rename MvPolynomial.rename

@[simp]
theorem rename_C (f : σ → τ) (r : R) : rename f (C r) = C r :=
  eval₂_C _ _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.rename_C MvPolynomial.rename_C

@[simp]
theorem rename_X (f : σ → τ) (i : σ) : rename f (X i : MvPolynomial σ R) = X (f i) :=
  eval₂_X _ _ _
set_option linter.uppercaseLean3 false in
#align mv_polynomial.rename_X MvPolynomial.rename_X

theorem map_rename (f : R →+* S) (g : σ → τ) (p : MvPolynomial σ R) :
    map f (rename g p) = rename g (map f p) := by
  apply MvPolynomial.induction_on p
    (fun a => by simp only [map_C, rename_C])
    (fun p q hp hq => by simp only [hp, hq, AlgHom.map_add, RingHom.map_add]) fun p n hp => by
    simp only [hp, rename_X, map_X, RingHom.map_mul, AlgHom.map_mul]
#align mv_polynomial.map_rename MvPolynomial.map_rename

@[simp]
theorem rename_rename (f : σ → τ) (g : τ → α) (p : MvPolynomial σ R) :
    rename g (rename f p) = rename (g ∘ f) p :=
  show rename g (eval₂ C (X ∘ f) p) = _ by
    simp only [rename, aeval_eq_eval₂Hom]
    -- ⊢ ↑(eval₂Hom (algebraMap R (MvPolynomial α R)) (X ∘ g)) (eval₂ C (X ∘ f) p) =  …
    -- porting note: the Lean 3 proof of this was very fragile and included a nonterminal `simp`.
    -- Hopefully this is less prone to breaking
    rw [eval₂_comp_left (eval₂Hom (algebraMap R (MvPolynomial α R)) (X ∘ g)) C (X ∘ f) p]
    -- ⊢ eval₂ (RingHom.comp (eval₂Hom (algebraMap R (MvPolynomial α R)) (X ∘ g)) C)  …
    simp only [(· ∘ ·), eval₂Hom_X', coe_eval₂Hom]
    -- ⊢ eval₂ (RingHom.comp (eval₂Hom (algebraMap R (MvPolynomial α R)) fun x => X ( …
    refine' eval₂Hom_congr _ rfl rfl
    -- ⊢ RingHom.comp (eval₂Hom (algebraMap R (MvPolynomial α R)) fun x => X (g x)) C …
    ext1; simp only [comp_apply, RingHom.coe_comp, eval₂Hom_C]
    -- ⊢ ↑(RingHom.comp (eval₂Hom (algebraMap R (MvPolynomial α R)) fun x => X (g x)) …
          -- 🎉 no goals
#align mv_polynomial.rename_rename MvPolynomial.rename_rename

@[simp]
theorem rename_id (p : MvPolynomial σ R) : rename id p = p :=
  eval₂_eta p
#align mv_polynomial.rename_id MvPolynomial.rename_id

theorem rename_monomial (f : σ → τ) (d : σ →₀ ℕ) (r : R) :
    rename f (monomial d r) = monomial (d.mapDomain f) r := by
  rw [rename, aeval_monomial, monomial_eq (s := Finsupp.mapDomain f d),
    Finsupp.prod_mapDomain_index]
  · rfl
    -- 🎉 no goals
  · exact fun n => pow_zero _
    -- 🎉 no goals
  · exact fun n i₁ i₂ => pow_add _ _ _
    -- 🎉 no goals
#align mv_polynomial.rename_monomial MvPolynomial.rename_monomial

theorem rename_eq (f : σ → τ) (p : MvPolynomial σ R) :
    rename f p = Finsupp.mapDomain (Finsupp.mapDomain f) p := by
  simp only [rename, aeval_def, eval₂, Finsupp.mapDomain, algebraMap_eq, comp_apply,
    X_pow_eq_monomial, ← monomial_finsupp_sum_index]
  rfl
  -- 🎉 no goals
#align mv_polynomial.rename_eq MvPolynomial.rename_eq

theorem rename_injective (f : σ → τ) (hf : Function.Injective f) :
    Function.Injective (rename f : MvPolynomial σ R → MvPolynomial τ R) := by
  have :
    (rename f : MvPolynomial σ R → MvPolynomial τ R) = Finsupp.mapDomain (Finsupp.mapDomain f) :=
    funext (rename_eq f)
  rw [this]
  -- ⊢ Injective (Finsupp.mapDomain (Finsupp.mapDomain f))
  exact Finsupp.mapDomain_injective (Finsupp.mapDomain_injective hf)
  -- 🎉 no goals
#align mv_polynomial.rename_injective MvPolynomial.rename_injective

section

variable {f : σ → τ} (hf : Function.Injective f)

open Classical

/-- Given a function between sets of variables `f : σ → τ` that is injective with proof `hf`,
  `MvPolynomial.killCompl hf` is the `AlgHom` from `R[τ]` to `R[σ]` that is left inverse to
  `rename f : R[σ] → R[τ]` and sends the variables in the complement of the range of `f` to `0`. -/
def killCompl : MvPolynomial τ R →ₐ[R] MvPolynomial σ R :=
  aeval fun i => if h : i ∈ Set.range f then X <| (Equiv.ofInjective f hf).symm ⟨i, h⟩ else 0
#align mv_polynomial.kill_compl MvPolynomial.killCompl

theorem killCompl_comp_rename : (killCompl hf).comp (rename f) = AlgHom.id R _ :=
  algHom_ext fun i => by
    dsimp
    -- ⊢ ↑(killCompl hf) (↑(rename f) (X i)) = X i
    rw [rename, killCompl, aeval_X, comp_apply, aeval_X, dif_pos, Equiv.ofInjective_symm_apply]
    -- 🎉 no goals
#align mv_polynomial.kill_compl_comp_rename MvPolynomial.killCompl_comp_rename

@[simp]
theorem killCompl_rename_app (p : MvPolynomial σ R) : killCompl hf (rename f p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename hf) p
#align mv_polynomial.kill_compl_rename_app MvPolynomial.killCompl_rename_app

end

section

variable (R)

/-- `MvPolynomial.rename e` is an equivalence when `e` is. -/
@[simps apply]
def renameEquiv (f : σ ≃ τ) : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R :=
  { rename f with
    toFun := rename f
    invFun := rename f.symm
    left_inv := fun p => by rw [rename_rename, f.symm_comp_self, rename_id]
                            -- 🎉 no goals
    right_inv := fun p => by rw [rename_rename, f.self_comp_symm, rename_id] }
                             -- 🎉 no goals
#align mv_polynomial.rename_equiv MvPolynomial.renameEquiv

@[simp]
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl :=
  AlgEquiv.ext rename_id
#align mv_polynomial.rename_equiv_refl MvPolynomial.renameEquiv_refl

@[simp]
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm :=
  rfl
#align mv_polynomial.rename_equiv_symm MvPolynomial.renameEquiv_symm

@[simp]
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ α) :
    (renameEquiv R e).trans (renameEquiv R f) = renameEquiv R (e.trans f) :=
  AlgEquiv.ext (rename_rename e f)
#align mv_polynomial.rename_equiv_trans MvPolynomial.renameEquiv_trans

end

section

variable (f : R →+* S) (k : σ → τ) (g : τ → S) (p : MvPolynomial σ R)

theorem eval₂_rename : (rename k p).eval₂ f g = p.eval₂ f (g ∘ k) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      -- ⊢ eval₂ f g (↑(rename k) (↑C a✝)) = eval₂ f (g ∘ k) (↑C a✝)
      -- ⊢ eval₂ f g (↑(rename k) (p✝ + q✝)) = eval₂ f (g ∘ k) (p✝ + q✝)
      -- 🎉 no goals
      -- ⊢ eval₂ f g (↑(rename k) (p✝ * X n✝)) = eval₂ f (g ∘ k) (p✝ * X n✝)
      -- 🎉 no goals
      simp [*]
      -- 🎉 no goals
#align mv_polynomial.eval₂_rename MvPolynomial.eval₂_rename

theorem eval₂Hom_rename : eval₂Hom f g (rename k p) = eval₂Hom f (g ∘ k) p :=
  eval₂_rename _ _ _ _
#align mv_polynomial.eval₂_hom_rename MvPolynomial.eval₂Hom_rename

theorem aeval_rename [Algebra R S] : aeval g (rename k p) = aeval (g ∘ k) p :=
  eval₂Hom_rename _ _ _ _
#align mv_polynomial.aeval_rename MvPolynomial.aeval_rename

theorem rename_eval₂ (g : τ → MvPolynomial σ R) :
    rename k (p.eval₂ C (g ∘ k)) = (rename k p).eval₂ C (rename k ∘ g) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      -- ⊢ ↑(rename k) (eval₂ C (g ∘ k) (↑C a✝)) = eval₂ C (↑(rename k) ∘ g) (↑(rename  …
      -- ⊢ ↑(rename k) (eval₂ C (g ∘ k) (p✝ + q✝)) = eval₂ C (↑(rename k) ∘ g) (↑(renam …
      -- 🎉 no goals
      -- ⊢ ↑(rename k) (eval₂ C (g ∘ k) (p✝ * X n✝)) = eval₂ C (↑(rename k) ∘ g) (↑(ren …
      -- 🎉 no goals
      simp [*]
      -- 🎉 no goals
#align mv_polynomial.rename_eval₂ MvPolynomial.rename_eval₂

theorem rename_prod_mk_eval₂ (j : τ) (g : σ → MvPolynomial σ R) :
    rename (Prod.mk j) (p.eval₂ C g) = p.eval₂ C fun x => rename (Prod.mk j) (g x) := by
  apply MvPolynomial.induction_on p <;>
    · intros
      -- ⊢ ↑(rename (Prod.mk j)) (eval₂ C g (↑C a✝)) = eval₂ C (fun x => ↑(rename (Prod …
      -- ⊢ ↑(rename (Prod.mk j)) (eval₂ C g (p✝ + q✝)) = eval₂ C (fun x => ↑(rename (Pr …
      -- 🎉 no goals
      -- ⊢ ↑(rename (Prod.mk j)) (eval₂ C g (p✝ * X n✝)) = eval₂ C (fun x => ↑(rename ( …
      -- 🎉 no goals
      simp [*]
      -- 🎉 no goals
#align mv_polynomial.rename_prodmk_eval₂ MvPolynomial.rename_prod_mk_eval₂

theorem eval₂_rename_prod_mk (g : σ × τ → S) (i : σ) (p : MvPolynomial τ R) :
    (rename (Prod.mk i) p).eval₂ f g = eval₂ f (fun j => g (i, j)) p := by
  apply MvPolynomial.induction_on p <;>
    · intros
      -- ⊢ eval₂ f g (↑(rename (Prod.mk i)) (↑C a✝)) = eval₂ f (fun j => g (i, j)) (↑C  …
      -- ⊢ eval₂ f g (↑(rename (Prod.mk i)) (p✝ + q✝)) = eval₂ f (fun j => g (i, j)) (p …
      -- 🎉 no goals
      -- ⊢ eval₂ f g (↑(rename (Prod.mk i)) (p✝ * X n✝)) = eval₂ f (fun j => g (i, j))  …
      -- 🎉 no goals
      simp [*]
      -- 🎉 no goals
#align mv_polynomial.eval₂_rename_prodmk MvPolynomial.eval₂_rename_prod_mk

theorem eval_rename_prod_mk (g : σ × τ → R) (i : σ) (p : MvPolynomial τ R) :
    eval g (rename (Prod.mk i) p) = eval (fun j => g (i, j)) p :=
  eval₂_rename_prod_mk (RingHom.id _) _ _ _
#align mv_polynomial.eval_rename_prodmk MvPolynomial.eval_rename_prod_mk

end

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_finset_rename (p : MvPolynomial σ R) :
    ∃ (s : Finset σ) (q : MvPolynomial { x // x ∈ s } R), p = rename (↑) q := by
  classical
  apply induction_on p
  · intro r
    exact ⟨∅, C r, by rw [rename_C]⟩
  · rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩
    refine' ⟨s ∪ t, ⟨_, _⟩⟩
    · refine' rename (Subtype.map id _) p + rename (Subtype.map id _) q <;>
        simp (config := { contextual := true }) only [id.def, true_or_iff, or_true_iff,
          Finset.mem_union, forall_true_iff]
    · simp only [rename_rename, AlgHom.map_add]
      rfl
  · rintro p n ⟨s, p, rfl⟩
    refine' ⟨insert n s, ⟨_, _⟩⟩
    · refine' rename (Subtype.map id _) p * X ⟨n, s.mem_insert_self n⟩
      simp (config := { contextual := true }) only [id.def, or_true_iff, Finset.mem_insert,
        forall_true_iff]
    · simp only [rename_rename, rename_X, Subtype.coe_mk, AlgHom.map_mul]
      rfl
#align mv_polynomial.exists_finset_rename MvPolynomial.exists_finset_rename

/-- `exists_finset_rename` for two polynomials at once: for any two polynomials `p₁`, `p₂` in a
  polynomial semiring `R[σ]` of possibly infinitely many variables, `exists_finset_rename₂` yields
  a finite subset `s` of `σ` such that both `p₁` and `p₂` are contained in the polynomial semiring
  `R[s]` of finitely many variables. -/
theorem exists_finset_rename₂ (p₁ p₂ : MvPolynomial σ R) :
    ∃ (s : Finset σ) (q₁ q₂ : MvPolynomial s R), p₁ = rename (↑) q₁ ∧ p₂ = rename (↑) q₂ := by
  obtain ⟨s₁, q₁, rfl⟩ := exists_finset_rename p₁
  -- ⊢ ∃ s q₁_1 q₂, ↑(rename Subtype.val) q₁ = ↑(rename Subtype.val) q₁_1 ∧ p₂ = ↑( …
  obtain ⟨s₂, q₂, rfl⟩ := exists_finset_rename p₂
  -- ⊢ ∃ s q₁_1 q₂_1, ↑(rename Subtype.val) q₁ = ↑(rename Subtype.val) q₁_1 ∧ ↑(ren …
  classical
    use s₁ ∪ s₂
    use rename (Set.inclusion <| s₁.subset_union_left s₂) q₁
    use rename (Set.inclusion <| s₁.subset_union_right s₂) q₂
    constructor -- porting note: was `<;> simp <;> rfl` but Lean couldn't infer the arguments
    · rw [rename_rename (Set.inclusion <| s₁.subset_union_left s₂)]
      rfl
    · rw [rename_rename (Set.inclusion <| s₁.subset_union_right s₂)]
      rfl
#align mv_polynomial.exists_finset_rename₂ MvPolynomial.exists_finset_rename₂

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_fin_rename (p : MvPolynomial σ R) :
    ∃ (n : ℕ) (f : Fin n → σ) (_hf : Injective f) (q : MvPolynomial (Fin n) R), p = rename f q := by
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p
  -- ⊢ ∃ n f _hf q_1, ↑(rename Subtype.val) q = ↑(rename f) q_1
  let n := Fintype.card { x // x ∈ s }
  -- ⊢ ∃ n f _hf q_1, ↑(rename Subtype.val) q = ↑(rename f) q_1
  let e := Fintype.equivFin { x // x ∈ s }
  -- ⊢ ∃ n f _hf q_1, ↑(rename Subtype.val) q = ↑(rename f) q_1
  refine' ⟨n, (↑) ∘ e.symm, Subtype.val_injective.comp e.symm.injective, rename e q, _⟩
  -- ⊢ ↑(rename Subtype.val) q = ↑(rename (Subtype.val ∘ ↑e.symm)) (↑(rename ↑e) q)
  rw [← rename_rename, rename_rename e]
  -- ⊢ ↑(rename Subtype.val) q = ↑(rename Subtype.val) (↑(rename (↑e.symm ∘ ↑e)) q)
  simp only [Function.comp, Equiv.symm_apply_apply, rename_rename]
  -- 🎉 no goals
#align mv_polynomial.exists_fin_rename MvPolynomial.exists_fin_rename

end Rename

theorem eval₂_cast_comp (f : σ → τ) (c : ℤ →+* R) (g : τ → R) (p : MvPolynomial σ ℤ) :
    eval₂ c (g ∘ f) p = eval₂ c g (rename f p) := by
  apply MvPolynomial.induction_on p (fun n => by simp only [eval₂_C, rename_C])
    (fun p q hp hq => by simp only [hp, hq, rename, eval₂_add, AlgHom.map_add])
    fun p n hp => by simp only [eval₂_mul, hp, eval₂_X, comp_apply, map_mul, rename_X, eval₂_mul]
#align mv_polynomial.eval₂_cast_comp MvPolynomial.eval₂_cast_comp

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
    simp only [*, AlgHom.map_add, coeff_add]
#align mv_polynomial.coeff_rename_map_domain MvPolynomial.coeff_rename_mapDomain

theorem coeff_rename_eq_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
    (h : ∀ u : σ →₀ ℕ, u.mapDomain f = d → φ.coeff u = 0) : (rename f φ).coeff d = 0 := by
  classical
  rw [rename_eq, ← not_mem_support_iff]
  intro H
  replace H := mapDomain_support H
  rw [Finset.mem_image] at H
  obtain ⟨u, hu, rfl⟩ := H
  specialize h u rfl
  simp at h hu
  contradiction
#align mv_polynomial.coeff_rename_eq_zero MvPolynomial.coeff_rename_eq_zero

theorem coeff_rename_ne_zero (f : σ → τ) (φ : MvPolynomial σ R) (d : τ →₀ ℕ)
    (h : (rename f φ).coeff d ≠ 0) : ∃ u : σ →₀ ℕ, u.mapDomain f = d ∧ φ.coeff u ≠ 0 := by
  contrapose! h
  -- ⊢ coeff d (↑(rename f) φ) = 0
  apply coeff_rename_eq_zero _ _ _ h
  -- 🎉 no goals
#align mv_polynomial.coeff_rename_ne_zero MvPolynomial.coeff_rename_ne_zero

@[simp]
theorem constantCoeff_rename {τ : Type*} (f : σ → τ) (φ : MvPolynomial σ R) :
    constantCoeff (rename f φ) = constantCoeff φ := by
  apply φ.induction_on
  · intro a
    -- ⊢ ↑constantCoeff (↑(rename f) (↑C a)) = ↑constantCoeff (↑C a)
    simp only [constantCoeff_C, rename_C]
    -- 🎉 no goals
  · intro p q hp hq
    -- ⊢ ↑constantCoeff (↑(rename f) (p + q)) = ↑constantCoeff (p + q)
    simp only [hp, hq, RingHom.map_add, AlgHom.map_add]
    -- 🎉 no goals
  · intro p n hp
    -- ⊢ ↑constantCoeff (↑(rename f) (p * X n)) = ↑constantCoeff (p * X n)
    simp only [hp, rename_X, constantCoeff_X, RingHom.map_mul, AlgHom.map_mul]
    -- 🎉 no goals
#align mv_polynomial.constant_coeff_rename MvPolynomial.constantCoeff_rename

end Coeff

section Support

theorem support_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} [DecidableEq τ]
    (h : Function.Injective f) :
    (rename f p).support = Finset.image (Finsupp.mapDomain f) p.support := by
  rw [rename_eq]
  -- ⊢ support (Finsupp.mapDomain (Finsupp.mapDomain f) p) = Finset.image (Finsupp. …
  exact Finsupp.mapDomain_support_of_injective (mapDomain_injective h) _
  -- 🎉 no goals
#align mv_polynomial.support_rename_of_injective MvPolynomial.support_rename_of_injective

end Support

end MvPolynomial
