module
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.Category.MonCat.Basic

/-!
# AdjoinRootKummer

## Main definitions

* Definition `KummerPolynomial n s := X^n - s`

## Main statements

* The following instances of `AdjoinRoot (KummerPolynomial n s)`
· `Faithfullyflat`
· `SmoothOfRelativeDimension 0`
· `Etale`

## Implementation details

We explicitly construct a submersive presentation for `AdjoinRoot (KummerPolynomial n s)` using the
existing naive presentation for an R-algebra given by generators and relations.

-/

@[expose] public section

noncomputable section

namespace Kummer

open MvPolynomial Ideal Algebra

variable {R : Type*} [CommRing R] {s : R} {n : ℕ}
abbrev ι := Unit

noncomputable def KummerPolynomial (n : ℕ) (s : R) := (Polynomial.X)^n - (Polynomial.C s)

instance : CommRing (AdjoinRoot (KummerPolynomial n s)) := inferInstance

noncomputable instance : Algebra R (AdjoinRoot (KummerPolynomial n s)) := inferInstance

private lemma hnzero (hn : IsUnit (n : R)) [Nontrivial R] : n ≠ 0 := by
      by_contra h
      have : (n : R) = 0 := by rw[h]; exact AddMonoidWithOne.natCast_zero
      have h2 := IsUnit.ne_zero hn
      contradiction

lemma KummerPolynomial_monic_of_IsUnit (hn : IsUnit (n : R)) [Nontrivial R] :
  (KummerPolynomial n s).Monic :=
   Polynomial.leadingCoeff_X_pow_sub_C (Nat.zero_lt_of_ne_zero (hnzero hn))

--needed for kummer sequence, could also move it there, also idk why none of the tactics worked here
lemma root_exists (n : ℕ) (s : R) : ∃ t : AdjoinRoot (KummerPolynomial n s), t^n
  = algebraMap R (AdjoinRoot (KummerPolynomial n s)) s := by
  refine ⟨AdjoinRoot.root (KummerPolynomial n s), ?_⟩
  have hrewrite :
      (AdjoinRoot.root (KummerPolynomial n s)) ^ n -
        algebraMap R (AdjoinRoot (KummerPolynomial n s)) s =
        (KummerPolynomial n s).eval₂ (algebraMap R (AdjoinRoot (KummerPolynomial n s)))
        (AdjoinRoot.root (KummerPolynomial n s))
       := by
      change AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C s) ^ n +
          -(algebraMap R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C s)) s)
          =
           Polynomial.eval₂ (algebraMap R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C s)))
          (AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C s))
          (Polynomial.X ^ n + -Polynomial.C s)
      simp only [AdjoinRoot.algebraMap_eq, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_neg, Polynomial.eval₂_C]
  exact sub_eq_zero.mp (hrewrite.trans (AdjoinRoot.eval₂_root (KummerPolynomial n s)))

--These definitions are used to define a submersive presentation of AdjoinRoot KummerPolynomial
--need better names?
noncomputable def v (n : ℕ) (s : R) : ι → (MvPolynomial ι R) :=
  fun 0 => (X 0)^n - MvPolynomial.C s

noncomputable def I (n : ℕ) (s : R) :=  (Ideal.span <| Set.range (v n s))

noncomputable def t (n : ℕ) (s : R) : (MvPolynomial ι R)⧸ (I n s) → (MvPolynomial ι R) :=
  Function.surjInv Ideal.Quotient.mk_surjective

--useful rewrite
lemma _mem_I (x : MvPolynomial ι R) :
  x ∈ I n s ↔ ∃ g, ((X 0)^n - MvPolynomial.C s)* g = x := by
  have hv : Set.range (v n s) = {(X 0)^n - MvPolynomial.C s} := by simp[v]
  have : Ideal.span {(X 0)^n - MvPolynomial.C s} = Ideal.span {(X 0)^n - MvPolynomial.C s} * ⊤ :=
    by simp
  simp [I, hv]
  simpa [this] using
    (@Ideal.mem_span_singleton_mul (MvPolynomial ι R) _ x ((X 0)^n - MvPolynomial.C s) ⊤)

-- name?
noncomputable instance Quotient_iso_AdjoinRoot (n : ℕ) (s : R) :
  ((MvPolynomial ι R)⧸ (I n s)) ≃ₐ[R] (AdjoinRoot (KummerPolynomial n s)) := by
  let base_map : MvPolynomial ι R →ₐ[R] AdjoinRoot (KummerPolynomial n s) :=
    AlgHom.comp (Ideal.Quotient.mkₐ R (Ideal.span {KummerPolynomial n s}))
    (MvPolynomial.pUnitAlgEquiv R)
  have hI : I n s = RingHom.ker base_map.toRingHom := by
    ext a
    constructor
    · intro h
      change (Ideal.Quotient.mkₐ R (Ideal.span {KummerPolynomial n s}))
       (MvPolynomial.pUnitAlgEquiv R a) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have : Ideal.span {KummerPolynomial n s} = Ideal.span {KummerPolynomial n s} * ⊤ := by simp
      rw[this]
      apply (@Ideal.mem_span_singleton_mul (Polynomial R) _ (MvPolynomial.pUnitAlgEquiv R a)
       (KummerPolynomial n s) ⊤).mpr
      obtain ⟨g, hg⟩ := (_mem_I a).mp h
      use (pUnitAlgEquiv R) g
      exact ⟨by simp, by simp[KummerPolynomial, hg.symm]⟩
    intro h
    simp only[base_map] at h
    apply Ideal.Quotient.eq_zero_iff_mem.mp at h
    rw[_mem_I]
    rw[← mul_top (Ideal.span {KummerPolynomial n s})] at h
    obtain ⟨g, hg⟩ :=
      (@Ideal.mem_span_singleton_mul (Polynomial R) _ ((MvPolynomial.pUnitAlgEquiv R a))
      (KummerPolynomial n s) ⊤).mp h
    use (MvPolynomial.pUnitAlgEquiv R).symm g
    have : (MvPolynomial.pUnitAlgEquiv R).symm (KummerPolynomial n s) =
     ((X 0 ^ n - MvPolynomial.C s) : MvPolynomial ι R):= by simp only [KummerPolynomial,
       pUnitAlgEquiv_symm_apply, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C,
       PUnit.zero_eq]
    rw[← this, ← map_mul, hg.2]
    exact ((pUnitAlgEquiv R).left_inv a)
  rw[hI]
  refine quotientKerAlgEquivOfSurjective ?_
  intro x
  have : ∃ y,  x = (Ideal.Quotient.mkₐ R _) y := by
    obtain ⟨y, hy⟩ := Quotient.mkₐ_surjective R (Ideal.span {KummerPolynomial n s}) x
    exact ⟨y, hy.symm⟩
  obtain ⟨p, hy⟩ := this
  use (MvPolynomial.pUnitAlgEquiv R).symm p
  simp only[base_map, hy]
  refine (DFunLike.congr_arg (Quotient.mkₐ R (Ideal.span {KummerPolynomial n s})) ?_)
  exact (pUnitAlgEquiv R).right_inv p

--stronger than the existing nontrivial for R a domain
theorem nontrivial [Nontrivial R] (hn : n ≠ 0) (hs : s ≠ 0) :
  Nontrivial (AdjoinRoot (KummerPolynomial n s)) := by
    simp only[AdjoinRoot]
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    refine (ne_top_iff_one (Ideal.span {KummerPolynomial n s})).mpr ?_
    intro h
    have : Ideal.span {KummerPolynomial n s} = Ideal.span {KummerPolynomial n s} * ⊤ := by simp
    rw[this] at h
    apply (@Ideal.mem_span_singleton_mul (Polynomial R) _ 1 (KummerPolynomial n s) ⊤).mp at h
    rcases h with ⟨g, ⟨hg1,hgf⟩⟩
    have hdeg : ((KummerPolynomial n s) * g).degree = 0 := by
      rw[hgf]
      exact Polynomial.degree_one
    by_cases hgz: g ≠ 0
    · have hdeg' : n + g.natDegree ≤ ((KummerPolynomial n s) * g).degree  := by
        refine @Polynomial.le_degree_of_ne_zero R (n + g.natDegree) _ _ ?_
        have hgdeg: g.natDegree = g.degree := Eq.symm (Polynomial.degree_eq_natDegree hgz)
        have hprod : ((KummerPolynomial n s) * g).coeff ((n + g.natDegree)) = g.leadingCoeff := by
          rw[Polynomial.mul_eq_sum_sum]
          have : (KummerPolynomial n s).support = {0 , n} := by
            ext x
            simp only [Polynomial.mem_support_iff, ne_eq, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · contrapose!
              intro hx
              simp only [KummerPolynomial, Polynomial.coeff_sub, Polynomial.coeff_X_pow, hx,
                ↓reduceIte, Polynomial.coeff_C, sub_self]
            · intro hx
              dsimp [KummerPolynomial]
              rcases hx with h1 | h2
              · simp only [h1, Polynomial.coeff_sub, Polynomial.coeff_X_pow, hn.symm, ↓reduceIte,
                Polynomial.coeff_C_zero, zero_sub, neg_eq_zero]
                exact hs
              simp only [h2, Polynomial.coeff_sub, Polynomial.coeff_X_pow, ↓reduceIte,
                Polynomial.coeff_C_ne_zero hn, sub_zero, one_ne_zero, not_false_eq_true]
          rw[this]
          have : (∑ i ∈ {0, n}, g.sum fun j a ↦
            (Polynomial.monomial (i + j)) ((KummerPolynomial n s).coeff i * a))
            = (Polynomial.X)^n * g - (Polynomial.C s) * g := by
            simp only [Polynomial.sum, KummerPolynomial, Polynomial.coeff_sub,
            Polynomial.coeff_X_pow]
            rw[Finset.sum_pair]
            · rw[Polynomial.coeff_C_zero, Polynomial.coeff_C_ne_zero hn]
              simp only [zero_add, hn.symm, ↓reduceIte, zero_sub, neg_mul, Polynomial.monomial_neg,
                Finset.sum_neg_distrib, sub_zero, one_mul]
              simp_rw [← Polynomial.C_mul_monomial]
              rw [← Finset.mul_sum]
              have hcoeff : ∀ (x : g.support), g.coeff x = (1 : R) * (g.coeff x) :=
                fun x => (one_mul (g.coeff x)).symm
              have : ∑ x ∈ g.support, (Polynomial.monomial (n + x)) (g.coeff x)
                =  (∑ x ∈ g.support,
                  (Polynomial.monomial n 1) * ((Polynomial.monomial x) (g.coeff x))) := by
                  apply Finset.sum_congr rfl
                  intro x hx
                  rw[hcoeff ⟨x,hx⟩]
                  simp [Polynomial.monomial_mul_monomial]
              rw[this,← Finset.mul_sum,← Polynomial.as_sum_support,
                Polynomial.monomial_one_right_eq_X_pow]
              ring_nf
            · exact hn.symm
          rw[this]
          simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
          rw[← Polynomial.monomial_one_right_eq_X_pow]
          rw [add_comm, Polynomial.coeff_monomial_mul, Polynomial.coeff_natDegree]
          have hcoeff0 : g.coeff (g.natDegree + n) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt
              (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hn))
          simp only [one_mul, hcoeff0, mul_zero, sub_zero]
        rw[hprod]
        exact Polynomial.leadingCoeff_ne_zero.mpr hgz
      have : ((KummerPolynomial n s) * g).degree ≠ 0 := by
        have hpos : 0 < n + g.natDegree := Nat.lt_add_right g.natDegree (pos_iff_ne_zero.mpr hn)
        have : 0 < (KummerPolynomial n s * g).degree :=
          by simpa using lt_of_le_of_lt' hdeg' (mod_cast hpos)
        exact Ne.symm (ne_of_lt this)
      contradiction
    · push_neg at hgz
      have : (KummerPolynomial n s) * g = 0 := mul_eq_zero_of_right (KummerPolynomial n s) hgz
      rw[hgf] at this
      have : (1: Polynomial R) ≠ 0 := one_ne_zero
      contradiction

set_option backward.isDefEq.respectTransparency false in
theorem FaithFullyFlat (hn : IsUnit (n : R)) (hs : IsUnit s) :
  Module.FaithfullyFlat R (AdjoinRoot (KummerPolynomial n s)) := by
  by_cases h : Nontrivial R
  · have := nontrivial (hnzero hn) (hs.ne_zero)
    have hfree : Module.Free R (AdjoinRoot (KummerPolynomial n s)) :=
    Polynomial.Monic.free_adjoinRoot (KummerPolynomial_monic_of_IsUnit hn)
    exact Module.FaithfullyFlat.instOfNontrivialOfFree R _
  · apply not_nontrivial_iff_subsingleton.mp at h
    have : Module.Flat R (AdjoinRoot (KummerPolynomial n s)) := by
      refine Module.Flat.iff_lTensor_injectiveₛ.mpr ?_
      intro M i1 i2 N
      have tp1 : Subsingleton (TensorProduct R (AdjoinRoot (KummerPolynomial n s)) N) :=
        (Module.subsingletonEquiv R (TensorProduct R _ N) Empty).subsingleton
      intro x y hxy
      exact tp1.allEq x y
    apply (Module.FaithfullyFlat.iff_flat_and_proper_ideal R _).mpr
    constructor
    · exact this
    intro I hI
    have : I = ⊤ := by
      ext x
      have hx : x = 0 := by exact Subsingleton.eq_zero x
      rw[hx]
      simp only [zero_mem]
    contradiction

noncomputable instance _instPreSubmersive (n : ℕ) (s : R) :
   Algebra.PreSubmersivePresentation R ((MvPolynomial ι R)⧸ (I n s)) ι ι :=
 have : ∀ x, Ideal.Quotient.mk _ ((t n s) x) = x := by apply Function.surjInv_eq
 PreSubmersivePresentation.naive (id : ι → ι) (by exact fun ⦃a₁ a₂⦄ ↦ congrFun rfl) (t n s) (this)

lemma _jacobi : (_instPreSubmersive n s).jacobiMatrix =
  Matrix.diagonal (fun () ↦ ((v n s) ()).pderiv ()) := by
  ext (i : Unit) (j : Unit) : 1
  simp[I, _instPreSubmersive, v, PreSubmersivePresentation.jacobiMatrix,
    PreSubmersivePresentation.differential]

lemma _jacobian : (_instPreSubmersive n s).jacobian =
  Ideal.Quotient.mk _ ((MvPolynomial.C (n : R))*(X (0:ι))^(n-1)) := by
  have : ((v n s) ()).pderiv () = (MvPolynomial.C (n : R))*(X (0:ι))^(n-1) := by simp[v]
  rw[← this]
  rw[PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, _jacobi]
  simp only [Matrix.det_unique, PUnit.default_eq_unit, Matrix.diagonal_apply_eq,
    Generators.algebraMap_apply]
  simp only [pderiv, v, PUnit.zero_eq, map_sub, Derivation.leibniz_pow, mkDerivation_X,
    Pi.single_eq_same, smul_eq_mul, mul_one, nsmul_eq_mul, derivation_C, sub_zero, map_mul,
    map_natCast, map_pow, MvPolynomial.aeval_X]
  exact MonCat.mul_of (↑n) ((_instPreSubmersive n s).val PUnit.unit ^ (n - 1))

--is transported to adjoin root later
noncomputable instance _instSubmersivePresentation (hn : IsUnit (n : R)) (hs : IsUnit s) :
  SubmersivePresentation R ((MvPolynomial ι R)⧸ (I n s)) ι ι where
  __ := _instPreSubmersive (n : ℕ) (s: R)
  jacobian_isUnit := by
    by_cases h : Nontrivial R
    · have hnzero : n≠ 0 := hnzero hn
      obtain ⟨s', hu⟩ := IsUnit.exists_right_inv hs
      obtain ⟨n', hn⟩ := IsUnit.exists_left_inv hn
      have : Ideal.Quotient.mk (I n s) ((X 0)^n) = Ideal.Quotient.mk (_) (MvPolynomial.C s) := by
        apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (X ()^n) (C s)).mpr
        simp only [I]
        apply Ideal.subset_span
        use 1
        rw[v]
      have : Ideal.Quotient.mk (I n s) ((X 0)^n) = (algebraMap R ((MvPolynomial ι R)⧸ (I n s)) s)
        := by rw[this]; rfl
      let a := Ideal.Quotient.mk (I n s) ((MvPolynomial.C (n : R))*(X (0:ι))^(n-1))
      let b := (Ideal.Quotient.mk _
        ((MvPolynomial.C (n':R))*(X 0)))*algebraMap R ((MvPolynomial ι R)⧸ (I n s)) s'
      have : a * b = 1 := by
        calc a * b = (Ideal.Quotient.mk (I n s) ((MvPolynomial.C (n : R))*(X (0:ι))^(n-1))) *
                    (Ideal.Quotient.mk _ ((MvPolynomial.C (n':R))*(X 0)))*algebraMap R
                    ((MvPolynomial ι R)⧸ (I n s)) s' := by ring
                  _ = Ideal.Quotient.mk (I n s) ((MvPolynomial.C (n : R))*(X (0:ι))^(n-1) *
                    (MvPolynomial.C (n':R))*(X 0)) *
                    (algebraMap R ((MvPolynomial ι R)⧸ (I n s)) s') := by
                        rw[← map_mul (Ideal.Quotient.mk (I n s)) _ _]
                        group
                  _ = Ideal.Quotient.mk (I n s) ((MvPolynomial.C (1 : R)) * (X (0:ι))^n)
                    * (algebraMap R ((MvPolynomial ι R)⧸ (I n s)) s'):= by
                      rw[mul_comm (MvPolynomial.C ((n : R))*(X (0:ι))^(n-1)) (MvPolynomial.C n')]
                      rw[← mul_assoc,← map_mul MvPolynomial.C, hn, mul_assoc]
                      rw[mul_comm ((X (0:ι))^(n-1)) (X 0), mul_pow_sub_one (hnzero) (X 0)]
                  _ = 1* Ideal.Quotient.mk (_) ((X 0)^n) *
                    (algebraMap R ((MvPolynomial ι R)⧸ (I n s)) s') := by
                      rw[map_mul (Ideal.Quotient.mk (_))]
                      repeat rw[map_one]
                  _ = 1 := by
                      rw[this, mul_assoc, ← map_mul, hu]
                      simp only [map_one, mul_one]
      rw [_jacobian]
      refine IsUnit.of_mul_eq_one b this
    apply not_nontrivial_iff_subsingleton.mp at h
    have : MulActionWithZero R (MvPolynomial ι R ⧸ I n s) := by exact Module.toMulActionWithZero
    have hsub : Subsingleton (MvPolynomial ι R ⧸ I n s) := Module.subsingleton R _
    refine (@isUnit_iff_eq_one (MvPolynomial ι R ⧸ I n s) _ ?_).mpr ?_
    exact Subsingleton.eq_one (_instPreSubmersive n s).jacobian


noncomputable instance instSubmersivePresentation (hn : IsUnit (n : R)) (hs : IsUnit s) :
  SubmersivePresentation R (AdjoinRoot (KummerPolynomial n s)) ι ι :=
  Algebra.SubmersivePresentation.ofAlgEquiv (_instSubmersivePresentation hn hs)
    (Quotient_iso_AdjoinRoot n s)

noncomputable instance instIsStandardSmoothOfRelativeDimension_zero (hn : IsUnit (n : R))
  (hs : IsUnit s) : Algebra.IsStandardSmoothOfRelativeDimension 0 R
  (AdjoinRoot (KummerPolynomial n s))
  := ⟨ι, ι, inferInstance, inferInstance, instSubmersivePresentation (hn) (hs),
   by simp[Presentation.dimension]⟩

noncomputable instance instEtale (hn : IsUnit (n : R)) (hs : IsUnit s) :
  Algebra.Etale R (AdjoinRoot (KummerPolynomial n s)) :=
  @Algebra.instEtaleOfIsStandardSmoothOfRelativeDimensionOfNatNat _ _ _ _ _
  (instIsStandardSmoothOfRelativeDimension_zero hn hs)

end Kummer
