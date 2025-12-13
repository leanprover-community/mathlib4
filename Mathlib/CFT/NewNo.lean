module

public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-! #foo -/

@[expose] public section

open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

section

open scoped Polynomial
open TensorProduct

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (n m k : ℕ) (hn : n = m + k)

variable {R n} (p : Polynomial.MonicDegreeEq R n)

namespace Polynomial

local notation "𝓡" => UniversalFactorizationRing m k hn p

local notation "𝓡'" => UniversalCoprimeFactorizationRing m k hn p

open scoped nonZeroDivisors

/-- If a monic polynomial `p : R[X]` factors into a product of coprime monic polynomials `p = f * g`
in the residue field `κ(P)` of some `P : Spec R`,
then there exists `Q : Spec R_univ` in the universal coprime factorization ring lying over `P`,
such that `κ(P) = κ(Q)` and `f` and `g` are the image of the universal factors. -/
@[stacks 00UH]
lemma UniversalCoprimeFactorizationRing.exists_liesOver_residueFieldMap_bijective
    (P : Ideal R) [P.IsPrime]
    (f : MonicDegreeEq P.ResidueField m) (g : MonicDegreeEq P.ResidueField k)
    (H : p.1.map (algebraMap R _) = f.1 * g.1) (Hpq : IsCoprime f.1 g.1) :
    ∃ (Q : Ideal 𝓡') (_ : Q.IsPrime) (_ : Q.LiesOver P),
    Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)) ∧
    f.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      (factor₁ m k hn p).map (algebraMap _ _) ∧
    g.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      (factor₂ m k hn p).map (algebraMap _ _) := by
  let φ : 𝓡' →ₐ[R] P.ResidueField :=
    (UniversalCoprimeFactorizationRing.homEquiv _ m k hn p).symm ⟨(f, g), H.symm, Hpq⟩
  let Q := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : Q.LiesOver P := ⟨by rw [Ideal.under, RingHom.comap_ker, AlgHom.toRingHom_eq_coe,
      φ.comp_algebraMap, Ideal.ker_algebraMap_residueField]⟩
  let φ' : Q.ResidueField →ₐ[R] P.ResidueField := Ideal.ResidueField.liftₐ _ φ le_rfl (by
    simp [SetLike.le_def, IsUnit.mem_submonoid_iff, Q])
  let φi : P.ResidueField →ₐ[R] Q.ResidueField :=
    Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) (Ideal.over_def _ _)
  let e : P.ResidueField ≃ₐ[R] Q.ResidueField :=
    .ofAlgHom φi φ' (AlgHom.ext fun x ↦ φ'.injective <|
      show (φ'.comp φi) (φ' x) = AlgHom.id R _ (φ' x) by congr; ext) (by ext)
  have H : φi.comp φ = (IsScalarTower.toAlgHom _ _ _) :=
    AlgHom.ext fun x ↦ e.eq_symm_apply.mp (by simp [e, φ'])
  refine ⟨Q, ‹_›, ‹_›, e.bijective, ?_, ?_⟩
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.1
    · simp [homEquiv_comp_fst, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₁,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.2
    · simp [homEquiv_comp_snd, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₂,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl

open UniversalCoprimeFactorizationRing in
/-- If a monic polynomial `p : R[X]` factors into a product of coprime monic polynomials `p = f * g`
in the residue field `κ(P)` of some `P : Spec R`,
then there exists `Q : Spec R_univ` in the universal coprime factorization ring lying over `P`,
such that `κ(P) = κ(Q)` and `f` and `g` are the image of the universal factors. -/
@[stacks 00UH]
lemma exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime.{u}
    {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] (p : R[X])
    (f g : P.ResidueField[X]) (hp : p.Monic) (hf : f.Monic) (hg : g.Monic)
    (H : p.map (algebraMap R _) = f * g) (Hpq : IsCoprime f g) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (Q : Ideal R') (_ : Q.IsPrime) (_ : Q.LiesOver P) (f' g' : R'[X]),
    Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)) ∧
    f'.Monic ∧ g'.Monic ∧ p.map (algebraMap R R') = f' * g' ∧ IsCoprime f' g' ∧
    f.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      f'.map (algebraMap _ _) ∧
    g.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      g'.map (algebraMap _ _) := by
  obtain ⟨Q, _, _, h₁, h₂, h₃⟩ :=
    exists_liesOver_residueFieldMap_bijective f.natDegree g.natDegree
    (by simpa [hf.natDegree_mul hg, hp.natDegree_map] using congr(($H).natDegree)) (.mk p hp rfl)
    P (.mk f hf rfl) (.mk g hg rfl) H Hpq
  exact ⟨_, _, _, inferInstance, Q, ‹_›, ‹_›, (factor₁ ..).1, (factor₂ ..).1, h₁,
    (factor₁ ..).monic, (factor₂ ..).monic, (factor₁_mul_factor₂ ..).symm,
    isCoprime_factor₁_factor₂ .., congr(($h₂).1), congr(($h₃).1)⟩

end Polynomial

end

noncomputable
def Ideal.tensorProductEquivOfBijectiveResidueFieldMap
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p))) :
    q.primesOver (R' ⊗[R] S) ≃o p.primesOver S :=
  let e : q.Fiber (R' ⊗[R] S) ≃ₐ[p.ResidueField] p.Fiber S :=
    ((Algebra.TensorProduct.cancelBaseChange _ _ q.ResidueField _ _).restrictScalars _).trans
      (Algebra.TensorProduct.congr (.symm <| .ofBijective (Algebra.ofId _ _) H) .refl)
  (PrimeSpectrum.primesOverOrderIsoFiber ..).trans <|
    (PrimeSpectrum.comapEquiv e.toRingEquiv).trans (PrimeSpectrum.primesOverOrderIsoFiber ..).symm

@[simp]
lemma PrimeSpectrum.comapEquiv_symm_apply'.{u, v} {R : Type u} {S : Type v} [CommSemiring R]
    [CommSemiring S] (e : R ≃+* S) : (comapEquiv e).symm = comapEquiv e.symm := rfl

lemma Ideal.comap_tensorProductEquivOfBijectiveResidueFieldMap_symm
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : p.primesOver S) :
    ((Ideal.tensorProductEquivOfBijectiveResidueFieldMap H).symm Q).1.comap
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) = Q.1 := by
  ext x
  simp [Ideal.tensorProductEquivOfBijectiveResidueFieldMap,
    PrimeSpectrum.primesOverOrderIsoFiber, PrimeSpectrum.preimageOrderIsoFiber,
    PrimeSpectrum.preimageEquivFiber]

@[simp]
lemma Ideal.comap_tensorProductEquivOfBijectiveResidueFieldMap_apply
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : q.primesOver (R' ⊗[R] S)) :
    (Ideal.tensorProductEquivOfBijectiveResidueFieldMap H Q).1 =
      Q.1.comap Algebra.TensorProduct.includeRight := by
  simpa using (Ideal.comap_tensorProductEquivOfBijectiveResidueFieldMap_symm H
    (Ideal.tensorProductEquivOfBijectiveResidueFieldMap H Q)).symm

lemma Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (P₁ P₂ : Ideal (R' ⊗[R] S)) [P₁.IsPrime] [P₂.IsPrime] [P₁.LiesOver q] [P₂.LiesOver q]
    (H₂ : P₁.comap Algebra.TensorProduct.includeRight.toRingHom =
      P₂.comap Algebra.TensorProduct.includeRight.toRingHom) : P₁ = P₂ := by
  refine congr_arg Subtype.val ((Ideal.tensorProductEquivOfBijectiveResidueFieldMap
  (S := S) H).injective (a₁ := ⟨P₁, ‹_›, ‹_›⟩) (a₂ := ⟨P₂, ‹_›, ‹_›⟩) (by ext1; simpa))

lemma PrimeSpectrum.toPiLocalization_bijective {R : Type*} [CommRing R]
    [DiscreteTopology (PrimeSpectrum R)] : Function.Bijective (PrimeSpectrum.toPiLocalization R) :=
  PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp inferInstance

lemma IsArtinianRing.exists_not_mem_forall_mem_of_ne
    {R : Type*} [CommRing R] [IsArtinianRing R] (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, IsIdempotentElem r ∧ ∀ q : Ideal R, q.IsPrime → q ≠ p → r ∈ q := by
  classical
  obtain ⟨r, hr⟩ := PrimeSpectrum.toPiLocalization_bijective.2 (Pi.single ⟨p, inferInstance⟩ 1)
  have : algebraMap R (Localization p.primeCompl) r = 1 := by
    simpa [PrimeSpectrum.toPiLocalization,
      -FaithfulSMul.algebraMap_eq_one_iff] using funext_iff.mp hr ⟨p, inferInstance⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, this]
    simp
  · apply PrimeSpectrum.toPiLocalization_bijective.injective
    simp [map_mul, hr, ← Pi.single_mul]
  · intro q hq e
    have : PrimeSpectrum.mk q inferInstance ≠ ⟨p, inferInstance⟩ := ne_of_apply_ne (·.1) e
    have : (algebraMap R (Localization.AtPrime q)) r = 0 := by
      simpa [PrimeSpectrum.toPiLocalization, this,
        -FaithfulSMul.algebraMap_eq_zero_iff] using funext_iff.mp hr ⟨q, inferInstance⟩
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, this]
    simp

attribute [local instance high] Algebra.TensorProduct.leftAlgebra IsScalarTower.right
  DivisionRing.instIsArtinianRing in
lemma exists_not_mem_forall_mem_of_ne_of_liesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    ∃ s ∉ q, ∀ q' : Ideal S, q'.IsPrime → q' ≠ q → q'.LiesOver p → s ∈ q' := by
  classical
  let F := p.Fiber S
  let e := PrimeSpectrum.preimageEquivFiber _ S ⟨p, inferInstance⟩
  let : IsArtinianRing F := .of_finite p.ResidueField _
  obtain ⟨r : p.Fiber S, hr, hr'⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne
    (e ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩).asIdeal
  obtain ⟨s, hs, x, hsx⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ r
  have : x ∉ q := by
    rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal,
        ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s), ← Algebra.smul_def, hsx] at hr
    · simpa using hr
    · simpa [IsScalarTower.algebraMap_apply R S q.ResidueField, q.over_def p] using hs
  refine ⟨x, this, fun q' _ hq' _ ↦ ?_⟩
  have := Ideal.mul_mem_left _ (algebraMap _ _ s) (hr'.2 (e ⟨⟨q', ‹_›⟩,  PrimeSpectrum.ext
    (q'.over_def p).symm⟩).asIdeal inferInstance (mt PrimeSpectrum.ext (e.injective.ne (by simpa))))
  rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal, ← Algebra.smul_def, hsx] at this
  simpa using this

@[simp]
lemma MonicDegreeEq.coe_mk {R : Type*} [CommRing R] {n : ℕ} (p : Polynomial R) (hp : p.Monic)
  (hp' : p.natDegree = n) : (Polynomial.MonicDegreeEq.mk p hp hp').1 = p := rfl

open Polynomial in
/--
Let `S` be a module-finite `R`-algebra, and `q` a prime lying over `p`.
We may construct an etale `R`-algebra `R'` and a prime `P` lying over `p` with `κ(P) = κ(p)`,
such that `R' ⊗[R] S = A × B` with a unique prime in `A` lying over `P`, which also lies over `q`.

The actual lemma is stated in terms of the idempotent element `e = (1, 0)`.
-/
@[stacks 00UJ]
lemma exists_etale_isIdempotentElem_forall_liesOver_eq.{u, v}
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S) (_ : IsIdempotentElem e)
      (P' : Ideal (R' ⊗[R] S)) (_ : P'.IsPrime) (_ : P'.LiesOver P), P'.comap
        Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ P' ∧
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P' := by
  classical
  obtain ⟨s, hsq, hs⟩ := exists_not_mem_forall_mem_of_ne_of_liesOver p q
  obtain ⟨m, f, b, hfm, hbm, hab, hfab, hf⟩ : ∃ (m : ℕ) (f : R[X])
      (b : p.ResidueField[X]), f.Monic ∧ b.Monic ∧ IsCoprime (X ^ (m + 1)) b ∧
        f.map (algebraMap _ _) = X ^ (m + 1) * b ∧ aeval s f = 0 := by
    have hs := Algebra.IsIntegral.isIntegral (R := R) s
    let f := X * minpoly R s
    obtain ⟨q, hq, hq'⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd
      ((minpoly R s).map (algebraMap R p.ResidueField)) ((minpoly.monic hs).map _).ne_zero 0
    have hqm : q.Monic := by
      simpa [((minpoly.monic hs).map _).leadingCoeff] using congr(leadingCoeff $hq).symm
    set m' := rootMultiplicity 0 ((minpoly R s).map (algebraMap R p.ResidueField))
    refine ⟨m', f, q, monic_X.mul (minpoly.monic hs), hqm, ?_,
      by simp [f, hq, pow_succ', mul_assoc], by simp [f]⟩
    simpa [IsCoprime.pow_left_iff,
      (prime_X (R := p.ResidueField)).irreducible.coprime_iff_not_dvd] using hq'
  obtain ⟨R', _, _, _, P, _, _, a', b', hP, ha'm, hb'm, hfab', ⟨c, d, hcd⟩, ha', hb'⟩ :=
    exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime p f
      (X ^ (m + 1)) b hfm (monic_X.pow _) hbm hfab hab
  let s' : R' ⊗[R] S := 1 ⊗ₜ s
  have hs'f : aeval s' f = 0 :=
    show aeval (Algebra.TensorProduct.includeRight s) f = 0 by rw [aeval_algHom_apply, hf, map_zero]
  let e := aeval s' (c * a')
  have he : IsIdempotentElem e := by
    dsimp only [e, IsIdempotentElem]
    nth_rw 2 [eq_sub_iff_add_eq.mpr hcd]
    rw [← map_mul, mul_sub, mul_one, mul_mul_mul_comm, ← hfab']
    simp only [map_mul, map_sub, aeval_map_algebraMap, hs'f, mul_zero, sub_zero]
  let P' := (Ideal.tensorProductEquivOfBijectiveResidueFieldMap hP).symm ⟨q, ‹_›, ‹_›⟩
  have hP'q : P'.1.comap Algebra.TensorProduct.includeRight.toRingHom = q :=
    Ideal.comap_tensorProductEquivOfBijectiveResidueFieldMap_symm ..
  have hs'P' : s' ∉ P'.1 := mt (fun h ↦ hP'q.le h) hsq
  have ha'P' : aeval s' a' ∉ P'.1 := by
    simpa using show IsScalarTower.toAlgHom R' _ P'.1.ResidueField (aeval s' a') ≠ 0 by
      rw [← aeval_algHom_apply, ← aeval_map_algebraMap P.ResidueField, ← ha']; simpa
  have hb'P' : aeval s' b' ∈ P'.1 := by
    rw [← Ideal.IsPrime.mul_mem_left_iff ha'P', ← map_mul, ← hfab']
    simp [hs'f]
  have heP' : e ∉ P'.1 := by
    intro H
    have := P'.1.mul_mem_left (aeval s' d) hb'P'
    rw [← map_mul, eq_sub_iff_add_eq'.mpr hcd, map_sub, Submodule.sub_mem_iff_left _ H,
      map_one] at this
    exact Ideal.one_notMem _ this
  refine ⟨_, inferInstance, inferInstance, inferInstance, P, ‹_›, ‹_›,
    e, he, P', inferInstance, P'.2.2, hP'q, heP', hP, fun P'' _ _ H ↦ ?_⟩
  apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hP
  rw [hP'q]
  contrapose! H
  have : s' ∈ P'' := hs _ inferInstance H (by simp [Ideal.liesOver_iff, Ideal.under,
    Ideal.comap_comap, Ideal.over_def P p, Ideal.over_def P'' P, ← IsScalarTower.algebraMap_eq])
  rw [← Ideal.algebraMap_residueField_eq_zero, ← aeval_algebraMap_apply,
    Ideal.algebraMap_residueField_eq_zero.mpr this, ← eval_map_algebraMap, Polynomial.map_mul,
    mul_comm, ← (Ideal.ResidueField.mapₐ P P'' (Algebra.ofId _ _) (P''.over_def P)).comp_algebraMap,
    ← Polynomial.map_map, ← ha']
  simp
