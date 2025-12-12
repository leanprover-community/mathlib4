import Mathlib
-- import Mathlib.CFT.Resultant
-- import Mathlib.CFT.StandardEtale
import Mathlib.CFT.UniversalFactorizationRing

open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

open Algebra.TensorProduct in
noncomputable
def tensorResidueFieldEquiv
    {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    S ⊗[R] p.ResidueField ≃ₐ[S ⧸ Ideal.map (algebraMap R S) p]
    ((S ⧸ Ideal.map (algebraMap R S) p) ⊗[R ⧸ p] p.ResidueField) :=
  letI e : S ⊗[R] p.ResidueField ≃ₐ[R]
    ((S ⧸ Ideal.map (algebraMap R S) p) ⊗[R ⧸ p] p.ResidueField) := by
    refine (Algebra.TensorProduct.comm _ _ _).trans ?_
    refine ((cancelBaseChange R (R ⧸ p) (R ⧸ p) _ _).restrictScalars R).symm.trans ?_
    refine .trans ?_ ((Algebra.TensorProduct.comm _ _ _).restrictScalars R)
    refine (congr (S := R ⧸ p) .refl ?_).restrictScalars R
    refine AlgEquiv.extendScalarsOfSurjective (R := R) Ideal.Quotient.mk_surjective ?_
    refine (Algebra.TensorProduct.comm _ _ _).trans ?_
    exact (quotIdealMapEquivTensorQuot S p).symm.restrictScalars R
  { __ := e, commutes' := Ideal.Quotient.mk_surjective.forall.mpr fun x ↦ by simp [e] }

@[simp]
lemma tensorResidueFieldEquiv_tmul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
        (a : S) (b : p.ResidueField) :
    tensorResidueFieldEquiv S p (a ⊗ₜ b) = (Ideal.Quotient.mk _ a) ⊗ₜ b := by
  simp [tensorResidueFieldEquiv]

@[simp]
lemma tensorResidueFieldEquiv_symm_tmul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
        (a : S) (b : p.ResidueField) :
    (tensorResidueFieldEquiv S p).symm (a ⊗ₜ b) = a ⊗ₜ b :=
  (tensorResidueFieldEquiv S p).symm_apply_eq.mpr (by simp)

@[simp]
lemma tensorResidueFieldEquiv_symm_one_tmul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime]
        (b : p.ResidueField) :
    (tensorResidueFieldEquiv S p).symm (1 ⊗ₜ b) = 1 ⊗ₜ b :=
  (tensorResidueFieldEquiv S p).symm_apply_eq.mpr (by simp)

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ Ideal.map (algebraMap R S) p) (R ⧸ p)⁰)
      (S ⊗[R] p.ResidueField) :=
  have := IsLocalization.tensor p.ResidueField (R ⧸ p)⁰ (S := S ⧸ p.map (algebraMap R S))
  .isLocalization_of_algEquiv _ (tensorResidueFieldEquiv S p).symm

@[simp]
lemma MonicDegreeEq.coe_mk {R : Type*} [CommRing R] {n : ℕ} (p : Polynomial R) (hp : p.Monic)
  (hp' : p.natDegree = n) : (Polynomial.MonicDegreeEq.mk p hp hp').1 = p := rfl

instance {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {e : S} (he : IsIdempotentElem e) : Algebra R he.Corner where
  smul r x := ⟨r • x.1, by
    simp [he, Subsemigroup.mem_corner_iff, (Subsemigroup.mem_corner_iff he).mp x.2]⟩
  algebraMap :=
  { toFun r := ⟨r • e, by simp [he, Subsemigroup.mem_corner_iff, he.eq]⟩
    map_one' := by simp; rfl
    map_mul' a b := Subtype.ext <| show (a * b) • e = (a • e) * (b • e) by
      simp [he.eq, ← mul_smul, mul_comm]
    map_zero' := by simp; rfl
    map_add' a b := Subtype.ext (add_smul _ _ _) }
  commutes' r x := Subtype.ext (show r • e * x.1 = x.1 * r • e by
    simp [(Subsemigroup.mem_corner_iff he).mp x.2])
  smul_def' r x := Subtype.ext (show r • x.1 = (r • e) * x.1 by
    simp [(Subsemigroup.mem_corner_iff he).mp x.2])

instance {R R' S : Type*} [CommSemiring R] [CommSemiring R'] [Semiring S] [Algebra R S]
    [Algebra R R'] [Algebra R' S] [IsScalarTower R R' S]
    {e : S} (he : IsIdempotentElem e) : IsScalarTower R R' he.Corner :=
  .of_algebraMap_eq fun _ ↦ Subtype.ext (IsScalarTower.algebraMap_smul _ _ _).symm

attribute [-simp] FaithfulSMul.ker_algebraMap_eq_bot in
attribute [instance high] CommRing.toCommMonoid Algebra.toModule
  CommMonoid.toMonoid Monoid.toSemigroup Semigroup.toMul in
open Polynomial in
lemma exists_etale_isIdempotentElem_forall_liesOver_eq.{u, v}
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (e : R' ⊗[R] S) (_ : IsIdempotentElem e)
      (P' : Ideal (R' ⊗[R] S)) (_ : P'.IsPrime) (_ : P'.LiesOver P), P'.comap
        Algebra.TensorProduct.includeRight.toRingHom = q ∧ e ∉ P' ∧
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      ∀ P'' : Ideal (R' ⊗[R] S), P''.IsPrime → P''.LiesOver P →
      (e ∉ P'' ∨ P''.comap Algebra.TensorProduct.includeRight.toRingHom = q) → P'' = P' := by
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
  let φ := AlgEquiv.ofBijective _ hP
  let ψ : R' ⊗[R] S →ₐ[R] q.ResidueField := tensorToResidueFieldOfBijectiveMap hP q
  have hψs' : ψ s' = algebraMap S q.ResidueField s := by simp [ψ, s']
  have hψe : ψ e = 1 := by
    have hψa : a'.map ((RingHomClass.toRingHom ψ).comp (algebraMap R' _)) = X ^ (m + 1) := by
      trans (X ^ (m + 1)).map (Ideal.ResidueField.map p q _ (q.over_def p))
      · ext1 i
        simpa [ψ, tensorToResidueFieldOfBijectiveMap,
          (Ideal.ResidueField.map p q _ (q.over_def p)).injective.eq_iff,
          AlgEquiv.symm_apply_eq, -Polynomial.map_pow, -MonoidWithZeroHom.map_ite_one_zero] using
          congr(($ha').coeff i).symm
      · simp
    have : ψ (aeval s' a') ≠ 0 := by
      rw [aeval_def, ← AlgHom.coe_toRingHom, hom_eval₂, ← eval_map, hψa]; simpa [hψs']
    have : ψ (aeval s' b') = 0 := mul_right_injective₀ this <| by
      simp only [← map_mul, ← hfab', mul_zero, aeval_algebraMap_apply, aeval_map_algebraMap,
        ← aeval_algHom_apply, hψs', hf, map_zero]
    simp only [e, eq_sub_iff_add_eq.mpr hcd, map_sub, map_one]
    simp only [map_mul, this, mul_zero, sub_zero]
  let P' := RingHom.ker ψ.toRingHom
  have : P'.LiesOver P := ⟨(under_ker_tensorToResidueFieldOfBijectiveMap ..).symm⟩
  have hP'₁ : P'.comap Algebra.TensorProduct.includeRight.toRingHom = q := by ext; simp [ψ, P']
  refine ⟨_, inferInstance, inferInstance, inferInstance, P, ‹_›, ‹_›,
    e, he, P', inferInstance, ‹_›, hP'₁, by simp [P', hψe], hP, fun P'' _ _ H ↦ ?_⟩
  apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hP
  rw [hP'₁]
  refine H.elim (not_imp_comm.mp <| fun h ↦ ?_) id
  have : s' ∈ P'' := hs _ inferInstance h (by simp [Ideal.liesOver_iff, Ideal.under,
    Ideal.comap_comap, Ideal.over_def P p, Ideal.over_def P'' P, ← IsScalarTower.algebraMap_eq])
  rw [← Ideal.algebraMap_residueField_eq_zero, ← aeval_algebraMap_apply,
    Ideal.algebraMap_residueField_eq_zero.mpr this, ← eval_map_algebraMap, Polynomial.map_mul,
    mul_comm, ← (Ideal.ResidueField.mapₐ P P'' (Algebra.ofId _ _) (P''.over_def P)).comp_algebraMap,
    ← Polynomial.map_map, ← ha']
  simp

attribute [ext high] Ideal.Quotient.algHom_ext

instance {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (I : Ideal T) (J : Ideal R) [I.LiesOver J] : (I.comap f).LiesOver J := by
  constructor; ext; simp [I.over_def J]

lemma comap_smul'' {R M M' : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] {f : M →ₗ[R] M'} (hf : Function.Injective f) {p : Submodule R M'}
    (hp : p ≤ LinearMap.range f) {I : Ideal R} :
    Submodule.comap f (I • p) = I • Submodule.comap f p := by
  refine le_antisymm ?_ (by simp)
  conv_lhs => rw [← Submodule.map_comap_eq_self hp, ← Submodule.map_smul'']
  rw [Submodule.comap_map_eq_of_injective hf]

theorem exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq_aux.{v, u}
  {R : Type u} {S : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
  (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
  [q.LiesOver p] (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R'] (P : Ideal R')
  [P.IsPrime] [P.LiesOver p] (e : R' ⊗[R] S) (P' : Ideal (R' ⊗[R] S))
  [P'.IsPrime] [P'.LiesOver P]
  (hP'q : Ideal.comap Algebra.TensorProduct.includeRight.toRingHom P' = q)
  (heP' : e ∉ P') (hpP : Function.Bijective
    (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)))
  (H : ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P → e ∉ P'' → P'' = P')
  (R'' : Type u) [CommRing R''] [Algebra R' R''] [Algebra R R''] [IsScalarTower R R' R'']
  [Algebra.Etale R' R''] (Q : Ideal R'')
  [Q.IsPrime] [Q.LiesOver P] (n : ℕ)
  (e' : Fin ((n + 1) + 1) → R'' ⊗[R] S)
  (he' : CompleteOrthogonalIdempotents e')
  (he'0 : e' 0 = Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S) e)
  (Q' : Fin n → Ideal (R'' ⊗[R] S)) [∀ i, (Q' i).IsPrime] [∀ i, (Q' i).LiesOver Q]
  (hPQ : Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Q.over_def P)))
  (hQ' : ∀ (i : Fin n), e' i.succ.castSucc ∉ Q' i)
  (H' : ∀ (P'' : Ideal (R'' ⊗[R] S)), e' 0 ∈ P'' → P''.IsPrime → P''.LiesOver Q →
    e' (.last _) ∈ P'' ∧ ∀ (i : Fin n), e' i.succ.castSucc ∉ P'' → P'' = Q' i) :
  ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
    (_ : P.IsPrime) (_ : P.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
    (_ : CompleteOrthogonalIdempotents e) (P' : Fin n → Ideal (R' ⊗[R] S))
    (_ : ∀ i, (P' i).IsPrime) (_ : ∀ i, (P' i).LiesOver P),
    Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
    (∀ i, e i.castSucc ∉ P' i) ∧
    ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P →
      e (.last n) ∈ P'' ∧ ∀ i, e i.castSucc ∉ P'' → P'' = P' i := by
  let φ := Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S)
  have : Q.LiesOver p := .trans _ P _
  have hpQ :
    Function.Bijective (Ideal.ResidueField.mapₐ p Q (Algebra.ofId _ _) (Q.over_def p)) := by
    convert hPQ.comp hpP
    rw [← @AlgHom.coe_restrictScalars' R R', ← AlgHom.coe_comp]; congr 1; ext
  let P'φ := (Ideal.tensorProductEquivOfBijectiveResidueFieldMap hpQ).symm
    (Ideal.tensorProductEquivOfBijectiveResidueFieldMap hpP ⟨P', ‹_›, ‹_›⟩)
  have : P'φ.1.LiesOver P := .trans _ Q _
  have : (P'φ.1.comap φ.toRingHom).LiesOver P := inferInstanceAs ((P'φ.1.comap φ).LiesOver P)
  have hP'φ : P'φ.1.comap φ.toRingHom = P' := by
    apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hpP
    rw [Ideal.comap_comap]
    convert Ideal.comap_tensorProductEquivOfBijectiveResidueFieldMap_symm hpQ _
    ext; simp [φ]
  refine ⟨R'', inferInstance, _, .comp R R' R'', Q, ‹_›, .trans _ P _, _, _, he', Fin.cons P'φ
    Q', Fin.cases P'φ.2.1 ?_, Fin.cases P'φ.2.2 ?_, hpQ, Fin.cases ?_ ?_, ?_⟩
  · intro P'' _ _
    by_cases heP'' : e ∈ P''.comap φ
    · obtain ⟨h₁, h₂⟩ := H' P'' (by simpa [he'0]) inferInstance inferInstance
      exact ⟨h₁, Fin.cases (fun h ↦ (h (by simpa [he'0])).elim) (by simpa)⟩
    · have : P''.LiesOver P := .trans _ Q _
      obtain rfl := H _ inferInstance inferInstance heP''
      have : ∀ i ≠ 0, e' i ∈ P'' := by
        intro j hj
        rw [← Ideal.IsPrime.mul_mem_left_iff (I := P'') heP'']
        simp [φ, ← he'0, he'.ortho hj.symm]
      refine ⟨by simp [this], Fin.cases (fun _ ↦ ?_) (by simp [this])⟩
      simp only [Fin.cons_zero]
      apply Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap hpQ
      have : (φ.restrictScalars _).comp Algebra.TensorProduct.includeRight =
          Algebra.TensorProduct.includeRight := by ext; simp [φ]
      rw [← this]
      exact congr(($hP'φ).comap Algebra.TensorProduct.includeRight).symm
  · simp only [Fin.cons_succ]; infer_instance
  · simp only [Fin.cons_succ]; infer_instance
  · rw [← hP'φ] at heP'; simpa [he'0]
  · simpa

def Thing
    {R R' S : Type*} (R'' : Type*) [CommRing R] [CommRing R'] [CommRing R''] [CommRing S]
    [Algebra R R'] [Algebra R' R''] [Algebra R S]
    (e : R' ⊗[R] S) := R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e})
  deriving CommRing, Algebra R'', Algebra R'

instance fooo {R R' S : Type*} (R'' : Type*) [CommRing R] [CommRing R'] [CommRing R''] [CommRing S]
    [Algebra R R'] [Algebra R' R''] [Algebra R S]
    (e : R' ⊗[R] S) : IsScalarTower R' R'' (Thing R'' e) := isScalarTower_left

attribute [-simp] FaithfulSMul.ker_algebraMap_eq_bot map_eq_zero in
attribute [instance high] CommRing.toCommMonoid Algebra.toModule
  CommMonoid.toMonoid Monoid.toSemigroup Semigroup.toMul in
def tensorQuotientTensorEquiv
    {R R' R'' S : Type*} [CommRing R] [CommRing R'] [CommRing R''] [CommRing S]
    [Algebra R R'] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R''] [Algebra R S]
    (e : R' ⊗[R] S) :
    Thing R'' e ≃ₐ[R'']
    (R'' ⊗[R] S ⧸ Ideal.span {Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S) e}) :=
  letI φ := Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S)
  letI ψ : R'' ⊗[R] S →ₐ[R''] R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp
      ((Ideal.Quotient.mkₐ _ _).comp Algebra.TensorProduct.includeRight)) fun _ _ ↦ .all _ _
  haveI hψφ : (ψ.restrictScalars R').comp φ =
      (Algebra.TensorProduct.includeRight.restrictScalars R').comp (Ideal.Quotient.mkₐ _ _) := by
    ext; simp [ψ, φ]
  haveI heψ : Ideal.span {φ e} ≤ RingHom.ker ψ := by simpa [Ideal.span_le] using congr($hψφ e)
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (Ideal.quotientMapₐ _ φ
    (Ideal.map_le_iff_le_comap.mp (by simp [Ideal.map_span, φ]))) fun _ _ ↦ .all _ _)
    (Ideal.Quotient.liftₐ _ ψ heψ) (by ext; simp [Thing, ψ, φ]) (by delta Thing; ext; simp [φ, ψ])

lemma exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq_aux'
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (P : Ideal R) [P.IsPrime] (e : S) (P' : Ideal S) [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P') (H : (P.primesOver S).Finite) :
    (P.primesOver (S ⧸ Ideal.span {e})).ncard < (P.primesOver S).ncard := by
  rw [← Set.ncard_image_of_injective _
    (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective)]
  refine Set.ncard_lt_ncard (Set.ssubset_iff_exists.mpr ⟨?_, P', ⟨‹_›, ‹_›⟩, ?_⟩) H
  · rintro _ ⟨q, ⟨_, _⟩, rfl⟩
    exact ⟨inferInstance, inferInstanceAs ((q.comap (Ideal.Quotient.mkₐ R _)).LiesOver _)⟩
  · rintro ⟨q, ⟨_, _⟩, rfl⟩; simp at heP'

attribute [-simp] FaithfulSMul.ker_algebraMap_eq_bot map_eq_zero in
attribute [instance high] CommRing.toCommMonoid Algebra.toModule
  CommRing.toAddCommGroupWithOne AddCommGroupWithOne.toAddCommGroup
  AddCommGroup.toAddCommMonoid CommMonoid.toMonoid Monoid.toSemigroup Semigroup.toMul in
lemma exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq'.{u, v}
    {R : Type u} {S : Type max u v} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (P' : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (P' i).IsPrime) (_ : ∀ i, (P' i).LiesOver P),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      (∀ i, e i.castSucc ∉ P' i) ∧
      ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P →
        e (.last n) ∈ P'' ∧ ∀ i, e i.castSucc ∉ P'' → P'' = P' i := by
  induction h : (p.primesOver S).ncard using Nat.strong_induction_on generalizing R S with
  | h n IH =>
    have : IsArtinianRing (p.ResidueField ⊗[R] S) := IsArtinianRing.of_finite p.ResidueField _
    have hpSfin : (p.primesOver S).Finite :=
      (PrimeSpectrum.primesOverOrderIsoFiber R S p).finite_iff.mpr inferInstance
    cases n with
    | zero =>
      have := (Set.ncard_eq_zero hpSfin).mp h
      refine ⟨R, inferInstance, inferInstance, inferInstance, p, inferInstance, ⟨rfl⟩, 0, 1,
        ⟨⟨by simp [IsIdempotentElem],
          by simp only [Nat.reduceAdd, Pi.one_apply, mul_one, Subsingleton.pairwise]⟩,
          by simp⟩, nofun, nofun, nofun, ?_, nofun, ?_⟩
      · convert show Function.Bijective (AlgHom.id R _) from Function.bijective_id; ext
      · exact fun P h₁ h₂ ↦ (this.le
          ⟨inferInstanceAs (P.comap Algebra.TensorProduct.includeRight.toRingHom).IsPrime, ⟨by
          simp [P.over_def p, Ideal.under, Ideal.comap_comap]⟩⟩).elim
    | succ n =>
    obtain ⟨q, hq, hq'⟩ := Set.nonempty_of_ncard_ne_zero (h.trans_ne (by simp))
    obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hpP, H⟩ :=
      exists_etale_isIdempotentElem_forall_liesOver_eq p q
    have : (P.primesOver (R' ⊗[R] S ⧸ Ideal.span {e})).ncard < n + 1 := by
      let F := Ideal.tensorProductEquivOfBijectiveResidueFieldMap hpP (S := S)
      refine (exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq_aux' _ _
        P' heP' (F.finite_iff.mpr hpSfin)).trans_le ?_
      rw [← h, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr F]
    obtain ⟨R'', _, _, _, Q, _, _, n, e' : _ → Thing R'' e, he', Q' : _ → Ideal (Thing R'' e),
      _, _, hPQ, hQ', H'⟩ :=
      IH _ this (R := R') (S := R' ⊗[R] S ⧸ Ideal.span {e}) P rfl
    change ∀ (P'' : Ideal (Thing R'' e)), P''.IsPrime → P''.LiesOver Q →
      e' (Fin.last n) ∈ P'' ∧ ∀ (i : Fin n), e' i.castSucc ∉ P'' → P'' = Q' i at H'
    letI : Algebra R R'' := .compHom _ (algebraMap R R')
    haveI : IsScalarTower R R' R'' := .of_algebraMap_eq' rfl
    let φ := Algebra.TensorProduct.map (Algebra.ofId R' R'') (AlgHom.id R S)
    let e₁ : Thing R'' e ≃ₐ[R''] (R'' ⊗[R] S ⧸ Ideal.span {φ e}) :=
      tensorQuotientTensorEquiv (R'' := R'') e
    obtain ⟨e'', he'', he''e'⟩ := CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span
      (Ideal.Quotient.mk (Ideal.span {φ e})) (ι := Fin (n + 1)) (φ e) (he.map φ) (by simp)
      (e₁ ∘ e') (he'.map e₁.toRingHom) (fun _ ↦ Ideal.Quotient.mk_surjective _)
    have he''e'' (i : _) : e₁ (e' i) = e'' i := congr_fun he''e' i
    have hψe'' (i : _) : (e' i) = e₁.symm (e'' i) := e₁.eq_symm_apply.mpr (he''e'' i)
    refine exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq_aux p q R' P e P'
      hP'q heP' hpP (fun P'' h₁ h₂ heP'' ↦ H P'' h₁ h₂ (.inl heP'')) R'' Q n _
      ((CompleteOrthogonalIdempotents.equiv (finSuccEquiv _)).mpr he'') rfl
      (Q' · |>.comap (e₁.symm.toAlgHom.comp (Ideal.Quotient.mkₐ _ _))) hPQ
      (fun i ↦ by rw [Function.comp_def]; simpa [← hψe''] using hQ' i) ?_
    simp only [Function.comp_apply, finSuccEquiv_zero,
      show finSuccEquiv (n + 1) (Fin.last (n + 1)) = Fin.last n from rfl, Fin.castSucc_succ,
      finSuccEquiv_succ, AlgEquiv.toAlgHom_eq_coe]
    intro P'' heP'' _ _
    have : (P''.map (Ideal.Quotient.mk (.span {φ e}))).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa [Ideal.span_le])
    have : (P''.map (Ideal.Quotient.mk (.span {φ e}))).LiesOver Q := ⟨by
      have : P'' ⊔ Ideal.span {φ e} = P'' := by simpa [Ideal.span_le]
      rw [← Ideal.under_under (B := R'' ⊗[R] S)]
      simpa [Ideal.under, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, this] using P''.over_def Q⟩
    have := H' ((P''.map (Ideal.Quotient.mk (.span {φ e}))).comap e₁) inferInstance
      (inferInstanceAs <| ((P''.map (Ideal.Quotient.mk (.span {φ e}))).comap
        e₁.toAlgHom).LiesOver Q)
    have hP'' : (1 - φ e) ∉ P'' :=
      fun h ↦ ‹P''.IsPrime›.one_notMem (by convert add_mem heP'' h; ring)
    simp only [Ideal.mem_comap, he''e'',
      Ideal.mem_map_span_singleton_iff_of_isIdempotentElem (he.map φ),
      Ideal.IsPrime.mul_mem_left_iff hP''] at this
    refine ⟨this.1, fun i hi ↦ (this.2 i hi).symm ▸ ?_⟩
    change _ = Ideal.comap (Ideal.Quotient.mk _) (Ideal.comap (e₁.symm.trans e₁).toRingHom _)
    simp only [AlgEquiv.symm_trans_self, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_toRingHom, AlgEquiv.refl_toRingHom, Ideal.comap_id]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    simpa [left_eq_sup, ← RingHom.ker_eq_comap_bot, Ideal.span_le] using heP''

lemma exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq.{u, v}
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p) (n : ℕ) (e : Fin (n + 1) → R' ⊗[R] S)
      (_ : CompleteOrthogonalIdempotents e) (P' : Fin n → Ideal (R' ⊗[R] S))
      (_ : ∀ i, (P' i).IsPrime) (_ : ∀ i, (P' i).LiesOver P),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      (∀ i, e i.castSucc ∉ P' i) ∧
      ∀ (P'' : Ideal (R' ⊗[R] S)), P''.IsPrime → P''.LiesOver P →
        e (.last n) ∈ P'' ∧ ∀ i, e i.castSucc ∉ P'' → P'' = P' i := by
  have ⟨R', _, _, _, P, _, _, n, e, he, P', _, _, hP, hP', H⟩ :=
    exists_etale_completeOrthogonalIdempotents_forall_liesOver_eq' (S := ULift.{u} S) p
  let e₁ : R' ⊗[R] S ≃ₐ[R'] R' ⊗[R] ULift.{u} S :=
    Algebra.TensorProduct.congr .refl ULift.algEquiv.symm
  refine ⟨R', _, _, ‹_›, P, ‹_›, ‹_›, n, e₁.symm ∘ e, he.map _,
    fun i ↦ (P' i).comap e₁.toAlgHom, inferInstance, inferInstance, hP, by simpa,
    fun P'' _ _ ↦ ?_⟩
  have := H (P''.comap e₁.symm.toAlgHom) inferInstance inferInstance
  refine ⟨by simpa using this.1, fun i hi ↦ ?_⟩
  simp [← this.2 i (by simpa), Ideal.comap_comapₐ]
