import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.MvPolynomial.Tower
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.CFT.Stuff2
import Mathlib

open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

noncomputable
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    Algebra (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) :=
  (Ideal.Quotient.lift _ (algebraMap _ _) ((Ideal.map_le_iff_le_comap (K := RingHom.ker _)).mpr (by
    rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq,
      ← Algebra.TensorProduct.includeRight.comp_algebraMap, ← RingHom.comap_ker]
    refine (Ideal.ker_algebraMap_residueField _).symm.trans_le (Ideal.ker_le_comap _)))).toAlgebra

noncomputable
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    IsScalarTower S (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) :=
  .of_algebraMap_eq' rfl

noncomputable
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    IsScalarTower R (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) :=
  .of_algebraMap_eq' rfl

@[simp]
lemma algebraMap_quotient_tensorProduct_residueField_mk
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] (s : S) :
    algebraMap (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) (Ideal.Quotient.mk _ s) =
      s ⊗ₜ 1 := rfl

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

lemma IsIdempotentElem.toCorner_surjective
    {R : Type*} [CommSemiring R] {e : R} (he : IsIdempotentElem e) :
    Function.Surjective (algebraMap R he.Corner) :=
  fun x ↦ ⟨x.1, Subtype.ext ((Subsemigroup.mem_corner_iff he).mp x.2).2⟩

lemma IsIdempotentElem.ker_toCorner
    {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) :
    RingHom.ker (algebraMap R he.Corner) = Ideal.span {1 - e} := by
  apply le_antisymm
  · intro x hx
    refine Ideal.mem_span_singleton.mpr ⟨x, ?_⟩
    simp [show x * e = 0 from congr($(hx).1), sub_mul, mul_comm e]
  · simpa [Ideal.span_le, sub_eq_zero, -FaithfulSMul.ker_algebraMap_eq_bot] using
      Subtype.ext he.eq.symm

noncomputable
def tensorToResidueFieldOfBijectiveMap
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver p] :
    R' ⊗[R] S →ₐ[R] Q.ResidueField :=
  Algebra.TensorProduct.lift ((Ideal.ResidueField.mapₐ p Q (Algebra.ofId _ _) (Q.over_def p)).comp
    ((AlgEquiv.ofBijective _ H).symm.toAlgHom.comp (IsScalarTower.toAlgHom _ _ _)))
    (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _

@[simp]
lemma tensorToResidueFieldOfBijectiveMap_one_tmul
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver p] (b) :
    tensorToResidueFieldOfBijectiveMap H Q (1 ⊗ₜ b) = algebraMap _ _ b := by
  simp [tensorToResidueFieldOfBijectiveMap]

lemma under_ker_tensorToResidueFieldOfBijectiveMap
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver p] :
    (RingHom.ker (tensorToResidueFieldOfBijectiveMap H Q)).under R' = q := by
  ext; simp [tensorToResidueFieldOfBijectiveMap]

attribute [ext high] Ideal.Quotient.algHom_ext

open scoped nonZeroDivisors

lemma comp_tensorToResidueFieldOfBijectiveMap
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver p] (P : Ideal (R' ⊗[R] S)) [P.IsPrime] [P.LiesOver q]
    (hP : P.comap Algebra.TensorProduct.includeRight.toRingHom = Q) :
    (Ideal.ResidueField.map _ _ _ hP.symm).comp
      (tensorToResidueFieldOfBijectiveMap H Q).toRingHom = algebraMap _ _ := by
  letI e := AlgEquiv.ofBijective _ H
  let G : Q.ResidueField →ₐ[R] P.ResidueField :=
  { toRingHom := Ideal.ResidueField.map _ _ _ hP.symm,
    commutes' r := by
      simp [IsScalarTower.algebraMap_apply R S Q.ResidueField,
        - Algebra.TensorProduct.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply R _ P.ResidueField] }
  have hG : G.comp (Ideal.ResidueField.mapₐ p Q (Algebra.ofId _ _) (Q.over_def p)) =
    ((Ideal.ResidueField.mapₐ q P (Algebra.ofId _ _)
    (P.over_def q)).restrictScalars R).comp (AlgEquiv.ofBijective _ H).toAlgHom := by ext
  have hFG : G.comp (tensorToResidueFieldOfBijectiveMap H Q) = IsScalarTower.toAlgHom _ _ _ := by
    ext1
    · simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.comp_assoc,
        Algebra.TensorProduct.lift_comp_includeLeft, tensorToResidueFieldOfBijectiveMap]
      simp only [← AlgHom.comp_assoc, hG]
      ext; simp [-AlgEquiv.toAlgHom_ofBijective, -AlgEquiv.coe_ofBijective]; rfl
    · ext; simp [tensorToResidueFieldOfBijectiveMap, G]
  exact congr($hFG)

noncomputable
def Ideal.tensorProductEquivOfBijectiveResidueFieldMap
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p))) :
    q.primesOver (R' ⊗[R] S) ≃ p.primesOver S where
  toFun P := ⟨P.1.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance, ⟨by
    simp only [q.over_def p, P.1.over_def q, Ideal.under, Ideal.comap_comap,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, ← IsScalarTower.algebraMap_eq]⟩⟩
  invFun Q :=
    ⟨RingHom.ker (tensorToResidueFieldOfBijectiveMap H Q).toRingHom, inferInstance,
      ⟨by exact (under_ker_tensorToResidueFieldOfBijectiveMap H Q.1).symm⟩⟩
  left_inv P := by
    let Q := P.1.comap Algebra.TensorProduct.includeRight.toRingHom
    have : Q.LiesOver p := ⟨by
      simp only [q.over_def p, P.1.over_def q, Ideal.under, Ideal.comap_comap, Q,
        AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap_of_tower, ← IsScalarTower.algebraMap_eq]⟩
    ext1
    dsimp [← AlgHom.toRingHom_eq_coe]
    rw [← RingHom.ker_comp_of_injective _ (Ideal.ResidueField.map Q P.1 _ rfl).injective,
      comp_tensorToResidueFieldOfBijectiveMap H Q P.1 rfl, Ideal.ker_algebraMap_residueField]
  right_inv Q := by
    ext1
    dsimp [tensorToResidueFieldOfBijectiveMap]
    rw [RingHom.comap_ker, ← AlgHom.comp_toRingHom, Algebra.TensorProduct.lift_comp_includeRight',
      IsScalarTower.coe_toAlgHom, ker_algebraMap_residueField]

lemma Ideal.eq_of_comap_eq_comap_of_bijective_residueFieldMap
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (P₁ P₂ : Ideal (R' ⊗[R] S)) [P₁.IsPrime] [P₂.IsPrime] [P₁.LiesOver q] [P₂.LiesOver q]
    (H₂ : P₁.comap Algebra.TensorProduct.includeRight.toRingHom =
      P₂.comap Algebra.TensorProduct.includeRight.toRingHom) : P₁ = P₂ :=
  congr_arg Subtype.val ((Ideal.tensorProductEquivOfBijectiveResidueFieldMap
  (S := S) H).injective (a₁ := ⟨P₁, ‹_›, ‹_›⟩) (a₂ := ⟨P₂, ‹_›, ‹_›⟩) (Subtype.ext H₂))

lemma CompleteOrthogonalIdempotents.exists_eq_comp_of_ker_eq_span
    {R S ι : Type*} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (e₀ : R)
    (he₀ : IsIdempotentElem e₀) (hfe₀ : RingHom.ker f = .span {e₀})
    (e : ι → S) (he : CompleteOrthogonalIdempotents e) (he : ∀ i, e i ∈ f.range) :
    ∃ e', CompleteOrthogonalIdempotents (Option.rec e₀ e') ∧ e = f ∘ e' := by
  choose e' he' using he
  choose k hk using fun i ↦ Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (e' i * e' i - e' i) = 0 by simp [he', (he.1.1 i).eq]))
  refine ⟨(1 - e₀) • e', ⟨⟨Option.rec he₀ fun i ↦ ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro (_|i) (_|j) h
    · simp at h
    · dsimp; linear_combination - he₀.eq * e' j
    · dsimp; linear_combination - he₀.eq * e' i
    · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
        (hfe₀.le (show f (e' i * e' j) = 0 by simp [he', he.1.2 (by simpa using h)]))
      dsimp
      rw [mul_mul_mul_comm, hk, he₀.one_sub.eq, ← mul_assoc, he₀.one_sub_mul_self, zero_mul]
  · obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp
      (hfe₀.le (show f (∑ i, e' i - 1) = 0 by simpa [he', sub_eq_zero] using he.2))
    simp only [Fintype.sum_option, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      sub_eq_iff_eq_add.mp hk]
    linear_combination - he₀.eq * k
  · have : f e₀ = 0 := by simpa using hfe₀.ge (Ideal.mem_span_singleton_self _)
    aesop
  · dsimp [IsIdempotentElem]
    linear_combination congr($(he₀.eq) * ((e' i) ^ 2 - k i) + (1 - e₀) * $(hk i))

attribute [ext high] Ideal.Quotient.algHom_ext

instance {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (I : Ideal T) (J : Ideal R) [I.LiesOver J] : (I.comap f).LiesOver J := by
  constructor; ext; simp [I.over_def J]

lemma Ideal.mem_map_span_singleton_iff_of_isIdempotentElem
    {R : Type*} [CommRing R] {e r : R} (he : IsIdempotentElem e) {I : Ideal R} :
    Ideal.Quotient.mk _ r ∈ I.map (Ideal.Quotient.mk (Ideal.span {e})) ↔ (1 - e) * r ∈ I := by
  simp only [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
  refine ⟨?_, fun H ↦ ⟨_, H, by simp [sub_mul]⟩⟩
  rintro ⟨s, hs, t, hrst⟩
  convert I.mul_mem_left (1 - e) hs using 1
  linear_combination he.eq * t - (1 - e) * hrst

lemma Ideal.comap_tensorProductEquivOfBijectiveResidueFieldMap_symm
    {R R' S : Type*} [CommRing R] [CommRing R'] [CommRing S] [Algebra R R'] [Algebra R S]
    {p : Ideal R} {q : Ideal R'} [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (H : Function.Bijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId _ _) (q.over_def p)))
    (Q : p.primesOver S) :
    ((Ideal.tensorProductEquivOfBijectiveResidueFieldMap H).symm Q).1.comap
      Algebra.TensorProduct.includeRight.toRingHom = Q.1 :=
  congr($((Ideal.tensorProductEquivOfBijectiveResidueFieldMap H).apply_symm_apply Q))

attribute [ext high] Ideal.Quotient.algHom_ext

open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

noncomputable
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    Algebra (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) :=
  (Ideal.Quotient.lift _ (algebraMap _ _) ((Ideal.map_le_iff_le_comap (K := RingHom.ker _)).mpr (by
    rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq,
      ← Algebra.TensorProduct.includeRight.comp_algebraMap, ← RingHom.comap_ker]
    refine (Ideal.ker_algebraMap_residueField _).symm.trans_le (Ideal.ker_le_comap _)))).toAlgebra

noncomputable
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    IsScalarTower S (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) :=
  .of_algebraMap_eq' rfl

noncomputable
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
    IsScalarTower R (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) :=
  .of_algebraMap_eq' rfl

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.IsUnramifiedAt R q] : Algebra.IsSeparable p.ResidueField q.ResidueField :=
  ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1

instance {K A : Type*} [Field K] [CommRing A] [Algebra K A] (P : Ideal A) [P.IsPrime] :
    P.LiesOver (⊥ : Ideal K) :=
  ⟨((IsSimpleOrder.eq_bot_or_eq_top _).resolve_right Ideal.IsPrime.ne_top').symm⟩

instance {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime] :
    (⊥ : Ideal P.ResidueField).LiesOver P := ⟨P.ker_algebraMap_residueField.symm⟩

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (Q : Ideal S) [Q.IsPrime] :
  IsScalarTower R (S ⧸ Q) Q.ResidueField := .of_algebraMap_eq' rfl

lemma Ideal.isRadical_ker {R S : Type*} [CommRing R] [CommRing S] [IsReduced S] (f : R →+* S) :
    (RingHom.ker f).IsRadical := by
  simpa [IsRadical, SetLike.le_def, Ideal.mem_radical_iff] using fun _ _ ↦ IsReduced.pow_eq_zero

lemma Ideal.IsRadical.pow_mem_iff {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsRadical)
    {x : R} {n : ℕ} (hn : n ≠ 0) :
    x ^ n ∈ I ↔ x ∈ I :=
  ⟨fun h ↦ hI ⟨_, h⟩, (Ideal.pow_mem_of_mem _ · _ hn.bot_lt)⟩

-- attribute [-simp] FaithfulSMul.ker_algebraMap_eq_bot map_eq_zero
--   FaithfulSMul.algebraMap_eq_zero_iff in
-- noncomputable
-- def Algebra.IsUnramifiedAt.residueField2
--     {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
--     [Algebra.EssFiniteType R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime]
--     [Q.LiesOver P] [Algebra.IsUnramifiedAt R Q]
--     (Q' : Ideal (P.ResidueField ⊗[R] S)) [Q'.IsPrime]
--     (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
--   Q.ResidueField ≃ₐ[P.ResidueField] Localization.AtPrime Q' := by
--   let f₁ := Localization.localRingHom Q Q' _ hQ'
--   have hf₁ : Function.Surjective f₁ := by
--     subst hQ'
--     apply P.surjectiveOnStalks_residueField.baseChange'
--   have : IsLocalHom f₁ := .of_surjective _ hf₁
--   have := Algebra.IsUnramifiedAt.residueField P Q Q' hQ'
--   have := Algebra.FormallyUnramified.isField_of_isLocalRing P.ResidueField (Localization.AtPrime Q')
--   letI := this.toField
--   let f : Q.ResidueField →+* Localization.AtPrime Q' :=
--     IsLocalRing.ResidueField.lift f₁
--   refine .ofBijective ⟨f, ?_⟩ ⟨f.injective, Ideal.Quotient.lift_surjective_of_surjective _ _ hf₁⟩
--   intro r
--   change f.comp (algebraMap _ _) r = _
--   congr 1
--   ext x
--   change f₁ _ = _
--   simp [f₁, Localization.localRingHom_to_map,
--     ← IsScalarTower.algebraMap_apply R (Localization.AtPrime P) (Localization.AtPrime Q),
--     IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q)]
--   rfl

lemma Algebra.FormallyUnramified.isField_of_isLocalRing
    (R S : Type*) [Field R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] [IsLocalRing S] : IsField S :=
  have := finite_of_free R S
  have := IsArtinianRing.of_finite R S
  have := isReduced_of_field R S
  IsArtinianRing.isField_of_isReduced_of_isLocalRing _
