import Mathlib
import Mathlib.NumberTheory.KroneckerWeber.EigenSpace
import Mathlib.NumberTheory.KroneckerWeber.Discriminant
import Mathlib.NumberTheory.KroneckerWeber.IsInvariant
import Mathlib.NumberTheory.KroneckerWeber.KummersLemma


lemma IsPrimitiveRoot.pow_mod {R : Type*} [CommMonoid R] {ζ : R} {p : ℕ}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ) : ζ ^ (k % p) = ζ ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k p]
  simp [pow_add, pow_mul, hζ.pow_eq_one]

section IsSplittingField

open Polynomial

variable {K : Type*} [Field K]
variable {n : ℕ} [NeZero n] (hζ : (primitiveRoots n K).Nonempty)
variable {a : K} (H : Irreducible (X ^ n - C a))
variable (L : Type*) [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)]
variable {α : L} (hα : α ^ n = algebraMap K L a)

@[simps gen]
noncomputable
def powerBasisOfSplittingFieldXPowSubC : PowerBasis K L where
  __ := (AdjoinRoot.powerBasis' (monic_X_pow_sub_C a (NeZero.ne n))).map
    (adjoinRootXPowSubCEquiv hζ H hα)
  gen := α
  basis_eq_pow i := by
    simp only [PowerBasis.basis_eq_pow]
    simp [adjoinRootXPowSubCEquiv_root]

@[simp]
lemma powerBasisOfSplittingFieldXPowSubC_dim :
    (powerBasisOfSplittingFieldXPowSubC hζ H L hα).dim = n := by
  simp [powerBasisOfSplittingFieldXPowSubC]

include hα in
lemma autEquivZmod_symm_apply {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : ZMod n) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd m) α = ζ ^ m.val • α := by
  obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective m
  rw [autEquivZmod_symm_apply_natCast (hα := hα), ZMod.val_natCast, hζ.pow_mod]

include hα in
lemma autEquivZmod_symm_hasEigenvector (ζ : K) (hζ : IsPrimitiveRoot ζ n) (l : ZMod n) (i : ℕ)
    (hn : n ≠ 1) :
    Module.End.HasEigenvector ((autEquivZmod H L hζ).symm (.ofAdd l)).toLinearMap
      ((ζ ^ l.val) ^ i) (α ^ i) := by
  have hα' : α ≠ 0 := by
    rintro rfl
    obtain rfl : a = 0 := by simpa [NeZero.ne n] using hα.symm
    exact ne_zero_of_irreducible_X_pow_sub_C' hn H rfl
  refine ⟨?_, by simp [hα']⟩
  simp [autEquivZmod_symm_apply (H := H) (hα := hα), _root_.smul_pow]

end IsSplittingField

section IsGalois

variable {A K L B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] (p : Ideal A) (P : Ideal B) [P.LiesOver p]

-- theorem foo (K' : IntermediateField K L)



section foobar

open NumberField

open scoped NumberTheory

class IsAbelianGalois (K L : Type*) [Field K] [Field L] [Algebra K L] extends
  IsGalois K L, Std.Commutative (α := L ≃ₐ[K] L) (· * ·)

instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L] :
    CommGroup (L ≃ₐ[K] L) where
  mul_comm := Std.Commutative.comm

lemma IsAbelianGalois.tower_bot (K L M : Type*) [Field K] [Field L] [Algebra K L]
  [Field M] [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsAbelianGalois K M] :
  IsAbelianGalois K L := sorry

lemma IsAbelianGalois.tower_top (K L M : Type*) [Field K] [Field L] [Algebra K L]
  [Field M] [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsAbelianGalois K M] :
  IsAbelianGalois L M := sorry

instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L]
    (K' : IntermediateField K L) : IsAbelianGalois K K' :=
  .tower_bot K _ L

instance (K L : Type*) [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L]
    (K' : IntermediateField K L) : IsAbelianGalois K' L :=
  .tower_top K _ L

-- variable (p : ℕ+) [Fact (p : ℕ).Prime] (hp : Odd p.1)
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [CharZero K] [NumberField L]
variable [IsAbelianGalois ℚ L]

variable (P : Ideal ℤ) [P.IsMaximal]
-- variable (HL₃ : (P.primesOver (𝓞 K)).ncard ≤ 1)


instance IsIntegralClosure.faithfulSMul (A K L B : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [Algebra A K] [Algebra B L] [IsFractionRing A K]
    [Algebra A B]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [Algebra.IsAlgebraic K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    FaithfulSMul (L ≃ₐ[K] L) B := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  constructor
  intro σ₁ σ₂ H
  apply (galRestrict A K L B).injective
  ext a
  exact H a

instance IsIntegralClosure.smulCommClass (A K L B : Type*)
    [CommRing A] [CommRing B] [Field K] [Field L] [Algebra A K] [Algebra B L] [IsFractionRing A K]
    [Algebra A B]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [Algebra.IsAlgebraic K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    SMulCommClass (L ≃ₐ[K] L) A B :=
  letI := IsIntegralClosure.MulSemiringAction A K L B
  ⟨fun σ ↦ map_smul (galRestrict A K L B σ)⟩

example {G : Type*} [Group G] (N : Subgroup G) (x : G) [N.Normal] : (x : G ⧸ N) = 1 ↔ x ∈ N := by
  exact QuotientGroup.eq_one_iff x

attribute [local instance] Ideal.Quotient.field

attribute [local instance] Ideal.Quotient.field in
instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral ℤ S]
    (p : Ideal R) (q : Ideal S) [q.LiesOver p] [q.IsMaximal] :
    Algebra.IsSeparable (R ⧸ p) (S ⧸ q) := by
  have : Algebra.IsIntegral R S := .tower_top (R := ℤ)
  have : p.IsMaximal := ‹q.LiesOver p›.over ▸
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) q
  by_cases hp : p.under ℤ = ⊥
  · have : CharZero (R ⧸ p) := by
      refine charZero_of_injective_algebraMap (R := ℤ) ?_
      rwa [RingHom.injective_iff_ker_eq_bot, ← Ideal.Quotient.mk_comp_algebraMap,
        RingHom.ker_eq_comap_bot, ← Ideal.comap_comap, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker]
    exact Algebra.IsSeparable.of_integral _ _
  have : q.LiesOver (p.under ℤ) := ⟨by rw [‹q.LiesOver p›.over, Ideal.under_under]⟩
  have : IsScalarTower (ℤ ⧸ p.under ℤ) (R ⧸ p) (S ⧸ q) := IsScalarTower.of_algebraMap_eq <| by
    rintro ⟨x⟩; exact congr_arg _ (IsScalarTower.algebraMap_apply ℤ R S x)
  have := Ideal.fintypeQuotientOfFreeOfNeBot _ hp
  have : (p.under ℤ).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  exact Algebra.isSeparable_tower_top_of_isSeparable (ℤ ⧸ p.under ℤ) (R ⧸ p) (S ⧸ q)

theorem surjective_of_isUnramified
  (HL₁ : ∀ (I : Ideal (𝓞 L)) (_ : I.IsMaximal),
    I.under ℤ = P → Algebra.IsUnramifiedAt (𝓞 K) I)
  (HL₂ : ∀ (I : Ideal (𝓞 L)) (_ : I.IsMaximal),
    I.under ℤ ≠ P → Algebra.IsUnramifiedAt ℤ I) : Function.Surjective (algebraMap K L) := by
  by_contra hKL
  obtain ⟨Q, hQ₁, hQ₂⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) P (fun _ ↦ by simp +contextual)
  have := Ideal.LiesOver.mk hQ₂.symm
  have hQ : Q ≠ ⊥ := fun e ↦ by
    obtain hP : ⊥ = P := by simpa [e, SetLike.ext_iff] using hQ₂
    exact Ring.ne_bot_of_isMaximal_of_not_isField ‹P.IsMaximal› Int.not_isField hP.symm
  letI := IsIntegralClosure.MulSemiringAction ℤ ℚ L (𝓞 L)
  letI := Algebra.isInvariant_of_isGalois ℤ ℚ L (𝓞 L)
  let I : Subgroup (L ≃ₐ[ℚ] L) := Q.toAddSubgroup.inertia (L ≃ₐ[ℚ] L)
  let LI : IntermediateField ℚ L := .fixedField I
  have : NumberField LI := ⟨⟩
  have : 1 < Module.finrank ℚ LI := by
    by_contra! H
    have := Module.finrank_pos (R := ℚ) (M := LI)
    have : LI = ⊥ := IntermediateField.finrank_eq_one_iff.mp (by linarith)
    apply_fun IntermediateField.fixingSubgroup at this
    have HI : I = ⊤ := by simpa [LI, IntermediateField.fixingSubgroup_fixedField] using this
    have : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ _ _
    have : FiniteDimensional ℚ K := Module.Finite.of_injective
      (IsScalarTower.toAlgHom ℚ K L).toLinearMap (algebraMap K L).injective
    have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
    have : NumberField K := ⟨⟩
    have hQ' : Q.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hQ
    letI := IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
    letI := Algebra.isInvariant_of_isGalois (𝓞 K) K L (𝓞 L)
    have : Algebra.IsUnramifiedAt (𝓞 K) Q := HL₁ _ hQ₁ hQ₂
    have := Algebra.IsInvariant.card_inertia (L ≃ₐ[K] L) (Q.under (𝓞 K)) hQ' Q
    rw [Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (hp := hQ), Subgroup.card_eq_one] at this
    have hKL : (Algebra.ofId K L).fieldRange ≠ ⊤ := by rwa [ne_eq, AlgHom.fieldRange_eq_top]
    apply hKL
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    apply OrderDual.ofDual.injective
    rw [map_top, OrderDual.ofDual_top, ← le_bot_iff, ← this]
    intro σ hσ x
    exact HI.ge (Subgroup.mem_top (σ.restrictScalars ℚ)) x
  obtain ⟨q, hq, H⟩ := NumberField.exists_ramified_of_isGalois (K := LI) (𝒪 := 𝓞 LI) this
  by_cases h : Ideal.span {q} = P
  · have : Algebra.IsInvariant (𝓞 LI) (𝓞 L) I := by
      refine ⟨fun x H ↦ ⟨⟨⟨(x : L), fun σ ↦ ?_⟩, ?_⟩, rfl⟩⟩
      · conv_rhs => rw [← H σ]
        exact (algebraMap_galRestrict_apply ℤ σ.1 x).symm
      · rw [mem_integralClosure_iff, ← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ LI L)]
        · exact x.2
        · exact (algebraMap LI L).injective
    have : SMulCommClass I (𝓞 LI) (𝓞 L) := by
      refine ⟨fun σ s t ↦ ?_⟩
      rw [Algebra.smul_def, smul_mul', Algebra.smul_def]
      congr 1
      ext1
      exact (algebraMap_galRestrict_apply ℤ σ.1 (algebraMap (𝓞 LI) (𝓞 L) s)).trans (s.1.2 σ)
    apply H (Q.under _) inferInstance (by rw [Ideal.under_under, h, ← hQ₂])
    exact Algebra.IsInvariant.isUnramifiedAt_of_isInvariant_inertia
      (R := ℤ) (S := 𝓞 LI) (T := 𝓞 L) (G := L ≃ₐ[ℚ] L) Q hQ
  have : (Ideal.span {q}).IsMaximal :=
    ((Ideal.span_singleton_prime hq.ne_zero).mpr hq).isMaximal (by simpa using hq.ne_zero)
  obtain ⟨Q', hQ'₁, hQ'₂⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) (.span {q})
      (fun _ ↦ by simp +contextual)
  have : Q'.LiesOver (.span {q}) := ⟨hQ'₂.symm⟩
  have : Module.Finite ℤ (𝓞 L) :=
    IsIntegralClosure.finite ℤ ℚ L (𝓞 L)
  have : Algebra.IsUnramifiedAt ℤ Q' := by
    refine HL₂ Q' hQ'₁ ?_
    contrapose! h
    rw [← h, ← hQ'₂]
  apply H (Q'.under _) inferInstance (by rw [Ideal.under_under, ← hQ'₂])
  exact .of_liesOver ℤ _ Q'

open IntermediateField

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
lemma IsIntegrallyClosed.algebraMap_dvd_iff
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
    [Algebra.IsIntegral R S] [IsIntegrallyClosed R] [FaithfulSMul R S] {x y : R}
    (H : algebraMap R S x ∣ algebraMap R S y) : x ∣ y := by
  by_cases hx : x = 0
  · obtain rfl : y = 0 := by simpa [hx] using H
    simp [hx]
  let K := FractionRing R
  let L := FractionRing S
  suffices IsIntegral R (algebraMap R K y / algebraMap R K x) by
    obtain ⟨z, hz⟩ := IsIntegralClosure.isIntegral_iff (A := R).mp this
    rw [eq_div_iff (by simpa), ← map_mul, (FaithfulSMul.algebraMap_injective R K).eq_iff] at hz
    exact ⟨z, mul_comm x z ▸ hz.symm⟩
  rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L) (algebraMap K L).injective, map_div₀]
  obtain ⟨z, hz⟩ := H
  convert (Algebra.IsIntegral.isIntegral (R := R) z).map (IsScalarTower.toAlgHom R S L)
  simpa [div_eq_iff, hx] using congr(algebraMap S L $(hz.trans (mul_comm _ _)))


lemma RingHom.IsIntegral.isLocalHom
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.IsIntegral)
    (hf' : Function.Injective f) : IsLocalHom f where
  map_nonunit x := by
    simpa [Ideal.map_span] using (Ideal.map_eq_top_iff f (I := .span {x}) hf' hf).mp

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [FaithfulSMul R S]
    [Algebra.IsIntegral R S] : IsLocalHom (algebraMap R S) :=
  RingHom.IsIntegral.isLocalHom Algebra.IsIntegral.isIntegral
    (FaithfulSMul.algebraMap_injective R S)

lemma Subalgebra.map_le_map_iff_of_injective
    {F K L : Type*} [CommRing F] [CommRing K] [CommRing L] [Algebra F K]
    [Algebra F L] (f : K →ₐ[F] L) (hf : Function.Injective f) {A B : Subalgebra F K} :
    A.map f ≤ B.map f ↔ A ≤ B :=
  Submodule.map_le_map_iff_of_injective (f := f.toLinearMap) hf A.toSubmodule B.toSubmodule

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem mem_adjoin_of_isPrimitiveRoot_of_isUnramifiedAt
    (p : ℕ) (hp : p.Prime) (hp' : p ≠ 2) (ζ : 𝓞 L) (hζ : IsPrimitiveRoot ζ (p ^ 2))
    (HL₁ : ∀ (I : Ideal (𝓞 L)) (_ : I.IsMaximal),
      I.under ℤ ≠ .span {(p : ℤ)} → Algebra.IsUnramifiedAt ℤ I)
    (α : L) (a : 𝓞 L) (haζ : a.1 ∈ ℚ⟮ζ.1⟯) (hα : α ^ p = a) (ha : (ζ ^ p - 1) ^ p ∣ a - 1) :
    α ∈ ℚ⟮ζ.1⟯ := by
  have := hp.pos
  let l : 𝓞 L := ζ ^ p - 1
  let ζ' : 𝓞 ℚ⟮ζ.1⟯ := ⟨⟨ζ, mem_adjoin_simple_self _ _⟩,
      (isIntegral_algebraMap_iff Subtype.val_injective).mp ζ.2⟩
  let a' : 𝓞 ℚ⟮ζ.1⟯ := ⟨⟨a.1, haζ⟩, (isIntegral_algebraMap_iff Subtype.val_injective).mp a.2⟩
  have hζ' : IsPrimitiveRoot ζ' (p ^ 2) := hζ.of_map_of_injective (f := algebraMap _ (𝓞 L))
    (FaithfulSMul.algebraMap_injective _ _)
  have hζ'' : IsPrimitiveRoot (ζ' ^ p : ℚ⟮ζ.1⟯) p :=
    (hζ'.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 ℚ⟮ζ.1⟯) ℚ⟮ζ.1⟯)).pow
      (show 0 < p ^ 2 by positivity) (pow_two _)
  have : Fact (PNat.Prime ⟨p, hp.pos⟩) := ⟨hp⟩
  have ha' : ((hζ''.unit' (p := ⟨p, hp.pos⟩)).1 - 1) ^ p ∣ a' - 1 := by
    apply IsIntegrallyClosed.algebraMap_dvd_iff (S := 𝓞 L)
    simpa using ha
  have : IsAbelianGalois ℚ ℚ⟮ζ.1⟯⟮α⟯ := .tower_bot ℚ _ L
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal
    ((Ideal.span_singleton_prime (by simp [hp.ne_zero])).mpr
    (Nat.prime_iff_prime_int.mp hp)) (by simp [hp.ne_zero])
  have ⟨⟨α'', h₁⟩, h₂⟩ := surjective_of_isUnramified (K := ℚ⟮ζ.1⟯) (L := ℚ⟮ζ.1⟯⟮α⟯)
    (.span {(p : ℤ)}) ?_ ?_ ⟨α, mem_adjoin_simple_self _ α⟩
  · obtain rfl : α'' = α := congr($(h₂).1)
    exact h₁
  · simp_rw [← not_dvd_differentIdeal_iff, Ideal.dvd_iff_le]
    intro P hP H hP'
    let α' := KummersLemma.polyRoot (p := ⟨p, hp.pos⟩) (by simpa [← PNat.coe_inj] using hp')
      hζ'' a' ha' (L := ℚ⟮ζ.1⟯⟮α⟯) ⟨α, mem_adjoin_simple_self _ _⟩ (by ext; exact hα) 1
    have hα'' : IsIntegral ℚ⟮ζ.1⟯ α := by
      refine .of_pow hp.pos ?_
      rw [hα]
      exact isIntegral_algebraMap (R := ℚ⟮ζ.1⟯) (x := ⟨a, haζ⟩)
    have := hP' (aeval_derivative_mem_differentIdeal (𝓞 ℚ⟮ζ.1⟯) ℚ⟮ζ.1⟯ ℚ⟮ζ.1⟯⟮α⟯
      (B := 𝓞 ℚ⟮ζ.1⟯⟮α⟯) α' ?_)
    · refine KummersLemma.aeval_derivative_minpoly_not_in (p := ⟨p, hp.pos⟩)
        (by simpa [← PNat.coe_inj] using hp') hζ'' a' ha' (L := ℚ⟮ζ.1⟯⟮α⟯)
        ⟨α, mem_adjoin_simple_self _ _⟩ (by ext; exact hα) P ?_ _ this
      have : algebraMap _ _ (((hζ''.unit' (p := ⟨p, hp.pos⟩)).1 - 1) ^ p) ∈ P := by
        conv_rhs => enter [2, 2]; rw [← tsub_add_cancel_of_le hp.one_le]
        obtain ⟨u, hu⟩ := (associated_zeta_sub_one_pow_prime (p := ⟨p, hp.pos⟩) hζ'').symm
        simp only [PNat.mk_coe] at hu
        rw [pow_succ, ← hu, mul_assoc, map_mul, map_natCast, ← map_natCast (algebraMap ℤ _)]
        refine Ideal.mul_mem_right _ _ ?_
        show (p : ℤ) ∈ P.under ℤ
        exact H.ge (Ideal.mem_span_singleton_self _)
      have : algebraMap _ _ (a' - 1) ∈ P :=
        Ideal.mem_of_dvd _ (RingHom.map_dvd _ ha') this
      simp only [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_one] at this
      have : Ideal.Quotient.mk (P.under _) a' = 1 :=
        (FaithfulSMul.algebraMap_eq_one_iff _ (𝓞 ℚ⟮ζ.1⟯⟮α⟯ ⧸ P)).mp this
      rw [this]
      exact isUnit_one
    · rw [← top_le_iff]
      have := KummersLemma.mem_adjoin_polyRoot (p := ⟨p, hp.pos⟩)
        (by simpa [← PNat.coe_inj] using hp')
        hζ'' a' ha' (L := ℚ⟮ζ.1⟯⟮α⟯) ⟨α, mem_adjoin_simple_self _ _⟩ (by ext; exact hα) 1
      rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← Algebra.adjoin_le_iff] at this
      refine le_trans ?_ this
      rw [← Subalgebra.map_le_map_iff_of_injective (IntermediateField.val _) (RingHom.injective _)]
      simp only [Algebra.map_top, range_val, AlgHom.map_adjoin, Set.image_singleton]
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_integral hα'']
      rfl
  · intro P hP H
    obtain ⟨Q, hQ₁, hQ₂⟩ :=
      Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 L) P (fun _ ↦ by simp +contextual)
    have := Ideal.LiesOver.mk hQ₂.symm
    have := HL₁ Q hQ₁ (by rwa [← hQ₂, Ideal.under_under] at H)
    exact Algebra.IsUnramifiedAt.of_liesOver _ _ Q

open Polynomial in
lemma isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top'
    {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] [FiniteDimensional K L] (n : ℕ) (hn : 0 < n)
    (hK : (primitiveRoots n K).Nonempty)
    {a : K} {α : L} (ha : α ^ n = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    IsSplittingField K L (X ^ n - C a) := by
  constructor
  · rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hK
    rw [mem_primitiveRoots hn] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective) ha
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← hα,
      IntermediateField.adjoin_simple_toSubalgebra_of_integral (IsIntegral.of_finite K α)]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero hn a),
      aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C, ha, sub_self]

lemma IntermediateField.adjoin_adjoinSimpleGen (K : Type*)
    {L : Type*} [Field K] [Field L] [Algebra K L] (x : L) : K⟮AdjoinSimple.gen K x⟯ = ⊤ := by
  apply map_injective (val _)
  simp [adjoin_map, ← AlgHom.fieldRange_eq_map]

set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem IsAbelianGalois.exists_apply_eq_mul_pow
    (p : ℕ) (hp : p.Prime) (hp' : p ≠ 2) (ζ : 𝓞 L) (hζ : IsPrimitiveRoot ζ (p ^ 2))
    (α : L) (a : 𝓞 L) (haζ : a.1 ∈ ℚ⟮ζ.1⟯) (hα : α ^ p = a)
    (σ τ : L ≃ₐ[ℚ] L) (l : ℕ) (hσ : σ α = ζ ^ p * α) (hσ' : σ ζ = ζ) (hτ : τ ζ = ζ ^ l) :
    ∃ c ∈ ℚ⟮ζ.1⟯, τ α = c * α ^ l := by
  by_cases hα0 : α = 0
  · exact ⟨0, zero_mem _, by simp [hα0]⟩
  have := hp.pos
  let ζ' : 𝓞 ℚ⟮ζ.1⟯ := ⟨⟨ζ, mem_adjoin_simple_self _ _⟩,
      (isIntegral_algebraMap_iff Subtype.val_injective).mp ζ.2⟩
  let a' : 𝓞 ℚ⟮ζ.1⟯ := ⟨⟨a.val, haζ⟩, (isIntegral_algebraMap_iff Subtype.val_injective).mp a.2⟩
  have hζ' : IsPrimitiveRoot ζ' (p ^ 2) := hζ.of_map_of_injective (f := algebraMap _ (𝓞 L))
    (FaithfulSMul.algebraMap_injective _ _)
  have hζ'' : IsPrimitiveRoot (ζ' ^ p : ℚ⟮ζ.1⟯) p :=
    (hζ'.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 ℚ⟮ζ.1⟯) ℚ⟮ζ.1⟯)).pow
      (show 0 < p ^ 2 by positivity) (pow_two _)
  have inst := isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top' p hp.pos
    ⟨(ζ'.1 ^ p : ℚ⟮ζ.1⟯), by simpa [hp.pos]⟩ (a := a')
    (α := AdjoinSimple.gen ℚ⟮ζ.1⟯ α) (by ext; exact hα)
    (IntermediateField.adjoin_adjoinSimpleGen _ _)
  have : NeZero p := ⟨hp.ne_zero⟩
  have : IsAbelianGalois ℚ ℚ⟮ζ.1⟯⟮α⟯ := .tower_bot _ _ L
  let σ₁ : L ≃ₐ[ℚ⟮ζ.1⟯] L :=
    { __ := σ
      commutes' r := by
        obtain ⟨r, hr⟩ := r
        induction hr using IntermediateField.adjoin_induction with
        | mem x hx =>
          obtain rfl : x = _ := hx
          simpa using hσ'
        | algebraMap x => simp
        | add x y hx hy _ _ => simp_all
        | inv x hx _ => simp_all
        | mul x y hx hy _ _ => simp_all }
  have hX : Irreducible (Polynomial.X ^ p - Polynomial.C (a' : ℚ⟮ζ.1⟯)) := by
    rw [← pow_one p]
    refine X_pow_sub_C_irreducible_of_prime_pow hp hp' _ ?_
    intro b hb
    have : b.1 ^ p = a := congr($(hb).1)
    obtain ⟨i, -, hi⟩ := (hζ.map_of_injective
      (FaithfulSMul.algebraMap_injective _ L)).eq_pow_of_pow_eq_one
      (ξ := α / b.1) (by rw [pow_two, pow_mul, div_pow, this, ← hα, div_self, one_pow]; simp [hα0])
    have : α ∈ ℚ⟮ζ.1⟯ := by
      rw [eq_div_iff_mul_eq] at hi
      · rw [← hi]
        exact mul_mem (pow_mem (mem_adjoin_simple_self _ _) _) b.2
      · intro e
        rw [e, zero_pow hp.pos.ne'] at this
        simp [← this, hα0] at hα
    have : (ζ : L) ^ p = 1 := by
      simpa [mul_eq_right₀ hα0] using hσ.symm.trans (σ₁.commutes ⟨α, this⟩)
    have := (hζ.map_of_injective (FaithfulSMul.algebraMap_injective _ L)).dvd_of_pow_eq_one _ this
    replace this : p * p ∣ p * 1 := by simpa [pow_two] using this
    rw [mul_dvd_mul_iff_left hp.ne_zero, ← isUnit_iff_dvd_one, Nat.isUnit_iff] at this
    exact hp.ne_one this
  let σ₂ := σ₁.restrictNormal ℚ⟮ζ.1⟯⟮α⟯
  have hσ₂ (x) : (σ₂ x).1 = σ x := σ₁.restrictNormal_commutes ℚ⟮ζ.1⟯⟮α⟯ x
  have H (i : ℕ) : Module.End.HasEigenvector σ₂.toLinearMap ((ζ' ^ p : ℚ⟮ζ.1⟯) ^ i)
      (AdjoinSimple.gen ℚ⟮ζ.1⟯ α ^ i) := by
    refine ⟨?_, by simp [Subtype.ext_iff, hα0]⟩
    simp only [Module.End.mem_genEigenspace_one, AlgEquiv.toLinearMap_apply, map_pow]
    ext1
    simp [hσ₂, hσ, mul_pow, IntermediateField.smul_def, ζ']
  have := Module.End.eigenspace_eq_span_singleton
    (powerBasisOfSplittingFieldXPowSubC ⟨(ζ' ^ p : ℚ⟮ζ.1⟯), by simpa [hp.pos]⟩ hX ℚ⟮ζ.1⟯⟮α⟯
      (α := AdjoinSimple.gen ℚ⟮ζ.1⟯ α) (by ext; exact hα)).basis
    (fun i ↦ (ζ' ^ p : ℚ⟮ζ.1⟯) ^ i.1) σ₂.toLinearMap (fun i ↦ by
      simpa only [id_eq, eq_mpr_eq_cast, PowerBasis.coe_basis,
        powerBasisOfSplittingFieldXPowSubC_gen] using H i)
    ⟨l % p, by simpa using Nat.mod_lt _ hp.pos⟩
    (by simpa only [Function.Injective, id_eq, eq_mpr_eq_cast, Fin.forall_iff,
      powerBasisOfSplittingFieldXPowSubC_dim, Fin.mk.injEq, Finset.coe_range] using hζ''.injOn_pow)
  have hτ' : (τ.restrictNormal _ (AdjoinSimple.gen ℚ⟮ζ.1⟯ α)).1 = τ α :=
    τ.restrictNormal_commutes ℚ⟮ζ.1⟯⟮α⟯ (AdjoinSimple.gen ℚ⟮ζ.1⟯ α)
  have hα₁ : τ.restrictNormal _ (AdjoinSimple.gen ℚ⟮ζ.1⟯ α) ∈
      Module.End.eigenspace σ₂.toLinearMap ((ζ' ^ p) ^ (l % p)) := by
    rw [hζ''.pow_mod]
    have : σ (τ α) = (↑ζ ^ l) ^ p * τ α := by
      simpa [hσ, hτ] using DFunLike.congr_fun (mul_comm σ τ) α
    simp only [adjoin_toSubfield, Module.End.mem_genEigenspace_one, AlgEquiv.toLinearMap_apply,
      Subtype.ext_iff, hσ₂, hτ', SetLike.val_smul, ζ', this, RingOfIntegers.val, smul_eq_mul,
      RingOfIntegers.map_mk, SubmonoidClass.mk_pow, ζ', IntermediateField.smul_def, ← pow_mul,
      mul_comm l p]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (this.le hα₁)
  replace hc := congr($(hc).1).trans
    (τ.restrictNormal_commutes ℚ⟮ζ.1⟯⟮α⟯ (AdjoinSimple.gen ℚ⟮ζ.1⟯ α))
  replace hc : c • α ^ (l % p) = τ α := by simpa using hc
  refine ⟨_, (c / a'.1 ^ (l / p)).2, hc.symm.trans ?_⟩
  simp only [← hα, SubmonoidClass.mk_pow, ← pow_mul, div_eq_mul_inv, MulMemClass.coe_mul, a',
    IntermediateField.smul_def, smul_eq_mul, Subtype.coe_mk, IntermediateField.coe_inv]
  conv_rhs => enter [2]; rw [← l.div_add_mod p]
  rw [mul_assoc, pow_add, inv_mul_cancel_left₀]
  simp [hα0]

theorem IsLocalization.exists_reduced_fraction_of_WfDvdMonoid
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R)
    (hM : ∀ x y, x * y ∈ M → x ∈ M)
    [IsLocalization M S] [WfDvdMonoid R] (x : S) (p : R) (hp : ¬ IsUnit p) :
    ∃ (y : R) (s : M), x = IsLocalization.mk' S y s ∧ (p ∣ y → p ∣ s → False) := by
  obtain ⟨y, ⟨s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  by_cases hy : y = 0
  · exact ⟨0, 1, by simp [hy], by simpa [← isUnit_iff_dvd_one]⟩
  by_cases hs' : s = 0
  · refine ⟨0, 1, ?_, by simpa [← isUnit_iff_dvd_one]⟩
    simp only [mk'_zero, mk'_eq_zero_iff, Subtype.exists, exists_prop]
    exact ⟨0, hs' ▸ hs, zero_mul _⟩
  obtain ⟨m, a, hm, rfl⟩ := WfDvdMonoid.max_power_factor' hy hp
  obtain ⟨n, b, hn, rfl⟩ := WfDvdMonoid.max_power_factor' hs' hp
  refine ⟨p ^ (m - min m n) * a, ⟨p ^ (n - min m n) * b, ?_⟩, ?_, ?_⟩
  · apply hM (y := p ^ (min m n))
    rwa [mul_right_comm, ← pow_add, tsub_add_cancel_of_le inf_le_right]
  · rw [mk'_eq_iff_eq]
    congr 1
    simp only
    rw [mul_mul_mul_comm, ← pow_add, mul_mul_mul_comm, ← pow_add]
    congr 2
    omega
  · cases le_total m n with
  | inl h => simp [h, hm]
  | inr h => simp [h, hn]

open nonZeroDivisors in
theorem IsFractionRing.exists_reduced_fraction_of_WfDvdMonoid
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsFractionRing R S] [WfDvdMonoid R] (x : S) (p : R) (hp : ¬ IsUnit p) :
    ∃ (y : R) (s : R⁰), x = IsLocalization.mk' S y s ∧ (p ∣ y → p ∣ s → False) :=
  IsLocalization.exists_reduced_fraction_of_WfDvdMonoid _
    (by simp +contextual [mul_mem_nonZeroDivisors]) _ _ hp

theorem IsAbelianGalois.exists_apply_eq_mul_powe
    (p : ℕ) (hp : p.Prime) (hp' : p ≠ 2) (ζ : 𝓞 L) (hζ : IsPrimitiveRoot ζ (p ^ 2))
    (α : L) (a : 𝓞 L) (haζ : a.1 ∈ ℚ⟮ζ.1⟯) (hα : α ^ p = a)
    (σ τ : L ≃ₐ[ℚ] L) (l : ℕ) (hσ : σ α = ζ ^ p * α) (hσ' : σ ζ = ζ) (hτ : τ ζ = ζ ^ l) :
    ∃ c ∈ ℚ⟮ζ.1⟯, τ α = c * α ^ l := by
  obtain ⟨m, a, hyp1, hyp2⟩ := WfDvdMonoid.max_power_factor ha₀ hx


set_option maxHeartbeats 0 in
set_option synthInstance.maxHeartbeats 0 in
theorem pow_sub_pow_dvd_sub
    (p : ℕ) (hp : p.Prime) (hp' : p ≠ 2) (ζ : 𝓞 L) (hζ : IsPrimitiveRoot ζ (p ^ 2))
    (α : L) (a : 𝓞 L) (haζ : a.1 ∈ ℚ⟮ζ.1⟯) (hα : α ^ p = a) (ha : ζ ^ p - 1 ∣ a - 1)
    (σ τ : L ≃ₐ[ℚ] L) (l : ℕ) (hl : ¬p ∣ l)
    (hσ : σ α = ζ ^ p * α) (hσ' : σ ζ = ζ) (hτ : τ ζ = ζ ^ l) :
    (ζ ^ p - 1) ^ p ∣ a - 1 := by
  have := hp.pos
  obtain ⟨c, hc, hc'⟩ := IsAbelianGalois.exists_apply_eq_mul_pow
    p hp hp' ζ hζ α a haζ hα σ τ l hσ hσ' hτ
  obtain ⟨c₁, ⟨c₂, hc₂⟩, rfl, hc''⟩ :=
    IsFractionRing.exists_reduced_fraction_of_WfDvdMonoid c (ζ ^ p - 1) sorry
  simp only [mem_nonZeroDivisors_iff_ne_zero] at hc₂
  let τ' := galRestrict ℤ ℚ L (𝓞 L) τ
  have hc' : c₂ ^ p * τ' a = c₁ ^ p * a ^ l := by sorry
    -- apply FaithfulSMul.algebraMap_injective _ L
    -- replace hc' := congr((c₂ * $hc') ^ p)
    -- simp only [IsFractionRing.mk'_eq_div, ← mul_assoc, ne_eq,
    --   FaithfulSMul.algebraMap_eq_zero_iff, hc₂, not_false_eq_true, mul_div_cancel₀,
    --   mul_pow, ← map_pow, pow_right_comm α l, hα] at hc'
    -- simpa [τ', algebraMap_galRestrict_apply] using hc'
  let Λ := ζ ^ p - 1
  have H : Associated Λ (τ' Λ) := by sorry
    -- have : τ' ζ = ζ ^ l := by ext; exact ((algebraMap_galRestrict_apply _ _ _).trans hτ)
    -- simp only [map_sub, map_pow, this, map_one, Λ]
    -- apply (hζ.pow (show 0 < p ^ 2 by positivity) (pow_two _)).associated_sub_one hp ?_
    --   (by simp [hp.pos])
    -- · rwa [← pow_mul, ne_eq, hζ.pow_eq_one_iff_dvd, pow_two, mul_dvd_mul_iff_right hp.ne_zero]
    -- · simp only [hp.pos, Polynomial.mem_nthRootsFinset, ← pow_mul]
    --   rw [mul_assoc, ← pow_two, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  let τ'' : 𝓞 L ⧸ Ideal.span {Λ} →+* 𝓞 L ⧸ Ideal.span {Λ} :=
    Ideal.quotientMap _ τ'.toRingHom <| by
      suffices τ' Λ ∈ Ideal.span {Λ} by simpa [Ideal.span_le] using this
      rw [Ideal.span_singleton_eq_span_singleton.mpr H]
      exact Ideal.mem_span_singleton_self _
  have : τ'' (Ideal.Quotient.mk _ 1) = Ideal.Quotient.mk _ 1 := τ''.map_one

  obtain ⟨c₃, hc₃⟩ : ζ ^ p - 1 ∣ τ' a - 1 := by simpa using H.dvd.trans (τ'.map_dvd ha)
  obtain ⟨c₄, hc₄⟩ : ζ ^ p - 1 ∣ a ^ l - 1 := by simpa using ha.trans (sub_dvd_pow_sub_pow _ _ l)
  rw [sub_eq_iff_eq_add] at hc₃ hc₄
  -- rw [hc₃, hc₄] at
  sorry

end foobar

lemma fooo
    (p : ℕ) (hp : p.Prime) (hp' : p ≠ 2)
    (L : Type*) [Field L] [NumberField L] [IsAbelianGalois ℚ L]
    (ζ : 𝓞 L) (hζ : IsPrimitiveRoot ζ (p ^ 2)) (K : IntermediateField ℚ L)
    (HL : ∀ (I : Ideal (𝓞 L)) (_ : I.IsMaximal),
      I.under ℤ ≠ .span {(p : ℤ)} → Algebra.IsUnramifiedAt ℤ I) :


-- Let `p` be an odd prime and `ζ` be a primitive `p`-th root of unity.
-- Given `L/ℚ(ζ)/ℚ` such that `L/ℚ(ζ)` is (galois and) cyclic of order `p`, and `L/ℚ` is abelian.
variable (p : ℕ+) (hp : (p : ℕ).Prime) (hp' : p.1 ≠ 2)
variable {L K : Type*} [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L]
variable [IsCyclotomicExtension {p ^ 2} ℚ K] [IsAbelianGalois ℚ L]
variable [FiniteDimensional K L] [IsGalois ℚ L] [IsCyclic (L ≃ₐ[K] L)]
variable (hrank : Module.finrank K L = p)

open Module (finrank)
open IntermediateField NumberField

include hp hp' hrank

lemma foo1 : ∃ (α : 𝓞 L),
    (α : L) ^ (p : ℕ) ∈ Set.range (algebraMap K L) ∧ ¬ (p : 𝓞 L) ∣ α ∧ K⟮(α : L)⟯ = ⊤ := by
  have := Fact.mk hp
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {p ^ 2} _ _
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois (p ^ 2) _ _
  have : IsGalois K L := IsGalois.tower_top_of_isGalois ℚ K L
  let ζ := IsCyclotomicExtension.zeta (p ^ 2) ℚ K
  have hζ : IsPrimitiveRoot ζ (p ^ 2) := IsCyclotomicExtension.zeta_spec (p ^ 2) ℚ K
  have hζ' : IsPrimitiveRoot (ζ ^ p.1) p := hζ.pow (p ^ 2).2 (pow_two _)
  have ⟨α₁, ⟨a, ha⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic K L
    ⟨ζ ^ p.1, by simpa [hrank]⟩
  have hX := irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα
  have inst := isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top ⟨ζ ^ p.1, by simpa [hrank]⟩
    ha.symm hα
  simp_rw [hrank] at hX inst ha
  have : FiniteDimensional ℚ K := IsCyclotomicExtension.finiteDimensional {p ^ 2} _ _
  have : IsCyclic (ZMod ↑(p ^ 2))ˣ := sorry
  obtain ⟨l, hl⟩ := IsCyclic.exists_monoid_generator (α := (ZMod ↑(p ^ 2))ˣ)
  let τ := (IsCyclotomicExtension.autEquivPow K
    (Polynomial.cyclotomic.irreducible_rat (p ^ 2).2)).symm l
  have hτ₁ : τ = IsCyclotomicExtension.fromZetaAut
      (hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime l))
      (Polynomial.cyclotomic.irreducible_rat p.2) := by
    dsimp [τ, IsCyclotomicExtension.fromZetaAut]
    congr 2
    generalize_proofs h
    refine h.choose_spec.2.symm.trans ?_
    rw [ZMod.val_natCast, hζ.pow_mod]
  have hτ : τ ζ = ζ ^ l.1.val := by
    rw [hτ₁, IsCyclotomicExtension.fromZetaAut_spec]
  let σ := (autEquivZmod hX L hζ).symm (Multiplicative.ofAdd 1)
  have hσ : σ α₁ = ζ • α₁ := by
    simpa using autEquivZmod_symm_apply_intCast hX L ha.symm hζ 1
  have := IsAbelianGalois.exists_apply_eq_mul_pow p hp hp' ζ
  -- obtain ⟨c, hc⟩ : ∃ c : K, c • α₁ ^ l.1.val = τ.liftNormal L α₁ := by sorry
  --   -- have := Std.Commutative.comm (op := (· * ·)) (σ.restrictScalars ℚ) (τ.liftNormal L)
  --   -- have hα₁ : τ.liftNormal L α₁ ∈ Module.End.eigenspace σ.toLinearMap (ζ ^ l.1.val) := by
  --   --   simpa [hσ, Algebra.smul_def, hτ] using DFunLike.congr_fun this α₁
  --   -- have := Module.End.eigenspace_eq_span_singleton
  --   --   (powerBasisOfSplittingFieldXPowSubC ⟨ζ, (mem_primitiveRoots p.pos).mpr hζ⟩ hX L ha.symm).basis
  --   --   (fun i ↦ ζ ^ i.1) σ.toLinearMap (fun i ↦ by
  --   --     simpa [ZMod.val_one] using autEquivZmod_symm_hasEigenvector
  --   --       hX L ha.symm ζ hζ 1 i.1 ‹Fact (p : ℕ).Prime›.1.ne_one)
  --   --   ⟨l.1.val, by simpa [← PowerBasis.finrank, hrank] using ZMod.val_lt l.1⟩
  --   --   (by simpa [← PowerBasis.finrank, hrank, Function.Injective, Fin.forall_iff] using hζ.injOn_pow)
  --   -- obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (this.le hα₁)
  --   -- exact ⟨c, by simpa using hc⟩
