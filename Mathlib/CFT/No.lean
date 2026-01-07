module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.CFT.NewNo

/-! #foo -/

@[expose] public section

open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

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

lemma Ideal.mem_map_span_singleton_iff_of_isIdempotentElem
    {R : Type*} [CommRing R] {e r : R} (he : IsIdempotentElem e) {I : Ideal R} :
    Ideal.Quotient.mk _ r ∈ I.map (Ideal.Quotient.mk (Ideal.span {e})) ↔ (1 - e) * r ∈ I := by
  simp only [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_span_singleton]
  refine ⟨?_, fun H ↦ ⟨_, H, by simp [sub_mul]⟩⟩
  rintro ⟨s, hs, t, hrst⟩
  convert I.mul_mem_left (1 - e) hs using 1
  linear_combination he.eq * t - (1 - e) * hrst

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
    · ext; simp [φ]
    · simp; rfl
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
      rw [← h, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr F.toEquiv]
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
      hP'q heP' hpP (fun P'' h₁ h₂ heP'' ↦ H P'' h₁ h₂ heP'') R'' Q n _
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
