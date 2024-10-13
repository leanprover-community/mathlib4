import Mathlib.FieldTheory.Fixed
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.Ideal.Pointwise

open scoped Pointwise

section ForMathlib

instance Ideal.IsPrime.smul {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    {P : Ideal R} [P.IsPrime] (g : G) : (g • P).IsPrime :=
  Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv _ _ g)

lemma tada {A : Type*} [CommMonoid A] {G : Type*} [Group G] [Fintype G] [MulDistribMulAction G A]
    (a : A) (g0 : G) : g0 • (∏ g : G, g • a) = ∏ g : G, g • a := by
  simp_rw [Finset.smul_prod', smul_smul]
  exact Finset.prod_bijective (fun g ↦ g0 * g)
    (Group.mulLeft_bijective g0) (by simp) (fun g _ ↦ rfl)

lemma comap_smul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    (P : Ideal B) (g : G) : (g • P).comap (algebraMap A B) = P.comap (algebraMap A B) := by
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

lemma tada'' {G : Type*} [Monoid G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) (n : ℕ) : a ≤ g ^ n • a := by
  induction' n with n hn
  · rw [pow_zero, one_smul]
  · rw [pow_succ', mul_smul]
    exact h.trans (smul_mono_right g hn)

lemma tada' {G : Type*} [Group G] [Finite G] {α : Type*} [PartialOrder α] {g : G} {a : α}
    [MulAction G α] [CovariantClass G α HSMul.hSMul LE.le]
    (h : a ≤ g • a) : g • a = a := by
  have key := smul_mono_right g (tada'' h (Nat.card G - 1))
  rw [smul_smul, ← pow_succ',
    Nat.sub_one_add_one_eq_of_pos Nat.card_pos, pow_card_eq_one', one_smul] at key
  exact le_antisymm key h

end ForMathlib

section part_a

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]

-- (Part a of Théorème 2 in section 2 of chapter 5 of Bourbaki Alg Comm)
theorem part_a (P Q : Ideal B) [hP : P.IsPrime] [hQ : Q.IsPrime]
    (hPQ : Ideal.comap (algebraMap A B) P = Ideal.comap (algebraMap A B) Q)
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a) :
    ∃ g : G, Q = g • P := by
  cases nonempty_fintype G
  have : ∀ (P Q : Ideal B) [P.IsPrime] [Q.IsPrime],
      P.comap (algebraMap A B) = Q.comap (algebraMap A B) → ∃ g ∈ (⊤ : Finset G), Q ≤ g • P := by
    intro P Q hP hQ hPQ
    rw [← Ideal.subset_union_prime 1 1 (fun _ _ _ _ ↦ hP.smul _)]
    intro b hb
    suffices h : ∃ g ∈ Finset.univ, g • b ∈ P by
      obtain ⟨g, -, hg⟩ := h
      apply Set.mem_biUnion (Finset.mem_univ g⁻¹) (Ideal.mem_inv_pointwise_smul_iff.mpr hg)
    obtain ⟨a, ha⟩ := hAB (∏ g : G, g • b) (tada b)
    rw [← hP.prod_mem_iff, ha, ← P.mem_comap, hPQ, Q.mem_comap, ← ha, hQ.prod_mem_iff]
    exact ⟨1, Finset.mem_univ 1, (one_smul G b).symm ▸ hb⟩
  obtain ⟨g, -, hg⟩ := this P Q hPQ
  obtain ⟨g', -, hg'⟩ := this Q (g • P) ((comap_smul P g).trans hPQ).symm
  have hg'' := hg.trans hg'
  have key := tada' hg''
  rw [key] at hg'
  exact ⟨g, le_antisymm hg hg'⟩

end part_a

section lifting

variable (A B : Type*)
  [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B]
  (K L : Type*) [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A B L] [IsScalarTower A K L]

noncomputable def lift (f : B ≃ₐ[A] B) : L ≃ₐ[K] L where
  __ := IsFractionRing.fieldEquivOfRingEquiv f.toRingEquiv
  commutes' := by
    intro x
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe,
      EquivLike.coe_coe]
    rw [map_div₀, map_div₀]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A B L]
    simp only [IsFractionRing.fieldEquivOfRingEquiv, IsLocalization.ringEquivOfRingEquiv_eq]
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]

noncomputable def liftHom : (B ≃ₐ[A] B) →* (L ≃ₐ[K] L) where
  toFun := lift A B K L
  map_one' := by
    ext x
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    simp [lift, IsFractionRing.fieldEquivOfRingEquiv]
  map_mul' := fun f g ↦ by
    ext x
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    simp [lift, IsFractionRing.fieldEquivOfRingEquiv]

lemma liftHom_commutes (f : B ≃ₐ[A] B) (b : B) :
    liftHom A B K L f (algebraMap B L b) = algebraMap B L (f b) := by
  simp [liftHom, lift, IsFractionRing.fieldEquivOfRingEquiv]

end lifting

section MulSemiringAction

variable {G : Type*} (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
variable [Group G]

@[simps]
def MulSemiringAction.ofAlgEquivHom (h : G →* A ≃ₐ[R] A) : MulSemiringAction G A where
  smul := fun g r ↦ h g r
  one_smul := DFunLike.ext_iff.mp (map_one h)
  mul_smul := fun g g' ↦ DFunLike.ext_iff.mp (map_mul h g g')
  smul_zero := fun g ↦ map_zero (h g)
  smul_add := fun g ↦ map_add (h g)
  smul_one := fun g ↦ map_one (h g)
  smul_mul := fun g ↦ map_mul (h g)


variable [MulSemiringAction G A] [SMulCommClass G R A]

@[simps]
def MulSemiringAction.toAlgEquivHom : G →* A ≃ₐ[R] A where
  toFun := MulSemiringAction.toAlgEquiv R A
  map_one' := by ext; rw [toAlgEquiv_apply, one_smul]; rfl
  map_mul' := fun f g ↦ by ext; rw [toAlgEquiv_apply, mul_smul]; rfl

end MulSemiringAction

section MulSemiringAction

variable {G : Type*} (R : Type*) [Semiring R] [Group G]

def MulSemiringAction.ofHom (h : G →* R ≃+* R) : MulSemiringAction G R where
  smul := fun g r ↦ h g r
  one_smul := DFunLike.ext_iff.mp (map_one h)
  mul_smul := fun g g' ↦ DFunLike.ext_iff.mp (map_mul h g g')
  smul_zero := fun g ↦ map_zero (h g)
  smul_add := fun g ↦ map_add (h g)
  smul_one := fun g ↦ map_one (h g)
  smul_mul := fun g ↦ map_mul (h g)

variable [MulSemiringAction G R]

def MulSemiringAction.toHom : G →* R ≃+* R  where
  toFun := MulSemiringAction.toRingEquiv G R
  map_one' := by ext; rw [toRingEquiv_apply, one_smul]; rfl
  map_mul' := fun f g ↦ by ext; rw [toRingEquiv_apply, mul_smul]; rfl

end MulSemiringAction

section fixedfield

/-- `MulSemiringAction.toAlgHom` is bijective. -/
theorem toAlgHom_bijective' (G F : Type*) [Field F] [Group G] [Finite G]
    [MulSemiringAction G F] [FaithfulSMul G F] :
    Function.Bijective
      (MulSemiringAction.toAlgEquivHom _ _ : G →* F ≃ₐ[FixedPoints.subfield G F] F) := by
  constructor
  · intro f g h
    apply (FixedPoints.toAlgHom_bijective G F).injective
    convert h
    simp [DFunLike.ext_iff]
  · intro f
    obtain ⟨g, h⟩ := (FixedPoints.toAlgHom_bijective G F).surjective f
    use g
    convert h
    simp [DFunLike.ext_iff]

/-- `MulSemiringAction.toAlgHom` is surjective. -/
theorem toAlgHom_surjective (G F : Type*) [Field F] [Group G] [Finite G]
    [MulSemiringAction G F] :
    Function.Surjective
      (MulSemiringAction.toAlgEquivHom _ _ : G →* F ≃ₐ[FixedPoints.subfield G F] F) := by
  let f : G →* F ≃ₐ[FixedPoints.subfield G F] F := MulSemiringAction.toAlgEquivHom _ _
  let H := f.ker
  let Q := G ⧸ H
  let h : Q →* F ≃ₐ[FixedPoints.subfield G F] F := QuotientGroup.kerLift f
  let action : MulSemiringAction Q F := MulSemiringAction.ofAlgEquivHom _ _ h
  have key : ∀ (g : G) (f : F), (Quotient.mk'' g : Q) • f = g • f := by
    intro g f
    rfl
  have : FaithfulSMul Q F := ⟨by
    intro q₁ q₂
    refine Quotient.inductionOn₂' q₁ q₂ ?_
    intro g₁ g₂ h
    simp [key, ← inv_smul_eq_iff, ← mul_smul] at h
    have key' : g₂⁻¹ * g₁ ∈ H := by
      change _ = _
      ext a
      exact h a
    symm
    exact QuotientGroup.eq.mpr key'⟩
  have key := toAlgHom_bijective' Q F
  have key' : FixedPoints.subfield Q F = FixedPoints.subfield G F := by
    ext x
    change (∀ q : Q, q • x = x) ↔ (∀ g : G, g • x = x)
    constructor
    · intro h g
      exact h g
    · intro h q
      refine Quotient.inductionOn' q ?_
      intro g
      exact h g
  intro f
  let f' : F ≃ₐ[FixedPoints.subfield Q F] F := AlgEquiv.ofRingEquiv (f := f) (by
    intro ⟨g, hg⟩
    change f g = g
    rw [key'] at hg
    exact f.commutes' ⟨g, hg⟩
  )
  obtain ⟨q, hq⟩ := key.surjective f'
  revert hq
  refine Quotient.inductionOn' q ?_
  intro g hg
  refine ⟨g, ?_⟩
  rw [AlgEquiv.ext_iff] at hg ⊢
  exact hg


end fixedfield

section integrallemma

-- this only requires algebraic, not integral
theorem Polynomial.nonzero_const_if_isIntegral (R S : Type*) [CommRing R] [Nontrivial R]
    [CommRing S] [Algebra R S] [Algebra.IsAlgebraic R S] [IsDomain S] (s : S) (hs : s ≠ 0) :
    ∃ (q : Polynomial R), q.coeff 0 ≠ 0 ∧ q.eval₂ (algebraMap R S) s = 0 := by
  obtain ⟨p, p_monic, p_eval⟩ := (@Algebra.isAlgebraic_def R S).mp inferInstance s
  have p_nzero := p_monic
  obtain ⟨q, p_eq, q_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p p_nzero 0
  rw [C_0, sub_zero] at p_eq
  rw [C_0, sub_zero] at q_ndvd
  use q
  constructor
  · intro q_coeff_0
    exact q_ndvd <| X_dvd_iff.mpr q_coeff_0
  · rw [p_eq, map_mul] at p_eval
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero p_eval with Xpow_eval | q_eval
    · by_contra
      apply hs
      rw [aeval_X_pow] at Xpow_eval
      exact pow_eq_zero Xpow_eval
    · exact q_eval

theorem Algebra.exists_dvd_nonzero_if_isIntegral (R S : Type*) [CommRing R] [Nontrivial R]
    [CommRing S] [Algebra R S] [Algebra.IsAlgebraic R S] [IsDomain S] (s : S) (hs : s ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ s ∣ (algebraMap R S) r := by
  obtain ⟨q, q_zero_coeff, q_eval_zero⟩ := Polynomial.nonzero_const_if_isIntegral R S s hs
  use q.coeff 0
  refine ⟨q_zero_coeff, ?_⟩
  rw [← Polynomial.eval₂_X (algebraMap R S) s, ← dvd_neg, ← Polynomial.eval₂_C (algebraMap R S) s]
  rw [← zero_add (-_), Mathlib.Tactic.RingNF.add_neg, ← q_eval_zero, ← Polynomial.eval₂_sub]
  apply Polynomial.eval₂_dvd
  exact Polynomial.X_dvd_sub_C

end integrallemma

section part_b

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime]
  [Algebra (A ⧸ P) (B ⧸ Q)] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
  -- from this, we can prove that P = comap Q
  variable (K L : Type*) [Field K] [Field L]
  [Algebra (A ⧸ P) K] [IsFractionRing (A ⧸ P) K]
  [Algebra (B ⧸ Q) L] [IsFractionRing (B ⧸ Q) L]
  [Algebra (A ⧸ P) L] [IsScalarTower (A ⧸ P) (B ⧸ Q) L]
  [Algebra K L] [IsScalarTower (A ⧸ P) K L]

-- these first few lemmas might not be necessary!

omit [Algebra A B] [P.IsPrime] [Q.IsPrime] [IsScalarTower A (A ⧸ P) (B ⧸ Q)]
  [IsFractionRing (B ⧸ Q) L] in
include K L in
theorem APBQ_injective (x : A ⧸ P) : algebraMap (A ⧸ P) (B ⧸ Q) x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    replace hx : algebraMap (A ⧸ P) L x = 0 := by
      rw [IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L, hx, map_zero]
    rw [IsScalarTower.algebraMap_apply (A ⧸ P) K L] at hx
    rw [← map_zero (algebraMap K L), (algebraMap K L).injective.eq_iff] at hx
    rw [← map_zero (algebraMap (A ⧸ P) K), (IsFractionRing.injective (A ⧸ P) K).eq_iff] at hx
    exact hx
  · intro hx
    rw [hx, map_zero]

include K L in
omit [P.IsPrime] [Q.IsPrime] [IsFractionRing (B ⧸ Q) L] in
theorem comap_Q_eq_P : Q.comap (algebraMap A B) = P := by
  ext x
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
  rw [IsScalarTower.algebraMap_apply A (A ⧸ P) (B ⧸ Q), APBQ_injective P Q K L]
  rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]



def stabilizerAction : MulAction.stabilizer G Q →* ((B ⧸ Q) ≃ₐ[A ⧸ P] (B ⧸ Q)) where
  toFun := sorry
  map_one' := sorry
  map_mul' := sorry

theorem fullHom_surjective2
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a)
    (f : L ≃ₐ[K] L) (b : B ⧸ Q)
    (hx : ∀ g : MulAction.stabilizer G Q, stabilizerAction G P Q g b = b) :
    f (algebraMap (B ⧸ Q) L b) = (algebraMap (B ⧸ Q) L b) := by
  -- pick lift of b in Q' for all Q' ≠ Q
  -- then (X - g • b) will reduce to (X - b) when g ∈ Stab Q and to X when g ∉ Stab Q
  sorry

noncomputable def fullHom : MulAction.stabilizer G Q →* (L ≃ₐ[K] L) :=
  MonoidHom.comp (liftHom (A ⧸ P) (B ⧸ Q) K L) (stabilizerAction G P Q)

theorem fullHom_surjective1
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a)
    (f : L ≃ₐ[K] L) (x : L) (hx : ∀ g : MulAction.stabilizer G Q, fullHom G P Q K L g x = x) :
    f x = x := by
  have : NoZeroSMulDivisors (A ⧸ P) L := by
    simp only [NoZeroSMulDivisors.iff_algebraMap_injective,
        injective_iff_map_eq_zero,
        IsScalarTower.algebraMap_eq (A ⧸ P) K L,
        RingHom.comp_apply,
        NoZeroSMulDivisors.algebraMap_eq_zero_iff]
    simp
  have : NoZeroSMulDivisors (A ⧸ P) (B ⧸ Q) := by
    rw [NoZeroSMulDivisors.iff_algebraMap_injective] at this ⊢
    rw [IsScalarTower.algebraMap_eq (A ⧸ P) (B ⧸ Q) L] at this
    exact Function.Injective.of_comp this
  have key : ∃ (a : A ⧸ P) (b : B ⧸ Q), a ≠ 0 ∧
      x = (algebraMap (B ⧸ Q) L b) / (algebraMap (A ⧸ P) L a) := by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B ⧸ Q) x
    replace hy : y ≠ 0 := by
      rintro rfl
      exact zero_not_mem_nonZeroDivisors hy
    have : Algebra.IsAlgebraic (A ⧸ P) (B ⧸ Q) := sorry
    obtain ⟨a, ha, b, hb⟩ := Algebra.exists_dvd_nonzero_if_isIntegral (A ⧸ P) (B ⧸ Q) y hy
    refine ⟨a, x * b, ha, ?_⟩
    rw [IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L, hb]
    simp only [map_mul]
    rw [mul_div_mul_right]
    rw [Ne, NoZeroSMulDivisors.algebraMap_eq_zero_iff]
    rintro rfl
    rw [mul_zero] at hb
    rw [NoZeroSMulDivisors.algebraMap_eq_zero_iff] at hb
    exact ha hb
  obtain ⟨a, b, ha, rfl⟩ := key
  simp only [map_div₀, IsScalarTower.algebraMap_apply (A ⧸ P) K L,
    AlgEquiv.commutes] at hx ⊢
  have key : algebraMap (A ⧸ P) L a ≠ 0 := by
    rwa [Ne, NoZeroSMulDivisors.algebraMap_eq_zero_iff]
  simp only [← IsScalarTower.algebraMap_apply (A ⧸ P) K L] at hx ⊢
  simp only [div_left_inj' key] at hx ⊢
  refine fullHom_surjective2 G P Q K L hAB f b ?_
  intro g
  specialize hx g
  apply IsFractionRing.injective (B ⧸ Q) L
  rw [fullHom] at hx
  simp only [MonoidHom.coe_comp, Function.comp_apply] at hx
  rw [← hx]
  symm
  apply liftHom_commutes

theorem fullHom_surjective
    (hAB : ∀ (b : B), (∀ (g : G), g • b = b) → ∃ a : A, b = algebraMap A B a) :
    Function.Surjective (fullHom G P Q K L : MulAction.stabilizer G Q →* (L ≃ₐ[K] L)) := by
  let action : MulSemiringAction (MulAction.stabilizer G Q) L :=
    MulSemiringAction.ofAlgEquivHom _ _
      (fullHom G P Q K L : MulAction.stabilizer G Q →* (L ≃ₐ[K] L))
  have key := toAlgHom_surjective (MulAction.stabilizer G Q) L
  intro f
  obtain ⟨g, hg⟩ := key (AlgEquiv.ofRingEquiv (f := f)
    (fun x ↦ fullHom_surjective1 G P Q K L hAB f x x.2))
  exact ⟨g, by rwa [AlgEquiv.ext_iff] at hg ⊢⟩

-- theorem part_b :

end part_b

/-
B ---> B / Q -----> L = Frac(B/Q)
/\       /\         /\
|        |          |
|        |          |
A ---> A / P ----> K = Frac(A/P)
-/

-- for part b, we need to show that (Stab Q) surjects
-- really should show: (Stab Q) surjects onto Aut((B/Q)/(A/P)) which bijects to Aut(L/K)
-- but maybe it actually is easier to do it in one go

-- find key element of B that generates L/K ?
-- fix an automorphism sigma which does something to b

-- can we show that (Stab Q) acts nicely on (B/Q)/(A/P),
-- effectively reducing to the case of integral domains?

-- easiest case: fields
-- suppose that K = L^G
-- can we show that G surjects onto Aut(L/K)?
-- FieldTheory/Fixed tells us exactly this!

-- next case: integral domains with primes 0 over 0
-- B > L
-- ^   ^
-- A > K
-- suppose that A = B^G
-- then K = L^G (let x=b/a in L be fixed by G, then b in B^G = A)
-- so we're done already...

-- general strategy: we know that (Stab Q) acts on L
-- if we can show that L ^ (Stab Q) = K, then we win
-- apparently L ^ (Stab Q) might be a purely inseparable extension of K?
-- but this is fine, since the automorphism group will still descend

-- general case: A = B ^ G
-- issue: (A/P) = (B/Q) ^ (Stab Q) requires H^1(G,Q)=1

-- we must show that any Aut(L/K) must fix L^(Stab Q) pointwise
-- since we know that Stab Q surjects onto Aut(L/L^(Stab Q))
-- maybe show that b fixed by (Stab Q) mod Q satisfies a nice polynomial?
