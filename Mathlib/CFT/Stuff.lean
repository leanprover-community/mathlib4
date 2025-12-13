import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Unramified.LocalRing

open TensorProduct

attribute [local instance] RingHom.ker_isPrime

open scoped nonZeroDivisors

attribute [ext high] Ideal.Quotient.algHom_ext

-- noncomputable
-- instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
--     Algebra (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) :=
--   (Ideal.Quotient.lift _ (algebraMap _ _) ((Ideal.map_le_iff_le_comap (K := RingHom.ker _)).mpr (by
--     rw [RingHom.comap_ker, ← IsScalarTower.algebraMap_eq,
--       ← Algebra.TensorProduct.includeRight.comp_algebraMap, ← RingHom.comap_ker]
--     refine (Ideal.ker_algebraMap_residueField _).symm.trans_le (Ideal.ker_le_comap _)))).toAlgebra

-- noncomputable
-- instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
--     IsScalarTower S (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) :=
--   .of_algebraMap_eq' rfl

-- noncomputable
-- instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] :
--     IsScalarTower R (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) :=
--   .of_algebraMap_eq' rfl

-- @[simp]
-- lemma algebraMap_quotient_tensorProduct_residueField_mk
--     {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] (s : S) :
--     algebraMap (S ⧸ p.map (algebraMap R S)) (S ⊗[R] p.ResidueField) (Ideal.Quotient.mk _ s) =
--       s ⊗ₜ 1 := rfl

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

instance {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) (I : Ideal T) (J : Ideal R) [I.LiesOver J] : (I.comap f).LiesOver J := by
  constructor; ext; simp [I.over_def J]

instance {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.IsUnramifiedAt R q] : Algebra.IsSeparable p.ResidueField q.ResidueField :=
  ((Algebra.isUnramifiedAt_iff_map_eq _ _ _).mp inferInstance).1

lemma Ideal.isRadical_ker {R S : Type*} [CommRing R] [CommRing S] [IsReduced S] (f : R →+* S) :
    (RingHom.ker f).IsRadical := by
  simpa [IsRadical, SetLike.le_def, Ideal.mem_radical_iff] using fun _ _ ↦ IsReduced.pow_eq_zero

lemma Ideal.IsRadical.pow_mem_iff {R : Type*} [CommRing R] {I : Ideal R} (hI : I.IsRadical)
    {x : R} {n : ℕ} (hn : n ≠ 0) :
    x ^ n ∈ I ↔ x ∈ I :=
  ⟨fun h ↦ hI ⟨_, h⟩, (Ideal.pow_mem_of_mem _ · _ hn.bot_lt)⟩

lemma Algebra.FormallyUnramified.isField_of_isLocalRing
    (R S : Type*) [Field R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] [IsLocalRing S] : IsField S :=
  have := finite_of_free R S
  have := IsArtinianRing.of_finite R S
  have := isReduced_of_field R S
  IsArtinianRing.isField_of_isReduced_of_isLocalRing _
