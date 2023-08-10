import Mathlib.Order.KrullDimension
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.Algebra.Module.LocalizedModule

/--
The ring theoretic Krull dimension is the Krull dimension of prime spectrum ordered by inclusion.
-/
noncomputable def ringKrullDim (R : Type _) [CommRing R] : WithBot (WithTop ℕ) :=
  krullDim (PrimeSpectrum R)

namespace ringKrullDim

/--
If `R ⟶ S` is a surjective ring homomorphism, then `ringKrullDim S ≤ ringKrullDim R`.
-/
theorem le_of_surj (R S : Type _) [CommRing R] [CommRing S] (f : R →+* S)
  (hf : Function.Surjective f) : ringKrullDim S ≤ ringKrullDim R := by
{ refine' krullDim.le_of_strictMono (PrimeSpectrum.comap f)
    (Monotone.strictMono_of_injective ?_ (PrimeSpectrum.comap_injective_of_surjective f hf))
  · intro a b hab
    change ((PrimeSpectrum.comap f) a).asIdeal ≤ ((PrimeSpectrum.comap f) b).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
    exact Ideal.comap_mono hab }

/--
If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`.
-/
theorem le_of_quot (R : Type _) [CommRing R] (I : PrimeSpectrum R) :
  ringKrullDim (R ⧸ I.asIdeal) ≤ ringKrullDim R :=
le_of_surj _ _ (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective

/--
If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`.
-/
theorem eq_of_ringEquiv (R S : Type _) [CommRing R] [CommRing S] (e : R ≃+* S) :
  ringKrullDim R = ringKrullDim S :=
le_antisymm (le_of_surj S R (RingEquiv.symm e) (EquivLike.surjective (RingEquiv.symm e)))
  (le_of_surj R S e (EquivLike.surjective e))

/-
Here we aim to show that for any prime ideal `I` of a commutative ring `R`, the
height of `I` equals the krull dimension of `Localization.AtPrime I.asIdeal`.
-/
section aboutHeightAndLocalization

variable {R : Type _} [CommRing R] (J : Ideal R) (I : PrimeSpectrum R)

/--
For any ideal `J` and submonoid `x` of `R`, `Ideal.localization J x` is
the ideal `J.map (algebraMap R (Localization x))` of `Localization x`.
-/
abbrev _root_.Ideal.localization (x : Submonoid R) : Ideal (Localization x) :=
  J.map (algebraMap R (Localization x))

/--
For any ideals `J` and `I` of `R` such that `I` is prime, `Ideal.localizationAtPrime J I`
is defined as `J.localization I.asIdeal.primeCompl`.
-/
abbrev _root_.Ideal.localizationAtPrime := J.localization I.asIdeal.primeCompl


/-- The canonical map from the ideal J of R to its image JR_I in the localisation. -/
@[simps apply] def _root_.Ideal.toLocalization (x : Submonoid R) :
  J →ₗ[R] J.localization x where
  toFun := λ x ↦ ⟨Localization.mk x 1, Submodule.subset_span ⟨_, x.2, rfl⟩⟩
  map_add' := λ _ _ ↦ Subtype.ext (Localization.add_mk_self _ _ _).symm
  map_smul' := λ _ _ ↦ Subtype.ext (Localization.smul_mk _ _ _).symm

/--
For any ideal `J` and submonoid `y` of `R`, `Ideal.localization' J y` is defined
as the collection of all elements which can be written as `Localization.mk ↑a b`
for some `a : J` and `b : y`.
-/
@[simps!]
def _root_.Ideal.localization' (y : Submonoid R) : Ideal (Localization y) where
  carrier := { x | ∃ (a : J) (b : y), x = Localization.mk ↑a b }
  add_mem' := fun {x y} ⟨a1, ⟨b1, hx⟩⟩ ⟨a2, ⟨b2, hy⟩⟩ => hx.symm ▸ hy.symm ▸
    ⟨⟨_, J.add_mem (J.mul_mem_left b1 (SetLike.coe_mem a2))
      (J.mul_mem_left b2 (SetLike.coe_mem a1))⟩, ⟨b1 * b2, Localization.add_mk _ _ _ _⟩⟩
  zero_mem' := ⟨0, ⟨1, by
    simp only [ZeroMemClass.coe_zero, Localization.mk_eq_monoidOf_mk']
    rw [Submonoid.LocalizationMap.mk']
    simp only [map_one, inv_one, Units.val_one, mul_one]
    rw [Submonoid.LocalizationMap.toMap]
    exact Eq.symm (Localization.mk_zero 1)⟩⟩
  smul_mem' := λ c ↦ Localization.induction_on c $ by
    rintro ⟨c1, c2⟩ ⟨j, ⟨a, rfl⟩⟩
    exact ⟨⟨_, J.mul_mem_left c1 (SetLike.coe_mem j)⟩, ⟨c2 * a, Localization.mk_mul _ _ _ _⟩⟩

lemma _root_.Ideal.mem_localization'_iff {y : Submonoid R} (x : Localization y) :
  x ∈ J.localization' y ↔ ∃ (a : J) (b : y), x = Localization.mk ↑a b :=
Iff.rfl

lemma _root_.Ideal.mem_localization'_of_mem_localization (y : Submonoid R) :
    ∀ x, x ∈ J.localization y → x ∈ J.localization' y := by
  intro x hx
  apply Submodule.span_induction' ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y, hy1, rfl⟩; refine ⟨⟨y, hy1⟩, ⟨_, rfl⟩⟩
  · exact Ideal.zero_mem _
  · intro _ _ _ _; apply Ideal.add_mem
  · intro a _ _; exact Submodule.smul_mem _ a

lemma _root_.Ideal.localization'_eq_localization (y : Submonoid R) :
    J.localization' y = J.localization y :=
  le_antisymm (by
    rintro x ⟨⟨a, ha⟩, ⟨b, rfl⟩⟩
    rw [Subtype.coe_mk, ←one_mul a, ←mul_one b, ←Localization.mk_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha)) <|
  J.mem_localization'_of_mem_localization _

instance _root_.Ideal.localization'_IsPrime (J : Set.Iic I) :
  (J.1.asIdeal.localization' I.asIdeal.primeCompl).IsPrime where
ne_top' := fun hit => by
  rw [Ideal.eq_top_iff_one, Ideal.mem_localization'_iff] at hit
  rcases hit with ⟨a, ⟨b, hb⟩⟩
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime I.asIdeal) _
    (a : R) b).mp (by simpa only [←Localization.mk_eq_mk', ←hb] using isUnit_one) (J.2 a.2)
mem_or_mem' := by
    intro x y
    refine Localization.induction_on₂ x y ?_
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨⟨p, hp⟩, ⟨q, h⟩⟩
    rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h
    obtain ⟨c, hc⟩ := h
    have h : ↑c * (↑q * (a1 * b1)) ∈ J.1.asIdeal := hc.symm ▸ J.1.asIdeal.mul_mem_left _
      (J.1.asIdeal.mul_mem_left _ hp)
    rw [←mul_assoc] at h
    exact (J.1.IsPrime.mem_or_mem ((J.1.IsPrime.mem_or_mem h).resolve_left
      (fun h => Submonoid.mul_mem _ c.2 q.2 (J.2 h)))).elim
        (fun h => Or.intro_left _ ⟨⟨a1, h⟩, ⟨_, rfl⟩⟩)
        (fun h => Or.intro_right _ ⟨⟨b1, h⟩, ⟨_, rfl⟩⟩)

/--
There is a canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`.
-/
def _root_.PrimeSpectrum.IicToLocalizationAtPrime :
  Set.Iic I → PrimeSpectrum (Localization.AtPrime I.asIdeal) :=
λ I' ↦ ⟨I'.1.asIdeal.localization' I.asIdeal.primeCompl, inferInstance⟩

/--
There is a canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I`.
-/
@[simp]
 def _root_.PrimeSpectrum.LocalizationAtPrimeToIic :
   PrimeSpectrum (Localization.AtPrime I.asIdeal) → Set.Iic I :=
   λ J ↦ ⟨⟨_, Ideal.IsPrime.comap (hK := J.2) (algebraMap R (Localization.AtPrime I.asIdeal))⟩,
     λ z hz ↦
     @Decidable.byContradiction _ (Classical.dec _) $ λ hnz ↦ J.IsPrime.ne_top $ eq_top_iff.mpr $
     False.elim $ J.IsPrime.1 $ (Ideal.eq_top_iff_one _).mpr <| show 1 ∈ J.asIdeal by
       rw [show (1 : Localization.AtPrime I.asIdeal) = Localization.mk z 1 * Localization.mk 1
         (⟨z, hnz⟩ : I.asIdeal.primeCompl) by simpa only
           [Localization.mk_one_eq_algebraMap, ←Algebra.smul_def, Localization.smul_mk, smul_eq_mul,
             mul_one, eq_comm] using Localization.mk_self (⟨z, hnz⟩ : I.asIdeal.primeCompl)]
       exact Ideal.mul_mem_right _ _ hz⟩

/--
The canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I` is a left
inverse to the canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`.
-/
lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse :
  Function.LeftInverse (PrimeSpectrum.LocalizationAtPrimeToIic I)
    (PrimeSpectrum.IicToLocalizationAtPrime I) := by
{ intro J; ext x; constructor
  . intro hx
    change Localization.mk x 1 ∈ _root_.Ideal.localization' J.val.asIdeal I.asIdeal.primeCompl at hx
    rw [Ideal.mem_localization'_iff] at hx
    rcases hx with ⟨a, b, hab⟩
    erw [Localization.mk_eq_mk_iff, Localization.r_iff_exists, Submonoid.coe_one, one_mul] at hab
    rcases hab with ⟨c, hc⟩
    rw [←mul_assoc] at hc
    exact (or_iff_not_imp_left.1 (Ideal.IsPrime.mem_or_mem J.val.2 (@Set.mem_of_eq_of_mem R
      (↑c * ↑b * x) (↑c * ↑a) J.val.asIdeal hc (Ideal.mul_mem_left J.val.asIdeal ↑c a.2))))
        (λ hi ↦ (Submonoid.mul_mem I.asIdeal.primeCompl c.2 b.2) (J.2 hi))
  . intro hx
    change Localization.mk x 1 ∈ _root_.Ideal.localization' J.val.asIdeal I.asIdeal.primeCompl
    exact ⟨⟨x, hx⟩, ⟨1, rfl⟩⟩ }

/--
The canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I` is a right
inverse to the canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`.
-/
lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse :
  Function.RightInverse (PrimeSpectrum.LocalizationAtPrimeToIic I)
    (PrimeSpectrum.IicToLocalizationAtPrime I) := by
{ intro J; ext x; constructor
  . intro hx
    simp_rw [PrimeSpectrum.IicToLocalizationAtPrime, PrimeSpectrum.LocalizationAtPrimeToIic,
      Ideal.mem_comap, Ideal.mem_localization'_iff] at hx
    rcases hx with ⟨⟨a, ha⟩, ⟨b, hab⟩⟩
    dsimp at ha hab
    rw [←one_mul a, ←mul_one b, ←Localization.mk_mul] at hab; rw [hab]
    exact Ideal.mul_mem_left J.asIdeal (Localization.mk 1 b) ha
  . refine Localization.induction_on x ?_
    . rintro ⟨a, b⟩ hab
      refine' ⟨⟨a, ?_⟩, b, rfl⟩
      . change Localization.mk a 1 ∈ J.asIdeal
        rw [←show (Localization.mk (b : R) 1) * (Localization.mk a b) = Localization.mk a 1 by
          rw [Localization.mk_mul, mul_comm, ←Localization.mk_mul, Localization.mk_self, mul_one]]
        exact Ideal.mul_mem_left J.asIdeal (Localization.mk b 1) hab }

/--
The canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`
is bijective (not necessary for the proof).
-/
lemma _root_.PrimeSpectrum.IicToLocalizationAtPrime.bijective :
  Function.Bijective (PrimeSpectrum.IicToLocalizationAtPrime I) := by
rw [Function.bijective_iff_has_inverse]
exact ⟨PrimeSpectrum.LocalizationAtPrimeToIic I,
  ⟨PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse I,
    PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse I⟩⟩

/--
The canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I`
is bijective (not necessary for the proof).
-/
lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIic.bijective :
  Function.Bijective (PrimeSpectrum.LocalizationAtPrimeToIic I) := by
rw [Function.bijective_iff_has_inverse]
exact ⟨PrimeSpectrum.IicToLocalizationAtPrime I,
  ⟨PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse I,
    PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse I⟩⟩

/--
The canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`
is monotone.
-/
lemma _root_.PrimeSpectrum.IicToLocalizationAtPrime_IsMonotone :
  Monotone (PrimeSpectrum.IicToLocalizationAtPrime I) := by
{ intro J1 J2 H x hx; rcases hx with ⟨a, ⟨b, hab⟩⟩; exact ⟨⟨a, H a.2⟩, ⟨b, hab⟩⟩ }

/--
The canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I`
is monotone.
-/
lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIic_IsMonotone :
  Monotone (PrimeSpectrum.LocalizationAtPrimeToIic I) := by
{ intro J1 J2 H x hx; exact H hx }

/--
We can regard the canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`
as an equivalence.
-/
def _root_.PrimeSpectrum.IicToLocalizationAtPrimeEquiv :
  (Set.Iic I) ≃ (PrimeSpectrum (Localization.AtPrime I.asIdeal)) where
    toFun := PrimeSpectrum.IicToLocalizationAtPrime I
    invFun := PrimeSpectrum.LocalizationAtPrimeToIic I
    left_inv := PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse I
    right_inv := PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse I

/--
We can regard the canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to
`Set.Iic I` as an equivalence.
-/
def _root_.PrimeSpectrum.LocalizationAtPrimeToIicEquiv :
  (PrimeSpectrum (Localization.AtPrime I.asIdeal)) ≃ (Set.Iic I) where
    toFun := PrimeSpectrum.LocalizationAtPrimeToIic I
    invFun := PrimeSpectrum.IicToLocalizationAtPrime I
    left_inv := PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse I
    right_inv := PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse I

lemma _root_.PrimeSpectrum.IicToLocalizationAtPrimeEquiv_IsMonotone :
  Monotone (PrimeSpectrum.IicToLocalizationAtPrimeEquiv I) := by
{ exact PrimeSpectrum.IicToLocalizationAtPrime_IsMonotone I }

lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIicEquiv_IsMonotone :
  Monotone (PrimeSpectrum.LocalizationAtPrimeToIicEquiv I) := by
{ exact PrimeSpectrum.LocalizationAtPrimeToIic_IsMonotone I }

lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIicEquiv_is_symm :
  PrimeSpectrum.LocalizationAtPrimeToIicEquiv I =
    (PrimeSpectrum.IicToLocalizationAtPrimeEquiv I).symm := rfl

/--
We have a canonical order isomorphism from `Set.Iic I` to
`PrimeSpectrum (Localization.AtPrime I.asIdeal)`.
-/
@[simp]
def _root_.PrimeSpectrum.IicToLocalizationAtPrime_OrderIso :
  (Set.Iic I) ≃o (PrimeSpectrum (Localization.AtPrime I.asIdeal)) := by
exact Equiv.toOrderIso (PrimeSpectrum.IicToLocalizationAtPrimeEquiv I)
  (PrimeSpectrum.IicToLocalizationAtPrimeEquiv_IsMonotone I)
    (PrimeSpectrum.LocalizationAtPrimeToIicEquiv_IsMonotone I)

/--
The height of `I` is equal to the Krull dimension of `localization.at_prime I.as_ideal`.
-/
theorem primeIdealHeight_eq_ringKrullDim_of_Localization :
  height (PrimeSpectrum R) I = ringKrullDim (Localization.AtPrime I.asIdeal) :=
krullDim.eq_of_OrderIso (PrimeSpectrum.IicToLocalizationAtPrime_OrderIso I)

end aboutHeightAndLocalization

end ringKrullDim



/-
Codes written in the process of proving the theorem that the height of `I` is
equal to the Krull dimension of the localization of `R` at `I`, which were
later found to be unnecessary for the proof.
-/
section extraCodes

variable {R : Type _} [CommRing R] (J : Ideal R) (I : PrimeSpectrum R)

@[simps!] def _root_.Localization.divBy {x : Submonoid R} (s : x) :
  Module.End (Localization x) (Localization x) where
    toFun := λ x ↦ (Localization.mk 1 s) * x
    map_add' := mul_add _
    map_smul' := λ r x ↦ by dsimp; ring

lemma _root_.Localization.divBy_apply_mem {y : Submonoid R} (s : y)
  (x) (hx : x ∈ J.localization y) :
  Localization.divBy s x ∈ J.localization y := by
simpa only [Localization.divBy_apply] using
  (J.localization y).mul_mem_left
    (Submonoid.LocalizationMap.mk' (Localization.monoidOf y) 1 s) hx

variable {I}

def _root_.Localization.divBy' {y : Submonoid R} (s : y) :
  Module.End R (J.localization y) :=
(LinearMap.restrict _ $ Localization.divBy_apply_mem J s).restrictScalars R

lemma _root_.Localization.divBy'_right_inv {y : Submonoid R} (s : y) :
  algebraMap R _ s * Localization.divBy' J s = 1 :=
LinearMap.ext $ λ x ↦ show (s : R) • Localization.divBy' J s x = x from Subtype.ext $
  show (s : R) • (Localization.mk 1 s * x) = x by rw [←smul_mul_assoc, Localization.smul_mk,
    smul_eq_mul, mul_one, Localization.mk_self, one_mul]

lemma _root_.LocalizationAtPrime.divBy'_left_inv  {y : Submonoid R} (s : y) :
  (Localization.divBy' J s) * algebraMap R _ s = 1 :=
LinearMap.ext $ λ x ↦ Subtype.ext $ show Localization.mk 1 s * ((s : R) • x) = x
  by erw [mul_smul_comm, ←smul_mul_assoc, Localization.smul_mk, smul_eq_mul, mul_one,
    Localization.mk_self, one_mul]

lemma toIdealImageSpan_exist_eq  {z : Submonoid R} y :
  ∃ (x : J × z), (x.2 : R) • y = J.toLocalization z x.1 := by
{ rcases y with ⟨y, h⟩
  apply Submodule.span_induction' ?_ ?_ ?_ ?_ h
  · rintro _ ⟨_, h, rfl⟩
    refine ⟨⟨⟨_, h⟩, 1⟩, one_smul _ _⟩
  · refine ⟨⟨0, 1⟩, ?_⟩
    simp only [OneMemClass.coe_one, one_smul, map_zero, Submodule.mk_eq_zero]
  · rintro x hx y hy ⟨⟨mx, nx⟩, hmnx⟩ ⟨⟨my, ny⟩, hmny⟩
    refine ⟨⟨(nx : R) • my + (ny : R) • mx, nx * ny⟩, Subtype.ext ?_⟩
    have : ny.1 • nx.1 • x + nx.1 • ny.1 • y =
      ny.1 • Localization.mk mx.1 1 + nx • Localization.mk my.1 1
    · exact Subtype.ext_iff.mp (congr_arg₂ (. + .) (congr_arg ((. • .) (ny : R)) hmnx)
      (congr_arg ((. • .) (nx : R)) hmny))
    rw [smul_comm, ←smul_add, ←smul_add, Localization.smul_mk] at this
    erw [Localization.smul_mk] at this
    rw [Localization.add_mk_self, ←mul_smul, add_comm (_ • _)] at this
    exact this
  · rintro a x hx ⟨⟨c1, c2⟩, (hc : (c2 : R) • _ = _)⟩
    induction a using Localization.induction_on with | H a => ?_
    induction x using Localization.induction_on with | H x => ?_
    rcases a with ⟨d1, d2⟩
    rcases x with ⟨x1, x2⟩
    refine ⟨⟨⟨d1 • c1, J.mul_mem_left d1 (SetLike.coe_mem c1)⟩, d2 * c2⟩,
      Subtype.ext (?_ : (_ * _) • (Localization.mk _ _ * _) = Localization.mk (_ • _) _)⟩
    rw [←Localization.smul_mk (d1 : R) (c1 : R) 1, show Localization.mk c1.1 1 = c2.1 •
      Localization.mk _ _ from (Subtype.ext_iff.mp hc).symm, Localization.smul_mk,
      Localization.smul_mk, Localization.mk_mul, Localization.smul_mk, smul_eq_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by dsimp; ring⟩ }

lemma _root_.Ideal.toLocalization_apply_eq_iff (y : Submonoid R) (x₁ x₂) :
  J.toLocalization y x₁ = J.toLocalization y x₂ ↔
    ∃ (c : y), (c : R) • x₂ = (c : R) • x₁ :=
Subtype.ext_iff.trans $ Localization.mk_eq_mk_iff.trans $ Localization.r_iff_exists.trans $
  exists_congr $ λ x ↦ eq_comm.trans $ Iff.symm $ Subtype.ext_iff.trans $ by simp [smul_eq_mul]

instance (y : Submonoid R) : IsLocalizedModule y (J.toLocalization y) where
  map_units := λ s ↦ ⟨⟨_, _, Localization.divBy'_right_inv _ s,
    LocalizationAtPrime.divBy'_left_inv _ s⟩, rfl⟩
  surj' := toIdealImageSpan_exist_eq J
  eq_iff_exists' := J.toLocalization_apply_eq_iff _ _ _

noncomputable def _root_.Ideal.localizedModuleEquivLocalization (y : Submonoid R) :
  LocalizedModule y J ≃ₗ[R] J.localization y :=
IsLocalizedModule.iso _ $ J.toLocalization y

lemma _root_.Ideal.localizedModuleEquivLocalization_apply (y : Submonoid R) (a b) :
    J.localizedModuleEquivLocalization y (LocalizedModule.mk a b) =
    ⟨Localization.mk a b, by simpa only [show Localization.mk (a : R) b =
      (Localization.mk 1 b) * (Localization.mk ↑a 1) by rw [Localization.mk_mul, one_mul, mul_one]]
        using Ideal.mul_mem_left _ _ (Ideal.apply_coe_mem_map _ J a)⟩ :=
(Module.End_algebraMap_isUnit_inv_apply_eq_iff _ _ _ _).mpr <| by
  refine Subtype.ext (?_ : Localization.mk _ _ = _ • Localization.mk (a : R) b)
  rw [Localization.smul_mk, smul_eq_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp⟩

end extraCodes
