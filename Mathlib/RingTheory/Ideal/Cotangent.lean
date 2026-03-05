/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama

/-!
# The module `I ⧸ I ^ 2`

In this file, we provide special API support for the module `I ⧸ I ^ 2`. The official
definition is a quotient module of `I`, but the alternative definition as an ideal of `R ⧸ I ^ 2` is
also given, and the two are `R`-equivalent as in `Ideal.cotangentEquivIdeal`.

Additional support is also given to the cotangent space `m ⧸ m ^ 2` of a local ring.

-/

@[expose] public section


namespace Ideal

-- Universes need to be explicit to avoid bad universe levels in `quotCotangent`
universe u v w

variable {R : Type u} {S : Type v} {S' : Type w} [CommRing R] [CommSemiring S] [Algebra S R]
variable [CommSemiring S'] [Algebra S' R] [Algebra S S'] [IsScalarTower S S' R] (I : Ideal R)

/-- `I ⧸ I ^ 2` as a quotient of `I`. -/
def Cotangent : Type _ := I ⧸ (I • ⊤ : Submodule R I)
deriving Inhabited, AddCommGroup, Module (R ⧸ I)

deriving instance Module S, IsScalarTower S S' for Cotangent I

variable [IsNoetherian R I] in
deriving instance IsNoetherian R for Cotangent I

/-- The quotient map from `I` to `I ⧸ I ^ 2`. -/
@[simps! -isSimp apply]
def toCotangent : I →ₗ[R] I.Cotangent := Submodule.mkQ _

set_option backward.isDefEq.respectTransparency false in
theorem map_toCotangent_ker : (LinearMap.ker I.toCotangent).map I.subtype = I ^ 2 := by
  rw [Ideal.toCotangent, Submodule.ker_mkQ, pow_two, Submodule.map_smul'' I ⊤ (Submodule.subtype I),
    smul_eq_mul, Submodule.map_subtype_top]

theorem mem_toCotangent_ker {x : I} : x ∈ LinearMap.ker I.toCotangent ↔ (x : R) ∈ I ^ 2 := by
  rw [← I.map_toCotangent_ker]
  simp

theorem toCotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R) ∈ I ^ 2 := by
  rw [← sub_eq_zero]
  exact I.mem_toCotangent_ker

theorem toCotangent_eq_zero (x : I) : I.toCotangent x = 0 ↔ (x : R) ∈ I ^ 2 := I.mem_toCotangent_ker

theorem toCotangent_surjective : Function.Surjective I.toCotangent := Submodule.mkQ_surjective _

theorem toCotangent_range : LinearMap.range I.toCotangent = ⊤ := Submodule.range_mkQ _

theorem cotangent_subsingleton_iff : Subsingleton I.Cotangent ↔ IsIdempotentElem I := by
  constructor
  · intro H
    refine (pow_two I).symm.trans (le_antisymm (Ideal.pow_le_self two_ne_zero) ?_)
    exact fun x hx => (I.toCotangent_eq_zero ⟨x, hx⟩).mp (Subsingleton.elim _ _)
  · exact fun e =>
      ⟨fun x y =>
        Quotient.inductionOn₂' x y fun x y =>
          I.toCotangent_eq.mpr <| ((pow_two I).trans e).symm ▸ I.sub_mem x.prop y.prop⟩

/-- The inclusion map `I ⧸ I ^ 2` to `R ⧸ I ^ 2`. -/
def cotangentToQuotientSquare : I.Cotangent →ₗ[R] R ⧸ I ^ 2 :=
  Submodule.mapQ (I • ⊤) (I ^ 2) I.subtype
    (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top,
        Submodule.range_subtype, smul_eq_mul, pow_two])

theorem to_quotient_square_comp_toCotangent :
    I.cotangentToQuotientSquare.comp I.toCotangent = (I ^ 2).mkQ.comp (Submodule.subtype I) :=
  LinearMap.ext fun _ => rfl

@[simp]
theorem toCotangent_to_quotient_square (x : I) :
    I.cotangentToQuotientSquare (I.toCotangent x) = (I ^ 2).mkQ x := rfl

lemma cotangentToQuotientSquare_injective : Function.Injective I.cotangentToQuotientSquare := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
  rw [toCotangent_to_quotient_square] at hx
  rwa [Ideal.toCotangent_eq_zero, ← Submodule.Quotient.mk_eq_zero (I ^ 2)]

lemma Cotangent.smul_eq_zero_of_mem {I : Ideal R}
    {x} (hx : x ∈ I) (m : I.Cotangent) : x • m = 0 := by
  obtain ⟨m, rfl⟩ := Ideal.toCotangent_surjective _ m
  rw [← map_smul, Ideal.toCotangent_eq_zero, pow_two]
  exact Ideal.mul_mem_mul hx m.2

lemma isTorsionBySet_cotangent :
    Module.IsTorsionBySet R I.Cotangent I :=
  fun m x ↦ m.smul_eq_zero_of_mem x.2

/-- `I ⧸ I ^ 2` as an ideal of `R ⧸ I ^ 2`. -/
def cotangentIdeal (I : Ideal R) : Ideal (R ⧸ I ^ 2) :=
  Submodule.map (Quotient.mk (I ^ 2) |>.toSemilinearMap) I

theorem cotangentIdeal_square (I : Ideal R) : I.cotangentIdeal ^ 2 = ⊥ := by
  rw [eq_bot_iff, pow_two I.cotangentIdeal, ← smul_eq_mul]
  intro x hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; apply (Submodule.Quotient.eq _).mpr _
    rw [sub_zero, pow_two]; exact Ideal.mul_mem_mul hx hy
  · intro x y hx hy; exact add_mem hx hy

lemma mk_mem_cotangentIdeal {I : Ideal R} {x : R} :
    Quotient.mk (I ^ 2) x ∈ I.cotangentIdeal ↔ x ∈ I := by
  refine ⟨fun ⟨y, hy, e⟩ ↦ ?_, fun h ↦ ⟨x, h, rfl⟩⟩
  simpa using sub_mem hy (Ideal.pow_le_self two_ne_zero
    ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp e))

lemma comap_cotangentIdeal (I : Ideal R) :
    I.cotangentIdeal.comap (Quotient.mk (I ^ 2)) = I :=
  Ideal.ext fun _ ↦ mk_mem_cotangentIdeal

theorem range_cotangentToQuotientSquare :
    LinearMap.range I.cotangentToQuotientSquare = I.cotangentIdeal.restrictScalars R := by
  trans LinearMap.range (I.cotangentToQuotientSquare.comp I.toCotangent)
  · rw [LinearMap.range_comp, I.toCotangent_range, Submodule.map_top]
  · rw [to_quotient_square_comp_toCotangent, LinearMap.range_comp, I.range_subtype]; ext; rfl

/-- The equivalence of the two definitions of `I / I ^ 2`, either as the quotient of `I` or the
ideal of `R / I ^ 2`. -/
noncomputable def cotangentEquivIdeal : I.Cotangent ≃ₗ[R] I.cotangentIdeal := by
  refine
  { LinearMap.codRestrict (I.cotangentIdeal.restrictScalars R) I.cotangentToQuotientSquare
      fun x => by rw [← range_cotangentToQuotientSquare]; exact LinearMap.mem_range_self _ _,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · rintro x y e
    replace e := congr_arg Subtype.val e
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    obtain ⟨y, rfl⟩ := I.toCotangent_surjective y
    rw [I.toCotangent_eq]
    dsimp only [toCotangent_to_quotient_square, Submodule.mkQ_apply] at e
    rwa [Submodule.Quotient.eq] at e
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨I.toCotangent ⟨x, hx⟩, Subtype.ext rfl⟩

@[simp]
theorem cotangentEquivIdeal_apply (x : I.Cotangent) :
    ↑(I.cotangentEquivIdeal x) = I.cotangentToQuotientSquare x := rfl

theorem cotangentEquivIdeal_symm_apply (x : R) (hx : x ∈ I) :
    I.cotangentEquivIdeal.symm ⟨(I ^ 2).mkQ x, Submodule.mem_map_of_mem hx⟩ =
      I.toCotangent ⟨x, hx⟩ := by
  simp [I.cotangentEquivIdeal.symm_apply_eq, Subtype.ext_iff]

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The lift of `f : A →ₐ[R] B` to `A ⧸ J ^ 2 →ₐ[R] B` with `J` being the kernel of `f`. -/
def _root_.AlgHom.kerSquareLift (f : A →ₐ[R] B) : A ⧸ RingHom.ker f.toRingHom ^ 2 →ₐ[R] B := by
  refine { Ideal.Quotient.lift (RingHom.ker f.toRingHom ^ 2) f.toRingHom ?_ with commutes' := ?_ }
  · intro a ha; exact Ideal.pow_le_self two_ne_zero ha
  · intro r
    rw [IsScalarTower.algebraMap_apply R A, RingHom.toFun_eq_coe, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.lift_mk]
    exact f.map_algebraMap r

-- Can't be `simp`, because `RingHom.ker f.toRingHom` in the definition of `AlgHom.kerSquareLift`
-- is not simp NF. Will be fixed by removing `RingHomClass` in the definition of `RingHom.ker`.
-- (#25138)
lemma _root_.AlgHom.kerSquareLift_mk (f : A →ₐ[R] B) (x : A) : f.kerSquareLift x = f x :=
  rfl

theorem _root_.AlgHom.ker_kerSquareLift (f : A →ₐ[R] B) :
    RingHom.ker f.kerSquareLift.toRingHom = (RingHom.ker f.toRingHom).cotangentIdeal := by
  apply le_antisymm
  · intro x hx; obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x; exact ⟨x, hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩; exact hx

instance Algebra.kerSquareLift : Algebra (R ⧸ (RingHom.ker (algebraMap R A) ^ 2)) A :=
  (Algebra.ofId R A).kerSquareLift.toAlgebra

instance [Algebra A B] [IsScalarTower R A B] :
    IsScalarTower R (A ⧸ (RingHom.ker (algebraMap A B) ^ 2)) B :=
  IsScalarTower.of_algebraMap_eq'
    (IsScalarTower.toAlgHom R A B).kerSquareLift.comp_algebraMap.symm

/-- The quotient ring of `I ⧸ I ^ 2` is `R ⧸ I`. -/
def quotCotangent : (R ⧸ I ^ 2) ⧸ I.cotangentIdeal ≃+* R ⧸ I := by
  refine (Ideal.quotEquivOfEq (Ideal.map_eq_submodule_map _ _).symm).trans ?_
  refine (DoubleQuot.quotQuotEquivQuotSup _ _).trans ?_
  exact Ideal.quotEquivOfEq (sup_eq_right.mpr <| Ideal.pow_le_self two_ne_zero)

/-- The map `I/I² → J/J²` if `I ≤ f⁻¹(J)`. -/
def mapCotangent (I₁ : Ideal A) (I₂ : Ideal B) (f : A →ₐ[R] B) (h : I₁ ≤ I₂.comap f) :
    I₁.Cotangent →ₗ[R] I₂.Cotangent := by
  refine Submodule.mapQ ((I₁ • ⊤ : Submodule A I₁).restrictScalars R)
    ((I₂ • ⊤ : Submodule B I₂).restrictScalars R) ?_ ?_
  · exact f.toLinearMap.restrict (p := I₁.restrictScalars R) (q := I₂.restrictScalars R) h
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.smul_induction_on hx ?_ (fun _ _ ↦ add_mem)
    rintro a ha ⟨b, hb⟩ -
    simp only [SetLike.mk_smul_mk, smul_eq_mul, Submodule.mem_comap, Submodule.restrictScalars_mem]
    convert (Submodule.smul_mem_smul (M := I₂) (r := f a)
      (n := ⟨f b, h hb⟩) (h ha) (Submodule.mem_top)) using 1
    ext
    exact map_mul f a b

@[simp]
lemma mapCotangent_toCotangent
    (I₁ : Ideal A) (I₂ : Ideal B) (f : A →ₐ[R] B) (h : I₁ ≤ I₂.comap f) (x : I₁) :
    Ideal.mapCotangent I₁ I₂ f h (Ideal.toCotangent I₁ x) = Ideal.toCotangent I₂ ⟨f x, h x.2⟩ := rfl

section Lift

variable {S : Type*} [CommRing S] [Algebra R S] {I : Ideal S}
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Lift a linear map `f : I →ₗ[R] M` that vanishes on products to a linear map on the
cotangent space `I ⧸ I ^ 2`. -/
def Cotangent.lift (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) :
    I.Cotangent →ₗ[R] M where
  __ := QuotientAddGroup.lift _ f.toAddMonoidHom <| fun x hx ↦ by
    simp only [Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢
    refine Submodule.smul_induction_on hx (fun r hr y _ ↦ hf ⟨r, hr⟩ y) fun x y hx hy ↦ ?_
    simp only [map_add, hx, hy, add_zero]
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
    exact map_smul f _ _

@[simp]
lemma Cotangent.lift_toCotangent (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) (x : I) :
    Cotangent.lift f hf (I.toCotangent x) = f x :=
  rfl

@[simp]
lemma Cotangent.lift_comp_toCotangent (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) :
    Cotangent.lift f hf ∘ₗ I.toCotangent = f :=
  rfl

lemma Cotangent.lift_surjective_iff (f : I →ₗ[R] M) (hf : ∀ (x y : I), f (x * y) = 0) :
    Function.Surjective (Cotangent.lift f hf) ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← Cotangent.lift_comp_toCotangent f hf, LinearMap.coe_comp]
    exact Function.Surjective.comp h (toCotangent_surjective I)
  · dsimp [Cotangent.lift]
    exact QuotientAddGroup.lift_surjective_of_surjective _ _ h _

end Lift

end Ideal

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The `A ⧸ I`-vector space `I ⧸ I ^ 2`. -/
abbrev CotangentSpace : Type _ := (maximalIdeal R).Cotangent

instance : Module (ResidueField R) (CotangentSpace R) :=
  inferInstanceAs <| Module (R ⧸ maximalIdeal R) _

set_option backward.isDefEq.respectTransparency false in
instance : IsScalarTower R (ResidueField R) (CotangentSpace R) :=
  inferInstanceAs <| IsScalarTower R (R ⧸ maximalIdeal R) _

instance [IsNoetherianRing R] : FiniteDimensional (ResidueField R) (CotangentSpace R) :=
  Module.Finite.of_restrictScalars_finite R _ _

variable {R}

lemma subsingleton_cotangentSpace_iff [IsNoetherianRing R] :
    Subsingleton (CotangentSpace R) ↔ IsField R := by
  refine (maximalIdeal R).cotangent_subsingleton_iff.trans ?_
  rw [IsLocalRing.isField_iff_maximalIdeal_eq,
    Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing]
  simp [(maximalIdeal.isMaximal R).ne_top]

lemma CotangentSpace.map_eq_top_iff [IsNoetherianRing R] {M : Submodule R (maximalIdeal R)} :
    M.map (maximalIdeal R).toCotangent = ⊤ ↔ M = ⊤ := by
  refine ⟨fun H ↦ eq_top_iff.mpr ?_, by rintro rfl; simp [Ideal.toCotangent_range]⟩
  refine (Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype _) _ _).mp ?_
  rw [Submodule.map_top, Submodule.range_subtype]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
    (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
  rw [smul_eq_mul, ← pow_two, ← Ideal.map_toCotangent_ker, ← Submodule.map_sup,
    ← Submodule.comap_map_eq, H, Submodule.comap_top, Submodule.map_top, Submodule.range_subtype]

lemma CotangentSpace.span_image_eq_top_iff [IsNoetherianRing R] {s : Set (maximalIdeal R)} :
    Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' s) = ⊤ ↔
      Submodule.span R s = ⊤ := by
  rw [← map_eq_top_iff, ← (Submodule.restrictScalars_injective R ..).eq_iff,
    Submodule.restrictScalars_span]
  · simp only [Ideal.toCotangent_apply, Submodule.restrictScalars_top, Submodule.map_span]
  · exact Ideal.Quotient.mk_surjective

open Module

lemma finrank_cotangentSpace_eq_zero_iff [IsNoetherianRing R] :
    finrank (ResidueField R) (CotangentSpace R) = 0 ↔ IsField R := by
  rw [finrank_zero_iff, subsingleton_cotangentSpace_iff]

lemma finrank_cotangentSpace_eq_zero (R) [Field R] :
    finrank (ResidueField R) (CotangentSpace R) = 0 :=
  finrank_cotangentSpace_eq_zero_iff.mpr (Field.toIsField R)

open Submodule in
theorem finrank_cotangentSpace_le_one_iff [IsNoetherianRing R] :
    finrank (ResidueField R) (CotangentSpace R) ≤ 1 ↔ (maximalIdeal R).IsPrincipal := by
  rw [Module.finrank_le_one_iff_top_isPrincipal, isPrincipal_iff,
    (maximalIdeal R).toCotangent_surjective.exists, isPrincipal_iff]
  simp_rw [← Set.image_singleton, eq_comm (a := ⊤), CotangentSpace.span_image_eq_top_iff,
    ← (map_injective_of_injective (injective_subtype _)).eq_iff, map_span, Set.image_singleton,
    Submodule.map_top, range_subtype, eq_comm (a := maximalIdeal R)]
  exact ⟨fun ⟨x, h⟩ ↦ ⟨_, h⟩, fun ⟨x, h⟩ ↦ ⟨⟨x, h ▸ subset_span (Set.mem_singleton x)⟩, h⟩⟩

section spanRank

open IsLocalRing

set_option backward.isDefEq.respectTransparency false in
lemma spanFinrank_eq_finrank_quotient {M : Type*} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (fg : N.FG) : N.spanFinrank =
    Module.finrank (R ⧸ maximalIdeal R) (N ⧸ (maximalIdeal R) • (⊤ : Submodule R N)) := by
  let _ : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field (maximalIdeal R)
  let fin : Module.Finite R N := Module.Finite.iff_fg.mpr fg
  rw [Module.finrank_eq_spanFinrank_of_free]
  let k := R ⧸ maximalIdeal R
  let Q := N ⧸ (maximalIdeal R) • (⊤ : Submodule R N)
  apply le_antisymm
  · let s : Set Q := (⊤ : Submodule k Q).generators
    have hfgQ : (⊤ : Submodule k Q).FG := Module.Finite.fg_top
    have hs_span_R : Submodule.span R s = (⊤ : Submodule R Q) := by
      rw [← Submodule.coe_eq_univ, ← Submodule.coe_span_eq_span_of_surjective R k
        Ideal.Quotient.mk_surjective, Submodule.coe_eq_univ, Submodule.span_generators _]
    obtain ⟨t, ht_inj, ht_image, ht_span⟩ :=
      Submodule.exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot
        s fin.1 (IsLocalRing.maximalIdeal_le_jacobson _) (by simpa using hs_span_R)
    have htfinite : t.Finite := by
      simpa only [← Set.finite_image_iff ht_inj, ht_image] using hfgQ.finite_generators
    have hle : N.spanFinrank ≤ (Subtype.val '' t).ncard := by
      simpa [(Submodule.span_val_image_eq_iff N t).mpr ht_span] using
        (Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (htfinite.image Subtype.val))
    have hcard : t.ncard = s.ncard := by simpa only [← ht_image] using ht_inj.ncard_image.symm
    exact le_of_le_of_eq hle ((Set.ncard_image_of_injective _ (Subtype.val_injective)).trans
      (hcard.trans hfgQ.generators_ncard))
  · have : (⊤ : Submodule R N).spanFinrank = N.spanFinrank := by simp [Submodule.spanFinrank]
    rw [← this]
    let f : N →ₛₗ[Ideal.Quotient.mk (maximalIdeal R)] Q := { __ := Submodule.mkQ _ }
    convert Submodule.spanFinrank_map_le_of_fg f fin.1
    symm
    simpa [f, LinearMap.range_eq_top] using Submodule.mkQ_surjective _

lemma spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg (fg : (maximalIdeal R).FG) :
    (maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R) :=
  spanFinrank_eq_finrank_quotient _ fg

variable (R) in
lemma spanFinrank_maximalIdeal_eq_finrank_cotangentSpace [IsNoetherianRing R] :
    (maximalIdeal R).spanFinrank = Module.finrank (ResidueField R) (CotangentSpace R) :=
  spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg (maximalIdeal R).fg_of_isNoetherianRing

lemma spanFinrank_le_of_surjective (fg : (maximalIdeal R).FG) {R' : Type*} [CommRing R']
    [IsLocalRing R'] (f : R →+* R') (surj : Function.Surjective f) :
    (maximalIdeal R').spanFinrank ≤ (maximalIdeal R).spanFinrank := by
  have comapeq := ((local_hom_TFAE f).out 0 4).mp (surj.isLocalHom f)
  rw [← Ideal.map_comap_of_surjective f surj (maximalIdeal R'), comapeq]
  exact (maximalIdeal R).spanFinrank_map_le_of_fg f fg

lemma spanFinrank_eq_of_ringEquiv {R' : Type*} [CommRing R'] [IsLocalRing R'] (e : R ≃+* R') :
    (maximalIdeal R).spanFinrank = (maximalIdeal R').spanFinrank := by
  by_cases fgR : (maximalIdeal R).FG
  · have eqmap : maximalIdeal R' = (maximalIdeal R).map e := by
      rw [← Ideal.comap_symm, eq_comm]
      exact (((local_hom_TFAE _).out 0 4).mp (e.symm.surjective.isLocalHom (e.symm : R' →+* R)))
    refine le_antisymm (spanFinrank_le_of_surjective ?_ e.symm.toRingHom e.symm.surjective)
      (spanFinrank_le_of_surjective fgR e.toRingHom e.surjective)
    rw [eqmap]
    exact fgR.map e.toRingHom
  · by_cases fgR' : (maximalIdeal R').FG
    · have eqmap' : maximalIdeal R = (maximalIdeal R').map e.symm := by
        rw [Ideal.map_symm, eq_comm]
        exact ((local_hom_TFAE _).out 0 4).mp (e.surjective.isLocalHom (e : R →+* R'))
      absurd fgR
      rw [eqmap']
      exact fgR'.map e.symm.toRingHom
    · rw [Submodule.spanFinrank_of_not_fg fgR, Submodule.spanFinrank_of_not_fg fgR']

end spanRank

end IsLocalRing
