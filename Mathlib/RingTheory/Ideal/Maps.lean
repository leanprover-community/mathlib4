/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.Ideal.Operations

#align_import ring_theory.ideal.operations from "leanprover-community/mathlib"@"e7f0ddbf65bd7181a85edb74b64bdc35ba4bdc74"

/-!
# Maps on modules and ideals
-/

assert_not_exists Basis -- See `RingTheory.Ideal.Basis`
assert_not_exists Submodule.hasQuotient -- See `RingTheory.Ideal.QuotientOperations`

universe u v w x

open Pointwise

namespace Ideal

section MapAndComap

variable {R : Type u} {S : Type v}

section Semiring

variable {F : Type*} [Semiring R] [Semiring S]
variable [FunLike F R S] [rc : RingHomClass F R S]
variable (f : F)
variable {I J : Ideal R} {K L : Ideal S}

/-- `I.map f` is the span of the image of the ideal `I` under `f`, which may be bigger than
  the image itself. -/
def map (I : Ideal R) : Ideal S :=
  span (f '' I)
#align ideal.map Ideal.map

/-- `I.comap f` is the preimage of `I` under `f`. -/
def comap (I : Ideal S) : Ideal R where
  carrier := f ⁻¹' I
  add_mem' {x y} hx hy := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]
  smul_mem' c x hx := by
    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *
    exact mul_mem_left I _ hx
#align ideal.comap Ideal.comap

@[simp]
theorem coe_comap (I : Ideal S) : (comap f I : Set R) = f ⁻¹' I := rfl

variable {f}

theorem map_mono (h : I ≤ J) : map f I ≤ map f J :=
  span_mono <| Set.image_subset _ h
#align ideal.map_mono Ideal.map_mono

theorem mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : x ∈ I) : f x ∈ map f I :=
  subset_span ⟨x, h, rfl⟩
#align ideal.mem_map_of_mem Ideal.mem_map_of_mem

theorem apply_coe_mem_map (f : F) (I : Ideal R) (x : I) : f x ∈ I.map f :=
  mem_map_of_mem f x.2
#align ideal.apply_coe_mem_map Ideal.apply_coe_mem_map

theorem map_le_iff_le_comap : map f I ≤ K ↔ I ≤ comap f K :=
  span_le.trans Set.image_subset_iff
#align ideal.map_le_iff_le_comap Ideal.map_le_iff_le_comap

@[simp]
theorem mem_comap {x} : x ∈ comap f K ↔ f x ∈ K :=
  Iff.rfl
#align ideal.mem_comap Ideal.mem_comap

theorem comap_mono (h : K ≤ L) : comap f K ≤ comap f L :=
  Set.preimage_mono fun _ hx => h hx
#align ideal.comap_mono Ideal.comap_mono

variable (f)

theorem comap_ne_top (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
  (ne_top_iff_one _).2 <| by rw [mem_comap, map_one]; exact (ne_top_iff_one _).1 hK
#align ideal.comap_ne_top Ideal.comap_ne_top

variable {G : Type*} [FunLike G S R] [rcg : RingHomClass G S R]

theorem map_le_comap_of_inv_on (g : G) (I : Ideal R) (hf : Set.LeftInvOn g f I) :
    I.map f ≤ I.comap g := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_comap, hf hx]
  exact hx
#align ideal.map_le_comap_of_inv_on Ideal.map_le_comap_of_inv_on

theorem comap_le_map_of_inv_on (g : G) (I : Ideal S) (hf : Set.LeftInvOn g f (f ⁻¹' I)) :
    I.comap f ≤ I.map g := fun x (hx : f x ∈ I) => hf hx ▸ Ideal.mem_map_of_mem g hx
#align ideal.comap_le_map_of_inv_on Ideal.comap_le_map_of_inv_on

/-- The `Ideal` version of `Set.image_subset_preimage_of_inverse`. -/
theorem map_le_comap_of_inverse (g : G) (I : Ideal R) (h : Function.LeftInverse g f) :
    I.map f ≤ I.comap g :=
  map_le_comap_of_inv_on _ _ _ <| h.leftInvOn _
#align ideal.map_le_comap_of_inverse Ideal.map_le_comap_of_inverse

/-- The `Ideal` version of `Set.preimage_subset_image_of_inverse`. -/
theorem comap_le_map_of_inverse (g : G) (I : Ideal S) (h : Function.LeftInverse g f) :
    I.comap f ≤ I.map g :=
  comap_le_map_of_inv_on _ _ _ <| h.leftInvOn _
#align ideal.comap_le_map_of_inverse Ideal.comap_le_map_of_inverse

instance IsPrime.comap [hK : K.IsPrime] : (comap f K).IsPrime :=
  ⟨comap_ne_top _ hK.1, fun {x y} => by simp only [mem_comap, map_mul]; apply hK.2⟩
#align ideal.is_prime.comap Ideal.IsPrime.comap

variable (I J K L)

theorem map_top : map f ⊤ = ⊤ :=
  (eq_top_iff_one _).2 <| subset_span ⟨1, trivial, map_one f⟩
#align ideal.map_top Ideal.map_top

theorem gc_map_comap : GaloisConnection (Ideal.map f) (Ideal.comap f) := fun _ _ =>
  Ideal.map_le_iff_le_comap
#align ideal.gc_map_comap Ideal.gc_map_comap

@[simp]
theorem comap_id : I.comap (RingHom.id R) = I :=
  Ideal.ext fun _ => Iff.rfl
#align ideal.comap_id Ideal.comap_id

@[simp]
theorem map_id : I.map (RingHom.id R) = I :=
  (gc_map_comap (RingHom.id R)).l_unique GaloisConnection.id comap_id
#align ideal.map_id Ideal.map_id

theorem comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f : R →+* S) (g : S →+* T) :
    (I.comap g).comap f = I.comap (g.comp f) :=
  rfl
#align ideal.comap_comap Ideal.comap_comap

theorem map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R →+* S) (g : S →+* T) :
    (I.map f).map g = I.map (g.comp f) :=
  ((gc_map_comap f).compose (gc_map_comap g)).l_unique (gc_map_comap (g.comp f)) fun _ =>
    comap_comap _ _
#align ideal.map_map Ideal.map_map

theorem map_span (f : F) (s : Set R) : map f (span s) = span (f '' s) := by
  refine (Submodule.span_eq_of_le _ ?_ ?_).symm
  · rintro _ ⟨x, hx, rfl⟩; exact mem_map_of_mem f (subset_span hx)
  · rw [map_le_iff_le_comap, span_le, coe_comap, ← Set.image_subset_iff]
    exact subset_span
#align ideal.map_span Ideal.map_span

variable {f I J K L}

theorem map_le_of_le_comap : I ≤ K.comap f → I.map f ≤ K :=
  (gc_map_comap f).l_le
#align ideal.map_le_of_le_comap Ideal.map_le_of_le_comap

theorem le_comap_of_map_le : I.map f ≤ K → I ≤ K.comap f :=
  (gc_map_comap f).le_u
#align ideal.le_comap_of_map_le Ideal.le_comap_of_map_le

theorem le_comap_map : I ≤ (I.map f).comap f :=
  (gc_map_comap f).le_u_l _
#align ideal.le_comap_map Ideal.le_comap_map

theorem map_comap_le : (K.comap f).map f ≤ K :=
  (gc_map_comap f).l_u_le _
#align ideal.map_comap_le Ideal.map_comap_le

@[simp]
theorem comap_top : (⊤ : Ideal S).comap f = ⊤ :=
  (gc_map_comap f).u_top
#align ideal.comap_top Ideal.comap_top

@[simp]
theorem comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
  ⟨fun h => I.eq_top_iff_one.mpr (map_one f ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
    fun h => by rw [h, comap_top]⟩
#align ideal.comap_eq_top_iff Ideal.comap_eq_top_iff

@[simp]
theorem map_bot : (⊥ : Ideal R).map f = ⊥ :=
  (gc_map_comap f).l_bot
#align ideal.map_bot Ideal.map_bot

variable (f I J K L)

@[simp]
theorem map_comap_map : ((I.map f).comap f).map f = I.map f :=
  (gc_map_comap f).l_u_l_eq_l I
#align ideal.map_comap_map Ideal.map_comap_map

@[simp]
theorem comap_map_comap : ((K.comap f).map f).comap f = K.comap f :=
  (gc_map_comap f).u_l_u_eq_u K
#align ideal.comap_map_comap Ideal.comap_map_comap

theorem map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup
#align ideal.map_sup Ideal.map_sup

theorem comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L :=
  rfl
#align ideal.comap_inf Ideal.comap_inf

variable {ι : Sort*}

theorem map_iSup (K : ι → Ideal R) : (iSup K).map f = ⨆ i, (K i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup
#align ideal.map_supr Ideal.map_iSup

theorem comap_iInf (K : ι → Ideal S) : (iInf K).comap f = ⨅ i, (K i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf
#align ideal.comap_infi Ideal.comap_iInf

theorem map_sSup (s : Set (Ideal R)) : (sSup s).map f = ⨆ I ∈ s, (I : Ideal R).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup
#align ideal.map_Sup Ideal.map_sSup

theorem comap_sInf (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I ∈ s, (I : Ideal S).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_sInf
#align ideal.comap_Inf Ideal.comap_sInf

theorem comap_sInf' (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I ∈ comap f '' s, I :=
  _root_.trans (comap_sInf f s) (by rw [iInf_image])
#align ideal.comap_Inf' Ideal.comap_sInf'

theorem comap_isPrime [H : IsPrime K] : IsPrime (comap f K) :=
  ⟨comap_ne_top f H.ne_top, fun {x y} h => H.mem_or_mem <| by rwa [mem_comap, map_mul] at h⟩
#align ideal.comap_is_prime Ideal.comap_isPrime

variable {I J K L}

theorem map_inf_le : map f (I ⊓ J) ≤ map f I ⊓ map f J :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_l.map_inf_le _ _
#align ideal.map_inf_le Ideal.map_inf_le

theorem le_comap_sup : comap f K ⊔ comap f L ≤ comap f (K ⊔ L) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_u.le_map_sup _ _
#align ideal.le_comap_sup Ideal.le_comap_sup

-- TODO: Should these be simp lemmas?
theorem _root_.element_smul_restrictScalars {R S M}
    [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
    [Module R M] [Module S M] [IsScalarTower R S M] (r : R) (N : Submodule S M) :
    (algebraMap R S r • N).restrictScalars R = r • N.restrictScalars R :=
  SetLike.coe_injective (congrArg (· '' _) (funext (algebraMap_smul S r)))

theorem smul_restrictScalars {R S M} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
    [IsScalarTower R S M] (I : Ideal R) (N : Submodule S M) :
    (I.map (algebraMap R S) • N).restrictScalars R = I • N.restrictScalars R := by
  simp_rw [map, Submodule.span_smul_eq, ← Submodule.coe_set_smul,
    Submodule.set_smul_eq_iSup, ← element_smul_restrictScalars, iSup_image]
  exact (_root_.map_iSup₂ (Submodule.restrictScalarsLatticeHom R S M) _)

@[simp]
theorem smul_top_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (algebraMap R S)).restrictScalars R :=
  Eq.trans (smul_restrictScalars I (⊤ : Ideal S)).symm <|
    congrArg _ <| Eq.trans (Ideal.smul_eq_mul _ _) (Ideal.mul_top _)
#align ideal.smul_top_eq_map Ideal.smul_top_eq_map

@[simp]
theorem coe_restrictScalars {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (I : Ideal S) : (I.restrictScalars R : Set S) = ↑I :=
  rfl
#align ideal.coe_restrict_scalars Ideal.coe_restrictScalars

/-- The smallest `S`-submodule that contains all `x ∈ I * y ∈ J`
is also the smallest `R`-submodule that does so. -/
@[simp]
theorem restrictScalars_mul {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (I J : Ideal S) : (I * J).restrictScalars R = I.restrictScalars R * J.restrictScalars R :=
  le_antisymm
    (fun _ hx =>
      Submodule.mul_induction_on hx (fun _ hx _ hy => Submodule.mul_mem_mul hx hy) fun _ _ =>
        Submodule.add_mem _)
    (Submodule.mul_le.mpr fun _ hx _ hy => Ideal.mul_mem_mul hx hy)
#align ideal.restrict_scalars_mul Ideal.restrictScalars_mul

section Surjective

variable (hf : Function.Surjective f)

open Function

theorem map_comap_of_surjective (I : Ideal S) : map f (comap f I) = I :=
  le_antisymm (map_le_iff_le_comap.2 le_rfl) fun s hsi =>
    let ⟨r, hfrs⟩ := hf s
    hfrs ▸ (mem_map_of_mem f <| show f r ∈ I from hfrs.symm ▸ hsi)
#align ideal.map_comap_of_surjective Ideal.map_comap_of_surjective

/-- `map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  GaloisInsertion.monotoneIntro (gc_map_comap f).monotone_u (gc_map_comap f).monotone_l
    (fun _ => le_comap_map) (map_comap_of_surjective _ hf)
#align ideal.gi_map_comap Ideal.giMapComap

theorem map_surjective_of_surjective : Surjective (map f) :=
  (giMapComap f hf).l_surjective
#align ideal.map_surjective_of_surjective Ideal.map_surjective_of_surjective

theorem comap_injective_of_surjective : Injective (comap f) :=
  (giMapComap f hf).u_injective
#align ideal.comap_injective_of_surjective Ideal.comap_injective_of_surjective

theorem map_sup_comap_of_surjective (I J : Ideal S) : (I.comap f ⊔ J.comap f).map f = I ⊔ J :=
  (giMapComap f hf).l_sup_u _ _
#align ideal.map_sup_comap_of_surjective Ideal.map_sup_comap_of_surjective

theorem map_iSup_comap_of_surjective (K : ι → Ideal S) : (⨆ i, (K i).comap f).map f = iSup K :=
  (giMapComap f hf).l_iSup_u _
#align ideal.map_supr_comap_of_surjective Ideal.map_iSup_comap_of_surjective

theorem map_inf_comap_of_surjective (I J : Ideal S) : (I.comap f ⊓ J.comap f).map f = I ⊓ J :=
  (giMapComap f hf).l_inf_u _ _
#align ideal.map_inf_comap_of_surjective Ideal.map_inf_comap_of_surjective

theorem map_iInf_comap_of_surjective (K : ι → Ideal S) : (⨅ i, (K i).comap f).map f = iInf K :=
  (giMapComap f hf).l_iInf_u _
#align ideal.map_infi_comap_of_surjective Ideal.map_iInf_comap_of_surjective

theorem mem_image_of_mem_map_of_surjective {I : Ideal R} {y} (H : y ∈ map f I) : y ∈ f '' I :=
  Submodule.span_induction H (fun _ => id) ⟨0, I.zero_mem, map_zero f⟩
    (fun _ _ ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩ =>
      ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ map_add f _ _⟩)
    fun c _ ⟨x, hxi, hxy⟩ =>
    let ⟨d, hdc⟩ := hf c
    ⟨d * x, I.mul_mem_left _ hxi, hdc ▸ hxy ▸ map_mul f _ _⟩
#align ideal.mem_image_of_mem_map_of_surjective Ideal.mem_image_of_mem_map_of_surjective

theorem mem_map_iff_of_surjective {I : Ideal R} {y} : y ∈ map f I ↔ ∃ x, x ∈ I ∧ f x = y :=
  ⟨fun h => (Set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h), fun ⟨_, hx⟩ =>
    hx.right ▸ mem_map_of_mem f hx.left⟩
#align ideal.mem_map_iff_of_surjective Ideal.mem_map_iff_of_surjective

theorem le_map_of_comap_le_of_surjective : comap f K ≤ I → K ≤ map f I := fun h =>
  map_comap_of_surjective f hf K ▸ map_mono h
#align ideal.le_map_of_comap_le_of_surjective Ideal.le_map_of_comap_le_of_surjective

theorem map_eq_submodule_map (f : R →+* S) [h : RingHomSurjective f] (I : Ideal R) :
    I.map f = Submodule.map f.toSemilinearMap I :=
  Submodule.ext fun _ => mem_map_iff_of_surjective f h.1
#align ideal.map_eq_submodule_map Ideal.map_eq_submodule_map

end Surjective

section Injective

variable (hf : Function.Injective f)

theorem comap_bot_le_of_injective : comap f ⊥ ≤ I := by
  refine le_trans (fun x hx => ?_) bot_le
  rw [mem_comap, Submodule.mem_bot, ← map_zero f] at hx
  exact Eq.symm (hf hx) ▸ Submodule.zero_mem ⊥
#align ideal.comap_bot_le_of_injective Ideal.comap_bot_le_of_injective

theorem comap_bot_of_injective : Ideal.comap f ⊥ = ⊥ :=
  le_bot_iff.mp (Ideal.comap_bot_le_of_injective f hf)
#align ideal.comap_bot_of_injective Ideal.comap_bot_of_injective

end Injective

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm (map f I) = I`. -/
@[simp]
theorem map_of_equiv (I : Ideal R) (f : R ≃+* S) :
    (I.map (f : R →+* S)).map (f.symm : S →+* R) = I := by
  rw [← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, map_map,
    RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, map_id]
#align ideal.map_of_equiv Ideal.map_of_equiv

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`,
  then `comap f (comap f.symm I) = I`. -/
@[simp]
theorem comap_of_equiv (I : Ideal R) (f : R ≃+* S) :
    (I.comap (f.symm : S →+* R)).comap (f : R →+* S) = I := by
  rw [← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, comap_comap,
    RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, comap_id]
#align ideal.comap_of_equiv Ideal.comap_of_equiv

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f I = comap f.symm I`. -/
theorem map_comap_of_equiv (I : Ideal R) (f : R ≃+* S) : I.map (f : R →+* S) = I.comap f.symm :=
  le_antisymm (Ideal.map_le_comap_of_inverse _ _ _ (Equiv.left_inv' _))
      (Ideal.comap_le_map_of_inverse _ _ _ (Equiv.right_inv' _))
#align ideal.map_comap_of_equiv Ideal.map_comap_of_equiv

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `comap f.symm I = map f I`. -/
@[simp]
theorem comap_symm (I : Ideal R) (f : R ≃+* S) : I.comap f.symm = I.map f :=
  (map_comap_of_equiv I f).symm

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm I = comap f I`. -/
@[simp]
theorem map_symm (I : Ideal S) (f : R ≃+* S) : I.map f.symm = I.comap f :=
  map_comap_of_equiv I (RingEquiv.symm f)



end Semiring

section Ring

variable {F : Type*} [Ring R] [Ring S]
variable [FunLike F R S] [RingHomClass F R S] (f : F) {I : Ideal R}

section Surjective

variable (hf : Function.Surjective f)

theorem comap_map_of_surjective (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥ :=
  le_antisymm
    (fun r h =>
      let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h
      Submodule.mem_sup.2
        ⟨s, hsi, r - s, (Submodule.mem_bot S).2 <| by rw [map_sub, hfsr, sub_self],
          add_sub_cancel s r⟩)
    (sup_le (map_le_iff_le_comap.1 le_rfl) (comap_mono bot_le))
#align ideal.comap_map_of_surjective Ideal.comap_map_of_surjective

/-- Correspondence theorem -/
def relIsoOfSurjective : Ideal S ≃o { p : Ideal R // comap f ⊥ ≤ p } where
  toFun J := ⟨comap f J, comap_mono bot_le⟩
  invFun I := map f I.1
  left_inv J := map_comap_of_surjective f hf J
  right_inv I :=
    Subtype.eq <|
      show comap f (map f I.1) = I.1 from
        (comap_map_of_surjective f hf I).symm ▸ le_antisymm (sup_le le_rfl I.2) le_sup_left
  map_rel_iff' {I1 I2} :=
    ⟨fun H => map_comap_of_surjective f hf I1 ▸ map_comap_of_surjective f hf I2 ▸ map_mono H,
      comap_mono⟩
#align ideal.rel_iso_of_surjective Ideal.relIsoOfSurjective

/-- The map on ideals induced by a surjective map preserves inclusion. -/
def orderEmbeddingOfSurjective : Ideal S ↪o Ideal R :=
  (relIsoOfSurjective f hf).toRelEmbedding.trans (Subtype.relEmbedding (fun x y => x ≤ y) _)
#align ideal.order_embedding_of_surjective Ideal.orderEmbeddingOfSurjective

theorem map_eq_top_or_isMaximal_of_surjective {I : Ideal R} (H : IsMaximal I) :
    map f I = ⊤ ∨ IsMaximal (map f I) := by
  refine or_iff_not_imp_left.2 fun ne_top => ⟨⟨fun h => ne_top h, fun J hJ => ?_⟩⟩
  · refine
      (relIsoOfSurjective f hf).injective
        (Subtype.ext_iff.2 (Eq.trans (H.1.2 (comap f J) (lt_of_le_of_ne ?_ ?_)) comap_top.symm))
    · exact map_le_iff_le_comap.1 (le_of_lt hJ)
    · exact fun h => hJ.right (le_map_of_comap_le_of_surjective f hf (le_of_eq h.symm))
#align ideal.map_eq_top_or_is_maximal_of_surjective Ideal.map_eq_top_or_isMaximal_of_surjective

theorem comap_isMaximal_of_surjective {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K) := by
  refine ⟨⟨comap_ne_top _ H.1.1, fun J hJ => ?_⟩⟩
  suffices map f J = ⊤ by
    have := congr_arg (comap f) this
    rw [comap_top, comap_map_of_surjective _ hf, eq_top_iff] at this
    rw [eq_top_iff]
    exact le_trans this (sup_le (le_of_eq rfl) (le_trans (comap_mono bot_le) (le_of_lt hJ)))
  refine
    H.1.2 (map f J)
      (lt_of_le_of_ne (le_map_of_comap_le_of_surjective _ hf (le_of_lt hJ)) fun h =>
        ne_of_lt hJ (_root_.trans (congr_arg (comap f) h) ?_))
  rw [comap_map_of_surjective _ hf, sup_eq_left]
  exact le_trans (comap_mono bot_le) (le_of_lt hJ)
#align ideal.comap_is_maximal_of_surjective Ideal.comap_isMaximal_of_surjective

theorem comap_le_comap_iff_of_surjective (I J : Ideal S) : comap f I ≤ comap f J ↔ I ≤ J :=
  ⟨fun h => (map_comap_of_surjective f hf I).symm.le.trans (map_le_of_le_comap h), fun h =>
    le_comap_of_map_le ((map_comap_of_surjective f hf I).le.trans h)⟩
#align ideal.comap_le_comap_iff_of_surjective Ideal.comap_le_comap_iff_of_surjective

end Surjective


section Bijective

variable (hf : Function.Bijective f)

/-- Special case of the correspondence theorem for isomorphic rings -/
def relIsoOfBijective : Ideal S ≃o Ideal R where
  toFun := comap f
  invFun := map f
  left_inv := (relIsoOfSurjective f hf.right).left_inv
  right_inv J :=
    Subtype.ext_iff.1
      ((relIsoOfSurjective f hf.right).right_inv ⟨J, comap_bot_le_of_injective f hf.left⟩)
  map_rel_iff' {_ _} := (relIsoOfSurjective f hf.right).map_rel_iff'
#align ideal.rel_iso_of_bijective Ideal.relIsoOfBijective

theorem comap_le_iff_le_map {I : Ideal R} {K : Ideal S} : comap f K ≤ I ↔ K ≤ map f I :=
  ⟨fun h => le_map_of_comap_le_of_surjective f hf.right h, fun h =>
    (relIsoOfBijective f hf).right_inv I ▸ comap_mono h⟩
#align ideal.comap_le_iff_le_map Ideal.comap_le_iff_le_map

theorem map.isMaximal {I : Ideal R} (H : IsMaximal I) : IsMaximal (map f I) := by
  refine
    or_iff_not_imp_left.1 (map_eq_top_or_isMaximal_of_surjective f hf.right H) fun h => H.1.1 ?_
  calc
    I = comap f (map f I) := ((relIsoOfBijective f hf).right_inv I).symm
    _ = comap f ⊤ := by rw [h]
    _ = ⊤ := by rw [comap_top]
#align ideal.map.is_maximal Ideal.map.isMaximal

end Bijective

theorem RingEquiv.bot_maximal_iff (e : R ≃+* S) :
    (⊥ : Ideal R).IsMaximal ↔ (⊥ : Ideal S).IsMaximal :=
  ⟨fun h => map_bot (f := e.toRingHom) ▸ map.isMaximal e.toRingHom e.bijective h, fun h =>
    map_bot (f := e.symm.toRingHom) ▸ map.isMaximal e.symm.toRingHom e.symm.bijective h⟩
#align ideal.ring_equiv.bot_maximal_iff Ideal.RingEquiv.bot_maximal_iff

end Ring

section CommRing

variable {F : Type*} [CommRing R] [CommRing S]
variable [FunLike F R S] [rc : RingHomClass F R S]
variable (f : F)
variable {I J : Ideal R} {K L : Ideal S}
variable (I J K L)

theorem map_mul : map f (I * J) = map f I * map f J :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      mul_le.2 fun r hri s hsj =>
        show (f (r * s)) ∈ map f I * map f J by
          rw [_root_.map_mul]; exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
    (span_mul_span (↑f '' ↑I) (↑f '' ↑J) ▸ (span_le.2 <|
      Set.iUnion₂_subset fun i ⟨r, hri, hfri⟩ =>
        Set.iUnion₂_subset fun j ⟨s, hsj, hfsj⟩ =>
          Set.singleton_subset_iff.2 <|
            hfri ▸ hfsj ▸ by rw [← _root_.map_mul]; exact mem_map_of_mem f (mul_mem_mul hri hsj)))
#align ideal.map_mul Ideal.map_mul

/-- The pushforward `Ideal.map` as a monoid-with-zero homomorphism. -/
@[simps]
def mapHom : Ideal R →*₀ Ideal S where
  toFun := map f
  map_mul' I J := Ideal.map_mul f I J
  map_one' := by simp only [one_eq_top]; exact Ideal.map_top f
  map_zero' := Ideal.map_bot
#align ideal.map_hom Ideal.mapHom

protected theorem map_pow (n : ℕ) : map f (I ^ n) = map f I ^ n :=
  map_pow (mapHom f) I n
#align ideal.map_pow Ideal.map_pow

theorem comap_radical : comap f (radical K) = radical (comap f K) := by
  ext
  simp [radical]
#align ideal.comap_radical Ideal.comap_radical

variable {K}

theorem IsRadical.comap (hK : K.IsRadical) : (comap f K).IsRadical := by
  rw [← hK.radical, comap_radical]
  apply radical_isRadical
#align ideal.is_radical.comap Ideal.IsRadical.comap

variable {I J L}

theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
  map_le_iff_le_comap.2 fun r ⟨n, hrni⟩ => ⟨n, map_pow f r n ▸ mem_map_of_mem f hrni⟩
#align ideal.map_radical_le Ideal.map_radical_le

theorem le_comap_mul : comap f K * comap f L ≤ comap f (K * L) :=
  map_le_iff_le_comap.1 <|
    (map_mul f (comap f K) (comap f L)).symm ▸
      mul_mono (map_le_iff_le_comap.2 <| le_rfl) (map_le_iff_le_comap.2 <| le_rfl)
#align ideal.le_comap_mul Ideal.le_comap_mul

theorem le_comap_pow (n : ℕ) : K.comap f ^ n ≤ (K ^ n).comap f := by
  induction' n with n n_ih
  · rw [pow_zero, pow_zero, Ideal.one_eq_top, Ideal.one_eq_top]
    exact rfl.le
  · rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono_left n_ih).trans (Ideal.le_comap_mul f)
#align ideal.le_comap_pow Ideal.le_comap_pow

end CommRing

end MapAndComap

end Ideal

namespace RingHom

variable {R : Type u} {S : Type v} {T : Type w}

section Semiring

variable {F : Type*} {G : Type*} [Semiring R] [Semiring S] [Semiring T]
variable [FunLike F R S] [rcf : RingHomClass F R S] [FunLike G T S] [rcg : RingHomClass G T S]
variable (f : F) (g : G)

/-- Kernel of a ring homomorphism as an ideal of the domain. -/
def ker : Ideal R :=
  Ideal.comap f ⊥
#align ring_hom.ker RingHom.ker

/-- An element is in the kernel if and only if it maps to zero. -/
theorem mem_ker {r} : r ∈ ker f ↔ f r = 0 := by rw [ker, Ideal.mem_comap, Submodule.mem_bot]
#align ring_hom.mem_ker RingHom.mem_ker

theorem ker_eq : (ker f : Set R) = Set.preimage f {0} :=
  rfl
#align ring_hom.ker_eq RingHom.ker_eq

theorem ker_eq_comap_bot (f : F) : ker f = Ideal.comap f ⊥ :=
  rfl
#align ring_hom.ker_eq_comap_bot RingHom.ker_eq_comap_bot

theorem comap_ker (f : S →+* R) (g : T →+* S) : f.ker.comap g = ker (f.comp g) := by
  rw [RingHom.ker_eq_comap_bot, Ideal.comap_comap, RingHom.ker_eq_comap_bot]
#align ring_hom.comap_ker RingHom.comap_ker

/-- If the target is not the zero ring, then one is not in the kernel. -/
theorem not_one_mem_ker [Nontrivial S] (f : F) : (1 : R) ∉ ker f := by
  rw [mem_ker, map_one]
  exact one_ne_zero
#align ring_hom.not_one_mem_ker RingHom.not_one_mem_ker

theorem ker_ne_top [Nontrivial S] (f : F) : ker f ≠ ⊤ :=
  (Ideal.ne_top_iff_one _).mpr <| not_one_mem_ker f
#align ring_hom.ker_ne_top RingHom.ker_ne_top

lemma _root_.Pi.ker_ringHom {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]
    (φ : ∀ i, S →+* R i) : ker (Pi.ringHom φ) = ⨅ i, ker (φ i) := by
  ext x
  simp [mem_ker, Ideal.mem_iInf, Function.funext_iff]

@[simp]
theorem ker_rangeSRestrict (f : R →+* S) : ker f.rangeSRestrict = ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end Semiring

section Ring

variable {F : Type*} [Ring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

theorem injective_iff_ker_eq_bot : Function.Injective f ↔ ker f = ⊥ := by
  rw [SetLike.ext'_iff, ker_eq, Set.ext_iff]
  exact injective_iff_map_eq_zero' f
#align ring_hom.injective_iff_ker_eq_bot RingHom.injective_iff_ker_eq_bot

theorem ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 := by
  rw [← injective_iff_map_eq_zero f, injective_iff_ker_eq_bot]
#align ring_hom.ker_eq_bot_iff_eq_zero RingHom.ker_eq_bot_iff_eq_zero

@[simp]
theorem ker_coe_equiv (f : R ≃+* S) : ker (f : R →+* S) = ⊥ := by
  simpa only [← injective_iff_ker_eq_bot] using EquivLike.injective f
#align ring_hom.ker_coe_equiv RingHom.ker_coe_equiv

@[simp]
theorem ker_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S] (f : F') : ker f = ⊥ := by
  simpa only [← injective_iff_ker_eq_bot] using EquivLike.injective f
#align ring_hom.ker_equiv RingHom.ker_equiv

end Ring

section RingRing

variable {F : Type*} [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

theorem sub_mem_ker_iff {x y} : x - y ∈ ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]
#align ring_hom.sub_mem_ker_iff RingHom.sub_mem_ker_iff

@[simp]
theorem ker_rangeRestrict (f : R →+* S) : ker f.rangeRestrict = ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end RingRing

/-- The kernel of a homomorphism to a domain is a prime ideal. -/
theorem ker_isPrime {F : Type*} [Ring R] [Ring S] [IsDomain S]
    [FunLike F R S] [RingHomClass F R S] (f : F) :
    (ker f).IsPrime :=
  ⟨by
    rw [Ne, Ideal.eq_top_iff_one]
    exact not_one_mem_ker f,
   fun {x y} => by
    simpa only [mem_ker, map_mul] using @eq_zero_or_eq_zero_of_mul_eq_zero S _ _ _ _ _⟩
#align ring_hom.ker_is_prime RingHom.ker_isPrime

/-- The kernel of a homomorphism to a field is a maximal ideal. -/
theorem ker_isMaximal_of_surjective {R K F : Type*} [Ring R] [Field K]
    [FunLike F R K] [RingHomClass F R K] (f : F)
    (hf : Function.Surjective f) : (ker f).IsMaximal := by
  refine
    Ideal.isMaximal_iff.mpr
      ⟨fun h1 => one_ne_zero' K <| map_one f ▸ (mem_ker f).mp h1, fun J x hJ hxf hxJ => ?_⟩
  obtain ⟨y, hy⟩ := hf (f x)⁻¹
  have H : 1 = y * x - (y * x - 1) := (sub_sub_cancel _ _).symm
  rw [H]
  refine J.sub_mem (J.mul_mem_left _ hxJ) (hJ ?_)
  rw [mem_ker]
  simp only [hy, map_sub, map_one, map_mul, inv_mul_cancel (mt (mem_ker f).mpr hxf), sub_self]
#align ring_hom.ker_is_maximal_of_surjective RingHom.ker_isMaximal_of_surjective

end RingHom

namespace Ideal

variable {R : Type*} {S : Type*} {F : Type*}

section Semiring

variable [Semiring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S]

theorem map_eq_bot_iff_le_ker {I : Ideal R} (f : F) : I.map f = ⊥ ↔ I ≤ RingHom.ker f := by
  rw [RingHom.ker, eq_bot_iff, map_le_iff_le_comap]
#align ideal.map_eq_bot_iff_le_ker Ideal.map_eq_bot_iff_le_ker

theorem ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f ≤ comap f K := fun _ hx =>
  mem_comap.2 (((RingHom.mem_ker f).1 hx).symm ▸ K.zero_mem)
#align ideal.ker_le_comap Ideal.ker_le_comap

theorem map_isPrime_of_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S]
    (f : F') {I : Ideal R} [IsPrime I] : IsPrime (map f I) := by
  have h : I.map f = I.map ((f : R ≃+* S) : R →+* S) := rfl
  rw [h, map_comap_of_equiv I (f : R ≃+* S)]
  exact Ideal.IsPrime.comap (RingEquiv.symm (f : R ≃+* S))
#align ideal.map_is_prime_of_equiv Ideal.map_isPrime_of_equiv

end Semiring

section Ring

variable [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S]

theorem map_sInf {A : Set (Ideal R)} {f : F} (hf : Function.Surjective f) :
    (∀ J ∈ A, RingHom.ker f ≤ J) → map f (sInf A) = sInf (map f '' A) := by
  refine fun h => le_antisymm (le_sInf ?_) ?_
  · intro j hj y hy
    cases' (mem_map_iff_of_surjective f hf).1 hy with x hx
    cases' (Set.mem_image _ _ _).mp hj with J hJ
    rw [← hJ.right, ← hx.right]
    exact mem_map_of_mem f (sInf_le_of_le hJ.left (le_of_eq rfl) hx.left)
  · intro y hy
    cases' hf y with x hx
    refine hx ▸ mem_map_of_mem f ?_
    have : ∀ I ∈ A, y ∈ map f I := by simpa using hy
    rw [Submodule.mem_sInf]
    intro J hJ
    rcases (mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩
    have : x - x' ∈ J := by
      apply h J hJ
      rw [RingHom.mem_ker, map_sub, hx, sub_self]
    simpa only [sub_add_cancel] using J.add_mem this hx'
#align ideal.map_Inf Ideal.map_sInf

theorem map_isPrime_of_surjective {f : F} (hf : Function.Surjective f) {I : Ideal R} [H : IsPrime I]
    (hk : RingHom.ker f ≤ I) : IsPrime (map f I) := by
  refine ⟨fun h => H.ne_top (eq_top_iff.2 ?_), fun {x y} => ?_⟩
  · replace h := congr_arg (comap f) h
    rw [comap_map_of_surjective _ hf, comap_top] at h
    exact h ▸ sup_le (le_of_eq rfl) hk
  · refine fun hxy => (hf x).recOn fun a ha => (hf y).recOn fun b hb => ?_
    rw [← ha, ← hb, ← _root_.map_mul f, mem_map_iff_of_surjective _ hf] at hxy
    rcases hxy with ⟨c, hc, hc'⟩
    rw [← sub_eq_zero, ← map_sub] at hc'
    have : a * b ∈ I := by
      convert I.sub_mem hc (hk (hc' : c - a * b ∈ RingHom.ker f)) using 1
      abel
    exact
      (H.mem_or_mem this).imp (fun h => ha ▸ mem_map_of_mem f h) fun h => hb ▸ mem_map_of_mem f h
#align ideal.map_is_prime_of_surjective Ideal.map_isPrime_of_surjective

theorem map_eq_bot_iff_of_injective {I : Ideal R} {f : F} (hf : Function.Injective f) :
    I.map f = ⊥ ↔ I = ⊥ := by
  rw [map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot f).mp hf, le_bot_iff]
#align ideal.map_eq_bot_iff_of_injective Ideal.map_eq_bot_iff_of_injective

end Ring

section CommRing

variable [CommRing R] [CommRing S]

theorem map_eq_iff_sup_ker_eq_of_surjective {I J : Ideal R} (f : R →+* S)
    (hf : Function.Surjective f) : map f I = map f J ↔ I ⊔ RingHom.ker f = J ⊔ RingHom.ker f := by
  rw [← (comap_injective_of_surjective f hf).eq_iff, comap_map_of_surjective f hf,
    comap_map_of_surjective f hf, RingHom.ker_eq_comap_bot]
#align ideal.map_eq_iff_sup_ker_eq_of_surjective Ideal.map_eq_iff_sup_ker_eq_of_surjective

theorem map_radical_of_surjective {f : R →+* S} (hf : Function.Surjective f) {I : Ideal R}
    (h : RingHom.ker f ≤ I) : map f I.radical = (map f I).radical := by
  rw [radical_eq_sInf, radical_eq_sInf]
  have : ∀ J ∈ {J : Ideal R | I ≤ J ∧ J.IsPrime}, RingHom.ker f ≤ J := fun J hJ => h.trans hJ.left
  convert map_sInf hf this
  refine funext fun j => propext ⟨?_, ?_⟩
  · rintro ⟨hj, hj'⟩
    haveI : j.IsPrime := hj'
    exact
      ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_isPrime f j⟩, map_comap_of_surjective f hf j⟩⟩
  · rintro ⟨J, ⟨hJ, hJ'⟩⟩
    haveI : J.IsPrime := hJ.right
    exact ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_isPrime_of_surjective hf (le_trans h hJ.left)⟩
#align ideal.map_radical_of_surjective Ideal.map_radical_of_surjective

end CommRing

end Ideal

namespace RingHom

variable {A B C : Type*} [Ring A] [Ring B] [Ring C]
variable (f : A →+* B) (f_inv : B → A)

/-- Auxiliary definition used to define `liftOfRightInverse` -/
def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) :
    B →+* C :=
  { AddMonoidHom.liftOfRightInverse f.toAddMonoidHom f_inv hf ⟨g.toAddMonoidHom, hg⟩ with
    toFun := fun b => g (f_inv b)
    map_one' := by
      rw [← map_one g, ← sub_eq_zero, ← map_sub g, ← mem_ker g]
      apply hg
      rw [mem_ker f, map_sub f, sub_eq_zero, map_one f]
      exact hf 1
    map_mul' := by
      intro x y
      rw [← map_mul g, ← sub_eq_zero, ← map_sub g, ← mem_ker g]
      apply hg
      rw [mem_ker f, map_sub f, sub_eq_zero, map_mul f]
      simp only [hf _] }
#align ring_hom.lift_of_right_inverse_aux RingHom.liftOfRightInverseAux

@[simp]
theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (a : A) :
    (f.liftOfRightInverseAux f_inv hf g hg) (f a) = g a :=
  f.toAddMonoidHom.liftOfRightInverse_comp_apply f_inv hf ⟨g.toAddMonoidHom, hg⟩ a
#align ring_hom.lift_of_right_inverse_aux_comp_apply RingHom.liftOfRightInverseAux_comp_apply

/-- `liftOfRightInverse f hf g hg` is the unique ring homomorphism `φ`

* such that `φ.comp f = g` (`RingHom.liftOfRightInverse_comp`),
* where `f : A →+* B` has a right_inverse `f_inv` (`hf`),
* and `g : B →+* C` satisfies `hg : f.ker ≤ g.ker`.

See `RingHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
-/
def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : A →+* C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →+* C) where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
  invFun φ := ⟨φ.comp f, fun x hx => (mem_ker _).mpr <| by simp [(mem_ker _).mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply, Subtype.coe_mk]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]
#align ring_hom.lift_of_right_inverse RingHom.liftOfRightInverse

/-- A non-computable version of `RingHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[simp]
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) :
    { g : A →+* C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →+* C) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)
#align ring_hom.lift_of_surjective RingHom.liftOfSurjective

theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) (x : A) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x
#align ring_hom.lift_of_right_inverse_comp_apply RingHom.liftOfRightInverse_comp_apply

theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) :
    (f.liftOfRightInverse f_inv hf g).comp f = g :=
  RingHom.ext <| f.liftOfRightInverse_comp_apply f_inv hf g
#align ring_hom.lift_of_right_inverse_comp RingHom.liftOfRightInverse_comp

theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (h : B →+* C) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm
#align ring_hom.eq_lift_of_right_inverse RingHom.eq_liftOfRightInverse

end RingHom

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)

lemma coe_ker : RingHom.ker f = RingHom.ker (f : A →+* B) := rfl

lemma coe_ideal_map (I : Ideal A) :
    Ideal.map f I = Ideal.map (f : A →+* B) I := rfl

end AlgHom
