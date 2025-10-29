/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.Data.DFinsupp.Module
import Mathlib.RingTheory.Ideal.Operations

/-!
# Maps on modules and ideals

Main definitions include `Ideal.map`, `Ideal.comap`, `RingHom.ker`, `Module.annihilator`
and `Submodule.annihilator`.
-/

assert_not_exists Module.Basis -- See `RingTheory.Ideal.Basis`
  Submodule.hasQuotient -- See `RingTheory.Ideal.Quotient.Operations`

universe u v w x

open Pointwise

namespace Ideal

section MapAndComap

variable {R : Type u} {S : Type v}

section Semiring

variable {F : Type*} [Semiring R] [Semiring S]
variable [FunLike F R S]
variable (f : F)
variable {I J : Ideal R} {K L : Ideal S}

/-- `I.map f` is the span of the image of the ideal `I` under `f`, which may be bigger than
  the image itself. -/
def map (I : Ideal R) : Ideal S :=
  span (f '' I)

/-- `I.comap f` is the preimage of `I` under `f`. -/
def comap [RingHomClass F R S] (I : Ideal S) : Ideal R where
  carrier := f ⁻¹' I
  add_mem' {x y} hx hy := by
    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢
    exact add_mem hx hy
  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]
  smul_mem' c x hx := by
    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *
    exact mul_mem_left I _ hx

@[simp]
theorem coe_comap [RingHomClass F R S] (I : Ideal S) : (comap f I : Set R) = f ⁻¹' I := rfl

lemma comap_coe [RingHomClass F R S] (I : Ideal S) : I.comap (f : R →+* S) = I.comap f := rfl

lemma map_coe [RingHomClass F R S] (I : Ideal R) : I.map (f : R →+* S) = I.map f := rfl

variable {f}

theorem map_mono (h : I ≤ J) : map f I ≤ map f J :=
  span_mono <| Set.image_mono h

theorem mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : x ∈ I) : f x ∈ map f I :=
  subset_span ⟨x, h, rfl⟩

theorem apply_coe_mem_map (f : F) (I : Ideal R) (x : I) : f x ∈ I.map f :=
  mem_map_of_mem f x.2

theorem map_le_iff_le_comap [RingHomClass F R S] : map f I ≤ K ↔ I ≤ comap f K :=
  span_le.trans Set.image_subset_iff

@[simp]
theorem mem_comap [RingHomClass F R S] {x} : x ∈ comap f K ↔ f x ∈ K :=
  Iff.rfl

theorem comap_mono [RingHomClass F R S] (h : K ≤ L) : comap f K ≤ comap f L :=
  Set.preimage_mono fun _ hx => h hx

variable (f)

theorem comap_ne_top [RingHomClass F R S] (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
  (ne_top_iff_one _).2 <| by rw [mem_comap, map_one]; exact (ne_top_iff_one _).1 hK

lemma exists_ideal_comap_le_prime {S} [CommSemiring S] [FunLike F R S] [RingHomClass F R S]
    {f : F} (P : Ideal R) [P.IsPrime] (I : Ideal S) (le : I.comap f ≤ P) :
    ∃ Q ≥ I, Q.IsPrime ∧ Q.comap f ≤ P :=
  have ⟨Q, hQ, hIQ, disj⟩ := I.exists_le_prime_disjoint (P.primeCompl.map f) <|
    Set.disjoint_left.mpr fun _ ↦ by rintro hI ⟨r, hp, rfl⟩; exact hp (le hI)
  ⟨Q, hIQ, hQ, fun r hp' ↦ of_not_not fun hp ↦ Set.disjoint_left.mp disj hp' ⟨_, hp, rfl⟩⟩

variable {G : Type*} [FunLike G S R]

theorem map_le_comap_of_inv_on [RingHomClass G S R] (g : G) (I : Ideal R)
    (hf : Set.LeftInvOn g f I) :
    I.map f ≤ I.comap g := by
  refine Ideal.span_le.2 ?_
  rintro x ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_comap, hf hx]
  exact hx

theorem comap_le_map_of_inv_on [RingHomClass F R S] (g : G) (I : Ideal S)
    (hf : Set.LeftInvOn g f (f ⁻¹' I)) :
    I.comap f ≤ I.map g :=
  fun x (hx : f x ∈ I) => hf hx ▸ Ideal.mem_map_of_mem g hx

/-- The `Ideal` version of `Set.image_subset_preimage_of_inverse`. -/
theorem map_le_comap_of_inverse [RingHomClass G S R] (g : G) (I : Ideal R)
    (h : Function.LeftInverse g f) :
    I.map f ≤ I.comap g :=
  map_le_comap_of_inv_on _ _ _ <| h.leftInvOn _

variable [RingHomClass F R S]

instance (priority := low) [K.IsTwoSided] : (comap f K).IsTwoSided :=
  ⟨fun b ha ↦ by rw [mem_comap, map_mul]; exact mul_mem_right _ _ ha⟩

/-- The `Ideal` version of `Set.preimage_subset_image_of_inverse`. -/
theorem comap_le_map_of_inverse (g : G) (I : Ideal S) (h : Function.LeftInverse g f) :
    I.comap f ≤ I.map g :=
  comap_le_map_of_inv_on _ _ _ <| h.leftInvOn _

instance IsPrime.comap [hK : K.IsPrime] : (comap f K).IsPrime :=
  ⟨comap_ne_top _ hK.1, fun {x y} => by simp only [mem_comap, map_mul]; apply hK.2⟩

variable (I J K L)

theorem map_top : map f ⊤ = ⊤ :=
  (eq_top_iff_one _).2 <| subset_span ⟨1, trivial, map_one f⟩

theorem gc_map_comap : GaloisConnection (Ideal.map f) (Ideal.comap f) := fun _ _ =>
  Ideal.map_le_iff_le_comap

@[simp]
theorem comap_id : I.comap (RingHom.id R) = I :=
  Ideal.ext fun _ => Iff.rfl

@[simp]
lemma comap_idₐ {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (I : Ideal S) :
    Ideal.comap (AlgHom.id R S) I = I :=
  I.comap_id

@[simp]
theorem map_id : I.map (RingHom.id R) = I :=
  (gc_map_comap (RingHom.id R)).l_unique GaloisConnection.id comap_id

@[simp]
lemma map_idₐ {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] (I : Ideal S) :
    Ideal.map (AlgHom.id R S) I = I :=
  I.map_id

theorem comap_comap {T : Type*} [Semiring T] {I : Ideal T} (f : R →+* S) (g : S →+* T) :
    (I.comap g).comap f = I.comap (g.comp f) :=
  rfl

lemma comap_comapₐ {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
    [Algebra R B] [Semiring C] [Algebra R C] {I : Ideal C} (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (I.comap g).comap f = I.comap (g.comp f) :=
  I.comap_comap f.toRingHom g.toRingHom

theorem map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R →+* S) (g : S →+* T) :
    (I.map f).map g = I.map (g.comp f) :=
  ((gc_map_comap f).compose (gc_map_comap g)).l_unique (gc_map_comap (g.comp f)) fun _ =>
    comap_comap _ _

lemma map_mapₐ {R A B C : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B]
    [Algebra R B] [Semiring C] [Algebra R C] {I : Ideal A} (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (I.map f).map g = I.map (g.comp f) :=
  I.map_map f.toRingHom g.toRingHom

theorem map_span (f : F) (s : Set R) : map f (span s) = span (f '' s) := by
  refine (Submodule.span_eq_of_le _ ?_ ?_).symm
  · rintro _ ⟨x, hx, rfl⟩; exact mem_map_of_mem f (subset_span hx)
  · rw [map_le_iff_le_comap, span_le, coe_comap, ← Set.image_subset_iff]
    exact subset_span

variable {f I J K L}

theorem map_le_of_le_comap : I ≤ K.comap f → I.map f ≤ K :=
  (gc_map_comap f).l_le

theorem le_comap_of_map_le : I.map f ≤ K → I ≤ K.comap f :=
  (gc_map_comap f).le_u

theorem le_comap_map : I ≤ (I.map f).comap f :=
  (gc_map_comap f).le_u_l _

theorem map_comap_le : (K.comap f).map f ≤ K :=
  (gc_map_comap f).l_u_le _

@[simp]
theorem comap_top : (⊤ : Ideal S).comap f = ⊤ :=
  (gc_map_comap f).u_top

@[simp]
theorem comap_eq_top_iff {I : Ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
  ⟨fun h => I.eq_top_iff_one.mpr (map_one f ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
    fun h => by rw [h, comap_top]⟩

@[simp]
theorem map_bot : (⊥ : Ideal R).map f = ⊥ :=
  (gc_map_comap f).l_bot

theorem ne_bot_of_map_ne_bot (hI : map f I ≠ ⊥) : I ≠ ⊥ :=
  fun h => hI (Eq.mpr (congrArg (fun I ↦ map f I = ⊥) h) map_bot)

variable (f I J K L)

@[simp]
theorem map_comap_map : ((I.map f).comap f).map f = I.map f :=
  (gc_map_comap f).l_u_l_eq_l I

@[simp]
theorem comap_map_comap : ((K.comap f).map f).comap f = K.comap f :=
  (gc_map_comap f).u_l_u_eq_u K

theorem map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

theorem comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L :=
  rfl

variable {ι : Sort*}

theorem map_iSup (K : ι → Ideal R) : (iSup K).map f = ⨆ i, (K i).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

theorem comap_iInf (K : ι → Ideal S) : (iInf K).comap f = ⨅ i, (K i).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_iInf

theorem map_sSup (s : Set (Ideal R)) : (sSup s).map f = ⨆ I ∈ s, (I : Ideal R).map f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sSup

theorem comap_sInf (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I ∈ s, (I : Ideal S).comap f :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).u_sInf

theorem comap_sInf' (s : Set (Ideal S)) : (sInf s).comap f = ⨅ I ∈ comap f '' s, I :=
  _root_.trans (comap_sInf f s) (by rw [iInf_image])

/-- Variant of `Ideal.IsPrime.comap` where ideal is explicit rather than implicit. -/
theorem comap_isPrime [H : IsPrime K] : IsPrime (comap f K) :=
  H.comap f

variable {I J K L}

theorem map_inf_le : map f (I ⊓ J) ≤ map f I ⊓ map f J :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_l.map_inf_le _ _

theorem le_comap_sup : comap f K ⊔ comap f L ≤ comap f (K ⊔ L) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).monotone_u.le_map_sup _ _

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
  exact map_iSup₂ (Submodule.restrictScalarsLatticeHom R S M) _

@[simp]
theorem smul_top_eq_map {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (I : Ideal R) : I • (⊤ : Submodule R S) = (I.map (algebraMap R S)).restrictScalars R :=
  Eq.trans (smul_restrictScalars I (⊤ : Ideal S)).symm <|
    congrArg _ <| Eq.trans (Ideal.smul_eq_mul _ _) (Ideal.mul_top _)

@[simp]
theorem coe_restrictScalars {R S : Type*} [Semiring R] [Semiring S] [Module R S]
    [IsScalarTower R S S] (I : Ideal S) : (I.restrictScalars R : Set S) = ↑I :=
  rfl

/-- The smallest `S`-submodule that contains all `x ∈ I * y ∈ J`
is also the smallest `R`-submodule that does so. -/
@[simp]
theorem restrictScalars_mul {R S : Type*} [Semiring R] [Semiring S] [Module R S]
    [IsScalarTower R S S] (I J : Ideal S) :
    (I * J).restrictScalars R = I.restrictScalars R * J.restrictScalars R :=
  rfl

section Surjective

section

variable (hf : Function.Surjective f)
include hf

open Function

theorem map_comap_of_surjective (I : Ideal S) : map f (comap f I) = I :=
  le_antisymm (map_le_iff_le_comap.2 le_rfl) fun s hsi =>
    let ⟨r, hfrs⟩ := hf s
    hfrs ▸ (mem_map_of_mem f <| show f r ∈ I from hfrs.symm ▸ hsi)

/-- `map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity -/
def giMapComap : GaloisInsertion (map f) (comap f) :=
  GaloisInsertion.monotoneIntro (gc_map_comap f).monotone_u (gc_map_comap f).monotone_l
    (fun _ => le_comap_map) (map_comap_of_surjective _ hf)

theorem map_surjective_of_surjective : Surjective (map f) :=
  (giMapComap f hf).l_surjective

theorem comap_injective_of_surjective : Injective (comap f) :=
  (giMapComap f hf).u_injective

theorem map_sup_comap_of_surjective (I J : Ideal S) : (I.comap f ⊔ J.comap f).map f = I ⊔ J :=
  (giMapComap f hf).l_sup_u _ _

theorem map_iSup_comap_of_surjective (K : ι → Ideal S) : (⨆ i, (K i).comap f).map f = iSup K :=
  (giMapComap f hf).l_iSup_u _

theorem map_inf_comap_of_surjective (I J : Ideal S) : (I.comap f ⊓ J.comap f).map f = I ⊓ J :=
  (giMapComap f hf).l_inf_u _ _

theorem map_iInf_comap_of_surjective (K : ι → Ideal S) : (⨅ i, (K i).comap f).map f = iInf K :=
  (giMapComap f hf).l_iInf_u _

theorem mem_image_of_mem_map_of_surjective {I : Ideal R} {y} (H : y ∈ map f I) : y ∈ f '' I :=
  Submodule.span_induction (hx := H) (fun _ => id) ⟨0, I.zero_mem, map_zero f⟩
    (fun _ _ _ _ ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩ =>
      ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ map_add f _ _⟩)
    fun c _ _ ⟨x, hxi, hxy⟩ =>
    let ⟨d, hdc⟩ := hf c
    ⟨d * x, I.mul_mem_left _ hxi, hdc ▸ hxy ▸ map_mul f _ _⟩

theorem mem_map_iff_of_surjective {I : Ideal R} {y} : y ∈ map f I ↔ ∃ x, x ∈ I ∧ f x = y :=
  ⟨fun h => (Set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h), fun ⟨_, hx⟩ =>
    hx.right ▸ mem_map_of_mem f hx.left⟩

theorem le_map_of_comap_le_of_surjective : comap f K ≤ I → K ≤ map f I := fun h =>
  map_comap_of_surjective f hf K ▸ map_mono h

end

theorem map_comap_eq_self_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    (I : Ideal S) : map e (comap e I) = I :=
  I.map_comap_of_surjective e (EquivLike.surjective e)

theorem map_eq_submodule_map (f : R →+* S) [h : RingHomSurjective f] (I : Ideal R) :
    I.map f = Submodule.map f.toSemilinearMap I :=
  Submodule.ext fun _ => mem_map_iff_of_surjective f h.1

instance (priority := low) (f : R →+* S) [RingHomSurjective f] (I : Ideal R) [I.IsTwoSided] :
    (I.map f).IsTwoSided where
  mul_mem_of_left b ha := by
    rw [map_eq_submodule_map] at ha ⊢
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := f.surjective b
    rw [RingHom.coe_toSemilinearMap, ← map_mul]
    exact ⟨_, I.mul_mem_right _ ha, rfl⟩

open Function in
theorem IsMaximal.comap_piEvalRingHom {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]
    {i : ι} {I : Ideal (R i)} (h : I.IsMaximal) : (I.comap <| Pi.evalRingHom R i).IsMaximal := by
  refine isMaximal_iff.mpr ⟨I.ne_top_iff_one.mp h.ne_top, fun J x le hxI hxJ ↦ ?_⟩
  have ⟨r, y, hy, eq⟩ := h.exists_inv hxI
  classical
  convert J.add_mem (J.mul_mem_left (update 0 i r) hxJ)
    (b := update 1 i y) (le <| by apply update_self i y 1 ▸ hy)
  ext j
  obtain rfl | ne := eq_or_ne j i
  · simpa [eq_comm] using eq
  · simp [update_of_ne ne]

theorem comap_le_comap_iff_of_surjective (hf : Function.Surjective f) (I J : Ideal S) :
    comap f I ≤ comap f J ↔ I ≤ J :=
  ⟨fun h => (map_comap_of_surjective f hf I).symm.le.trans (map_le_of_le_comap h), fun h =>
    le_comap_of_map_le ((map_comap_of_surjective f hf I).le.trans h)⟩

/-- The map on ideals induced by a surjective map preserves inclusion. -/
def orderEmbeddingOfSurjective (hf : Function.Surjective f) : Ideal S ↪o Ideal R where
  toFun := comap f
  inj' _ _ eq := SetLike.ext' (Set.preimage_injective.mpr hf <| SetLike.ext'_iff.mp eq)
  map_rel_iff' := comap_le_comap_iff_of_surjective _ hf ..

theorem map_eq_top_or_isMaximal_of_surjective (hf : Function.Surjective f) {I : Ideal R}
    (H : IsMaximal I) : map f I = ⊤ ∨ IsMaximal (map f I) :=
  or_iff_not_imp_left.2 fun ne_top ↦ ⟨⟨ne_top, fun _J hJ ↦ comap_injective_of_surjective f hf <|
    H.1.2 _ (le_comap_map.trans_lt <| (orderEmbeddingOfSurjective f hf).strictMono hJ)⟩⟩

end Surjective

section Pi

variable {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]

theorem map_evalRingHom_pi {I : Π i, Ideal (R i)} (i : ι) :
    (pi I).map (Pi.evalRingHom R i) = I i := by
  ext r
  rw [mem_map_iff_of_surjective (Pi.evalRingHom R i) (Function.surjective_eval _)]
  classical refine ⟨?_, fun hr ↦ ⟨_, single_mem_pi hr, by simp⟩⟩
  rintro ⟨r, hr, rfl⟩
  exact hr i

/-- Ideals in a finite direct product semiring `Πᵢ Rᵢ` are identified with tuples of ideals
in the individual semirings, in an order-preserving way.

(Note that this is not in general true for infinite direct products:
If infinitely many of the `Rᵢ` are nontrivial, then there exists an ideal of `Πᵢ Rᵢ` that
is not of the form `Πᵢ Iᵢ`, namely the ideal of finitely supported elements of `Πᵢ Rᵢ`
(it is also not a principal ideal).) -/
@[simps!] def piOrderIso [Finite ι] : Ideal (Π i, R i) ≃o Π i, Ideal (R i) := .symm
{ toFun := pi
  invFun I i := I.map (Pi.evalRingHom R i)
  left_inv _ := funext map_evalRingHom_pi
  right_inv I := by
    ext r
    simp_rw [mem_pi, mem_map_iff_of_surjective (Pi.evalRingHom R _) (Function.surjective_eval _)]
    refine ⟨(fun ⟨r', hr'⟩ ↦ ?_) ∘ Classical.skolem.mp, fun hr i ↦ ⟨r, hr, rfl⟩⟩
    have := Fintype.ofFinite ι
    classical rw [show r = ∑ i, Pi.single i 1 * r' i from funext fun i ↦ by
      rw [← (hr' _).2, Finset.sum_apply, Fintype.sum_eq_single i fun j ne ↦ by simp [ne]]; simp]
    exact sum_mem fun i _ ↦ I.mul_mem_left _ (hr' i).1
  map_rel_iff' := pi_le_pi_iff }

instance [Finite ι] [∀ i, IsPrincipalIdealRing (R i)] : IsPrincipalIdealRing (Π i, R i) where
  principal I := by
    rw [← piOrderIso.symm_apply_apply I]
    exact ⟨_, congr(pi $(funext fun i ↦
      (Submodule.IsPrincipal.span_singleton_generator _).symm)).trans pi_span⟩

end Pi

section Injective

theorem comap_bot_le_of_injective (hf : Function.Injective f) : comap f ⊥ ≤ I := by
  refine le_trans (fun x hx => ?_) bot_le
  rw [mem_comap, Submodule.mem_bot, ← map_zero f] at hx
  exact Eq.symm (hf hx) ▸ Submodule.zero_mem ⊥

theorem comap_bot_of_injective (hf : Function.Injective f) : Ideal.comap f ⊥ = ⊥ :=
  le_bot_iff.mp (Ideal.comap_bot_le_of_injective f hf)

end Injective

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm (map f I) = I`. -/
@[simp]
theorem map_of_equiv {I : Ideal R} (f : R ≃+* S) :
    (I.map (f : R →+* S)).map (f.symm : S →+* R) = I := by
  rw [← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, map_map,
    RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, map_id]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`,
  then `comap f (comap f.symm I) = I`. -/
@[simp]
theorem comap_of_equiv {I : Ideal R} (f : R ≃+* S) :
    (I.comap (f.symm : S →+* R)).comap (f : R →+* S) = I := by
  rw [← RingEquiv.toRingHom_eq_coe, ← RingEquiv.toRingHom_eq_coe, comap_comap,
    RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, RingEquiv.symm_comp, comap_id]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f I = comap f.symm I`. -/
theorem map_comap_of_equiv {I : Ideal R} (f : R ≃+* S) : I.map (f : R →+* S) = I.comap f.symm :=
  le_antisymm (Ideal.map_le_comap_of_inverse _ _ _ (Equiv.left_inv' _))
    (Ideal.comap_le_map_of_inverse _ _ _ (Equiv.right_inv' _))

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `comap f.symm I = map f I`. -/
@[simp]
theorem comap_symm {I : Ideal R} (f : R ≃+* S) : I.comap f.symm = I.map f :=
  (map_comap_of_equiv f).symm

/-- If `f : R ≃+* S` is a ring isomorphism and `I : Ideal R`, then `map f.symm I = comap f I`. -/
@[simp]
theorem map_symm {I : Ideal S} (f : R ≃+* S) : I.map f.symm = I.comap f :=
  map_comap_of_equiv (RingEquiv.symm f)

@[simp]
theorem symm_apply_mem_of_equiv_iff {I : Ideal R} {f : R ≃+* S} {y : S} :
    f.symm y ∈ I ↔ y ∈ I.map f := by
  rw [← comap_symm, mem_comap]

@[simp]
theorem apply_mem_of_equiv_iff {I : Ideal R} {f : R ≃+* S} {x : R} :
    f x ∈ I.map f ↔ x ∈ I := by
  rw [← comap_symm, Ideal.mem_comap, f.symm_apply_apply]

theorem mem_map_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    {I : Ideal R} (y : S) : y ∈ map e I ↔ ∃ x ∈ I, e x = y := by
  constructor
  · intro h
    simp_rw [show map e I = _ from map_comap_of_equiv (e : R ≃+* S)] at h
    exact ⟨(e : R ≃+* S).symm y, h, (e : R ≃+* S).apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    exact mem_map_of_mem e hx

section Bijective

variable (hf : Function.Bijective f) {I : Ideal R} {K : Ideal S}
include hf

/-- Special case of the correspondence theorem for isomorphic rings -/
def relIsoOfBijective : Ideal S ≃o Ideal R where
  toFun := comap f
  invFun := map f
  left_inv := map_comap_of_surjective _ hf.2
  right_inv J :=
    le_antisymm
      (fun _ h ↦ have ⟨y, hy, eq⟩ := (mem_map_iff_of_surjective _ hf.2).mp h; hf.1 eq ▸ hy)
      le_comap_map
  map_rel_iff' {_ _} := by
    refine ⟨fun h ↦ ?_, comap_mono⟩
    have := map_mono (f := f) h
    simpa only [Equiv.coe_fn_mk, map_comap_of_surjective f hf.2] using this

theorem comap_le_iff_le_map : comap f K ≤ I ↔ K ≤ map f I :=
  ⟨fun h => le_map_of_comap_le_of_surjective f hf.right h, fun h =>
    (relIsoOfBijective f hf).right_inv I ▸ comap_mono h⟩

lemma comap_map_of_bijective : (I.map f).comap f = I :=
  le_antisymm ((comap_le_iff_le_map f hf).mpr fun _ ↦ id) le_comap_map

theorem isMaximal_map_iff_of_bijective : IsMaximal (map f I) ↔ IsMaximal I := by
  simpa only [isMaximal_def] using (relIsoOfBijective _ hf).symm.isCoatom_iff _

theorem isMaximal_comap_iff_of_bijective : IsMaximal (comap f K) ↔ IsMaximal K := by
  simpa only [isMaximal_def] using (relIsoOfBijective _ hf).isCoatom_iff _

alias ⟨_, IsMaximal.map_bijective⟩ := isMaximal_map_iff_of_bijective
alias ⟨_, IsMaximal.comap_bijective⟩ := isMaximal_comap_iff_of_bijective

/-- A ring isomorphism sends a maximal ideal to a maximal ideal. -/
instance map_isMaximal_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    {p : Ideal R} [hp : p.IsMaximal] : (map e p).IsMaximal :=
  hp.map_bijective e (EquivLike.bijective e)

/-- The pullback of a maximal ideal under a ring isomorphism is a maximal ideal. -/
instance comap_isMaximal_of_equiv {E : Type*} [EquivLike E R S] [RingEquivClass E R S] (e : E)
    {p : Ideal S} [hp : p.IsMaximal] : (comap e p).IsMaximal :=
  hp.comap_bijective e (EquivLike.bijective e)

theorem isMaximal_iff_of_bijective : (⊥ : Ideal R).IsMaximal ↔ (⊥ : Ideal S).IsMaximal :=
  ⟨fun h ↦ map_bot (f := f) ▸ h.map_bijective f hf, fun h ↦ have e := RingEquiv.ofBijective f hf
    map_bot (f := e.symm) ▸ h.map_bijective _ e.symm.bijective⟩

end Bijective

end Semiring

section Ring

variable {F : Type*} [Ring R] [Ring S]
variable [FunLike F R S] [RingHomClass F R S] (f : F) {I : Ideal R}

section Surjective

theorem comap_map_of_surjective (hf : Function.Surjective f) (I : Ideal R) :
    comap f (map f I) = I ⊔ comap f ⊥ :=
  le_antisymm
    (fun r h =>
      let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h
      Submodule.mem_sup.2
        ⟨s, hsi, r - s, (Submodule.mem_bot S).2 <| by rw [map_sub, hfsr, sub_self],
          add_sub_cancel s r⟩)
    (sup_le (map_le_iff_le_comap.1 le_rfl) (comap_mono bot_le))

/-- Correspondence theorem -/
def relIsoOfSurjective (hf : Function.Surjective f) :
    Ideal S ≃o { p : Ideal R // comap f ⊥ ≤ p } where
  toFun J := ⟨comap f J, comap_mono bot_le⟩
  invFun I := map f I.1
  left_inv J := map_comap_of_surjective f hf J
  right_inv I :=
    Subtype.ext <|
      show comap f (map f I.1) = I.1 from
        (comap_map_of_surjective f hf I).symm ▸ le_antisymm (sup_le le_rfl I.2) le_sup_left
  map_rel_iff' {I1 I2} :=
    ⟨fun H => map_comap_of_surjective f hf I1 ▸ map_comap_of_surjective f hf I2 ▸ map_mono H,
      comap_mono⟩

-- May not hold if `R` is a semiring: consider `ℕ →+* ZMod 2`.
theorem comap_isMaximal_of_surjective (hf : Function.Surjective f) {K : Ideal S} [H : IsMaximal K] :
    IsMaximal (comap f K) := by
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

end Surjective


end Ring

section CommRing

variable {F : Type*} [CommSemiring R] [CommSemiring S]
variable [FunLike F R S] [rc : RingHomClass F R S]
variable (f : F)
variable (I J : Ideal R) (K L : Ideal S)

protected theorem map_mul {R} [Semiring R] [FunLike F R S] [RingHomClass F R S]
    (f : F) (I J : Ideal R) :
    map f (I * J) = map f I * map f J :=
  le_antisymm
    (map_le_iff_le_comap.2 <|
      mul_le.2 fun r hri s hsj =>
        show (f (r * s)) ∈ map f I * map f J by
          rw [map_mul]; exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
    (span_mul_span (↑f '' ↑I) (↑f '' ↑J) ▸ (span_le.2 <| by
      rintro _ ⟨_, ⟨r, hri, rfl⟩, _, ⟨s, hsj, rfl⟩, rfl⟩
      simp_rw [← map_mul]; exact mem_map_of_mem f (mul_mem_mul hri hsj)))

/-- The pushforward `Ideal.map` as a (semi)ring homomorphism. -/
@[simps]
def mapHom : Ideal R →+* Ideal S where
  toFun := map f
  map_mul' := Ideal.map_mul f
  map_one' := by simp only [one_eq_top, Ideal.map_top f]
  map_add' I J := Ideal.map_sup f I J
  map_zero' := Ideal.map_bot

protected theorem map_pow (n : ℕ) : map f (I ^ n) = map f I ^ n :=
  map_pow (mapHom f) I n

theorem comap_radical : comap f (radical K) = radical (comap f K) := by
  ext
  simp [radical]

variable {K}

theorem IsRadical.comap (hK : K.IsRadical) : (comap f K).IsRadical := by
  rw [← hK.radical, comap_radical]
  apply radical_isRadical

variable {I J L}

theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
  map_le_iff_le_comap.2 fun r ⟨n, hrni⟩ => ⟨n, map_pow f r n ▸ mem_map_of_mem f hrni⟩

theorem le_comap_mul : comap f K * comap f L ≤ comap f (K * L) :=
  map_le_iff_le_comap.1 <|
    (Ideal.map_mul f (comap f K) (comap f L)).symm ▸
      mul_mono (map_le_iff_le_comap.2 <| le_rfl) (map_le_iff_le_comap.2 <| le_rfl)

theorem le_comap_pow (n : ℕ) : K.comap f ^ n ≤ (K ^ n).comap f := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.one_eq_top, Ideal.one_eq_top]
    exact rfl.le
  | succ n n_ih =>
    rw [pow_succ, pow_succ]
    exact (Ideal.mul_mono_left n_ih).trans (Ideal.le_comap_mul f)

lemma disjoint_map_primeCompl_iff_comap_le {S : Type*} [Semiring S] {f : R →+* S}
    {p : Ideal R} {I : Ideal S} [p.IsPrime] :
    Disjoint (I : Set S) (p.primeCompl.map f) ↔ I.comap f ≤ p :=
  (@Set.disjoint_image_right _ _ f p.primeCompl I).trans disjoint_compl_right_iff

/-- For a prime ideal `p` of `R`, `p` extended to `S` and
restricted back to `R` is `p` if and only if `p` is the restriction of a prime in `S`. -/
lemma comap_map_eq_self_iff_of_isPrime {S : Type*} [CommSemiring S] {f : R →+* S}
    (p : Ideal R) [p.IsPrime] :
    (p.map f).comap f = p ↔ (∃ (q : Ideal S), q.IsPrime ∧ q.comap f = p) := by
  refine ⟨fun hp ↦ ?_, ?_⟩
  · obtain ⟨q, hq₁, hq₂, hq₃⟩ := Ideal.exists_le_prime_disjoint _ _
      (disjoint_map_primeCompl_iff_comap_le.mpr hp.le)
    exact ⟨q, hq₁, le_antisymm (disjoint_map_primeCompl_iff_comap_le.mp hq₃)
      (map_le_iff_le_comap.mp hq₂)⟩
  · rintro ⟨q, hq, rfl⟩
    simp

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

instance (priority := low) : (ker f).IsTwoSided := inferInstanceAs (Ideal.comap f ⊥).IsTwoSided

variable {f} in
/-- An element is in the kernel if and only if it maps to zero. -/
@[simp] theorem mem_ker {r} : r ∈ ker f ↔ f r = 0 := by rw [ker, Ideal.mem_comap, Submodule.mem_bot]

theorem ker_eq : (ker f : Set R) = Set.preimage f {0} :=
  rfl

theorem ker_eq_comap_bot (f : F) : ker f = Ideal.comap f ⊥ :=
  rfl

theorem comap_ker (f : S →+* R) (g : T →+* S) : (ker f).comap g = ker (f.comp g) := by
  rw [RingHom.ker_eq_comap_bot, Ideal.comap_comap, RingHom.ker_eq_comap_bot]

/-- If the target is not the zero ring, then one is not in the kernel. -/
theorem one_notMem_ker [Nontrivial S] (f : F) : (1 : R) ∉ ker f := by
  rw [mem_ker, map_one]
  exact one_ne_zero

@[deprecated (since := "2025-05-23")] alias not_one_mem_ker := one_notMem_ker

theorem ker_ne_top [Nontrivial S] (f : F) : ker f ≠ ⊤ :=
  (Ideal.ne_top_iff_one _).mpr <| one_notMem_ker f

lemma _root_.Pi.ker_ringHom {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]
    (φ : ∀ i, S →+* R i) : ker (Pi.ringHom φ) = ⨅ i, ker (φ i) := by
  ext x
  simp [mem_ker, funext_iff]

@[simp]
theorem ker_rangeSRestrict (f : R →+* S) : ker f.rangeSRestrict = ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

@[simp]
theorem ker_coe_equiv (f : R ≃+* S) : ker (f : R →+* S) = ⊥ := by
  ext; simp

theorem ker_coe_toRingHom : ker (f : R →+* S) = ker f := rfl

@[simp]
theorem ker_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S] (f : F') :
    ker f = ⊥ := by
  ext; simp

lemma ker_equiv_comp (f : R →+* S) (e : S ≃+* T) :
    ker (e.toRingHom.comp f) = RingHom.ker f := by
  rw [← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe, RingHom.ker_coe_equiv, RingHom.ker]

end Semiring

section Ring

variable {F : Type*} [Ring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

theorem injective_iff_ker_eq_bot : Function.Injective f ↔ ker f = ⊥ := by
  rw [SetLike.ext'_iff, ker_eq, Set.ext_iff]
  exact injective_iff_map_eq_zero' f

theorem ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 := by
  rw [← injective_iff_map_eq_zero f, injective_iff_ker_eq_bot]

lemma ker_comp_of_injective [Semiring T] (g : T →+* R) {f : R →+* S} (hf : Function.Injective f) :
    ker (f.comp g) = RingHom.ker g := by
  rw [← RingHom.comap_ker, (injective_iff_ker_eq_bot f).mp hf, RingHom.ker]

/-- Synonym for `RingHom.ker_coe_equiv`, but given an algebra equivalence. -/
@[simp] theorem _root_.AlgHom.ker_coe_equiv {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    RingHom.ker (e : A →+* B) = ⊥ :=
  RingHom.ker_coe_equiv (e.toRingEquiv)

end Ring

section RingRing

variable {F : Type*} [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S] (f : F)

theorem sub_mem_ker_iff {x y} : x - y ∈ ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]

@[simp]
theorem ker_rangeRestrict (f : R →+* S) : ker f.rangeRestrict = ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end RingRing

/-- The kernel of a homomorphism to a domain is a prime ideal. -/
theorem ker_isPrime {F : Type*} [Semiring R] [Semiring S] [IsDomain S]
    [FunLike F R S] [RingHomClass F R S] (f : F) :
    (ker f).IsPrime :=
  have := Ideal.bot_prime (α := S)
  inferInstanceAs (Ideal.comap f ⊥).IsPrime

/-- The kernel of a homomorphism to a division ring is a maximal ideal. -/
theorem ker_isMaximal_of_surjective {R K F : Type*} [Ring R] [DivisionRing K]
    [FunLike F R K] [RingHomClass F R K] (f : F)
    (hf : Function.Surjective f) : (ker f).IsMaximal :=
  have := Ideal.bot_isMaximal (K := K)
  Ideal.comap_isMaximal_of_surjective _ hf

end RingHom

section annihilator

section Semiring

variable {R M M' : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (R M) in
/-- `Module.annihilator R M` is the ideal of all elements `r : R` such that `r • M = 0`. -/
def Module.annihilator : Ideal R := RingHom.ker (Module.toAddMonoidEnd R M)

theorem Module.mem_annihilator {r} : r ∈ Module.annihilator R M ↔ ∀ m : M, r • m = 0 :=
  ⟨fun h ↦ (congr($h ·)), (AddMonoidHom.ext ·)⟩

instance (priority := low) : (Module.annihilator R M).IsTwoSided :=
  inferInstanceAs (RingHom.ker _).IsTwoSided

theorem LinearMap.annihilator_le_of_injective (f : M →ₗ[R] M') (hf : Function.Injective f) :
    Module.annihilator R M' ≤ Module.annihilator R M := fun x h ↦ by
  rw [Module.mem_annihilator] at h ⊢; exact fun m ↦ hf (by rw [map_smul, h, f.map_zero])

theorem LinearMap.annihilator_le_of_surjective (f : M →ₗ[R] M')
    (hf : Function.Surjective f) : Module.annihilator R M ≤ Module.annihilator R M' := fun x h ↦ by
  rw [Module.mem_annihilator] at h ⊢
  intro m; obtain ⟨m, rfl⟩ := hf m
  rw [← map_smul, h, f.map_zero]

theorem LinearEquiv.annihilator_eq (e : M ≃ₗ[R] M') :
    Module.annihilator R M = Module.annihilator R M' :=
  (e.annihilator_le_of_surjective e.surjective).antisymm (e.annihilator_le_of_injective e.injective)

theorem Module.comap_annihilator {R₀} [CommSemiring R₀] [Module R₀ M]
    [Algebra R₀ R] [IsScalarTower R₀ R M] :
    (Module.annihilator R M).comap (algebraMap R₀ R) = Module.annihilator R₀ M := by
  ext x
  simp [mem_annihilator]

lemma Module.annihilator_eq_bot {R M} [Ring R] [AddCommGroup M] [Module R M] :
    Module.annihilator R M = ⊥ ↔ FaithfulSMul R M := by
  rw [← le_bot_iff]
  refine ⟨fun H ↦ ⟨fun {r s} H' ↦ ?_⟩, fun ⟨H⟩ {a} ha ↦ ?_⟩
  · rw [← sub_eq_zero]
    exact H (Module.mem_annihilator (r := r - s).mpr
      (by simp only [sub_smul, H', sub_self, implies_true]))
  · exact @H a 0 (by simp [Module.mem_annihilator.mp ha])

theorem Module.annihilator_eq_top_iff : annihilator R M = ⊤ ↔ Subsingleton M :=
  ⟨fun h ↦ ⟨fun m m' ↦ by
      rw [← one_smul R m, ← one_smul R m']
      simp_rw [mem_annihilator.mp (h ▸ Submodule.mem_top)]⟩,
    fun _ ↦ top_le_iff.mp fun _ _ ↦ mem_annihilator.mpr fun _ ↦ Subsingleton.elim _ _⟩

theorem Module.annihilator_prod : annihilator R (M × M') = annihilator R M ⊓ annihilator R M' := by
  ext
  simp_rw [Ideal.mem_inf, mem_annihilator,
    Prod.forall, Prod.smul_mk, Prod.mk_eq_zero, forall_and_left, ← forall_and_right]

theorem Module.annihilator_finsupp {ι : Type*} [Nonempty ι] :
    annihilator R (ι →₀ M) = annihilator R M := by
  ext r; simp_rw [mem_annihilator]
  constructor <;> intro h
  · refine Nonempty.elim ‹_› fun i : ι ↦ ?_
    simpa using fun m ↦ congr($(h (Finsupp.single i m)) i)
  · intro m; ext i; exact h _

section

variable {ι : Type*} {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

theorem Module.annihilator_dfinsupp : annihilator R (Π₀ i, M i) = ⨅ i, annihilator R (M i) := by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using DFunLike.congr_fun (h (DFinsupp.single i m)) i
  · intro m; ext i; exact h i _

theorem Module.annihilator_pi : annihilator R (Π i, M i) = ⨅ i, annihilator R (M i) := by
  ext r; simp only [mem_annihilator, Ideal.mem_iInf]
  constructor <;> intro h
  · intro i m
    classical simpa using congr_fun (h (Pi.single i m)) i
  · intro m; ext i; exact h i _

end

namespace Submodule

/-- `N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`. -/
abbrev annihilator (N : Submodule R M) : Ideal R :=
  Module.annihilator R N

theorem annihilator_top : (⊤ : Submodule R M).annihilator = Module.annihilator R M :=
  topEquiv.annihilator_eq

variable {I J : Ideal R} {N P : Submodule R M}

theorem mem_annihilator {r} : r ∈ N.annihilator ↔ ∀ n ∈ N, r • n = (0 : M) := by
  simp_rw [annihilator, Module.mem_annihilator, Subtype.forall, Subtype.ext_iff]; rfl

theorem annihilator_bot : (⊥ : Submodule R M).annihilator = ⊤ :=
  top_le_iff.mp fun _ _ ↦ mem_annihilator.mpr fun _ ↦ by rintro rfl; rw [smul_zero]

theorem annihilator_eq_top_iff : N.annihilator = ⊤ ↔ N = ⊥ := by
  rw [annihilator, Module.annihilator_eq_top_iff, Submodule.subsingleton_iff_eq_bot]

theorem annihilator_mono (h : N ≤ P) : P.annihilator ≤ N.annihilator := fun _ hrp =>
  mem_annihilator.2 fun n hn => mem_annihilator.1 hrp n <| h hn

theorem annihilator_iSup (ι : Sort w) (f : ι → Submodule R M) :
    annihilator (⨆ i, f i) = ⨅ i, annihilator (f i) :=
  le_antisymm (le_iInf fun _ => annihilator_mono <| le_iSup _ _) fun r H =>
    mem_annihilator.2 fun n hn ↦ iSup_induction f (motive := (r • · = 0)) hn
      (fun i ↦ mem_annihilator.1 <| (mem_iInf _).mp H i) (smul_zero _)
      fun m₁ m₂ h₁ h₂ ↦ by simp_rw [smul_add, h₁, h₂, add_zero]

theorem le_annihilator_iff {N : Submodule R M} {I : Ideal R} : I ≤ annihilator N ↔ I • N = ⊥ := by
  simp_rw [← le_bot_iff, smul_le, SetLike.le_def, mem_annihilator]; rfl

@[simp]
theorem annihilator_smul (N : Submodule R M) : annihilator N • N = ⊥ :=
  eq_bot_iff.2 (smul_le.2 fun _ => mem_annihilator.1)

@[simp]
theorem annihilator_mul (I : Ideal R) : annihilator I * I = ⊥ :=
  annihilator_smul I

end Submodule

end Semiring

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {N : Submodule R M}

theorem mem_annihilator' {r} : r ∈ N.annihilator ↔ N ≤ comap (r • (LinearMap.id : M →ₗ[R] M)) ⊥ :=
  mem_annihilator.trans ⟨fun H n hn => (mem_bot R).2 <| H n hn, fun H _ hn => (mem_bot R).1 <| H hn⟩

theorem mem_annihilator_span (s : Set M) (r : R) :
    r ∈ (Submodule.span R s).annihilator ↔ ∀ n : s, r • (n : M) = 0 := by
  rw [Submodule.mem_annihilator]
  constructor
  · intro h n
    exact h _ (Submodule.subset_span n.prop)
  · intro h n hn
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hn
    · intro x hx
      exact h ⟨x, hx⟩
    · exact smul_zero _
    · intro x y _ _ hx hy
      rw [smul_add, hx, hy, zero_add]
    · intro a x _ hx
      rw [smul_comm, hx, smul_zero]

theorem mem_annihilator_span_singleton (g : M) (r : R) :
    r ∈ (Submodule.span R ({g} : Set M)).annihilator ↔ r • g = 0 := by simp [mem_annihilator_span]

open LinearMap in
theorem annihilator_span (s : Set M) :
    (Submodule.span R s).annihilator = ⨅ g : s, ker (toSpanSingleton R M g.1) := by
  ext; simp [mem_annihilator_span]

open LinearMap in
theorem annihilator_span_singleton (g : M) :
    (Submodule.span R {g}).annihilator = ker (toSpanSingleton R M g) := by
  simp [annihilator_span]

@[simp]
theorem mul_annihilator (I : Ideal R) : I * annihilator I = ⊥ := by rw [mul_comm, annihilator_mul]

end Submodule

end annihilator

namespace Ideal

variable {R : Type*} {S : Type*} {F : Type*}

section Semiring

variable [Semiring R] [Semiring S] [FunLike F R S] [rc : RingHomClass F R S]

theorem map_eq_bot_iff_le_ker {I : Ideal R} (f : F) : I.map f = ⊥ ↔ I ≤ RingHom.ker f := by
  rw [RingHom.ker, eq_bot_iff, map_le_iff_le_comap]

theorem ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f ≤ comap f K := fun _ hx =>
  mem_comap.2 (RingHom.mem_ker.1 hx ▸ K.zero_mem)

/-- A ring isomorphism sends a prime ideal to a prime ideal. -/
instance map_isPrime_of_equiv {F' : Type*} [EquivLike F' R S] [RingEquivClass F' R S]
    (f : F') {I : Ideal R} [IsPrime I] : IsPrime (map f I) := by
  have h : I.map f = I.map ((f : R ≃+* S) : R →+* S) := rfl
  rw [h, map_comap_of_equiv (f : R ≃+* S)]
  exact Ideal.IsPrime.comap (RingEquiv.symm (f : R ≃+* S))

theorem map_eq_bot_iff_of_injective {I : Ideal R} {f : F} (hf : Function.Injective f) :
    I.map f = ⊥ ↔ I = ⊥ := by
  simp [map, span_eq_bot, ← map_zero f, -map_zero, hf.eq_iff, I.eq_bot_iff]

end Semiring

section Ring

variable [Ring R] [Ring S] [FunLike F R S] [rc : RingHomClass F R S]

lemma comap_map_of_surjective' (f : F) (hf : Function.Surjective f) (I : Ideal R) :
    (I.map f).comap f = I ⊔ RingHom.ker f :=
  comap_map_of_surjective f hf I

theorem map_sInf {A : Set (Ideal R)} {f : F} (hf : Function.Surjective f) :
    (∀ J ∈ A, RingHom.ker f ≤ J) → map f (sInf A) = sInf (map f '' A) := by
  refine fun h => le_antisymm (le_sInf ?_) ?_
  · intro j hj y hy
    obtain ⟨x, hx⟩ := (mem_map_iff_of_surjective f hf).1 hy
    obtain ⟨J, hJ⟩ := (Set.mem_image _ _ _).mp hj
    rw [← hJ.right, ← hx.right]
    exact mem_map_of_mem f (sInf_le_of_le hJ.left (le_of_eq rfl) hx.left)
  · intro y hy
    obtain ⟨x, hx⟩ := hf y
    refine hx ▸ mem_map_of_mem f ?_
    have : ∀ I ∈ A, y ∈ map f I := by simpa using hy
    rw [Submodule.mem_sInf]
    intro J hJ
    rcases (mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩
    have : x - x' ∈ J := by
      apply h J hJ
      rw [RingHom.mem_ker, map_sub, hx, sub_self]
    simpa only [sub_add_cancel] using J.add_mem this hx'

theorem map_isPrime_of_surjective {f : F} (hf : Function.Surjective f) {I : Ideal R} [H : IsPrime I]
    (hk : RingHom.ker f ≤ I) : IsPrime (map f I) := by
  refine ⟨fun h => H.ne_top (eq_top_iff.2 ?_), fun {x y} => ?_⟩
  · replace h := congr_arg (comap f) h
    rw [comap_map_of_surjective _ hf, comap_top] at h
    exact h ▸ sup_le (le_of_eq rfl) hk
  · refine fun hxy => (hf x).recOn fun a ha => (hf y).recOn fun b hb => ?_
    rw [← ha, ← hb, ← map_mul f, mem_map_iff_of_surjective _ hf] at hxy
    rcases hxy with ⟨c, hc, hc'⟩
    rw [← sub_eq_zero, ← map_sub] at hc'
    have : a * b ∈ I := by
      convert I.sub_mem hc (hk (hc' : c - a * b ∈ RingHom.ker f)) using 1
      abel
    exact
      (H.mem_or_mem this).imp (fun h => ha ▸ mem_map_of_mem f h) fun h => hb ▸ mem_map_of_mem f h

lemma IsMaximal.map_of_surjective_of_ker_le {f : F} (hf : Function.Surjective f) {m : Ideal R}
    [m.IsMaximal] (hk : RingHom.ker f ≤ m) : (m.map f).IsMaximal := by
  refine m.map_eq_top_or_isMaximal_of_surjective f hf ‹_› |>.resolve_left fun h => ?_
  apply congr_arg (comap f) at h
  rw [comap_map_of_surjective _ hf, comap_top, ← RingHom.ker_eq_comap_bot, sup_of_le_left hk] at h
  exact IsMaximal.ne_top ‹_› h

end Ring

section CommRing

variable [CommRing R] [CommRing S]

theorem map_ne_bot_of_ne_bot {S : Type*} [Ring S] [Nontrivial S] [Algebra R S]
    [NoZeroSMulDivisors R S] {I : Ideal R} (h : I ≠ ⊥) : map (algebraMap R S) I ≠ ⊥ :=
  (map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)).mp.mt h

theorem map_eq_iff_sup_ker_eq_of_surjective {I J : Ideal R} (f : R →+* S)
    (hf : Function.Surjective f) : map f I = map f J ↔ I ⊔ RingHom.ker f = J ⊔ RingHom.ker f := by
  rw [← (comap_injective_of_surjective f hf).eq_iff, comap_map_of_surjective f hf,
    comap_map_of_surjective f hf, RingHom.ker_eq_comap_bot]

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
      rw [← map_one g, ← sub_eq_zero, ← map_sub g, ← mem_ker]
      apply hg
      rw [mem_ker, map_sub f, sub_eq_zero, map_one f]
      exact hf 1
    map_mul' := by
      intro x y
      rw [← map_mul g, ← sub_eq_zero, ← map_sub g, ← mem_ker]
      apply hg
      rw [mem_ker, map_sub f, sub_eq_zero, map_mul f]
      simp only [hf _] }

@[simp]
theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (a : A) :
    (f.liftOfRightInverseAux f_inv hf g hg) (f a) = g a :=
  f.toAddMonoidHom.liftOfRightInverse_comp_apply f_inv hf ⟨g.toAddMonoidHom, hg⟩ a

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
  invFun φ := ⟨φ.comp f, fun x hx => mem_ker.mpr <| by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

/-- A non-computable version of `RingHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[simp]
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) :
    { g : A →+* C // RingHom.ker f ≤ RingHom.ker g } ≃ (B →+* C) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) (x : A) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : A →+* C // RingHom.ker f ≤ RingHom.ker g }) :
    (f.liftOfRightInverse f_inv hf g).comp f = g :=
  RingHom.ext <| f.liftOfRightInverse_comp_apply f_inv hf g

theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : A →+* C)
    (hg : RingHom.ker f ≤ RingHom.ker g) (h : B →+* C) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

end RingHom

/-- Any ring isomorphism induces an order isomorphism of ideals. -/
@[simps apply]
def RingEquiv.idealComapOrderIso {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) :
    Ideal S ≃o Ideal R where
  toFun I := I.comap e
  invFun I := I.map e
  left_inv I := I.map_comap_of_surjective _ e.surjective
  right_inv I := I.comap_map_of_bijective _ e.bijective
  map_rel_iff' := by
    simp [← Ideal.map_le_iff_le_comap, Ideal.map_comap_of_surjective _ e.surjective]

@[simp]
lemma RingEquiv.idealComapOrderIso_symm_apply
    {R S : Type*} [Semiring R] [Semiring S] (e : R ≃+* S) (I : Ideal R) :
    e.idealComapOrderIso.symm I = I.map e :=
  rfl

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)

lemma ker_coe : RingHom.ker f = RingHom.ker (f : A →+* B) := rfl

lemma coe_ideal_map (I : Ideal A) :
    Ideal.map f I = Ideal.map (f : A →+* B) I := rfl

lemma comap_ker {C : Type*} [Semiring C] [Algebra R C] (f : B →ₐ[R] C) (g : A →ₐ[R] B) :
    (RingHom.ker f).comap g = RingHom.ker (f.comp g) :=
  RingHom.comap_ker f.toRingHom g.toRingHom

end AlgHom

namespace Algebra

variable {R : Type*} [CommSemiring R] (S : Type*) [Semiring S] [Algebra R S]

/-- The induced linear map from `I` to the span of `I` in an `R`-algebra `S`. -/
@[simps!]
def idealMap (I : Ideal R) : I →ₗ[R] I.map (algebraMap R S) :=
  (Algebra.linearMap R S).restrict (q := (I.map (algebraMap R S)).restrictScalars R)
    (fun _ ↦ Ideal.mem_map_of_mem _)

end Algebra

@[simp]
theorem FaithfulSMul.ker_algebraMap_eq_bot (R A : Type*) [CommSemiring R] [Semiring A]
    [Algebra R A] [FaithfulSMul R A] : RingHom.ker (algebraMap R A) = ⊥ := by
  ext; simp

section PrincipalIdeal

instance {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (I : Ideal R) [I.IsPrincipal] :
    (I.map f).IsPrincipal := by
  obtain ⟨x, rfl⟩ := Submodule.IsPrincipal.principal I
  exact ⟨f x, by
    rw [← Ideal.span, ← Set.image_singleton, Ideal.map_span, Set.image_singleton,
      Ideal.submodule_span_eq]⟩

end PrincipalIdeal
