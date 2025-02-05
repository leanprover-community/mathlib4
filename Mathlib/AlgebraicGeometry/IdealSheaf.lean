/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Topology.LocalAtTarget

/-!
# Ideal sheaves on schemes

We define ideal sheaves of schemes and provide various constructors for it.

## Main definition
* `AlgebraicGeometry.Scheme.IdealSheafData`: A structure that contains the data to uniquely define
  an ideal sheaf, consisting of
  1. an ideal `I(U) ≤ Γ(X, U)` for every affine open `U`
  2. a proof that `I(D(f)) = I(U)_f` for every affine open `U` and every section `f : Γ(X, U)`.
* `AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals`:
  The largest ideal sheaf contained in a family of ideals.
* `AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`:
  Over affine schemes, ideal sheaves are in bijection with ideals of the global sections.
* `AlgebraicGeometry.Scheme.IdealSheafData.support`:
  The support of an ideal sheaf.

## Implementation detail

Ideal sheaves are not yet defined in this file as actual subsheaves of `𝒪ₓ`.
Instead, for the ease of development and application,
we define the structure `IdealSheafData` containing all necessary data to uniquely define an
ideal sheaf. This should be refectored as a constructor for ideal sheaves once they are introduced
into mathlib.

-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/--
A structure that contains the data to uniquely define an ideal sheaf, consisting of
1. an ideal `I(U) ≤ Γ(X, U)` for every affine open `U`
2. a proof that `I(D(f)) = I(U)_f` for every affine open `U` and every section `f : Γ(X, U)`.
-/
@[ext]
structure IdealSheafData (X : Scheme.{u}) : Type u where
  /-- The component of an ideal sheaf at an affine open. -/
  ideal : ∀ U : X.affineOpens, Ideal Γ(X, U)
  /-- Also see `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` -/
  map_ideal_basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)),
    (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
      ideal (X.affineBasicOpen f)

namespace IdealSheafData

section Order

instance : PartialOrder (IdealSheafData X) := PartialOrder.lift ideal fun _ _ ↦ IdealSheafData.ext

lemma le_def {I J : IdealSheafData X} : I ≤ J ↔ ∀ U, I.ideal U ≤ J.ideal U := .rfl

instance : CompleteSemilatticeSup (IdealSheafData X) where
  sSup s := ⟨sSup (ideal '' s), by
    have : sSup (ideal '' s) = ⨆ i : s, ideal i.1 := by
      conv_lhs => rw [← Subtype.range_val (s := s), ← Set.range_comp]
      rfl
    simp only [this, iSup_apply, Ideal.map_iSup, map_ideal_basicOpen, implies_true]⟩
  le_sSup s x hxs := le_sSup (s := ideal '' s) ⟨_, hxs, rfl⟩
  sSup_le s i hi := sSup_le (s := ideal '' s) (Set.forall_mem_image.mpr hi)

/-- The largest ideal sheaf contained in a family of ideals. -/
def ofIdeals (I : ∀ U : X.affineOpens, Ideal Γ(X, U)) : IdealSheafData X :=
  sSup { J : IdealSheafData X | J.ideal ≤ I }

lemma ideal_ofIdeals_le (I : ∀ U : X.affineOpens, Ideal Γ(X, U)) :
    (ofIdeals I).ideal ≤ I :=
  sSup_le (Set.forall_mem_image.mpr fun _ ↦ id)

/-- The galois coinsertion between ideal sheaves and arbitrary families of ideals. -/
protected def gci : GaloisCoinsertion ideal (ofIdeals (X := X)) where
  choice I hI := ⟨I, fun U f ↦
    (ideal_ofIdeals_le I).antisymm hI ▸ (ofIdeals I).map_ideal_basicOpen U f⟩
  gc _ _ := ⟨(le_sSup ·), (le_trans · (ideal_ofIdeals_le _))⟩
  u_l_le _ := sSup_le fun _ ↦ id
  choice_eq I hI := IdealSheafData.ext (hI.antisymm (ideal_ofIdeals_le I))

lemma strictMono_ideal : StrictMono (ideal (X := X)) := IdealSheafData.gci.strictMono_l
lemma ideal_mono : Monotone (ideal (X := X)) := strictMono_ideal.monotone
lemma ofIdeals_mono : Monotone (ofIdeals (X := X)) := IdealSheafData.gci.gc.monotone_u
lemma ofIdeals_ideal (I : IdealSheafData X) : ofIdeals I.ideal = I := IdealSheafData.gci.u_l_eq _
lemma le_ofIdeals_iff {I : IdealSheafData X} {J} : I ≤ ofIdeals J ↔ I.ideal ≤ J :=
  IdealSheafData.gci.gc.le_iff_le.symm

instance : CompleteLattice (IdealSheafData X) where
  __ := inferInstanceAs (CompleteSemilatticeSup (IdealSheafData X))
  __ := IdealSheafData.gci.liftCompleteLattice

@[simp]
lemma ideal_top : ideal (X := X) ⊤ = ⊤ :=
  top_le_iff.mp (ideal_mono (le_top (a := ⟨⊤, by simp [Ideal.map_top]⟩)))

@[simp]
lemma ideal_bot : ideal (X := X) ⊥ = ⊥ := rfl

@[simp]
lemma ideal_sup {I J : IdealSheafData X} : (I ⊔ J).ideal = I.ideal ⊔ J.ideal := rfl

@[simp]
lemma ideal_sSup {I : Set (IdealSheafData X)} : (sSup I).ideal = sSup (ideal '' I) := rfl

@[simp]
lemma ideal_iSup {ι : Type*} {I : ι → IdealSheafData X} : (iSup I).ideal = ⨆ i, (I i).ideal := by
  show sSup _ = sSup _
  rw [← Set.range_comp]
  rfl

@[simp]
lemma ideal_inf {I J : IdealSheafData X} : (I ⊓ J).ideal = I.ideal ⊓ J.ideal := by
  let K : IdealSheafData X := ⟨I.ideal ⊓ J.ideal, by
    intro U f
    dsimp
    have : (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom = algebraMap _ _ := rfl
    have inst := U.2.isLocalization_basicOpen f
    rw [← I.map_ideal_basicOpen U f, ← J.map_ideal_basicOpen U f, this]
    ext x
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective (.powers f) x
    simp only [IsLocalization.mk'_mem_map_algebraMap_iff, Submonoid.mem_powers_iff, Ideal.mem_inf,
      exists_exists_eq_and]
    refine ⟨fun ⟨n, h₁, h₂⟩ ↦ ⟨⟨n, h₁⟩, ⟨n, h₂⟩⟩, ?_⟩
    rintro ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    refine ⟨n₁ + n₂, ?_, ?_⟩
    · rw [add_comm, pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ h₁
    · rw [pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ h₂⟩
  exact (le_inf (ideal_mono inf_le_left) (ideal_mono inf_le_right)).antisymm
    ((le_ofIdeals_iff (I := K)).mpr le_rfl)

@[simp]
lemma ideal_biInf {ι : Type*} (I : ι → IdealSheafData X) {s : Set ι} (hs : s.Finite) :
    (⨅ i ∈ s, I i).ideal = ⨅ i ∈ s, (I i).ideal := by
  refine hs.induction_on _ (by simp) fun {i s} his hs e ↦ ?_
  simp only [iInf_insert, e, ideal_inf]

@[simp]
lemma ideal_iInf {ι : Type*} (I : ι → IdealSheafData X) [Finite ι] :
    (⨅ i, I i).ideal = ⨅ i, (I i).ideal := by
  simpa using ideal_biInf I Set.finite_univ

end Order

variable (I : IdealSheafData X)

section map_ideal

/-- subsumed by `IdealSheafData.map_ideal` below. -/
private lemma map_ideal_basicOpen_of_eq
    {U V : X.affineOpens} (f : Γ(X, U)) (hV : V = X.affineBasicOpen f) :
    (I.ideal U).map (X.presheaf.map
        (homOfLE (X := X.Opens) (hV.trans_le (X.affineBasicOpen_le f))).op).hom =
      I.ideal V := by
  subst hV; exact I.map_ideal_basicOpen _ _

lemma map_ideal {U V : X.affineOpens} (h : U ≤ V) :
    (I.ideal V).map (X.presheaf.map (homOfLE h).op).hom = I.ideal U := by
  rw [U.2.ideal_ext_iff]
  intro x hxU
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, h hxU⟩
  have := I.map_ideal_basicOpen_of_eq (V := X.affineBasicOpen g) f (Subtype.ext hfg.symm)
  rw [← I.map_ideal_basicOpen] at this
  apply_fun Ideal.map (X.presheaf.germ (X.basicOpen g) x (hfg ▸ hxf)).hom at this
  simp only [Ideal.map_map, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    affineBasicOpen_coe, X.presheaf.germ_res] at this ⊢
  simp only [homOfLE_leOfHom, TopCat.Presheaf.germ_res', this]

/-- A form of `map_ideal` that is easier to rewrite with. -/
lemma map_ideal' {U V : X.affineOpens} (h : Opposite.op V.1 ⟶ .op U.1) :
    (I.ideal V).map (X.presheaf.map h).hom = I.ideal U :=
  map_ideal _ _

lemma ideal_le_comap_ideal {U V : X.affineOpens} (h : U ≤ V) :
    I.ideal V ≤ (I.ideal U).comap (X.presheaf.map (homOfLE h).op).hom := by
  rw [← Ideal.map_le_iff_le_comap, ← I.map_ideal h]

end map_ideal

section IsAffine

/-- The ideal sheaf induced by an ideal of the global sections. -/
@[simps]
def ofIdealTop (I : Ideal Γ(X, ⊤)) : IdealSheafData X where
  ideal U := I.map (X.presheaf.map (homOfLE le_top).op).hom
  map_ideal_basicOpen U f := by rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl

lemma le_of_isAffine [IsAffine X] {I J : IdealSheafData X}
    (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ ≤ J.ideal ⟨⊤, isAffineOpen_top X⟩) : I ≤ J := by
  intro U
  rw [← map_ideal (U := U) (V := ⟨⊤, isAffineOpen_top X⟩) I (le_top (a := U.1)),
    ← map_ideal (U := U) (V := ⟨⊤, isAffineOpen_top X⟩) J (le_top (a := U.1))]
  exact Ideal.map_mono H

lemma ext_of_isAffine [IsAffine X] {I J : IdealSheafData X}
    (H : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J :=
  (le_of_isAffine H.le).antisymm (le_of_isAffine H.ge)

/-- Over affine schemes, ideal sheaves are in bijection with ideals of the global sections. -/
@[simps]
def equivOfIsAffine [IsAffine X] : IdealSheafData X ≃ Ideal Γ(X, ⊤) where
  toFun := (ideal · ⟨⊤, isAffineOpen_top X⟩)
  invFun := ofIdealTop
  left_inv I := ext_of_isAffine (by simp)
  right_inv I := by simp

end IsAffine

section support

/-- The support of an ideal sheaf. Also see `IdealSheafData.mem_support_iff_of_mem`. -/
def support (I : IdealSheafData X) : Set X := ⋂ U, X.zeroLocus (U := U.1) (I.ideal U)

lemma mem_support_iff {I : IdealSheafData X} {x} :
    x ∈ I.support ↔ ∀ U, x ∈ X.zeroLocus (U := U.1) (I.ideal U) := Set.mem_iInter

lemma support_subset_zeroLocus (I : IdealSheafData X) (U : X.affineOpens) :
    I.support ⊆ X.zeroLocus (U := U.1) (I.ideal U) := Set.iInter_subset _ _

lemma zeroLocus_inter_subset_support (I : IdealSheafData X) (U : X.affineOpens) :
    X.zeroLocus (U := U.1) (I.ideal U) ∩ U ⊆ I.support := by
  refine Set.subset_iInter fun V ↦ ?_
  apply (X.codisjoint_zeroLocus (U := V) (I.ideal V)).symm.left_le_of_le_inf_right
  rintro x ⟨⟨hx, hxU⟩, hxV⟩
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe] at hx ⊢
  intro s hfU hxs
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  have inst := U.2.isLocalization_basicOpen f
  have := (I.map_ideal (U := X.affineBasicOpen f) (hfg.trans_le (X.basicOpen_le g))).le
    (Ideal.mem_map_of_mem _ hfU)
  rw [← I.map_ideal_basicOpen] at this
  obtain ⟨⟨s', ⟨_, n, rfl⟩⟩, hs'⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (.powers f) Γ(X, X.basicOpen f)).mp this
  apply_fun (x ∈ X.basicOpen ·) at hs'
  refine hx s' s'.2 ?_
  cases n <;>
    simpa [RingHom.algebraMap_toAlgebra, ← hfg, hxf, hxs, Scheme.basicOpen_pow] using hs'

lemma mem_support_iff_of_mem {I : IdealSheafData X} {x} {U : X.affineOpens} (hxU : x ∈ U.1) :
    x ∈ I.support ↔ x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  ⟨fun h ↦ Set.iInter_subset _ U h, fun h ↦ I.zeroLocus_inter_subset_support U ⟨h, hxU⟩⟩

lemma support_inter (I : IdealSheafData X) (U : X.affineOpens) :
    I.support ∩ U = X.zeroLocus (U := U.1) (I.ideal U) ∩ U := by
  ext x
  by_cases hxU : x ∈ U.1
  · simp [hxU, mem_support_iff_of_mem hxU]
  · simp [hxU]

lemma isClosed_support (I : IdealSheafData X) : IsClosed I.support := by
  rw [isClosed_iff_coe_preimage_of_iSup_eq_top (iSup_affineOpens_eq_top X)]
  intro U
  refine ⟨(X.zeroLocus (U := U.1) (I.ideal U))ᶜ, (X.zeroLocus_isClosed _).isOpen_compl, ?_⟩
  simp only [Set.preimage_compl, compl_inj_iff]
  apply Subtype.val_injective.image_injective
  simp [Set.image_preimage_eq_inter_range, I.support_inter]

@[simp]
lemma support_top : support (X := X) ⊤ = ∅ := by
  ext x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  simpa [support] using ⟨U, hU, hxU⟩

@[simp]
lemma support_bot : support (X := X) ⊥ = Set.univ := by ext; simp [support]

lemma support_antitone : Antitone (support (X := X)) :=
  fun _ _ h ↦ Set.iInter_mono fun U ↦ X.zeroLocus_mono (h U)

lemma support_ofIdealTop (I : Ideal Γ(X, ⊤)) : (ofIdealTop I).support = X.zeroLocus (U := ⊤) I := by
  suffices ∀ U : X.affineOpens, (ofIdealTop I).support ∩ U = X.zeroLocus (U := ⊤) I ∩ U by
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    simpa [hxU] using congr(x ∈ $(this ⟨U, hU⟩))
  intro U
  rw [support_inter, ofIdealTop_ideal, Ideal.map, zeroLocus_span, zeroLocus_map,
    Set.union_inter_distrib_right, Set.compl_inter_self, Set.union_empty]

@[simp]
lemma support_eq_empty_iff : support I = ∅ ↔ I = ⊤ := by
  refine ⟨fun H ↦ top_le_iff.mp fun U ↦ ?_, by simp +contextual⟩
  have := (U.2.fromSpec_image_zeroLocus _).trans_subset
    ((zeroLocus_inter_subset_support I U).trans_eq H)
  simp only [Set.subset_empty_iff, Set.image_eq_empty] at this
  simp [PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp this]

end support

end AlgebraicGeometry.Scheme.IdealSheafData
