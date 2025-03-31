/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

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
* `AlgebraicGeometry.Scheme.IdealSheafData.support`: The support of an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`: The vanishing ideal of a set.
* `AlgebraicGeometry.Scheme.Hom.ker`: The kernel of a morphism.
* `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`: The subscheme associated to an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`: The inclusion from the subscheme.

## Main results
* `AlgebraicGeometry.Scheme.IdealSheafData.gc`:
  `support` and `vanishingIdeal` forms a galois connection.
* `AlgebraicGeometry.Scheme.Hom.support_ker`: The support of a kernel of a quasi-compact morphism
  is the closure of the range.

## Implementation detail

Ideal sheaves are not yet defined in this file as actual subsheaves of `𝒪ₓ`.
Instead, for the ease of development and application,
we define the structure `IdealSheafData` containing all necessary data to uniquely define an
ideal sheaf. This should be refactored as a constructor for ideal sheaves once they are introduced
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
  rw [← sSup_range, ← sSup_range, ideal_sSup, ← Set.range_comp, Function.comp_def]

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
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top X)]
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

section ofIsClosed

open _root_.PrimeSpectrum TopologicalSpace

/-- The radical of a ideal sheaf. -/
@[simps]
def radical (I : IdealSheafData X) : IdealSheafData X where
  ideal U := (I.ideal U).radical
  map_ideal_basicOpen U f :=
    letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_of_eq_basicOpen _ _ rfl
    (IsLocalization.map_radical (.powers f) Γ(X, X.basicOpen f) (I.ideal U)).trans
      congr($(I.map_ideal_basicOpen U f).radical)

/-- The nilradical of a scheme. -/
def _root_.AlgebraicGeometry.Scheme.nilradical (X : Scheme.{u}) : IdealSheafData X :=
  .radical ⊥

lemma le_radical : I ≤ I.radical := fun _ ↦ Ideal.le_radical

@[simp]
lemma radical_top : radical (X := X) ⊤ = ⊤ := top_le_iff.mp (le_radical _)

lemma radical_bot : radical ⊥ = nilradical X := rfl

lemma radical_sup {I J : IdealSheafData X} :
    radical (I ⊔ J) = radical (radical I ⊔ radical J) := by
  ext U : 2
  exact (Ideal.radical_sup (I.ideal U) (J.ideal U))

@[simp]
lemma radical_inf {I J : IdealSheafData X} :
    radical (I ⊓ J) = (radical I ⊓ radical J) := by
  ext U : 2
  simp only [radical_ideal, ideal_inf, Pi.inf_apply, Ideal.radical_inf]

/-- The vanishing ideal sheaf of a set,
which is the largest ideal sheaf whose support contains a subset.
When the set `Z` is closed, the reduced induced scheme structure is the quotient of this ideal. -/
@[simps]
nonrec def vanishingIdeal (Z : Set X) : IdealSheafData X where
  ideal U := vanishingIdeal (U.2.fromSpec.base ⁻¹' Z)
  map_ideal_basicOpen U f := by
    let F := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      suffices ∀ p, (X.affineBasicOpen f).2.fromSpec.base p ∈ Z → F.hom x ∈ p.asIdeal by
        simpa [PrimeSpectrum.mem_vanishingIdeal] using this
      intro x hxZ
      refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp hx
        ((Spec.map (X.presheaf.map (homOfLE _).op)).base x) ?_
      rwa [Set.mem_preimage, ← Scheme.comp_base_apply,
        IsAffineOpen.map_fromSpec _ (X.affineBasicOpen f).2]
    · letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) := F.hom.toAlgebra
      have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
        U.2.isLocalization_of_eq_basicOpen _ _ rfl
      intro x hx
      dsimp only at hx ⊢
      have : Topology.IsOpenEmbedding (Spec.map F).base :=
        localization_away_isOpenEmbedding Γ(X, X.basicOpen f) f
      rw [← U.2.map_fromSpec (X.affineBasicOpen f).2 (homOfLE (X.basicOpen_le f)).op,
        Scheme.comp_base, TopCat.coe_comp, Set.preimage_comp] at hx
      generalize U.2.fromSpec.base ⁻¹' Z = Z' at hx ⊢
      replace hx : x ∈ vanishingIdeal ((Spec.map F).base ⁻¹' Z') := hx
      obtain ⟨I, hI, e⟩ := (isClosed_iff_zeroLocus_radical_ideal _).mp (isClosed_closure (s := Z'))
      rw [← vanishingIdeal_closure,
        ← this.isOpenMap.preimage_closure_eq_closure_preimage this.continuous, e] at hx
      rw [← vanishingIdeal_closure, e]
      erw [preimage_comap_zeroLocus] at hx
      rwa [← PrimeSpectrum.zeroLocus_span, ← Ideal.map, vanishingIdeal_zeroLocus_eq_radical,
        ← RingHom.algebraMap_toAlgebra (X.presheaf.map _).hom,
        ← IsLocalization.map_radical (.powers f), ← vanishingIdeal_zeroLocus_eq_radical] at hx

lemma subset_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Set X} :
    Z ⊆ I.support ↔ I ≤ vanishingIdeal Z := by
  simp only [le_def, vanishingIdeal_ideal, ← PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal]
  trans ∀ U : X.affineOpens, Z ∩ U ⊆ I.support ∩ U
  · refine ⟨fun H U x hx ↦ ⟨H hx.1, hx.2⟩, fun H x hx ↦ ?_⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (H ⟨U, hU⟩ ⟨hx, hxU⟩).1
  refine forall_congr' fun U ↦ ?_
  rw [support_inter, ← Set.image_subset_image_iff U.2.fromSpec.isOpenEmbedding.injective,
    Set.image_preimage_eq_inter_range, IsAffineOpen.fromSpec_image_zeroLocus,
    IsAffineOpen.range_fromSpec]

/-- `support` and `vanishingIdeal` forms a galois connection.
This is the global version of `PrimeSpectrum.gc`. -/
lemma gc : @GaloisConnection X.IdealSheafData (Set X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·) :=
  fun _ _ ↦ subset_support_iff_le_vanishingIdeal

lemma vanishingIdeal_antimono {S T : Set X} (h : S ⊆ T) : vanishingIdeal T ≤ vanishingIdeal S :=
  gc.monotone_u h

lemma support_vanishingIdeal {Z : Set X} :
    (vanishingIdeal Z).support = closure Z := by
  ext x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  trans x ∈ (vanishingIdeal Z).support ∩ U
  · simp [hxU]
  rw [(vanishingIdeal Z).support_inter ⟨U, hU⟩, ← hU.fromSpec_image_zeroLocus,
    vanishingIdeal, zeroLocus_vanishingIdeal_eq_closure,
      ← hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
        hU.fromSpec.base.1.2,
      Set.image_preimage_eq_inter_range]
  simp [hxU]

lemma vanishingIdeal_support {I : IdealSheafData X} :
    vanishingIdeal I.support = I.radical := by
  ext U : 2
  dsimp
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  congr 1
  apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
  rw [Set.image_preimage_eq_inter_range, IsAffineOpen.range_fromSpec,
    IsAffineOpen.fromSpec_image_zeroLocus, support_inter]

end ofIsClosed

end IdealSheafData

section ker

open IdealSheafData

variable {Y Z : Scheme.{u}}

/-- The kernel of a morphism,
defined as the largest (quasi-coherent) ideal sheaf contained in the component-wise kernel.
This is usually only well-behaved when `f` is quasi-compact. -/
def Hom.ker (f : X.Hom Y) : IdealSheafData Y :=
  ofIdeals fun U ↦ RingHom.ker (f.app U).hom

@[simp]
lemma Hom.ker_apply (f : X.Hom Y) [QuasiCompact f] (U : Y.affineOpens) :
    f.ker.ideal U = RingHom.ker (f.app U).hom := by
  let I : IdealSheafData Y := ⟨fun U ↦ RingHom.ker (f.app U).hom, ?_⟩
  · exact congr($(ofIdeals_ideal I).ideal U)
  intro U s
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
    simp_rw [RingHom.comap_ker, ← CommRingCat.hom_comp, Scheme.affineBasicOpen_coe, f.naturality,
      CommRingCat.hom_comp, ← RingHom.comap_ker]
    exact Ideal.ker_le_comap _ hx
  · intro x hx
    have := U.2.isLocalization_basicOpen s
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (.powers s) x
    refine (IsLocalization.mk'_mem_map_algebraMap_iff _ _ _ _ _).mpr ?_
    suffices ∃ (V : X.Opens) (hV : V = X.basicOpen ((f.app U).hom s)),
        letI := hV.trans_le (X.basicOpen_le _); ((f.app U).hom x |_ V) = 0 by
      obtain ⟨_, rfl, H⟩ := this
      obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        X (U := f ⁻¹ᵁ U) (QuasiCompact.isCompact_preimage (f := f) _ U.1.2 U.2.isCompact)
        (f.app U x) (f.app U s) H
      exact ⟨_, ⟨n, rfl⟩, by simpa using hn⟩
    refine ⟨f ⁻¹ᵁ Y.basicOpen s, by simp, ?_⟩
    replace hx : (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op ≫ f.app _).hom x = 0 := by
      trans (f.app (Y.basicOpen s)).hom (algebraMap Γ(Y, U) _ x)
      · simp [-NatTrans.naturality, RingHom.algebraMap_toAlgebra]
      · simp only [Scheme.affineBasicOpen_coe, RingHom.mem_ker] at hx
        rw [← IsLocalization.mk'_spec' (M := .powers s), map_mul, hx, mul_zero]
    rwa [f.naturality] at hx

lemma Hom.le_ker_comp (f : X ⟶ Y) (g : Y.Hom Z) : g.ker ≤ (f ≫ g).ker := by
  refine ofIdeals_mono fun U ↦ ?_
  rw [Scheme.comp_app f g U, CommRingCat.hom_comp, ← RingHom.comap_ker]
  exact Ideal.ker_le_comap _

lemma ker_eq_top_of_isEmpty (f : X.Hom Y) [IsEmpty X] : f.ker = ⊤ :=
  top_le_iff.mp (le_ofIdeals_iff.mpr fun U x _ ↦ by simpa using Subsingleton.elim _ _)

lemma ker_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    f.ker = ofIdealTop (RingHom.ker f.appTop.hom) := by
  refine (le_of_isAffine ((ideal_ofIdeals_le _ _).trans (by simp))).antisymm
    (le_ofIdeals_iff.mpr fun U ↦ ?_)
  simp only [ofIdealTop_ideal, homOfLE_leOfHom, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
    ← CommRingCat.hom_comp, f.naturality]
  intro x
  simp +contextual

lemma Hom.range_subset_ker_support (f : X.Hom Y) :
    Set.range f.base ⊆ f.ker.support := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    (isBasis_affine_open Y).exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  refine ((support_inter f.ker ⟨U, hU⟩).ge ⟨?_, hxU⟩).1
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  intro s hs hxs
  have : x ∈ f ⁻¹ᵁ Y.basicOpen s := hxs
  rwa [Scheme.preimage_basicOpen, RingHom.mem_ker.mp (ideal_ofIdeals_le _ _ hs),
    Scheme.basicOpen_zero] at this

lemma Hom.iInf_ker_openCover_map_comp_apply
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) (U : Y.affineOpens) :
    ⨅ i, (𝒰.map i ≫ f).ker.ideal U = f.ker.ideal U := by
  refine le_antisymm ?_ (le_iInf fun i ↦ f.le_ker_comp (𝒰.map i) U)
  intro s hs
  simp only [Hom.ker_apply, RingHom.mem_ker]
  apply X.IsSheaf.section_ext
  rintro x hxU
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
  simp only [homOfLE_leOfHom, CommRingCat.forget_map, map_zero, exists_and_left]
  refine ⟨𝒰.map i ''ᵁ 𝒰.map i ⁻¹ᵁ f ⁻¹ᵁ U.1, ⟨_, hxU, rfl⟩,
    Set.image_preimage_subset (𝒰.map i).base (f ⁻¹ᵁ U), ?_⟩
  apply ((𝒰.map i).appIso _).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_toRingHom,
    Scheme.Hom.appIso_hom']
  simp only [homOfLE_leOfHom, Scheme.Hom.app_eq_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.appLE_comp_appLE]
  simpa [Scheme.Hom.appLE] using ideal_ofIdeals_le _ _ (Ideal.mem_iInf.mp hs i)

lemma Hom.iInf_ker_openCover_map_comp (f : X ⟶ Y) [QuasiCompact f] (𝒰 : X.OpenCover) :
    ⨅ i, (𝒰.map i ≫ f).ker = f.ker := by
  refine le_antisymm ?_ (le_iInf fun i ↦ f.le_ker_comp (𝒰.map i))
  refine iInf_le_iff.mpr fun I hI U ↦ ?_
  rw [← f.iInf_ker_openCover_map_comp_apply 𝒰, le_iInf_iff]
  exact fun i ↦ hI i U

lemma Hom.iUnion_support_ker_openCover_map_comp
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) [Finite 𝒰.J] :
    ⋃ i, (𝒰.map i ≫ f).ker.support = f.ker.support := by
  cases isEmpty_or_nonempty 𝒰.J
  · have : IsEmpty X := Function.isEmpty 𝒰.f
    simp [ker_eq_top_of_isEmpty]
  suffices ∀ U : Y.affineOpens, (⋃ i, (𝒰.map i ≫ f).ker.support) ∩ U = f.ker.support ∩ U by
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      (isBasis_affine_open Y).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    simpa [hxU] using congr(x ∈ $(this ⟨U, hU⟩))
  intro U
  simp only [Set.iUnion_inter, support_inter, ← f.iInf_ker_openCover_map_comp_apply 𝒰,
    Scheme.zeroLocus_iInf_of_nonempty]

lemma ker_morphismRestrict_ideal (f : X.Hom Y) [QuasiCompact f]
    (U : Y.Opens) (V : U.toScheme.affineOpens) :
    (f ∣_ U).ker.ideal V = f.ker.ideal ⟨U.ι ''ᵁ V, V.2.image_of_isOpenImmersion _⟩ := by
  have inst : QuasiCompact (f ∣_ U) := MorphismProperty.of_isPullback
      (isPullback_morphismRestrict _ _).flip inferInstance
  ext x
  simpa [Scheme.Hom.appLE] using map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).1

lemma ker_ideal_of_isPullback_of_isOpenImmersion {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) [IsOpenImmersion iV]
    [QuasiCompact f] (H : IsPullback f' iU iV f) (W) :
    f'.ker.ideal W =
      (f.ker.ideal ⟨iV ''ᵁ W, W.2.image_of_isOpenImmersion _⟩).comap (iV.appIso W).inv.hom := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback H.flip inferInstance
  have : IsOpenImmersion iU := MorphismProperty.of_isPullback H inferInstance
  ext x
  have : iU ''ᵁ f' ⁻¹ᵁ W = f ⁻¹ᵁ iV ''ᵁ W :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W
  let e : Γ(X, f ⁻¹ᵁ iV ''ᵁ W) ≅ Γ(U, f' ⁻¹ᵁ W) :=
    X.presheaf.mapIso (eqToIso this).op ≪≫ iU.appIso _
  have : (iV.appIso W).inv ≫ f.app _ = f'.app W ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    simp only [Scheme.Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
      eqToHom_op, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, e, Scheme.appLE_comp_appLE, H.w]
  simp only [Scheme.Hom.ker_apply, RingHom.mem_ker, Ideal.mem_comap, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appIso_inv_app, this]
  simpa using (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso e.inv).1).symm

lemma Hom.support_ker (f : X.Hom Y) [QuasiCompact f] :
    f.ker.support = closure (Set.range f.base) := by
  apply subset_antisymm
  · wlog hY : ∃ S, Y = Spec S
    · intro x hx
      let 𝒰 := Y.affineCover
      obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
      have inst : QuasiCompact (𝒰.pullbackHom f i) :=
        MorphismProperty.pullback_snd _ _ inferInstance
      have := this (𝒰.pullbackHom f i) ⟨_, rfl⟩
        ((support_inter _ ⟨⊤, isAffineOpen_top _⟩).ge ⟨?_, Set.mem_univ x⟩).1
      · have := image_closure_subset_closure_image (f := (𝒰.map i).base)
          (𝒰.map i).base.1.2 (Set.mem_image_of_mem _ this)
        rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_base, 𝒰.pullbackHom_map] at this
        exact closure_mono (Set.range_comp_subset_range _ _) this
      · rw [← (𝒰.map i).isOpenEmbedding.injective.mem_set_image, Scheme.image_zeroLocus,
          ker_ideal_of_isPullback_of_isOpenImmersion f (𝒰.pullbackHom f i)
            ((𝒰.pullbackCover f).map i) (𝒰.map i) (IsPullback.of_hasPullback _ _).flip,
          Ideal.coe_comap, Set.image_preimage_eq]
        · exact ⟨((support_inter _ _).le ⟨hx, by simp⟩).1, ⟨_, rfl⟩⟩
        · exact (ConcreteCategory.bijective_of_isIso ((𝒰.map i).appIso ⊤).inv).2
    obtain ⟨S, rfl⟩ := hY
    wlog hX : ∃ R, X = Spec R generalizing X S
    · intro x hx
      have inst : CompactSpace X := HasAffineProperty.iff_of_isAffine.mp ‹QuasiCompact f›
      let 𝒰 := X.affineCover.finiteSubcover
      obtain ⟨_, ⟨i, rfl⟩, hx⟩ := (f.iUnion_support_ker_openCover_map_comp 𝒰).ge hx
      have inst : QuasiCompact (𝒰.map i ≫ f) := HasAffineProperty.iff_of_isAffine.mpr
        (by show CompactSpace (Spec _); infer_instance)
      exact closure_mono (Set.range_comp_subset_range _ _) (this S (𝒰.map i ≫ f) ⟨_, rfl⟩ hx)
    obtain ⟨R, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    rw [ker_of_isAffine, support_ofIdealTop, Spec_zeroLocus, ← Ideal.coe_comap,
      RingHom.comap_ker, ← PrimeSpectrum.closure_range_comap, ← CommRingCat.hom_comp,
      ← Scheme.ΓSpecIso_inv_naturality]
    simp only [CommRingCat.hom_comp, PrimeSpectrum.comap_comp, ContinuousMap.coe_comp]
    exact closure_mono (Set.range_comp_subset_range _ (Spec.map φ).base)
  · rw [(isClosed_support _).closure_subset_iff]
    exact f.range_subset_ker_support

/-- The functor taking a morphism into `Y` to its kernel as an ideal sheaf on `Y`. -/
@[simps]
def kerFunctor (Y : Scheme.{u}) : (Over Y)ᵒᵖ ⥤ IdealSheafData Y where
  obj f := f.unop.hom.ker
  map {f g} hfg := homOfLE <| by
      simp only [Functor.id_obj, Functor.const_obj_obj, OrderDual.toDual_le_toDual]
      rw [← Over.w hfg.unop]
      exact f.unop.hom.le_ker_comp _
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end ker

section subscheme
namespace IdealSheafData

open _root_.PrimeSpectrum Limits

variable (I : IdealSheafData X)

/-- `Spec (𝒪ₓ(U)/I(U))`, the object to be glued into the closed subscheme. -/
def glueDataObj (U : X.affineOpens) : Scheme :=
  Spec (.of (Γ(X, U) ⧸ I.ideal U))

/-- `Spec (𝒪ₓ(U)/I(U)) ⟶ Spec (𝒪ₓ(U)) = U`, the closed immersion into `U`. -/
noncomputable
def glueDataObjι (U : X.affineOpens) : I.glueDataObj U ⟶ U.1 :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.isoSpec.inv

instance (U : X.affineOpens) : IsPreimmersion (I.glueDataObjι U) :=
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))) :=
    .mk_Spec_map
      (isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isEmbedding
      (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
  .comp _ _

lemma glueDataObjι_ι (U : X.affineOpens) : I.glueDataObjι U ≫ U.1.ι =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.fromSpec := by
  rw [glueDataObjι, Category.assoc]; rfl

lemma ker_glueDataObjι_appTop (U : X.affineOpens) :
    RingHom.ker (I.glueDataObjι U).appTop.hom = (I.ideal U).comap U.1.topIso.hom.hom := by
  let φ := CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  rw [← Ideal.mk_ker (I := I.ideal _)]
  show RingHom.ker (Spec.map φ ≫ _).appTop.hom = (RingHom.ker φ.hom).comap _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv, RingHom.comap_ker,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp]
  congr 2
  simp only [Scheme.comp_app, TopologicalSpace.Opens.map_top, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.Opens.topIso_hom]
  rw [← Scheme.Hom.appTop, U.2.isoSpec_inv_appTop, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Scheme.Opens.topIso_hom]

open scoped Set.Notation in
lemma range_glueDataObjι (U : X.affineOpens) :
    Set.range (I.glueDataObjι U).base =
      U.2.isoSpec.inv.base '' PrimeSpectrum.zeroLocus (I.ideal U) := by
  simp only [glueDataObjι, Scheme.comp_coeBase, TopCat.coe_comp, Set.range_comp,
    SetLike.coe_sort_coe]
  erw [range_comap_of_surjective]
  swap; · exact Ideal.Quotient.mk_surjective
  simp only [Ideal.mk_ker, CommRingCat.hom_ofHom]

lemma range_glueDataObjι_ι (U : X.affineOpens) :
    Set.range ⇑(I.glueDataObjι U ≫ U.1.ι).base = X.zeroLocus (U := U) (I.ideal U) ∩ U := by
  simp only [Scheme.comp_coeBase, TopCat.coe_comp, Set.range_comp, range_glueDataObjι]
  rw [← Set.image_comp, ← TopCat.coe_comp, ← Scheme.comp_base, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.fromSpec_image_zeroLocus]

/-- The underlying space of `Spec (𝒪ₓ(U)/I(U))` is homeomorphic to its image in `X`. -/
noncomputable
def glueDataObjEquiv (U : X.affineOpens) :
    (I.glueDataObj U).carrier ≅ TopCat.of ↑(X.zeroLocus (U := U) (I.ideal U) ∩ U) :=
  TopCat.isoOfHomeo ((Homeomorph.ofIsEmbedding _ (I.glueDataObjι U ≫ U.1.ι).isEmbedding).trans
    (Homeomorph.setCongr (I.range_glueDataObjι_ι U)))

/-- The open immersion `Spec Γ(𝒪ₓ/I, U) ⟶ Spec Γ(𝒪ₓ/I, V)` if `U ≤ V`. -/
noncomputable
def glueDataObjMap {U V : X.affineOpens} (h : U ≤ V) : I.glueDataObj U ⟶ I.glueDataObj V :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)))

lemma isLocalization_away {U V : X.affineOpens}
    (h : U ≤ V) (f : Γ(X, V.1)) (hU : U = X.affineBasicOpen f) :
      letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (I.ideal V) f) (Γ(X, U) ⧸ (I.ideal U)) := by
  letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
  let f' : Γ(X, V) ⧸ I.ideal V := Ideal.Quotient.mk _ f
  letI := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, U) := by
    subst hU; exact V.2.isLocalization_of_eq_basicOpen _ _ rfl
  simp only [IsLocalization.Away, f', ← Submonoid.map_powers]
  refine IsLocalization.of_surjective _ _ _ Ideal.Quotient.mk_surjective _
    Ideal.Quotient.mk_surjective ?_ ?_
  · simp [RingHom.algebraMap_toAlgebra, Ideal.quotientMap_comp_mk]; rfl
  · subst hU
    simp only [Ideal.mk_ker, RingHom.algebraMap_toAlgebra, I.map_ideal', le_refl]

instance isOpenImmersion_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) :
    IsOpenImmersion (I.glueDataObjMap (X.affineBasicOpen_le f)) := by
  letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk _ f)

lemma opensRange_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) :
      (I.glueDataObjMap (X.affineBasicOpen_le f)).opensRange =
        (I.glueDataObjι V) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ X.basicOpen f) := by
  letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  let f' : Γ(X, V) ⧸ I.ideal V := Ideal.Quotient.mk _ f
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  ext1
  refine (localization_away_comap_range _ f').trans ?_
  rw [← comap_basicOpen, ← V.2.fromSpec_preimage_basicOpen, ← Scheme.preimage_comp, glueDataObjι_ι]
  rfl

@[reassoc (attr := simp)]
lemma glueDataObjMap_glueDataObjι {U V : X.affineOpens} (h : U ≤ V) :
    I.glueDataObjMap h ≫ I.glueDataObjι V = I.glueDataObjι U ≫ X.homOfLE h := by
  rw [glueDataObjMap, glueDataObjι, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    Ideal.quotientMap_comp_mk, CommRingCat.ofHom_comp, Spec.map_comp_assoc, glueDataObjι,
    Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, IsAffineOpen.isoSpec_hom, CommRingCat.ofHom_hom]
  erw [Scheme.Opens.toSpecΓ_SpecMap_map_assoc U.1 V.1 h]
  rw [← IsAffineOpen.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]

lemma ideal_le_ker_glueDataObjι (U V : X.affineOpens) :
    I.ideal V ≤ RingHom.ker (U.1.ι.app V.1 ≫ (I.glueDataObjι U).app _).hom := by
  intro x hx
  apply (I.glueDataObj U).IsSheaf.section_ext
  intro p hp
  obtain ⟨f, g, hfg, hf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 ((I.glueDataObjι U).base p).1
      ⟨((I.glueDataObjι U).base p).2, hp⟩
  refine ⟨(I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f),
    fun x hx ↦ X.basicOpen_le g (hfg ▸ hx), hf, ?_⟩
  have := Hom.isIso_app (I.glueDataObjMap (X.affineBasicOpen_le f))
    (I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f) (by rw [opensRange_glueDataObjMap])
  apply ((ConcreteCategory.isIso_iff_bijective _).mp this).1
  simp only [CommRingCat.forget_map, map_zero, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Category.assoc]
  simp only [Scheme.Hom.app_eq_appLE, homOfLE_leOfHom, Scheme.Hom.map_appLE,
    Scheme.appLE_comp_appLE, Category.assoc, glueDataObjMap_glueDataObjι_assoc]
  rw [Scheme.Hom.appLE]
  have H : (X.homOfLE (X.basicOpen_le f) ≫ U.1.ι) ⁻¹ᵁ V.1 = ⊤ := by
    simp only [Scheme.homOfLE_ι, ← top_le_iff]
    exact fun x _ ↦ (hfg.trans_le (X.basicOpen_le g)) x.2
  simp only [Scheme.comp_app, Scheme.Opens.ι_app, Scheme.homOfLE_app, ← Functor.map_comp,
    Scheme.app_eq _ H, Scheme.Opens.toScheme_presheaf_map, ← Functor.map_comp_assoc, Category.assoc]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  convert RingHom.map_zero _ using 2
  rw [← RingHom.mem_ker, ker_glueDataObjι_appTop, ← Ideal.mem_comap, Ideal.comap_comap,
    ← CommRingCat.hom_comp]
  simp only [Scheme.affineBasicOpen_coe, homOfLE_leOfHom, Scheme.comp_coeBase,
    TopologicalSpace.Opens.map_comp_obj, eqToHom_op, eqToHom_unop, ← Functor.map_comp,
    Scheme.Opens.topIso_hom, Category.assoc, ← CommRingCat.hom_comp]
  exact I.ideal_le_comap_ideal (U := X.affineBasicOpen f) (V := V)
    (hfg.trans_le (X.basicOpen_le g)) hx

/-- (Implementation) The intersections `Spec Γ(𝒪ₓ/I, U) ∩ V` useful for gluing. -/
private noncomputable
abbrev glueDataObjPullback (U V : X.affineOpens) : Scheme :=
  pullback (I.glueDataObjι U) (X.homOfLE (U := U.1 ⊓ V.1) inf_le_left)

/-- (Implementation) Transition maps in the glue data for `𝒪ₓ/I`. -/
private noncomputable
def glueDataT (U V : X.affineOpens) :
    I.glueDataObjPullback U V ⟶ I.glueDataObjPullback V U := by
  letI F := pullback.snd (I.glueDataObjι U) (X.homOfLE (inf_le_left (b := V.1)))
  refine pullback.lift ((F ≫ X.homOfLE inf_le_right ≫
    V.2.isoSpec.hom).liftQuotient _ ?_) (F ≫ X.homOfLE (by simp)) ?_
  · intro x hx
    simp only [comp_app, comp_coeBase, TopologicalSpace.Opens.map_comp_obj,
      TopologicalSpace.Opens.map_top, homOfLE_app, homOfLE_leOfHom, Category.assoc,
      ← CommRingCat.hom_comp, RingHom.mem_ker, ← RingHom.comp_apply, Function.comp_apply]
    convert_to (U.1.ι.app V.1 ≫ (F ≫ X.homOfLE inf_le_left).appLE (U.1.ι ⁻¹ᵁ V.1) ⊤
      (by rw [← Scheme.preimage_comp, Category.assoc, X.homOfLE_ι]
          exact fun x _ ↦ by simpa using (F.base x).2.2)).hom x = 0 using 3
    · simp only [homOfLE_leOfHom, Opens.ι_app, comp_appLE, homOfLE_app]
      have H : ⊤ ≤ X.homOfLE (inf_le_left (b := V.1)) ⁻¹ᵁ U.1.ι ⁻¹ᵁ V.1 := by
        rw [← Scheme.preimage_comp, X.homOfLE_ι]; exact fun x _ ↦ by simpa using x.2.2
      rw [← F.map_appLE (show ⊤ ≤ F ⁻¹ᵁ ⊤ from le_rfl) (homOfLE H).op]
      simp only [homOfLE_leOfHom, Opens.toScheme_presheaf_map, Quiver.Hom.unop_op,
        Hom.opensFunctor_map_homOfLE, ← Functor.map_comp_assoc, IsAffineOpen.isoSpec_hom_appTop,
        Opens.topIso_inv, eqToHom_op, homOfLE_leOfHom, Category.assoc,
        Iso.inv_hom_id_assoc, F.app_eq_appLE]
      rfl
    · have : (U.1.ι.app V.1 ≫ (I.glueDataObjι U).app (U.1.ι ⁻¹ᵁ V.1)).hom x = 0 :=
        I.ideal_le_ker_glueDataObjι U V hx
      simp_rw [F, ← pullback.condition]
      simp only [Scheme.Opens.ι_app, CommRingCat.hom_comp, RingHom.coe_comp,
        Function.comp_apply, Scheme.Hom.appLE, Scheme.comp_app, Category.assoc, F] at this ⊢
      simp only [this, map_zero]
  · conv_lhs => enter [2]; rw [glueDataObjι]
    rw [Scheme.Hom.liftQuotient_comp_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.assoc, X.homOfLE_homOfLE]

@[reassoc (attr := simp)]
private lemma glueDataT_snd (U V : X.affineOpens) :
    I.glueDataT U V ≫ pullback.snd _ _ = pullback.snd _ _ ≫ X.homOfLE (by simp) :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private lemma glueDataT_fst (U V : X.affineOpens) :
    I.glueDataT U V ≫ pullback.fst _ _ ≫ glueDataObjι _ _ =
      pullback.snd _ _ ≫ X.homOfLE inf_le_right := by
  refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
  conv_lhs => enter [2]; rw [glueDataObjι]
  rw [Scheme.Hom.liftQuotient_comp_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- (Implementation) `t'` in the glue data for `𝒪ₓ/I`. -/
private noncomputable
def glueDataT'Aux (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W ≤ U₀) :
    pullback
      (pullback.fst _ _ : I.glueDataObjPullback U V ⟶ _)
      (pullback.fst _ _ : I.glueDataObjPullback U W ⟶ _) ⟶ I.glueDataObjPullback V U₀ :=
  pullback.lift
    (pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _)
    (IsOpenImmersion.lift (V.1 ⊓ U₀.1).ι
      (pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι) (by
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]
      constructor
      · rw [pullback.condition_assoc (f := I.glueDataObjι U), X.homOfLE_ι,
          ← Category.assoc, Scheme.comp_coeBase, TopCat.coe_comp]
        exact (Set.range_comp_subset_range _ _).trans (by simp)
      · rw [pullback.condition_assoc, pullback.condition_assoc, X.homOfLE_ι,
          ← Category.assoc, Scheme.comp_coeBase, TopCat.coe_comp]
        exact (Set.range_comp_subset_range _ _).trans (by simpa using hU₀))) (by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp [pullback.condition_assoc])

@[reassoc (attr := simp)]
private lemma glueDataT'Aux_fst (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W ≤ U₀) :
    I.glueDataT'Aux U V W U₀ hU₀ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
private lemma glueDataT'Aux_snd_ι (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W ≤ U₀) :
    I.glueDataT'Aux U V W U₀ hU₀ ≫ pullback.snd _ _ ≫ (V.1 ⊓ U₀.1).ι =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι :=
  (pullback.lift_snd_assoc _ _ _ _).trans (IsOpenImmersion.lift_fac _ _ _)

/-- (Implementation) The glue data for `𝒪ₓ/I`. -/
@[simps]
private noncomputable
def glueData : Scheme.GlueData where
  J := X.affineOpens
  U := I.glueDataObj
  V ij := I.glueDataObjPullback ij.1 ij.2
  f i j := pullback.fst _ _
  f_id i :=
    have : IsIso (X.homOfLE (inf_le_left (a := i.1) (b := i.1))) :=
      ⟨X.homOfLE (by simp), by simp, by simp⟩
    inferInstance
  t i j := I.glueDataT i j
  t_id i := by
    apply pullback.hom_ext
    · rw [← cancel_mono (glueDataObjι _ _)]
      simp [pullback.condition]
    · simp
  t' i j k := pullback.lift
    (I.glueDataT'Aux _ _ _ _ inf_le_right) (I.glueDataT'Aux _ _ _ _ inf_le_left) (by simp)
  t_fac i j k := by
    apply pullback.hom_ext
    · rw [← cancel_mono (glueDataObjι _ _)]
      simp
    · rw [← cancel_mono (Scheme.Opens.ι _)]
      simp [pullback.condition_assoc]
  cocycle i j k := by
    dsimp only
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [← cancel_mono (glueDataObjι _ _), ← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          glueDataT'Aux_fst, limit.lift_π_assoc, cospan_left, glueDataT_fst, Scheme.homOfLE_ι,
          glueDataT'Aux_snd_ι, glueDataT'Aux_fst_assoc, glueDataT_fst_assoc, Category.id_comp]
        rw [pullback.condition_assoc (f := I.glueDataObjι i)]
        simp
      · rw [← cancel_mono (Scheme.Opens.ι _)]
        simp [pullback.condition_assoc]
    · apply pullback.hom_ext
      · rw [← cancel_mono (glueDataObjι _ _), ← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          glueDataT'Aux_fst, limit.lift_π_assoc, cospan_left, glueDataT_fst, Scheme.homOfLE_ι,
          glueDataT'Aux_snd_ι, glueDataT'Aux_fst_assoc, glueDataT_fst_assoc, Category.id_comp]
        rw [← pullback.condition_assoc, pullback.condition_assoc (f := I.glueDataObjι i),
          X.homOfLE_ι]
      · rw [← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          glueDataT'Aux_snd_ι, limit.lift_π_assoc, cospan_left, glueDataT'Aux_fst_assoc,
          glueDataT_fst_assoc, Scheme.homOfLE_ι, Category.id_comp]
        rw [pullback.condition_assoc, pullback.condition_assoc, X.homOfLE_ι]
  f_open i j := inferInstance

/-- (Implementation) The map from `Spec(𝒪ₓ/I)` to `X`. See `IdealSheafData.subschemeι` instead. -/
private noncomputable
def gluedTo : I.glueData.glued ⟶ X :=
  Multicoequalizer.desc _ _ (fun i ↦ I.glueDataObjι i ≫ i.1.ι)
    (by simp [GlueData.diagram, pullback.condition_assoc])

@[reassoc (attr := simp)]
private lemma ι_gluedTo (U : X.affineOpens) :
    I.glueData.ι U ≫ I.gluedTo = I.glueDataObjι U ≫ U.1.ι :=
  Multicoequalizer.π_desc _ _ _ _ _

@[reassoc (attr := simp)]
private lemma glueDataObjMap_ι (U V : X.affineOpens) (h : U ≤ V) :
    I.glueDataObjMap h ≫ I.glueData.ι V = I.glueData.ι U := by
  have : IsIso (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) :=
    ⟨X.homOfLE (by simpa), by simp, by simp⟩
  have H : inv (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) = X.homOfLE (by simpa) := by
    rw [eq_comm, ← hom_comp_eq_id]; simp
  have := I.glueData.glue_condition U V
  simp only [glueData_J, glueData_V, glueData_t, glueData_U, glueData_f] at this
  rw [← IsIso.inv_comp_eq] at this
  rw [← Category.id_comp (I.glueData.ι U), ← this]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (glueDataObjι _ _)]
  simp [pullback_inv_fst_snd_of_right_isIso_assoc, H]

private lemma gluedTo_injective :
    Function.Injective I.gluedTo.base := by
  intro a b e
  obtain ⟨ia, a : I.glueDataObj ia, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective (Scheme.forgetToTop ⋙ forget _) a
  obtain ⟨ib, b : I.glueDataObj ib, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective (Scheme.forgetToTop ⋙ forget _) b
  show (I.glueData.ι ia).base a = (I.glueData.ι ib).base b
  have : ((I.glueDataObjι ia).base a).1 = ((I.glueDataObjι ib).base b).1 := by
    have : (I.glueData.ι ia ≫ I.gluedTo).base a =
      (I.glueData.ι ib ≫ I.gluedTo).base b := e
    rwa [ι_gluedTo, ι_gluedTo] at this
  obtain ⟨f, g, hfg, H⟩ := exists_basicOpen_le_affine_inter ia.2 ib.2
    ((I.glueDataObjι ia).base a).1
      ⟨((I.glueDataObjι ia).base a).2, this ▸ ((I.glueDataObjι ib).base b).2⟩
  have hmem (W) (hW : W = X.affineBasicOpen g) :
      b ∈ Set.range (I.glueDataObjMap (hW.trans_le (X.affineBasicOpen_le g))).base := by
    subst hW
    refine (I.opensRange_glueDataObjMap g).ge ?_
    show ((I.glueDataObjι ib).base b).1 ∈ X.basicOpen g
    rwa [← this, ← hfg]
  obtain ⟨a, rfl⟩ := (I.opensRange_glueDataObjMap f).ge H
  obtain ⟨b, rfl⟩ := hmem (X.affineBasicOpen f) (Subtype.ext hfg)
  simp only [glueData_U, ← Scheme.comp_base_apply, glueDataObjMap_glueDataObjι] at this ⊢
  simp only [Scheme.affineBasicOpen_coe, Scheme.comp_coeBase, TopCat.comp_app,
    Scheme.homOfLE_apply, SetLike.coe_eq_coe] at this
  obtain rfl := (I.glueDataObjι (X.affineBasicOpen f)).isEmbedding.injective this
  simp only [glueDataObjMap_ι]

lemma range_glueDataObjι_ι_eq_support_inter (U : X.affineOpens) :
    Set.range (I.glueDataObjι U ≫ U.1.ι).base = I.support ∩ U :=
  (I.range_glueDataObjι_ι U).trans (I.support_inter U).symm

private lemma range_gluedTo :
    Set.range I.gluedTo.base = I.support := by
  refine subset_antisymm (Set.range_subset_iff.mpr fun x ↦ ?_) ?_
  · obtain ⟨ix, x : I.glueDataObj ix, rfl⟩ :=
      I.glueData.toGlueData.ι_jointly_surjective (Scheme.forgetToTop ⋙ forget _) x
    show (I.glueData.ι _ ≫ I.gluedTo).base x ∈ I.support
    rw [ι_gluedTo]
    exact ((I.range_glueDataObjι_ι_eq_support_inter ix).le ⟨_, rfl⟩).1
  · intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      (isBasis_affine_open X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨y, rfl⟩ := (I.range_glueDataObjι_ι_eq_support_inter ⟨U, hU⟩).ge ⟨hx, hxU⟩
    rw [← ι_gluedTo]
    exact ⟨_, rfl⟩

private lemma range_glueData_ι (U : X.affineOpens) :
    Set.range (Scheme.Hom.toLRSHom' (X := I.glueDataObj U) <|
      I.glueData.ι U).base = (I.gluedTo ⁻¹ᵁ U : Set I.glueData.glued) := by
  simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.map_coe, glueData_U]
  apply I.gluedTo_injective.image_injective
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.comp_base, ι_gluedTo,
    range_glueDataObjι_ι, Set.image_preimage_eq_inter_range, range_gluedTo,
    ← support_inter, Set.inter_comm]

/-- (Implementation) identifying `Spec(Γ(X, U)/U)` with its image in `Spec(𝒪ₓ/I)`. -/
private noncomputable
def glueDataObjIso (U : X.affineOpens) :
    I.glueDataObj U ≅ I.gluedTo ⁻¹ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (I.glueData.ι U) (Scheme.Opens.ι _) (by
    simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.map_coe, glueData_U, range_glueData_ι])

@[reassoc (attr := simp)]
private lemma glueDataObjIso_hom_ι (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ (I.gluedTo ⁻¹ᵁ U).ι = I.glueData.ι U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private lemma glueDataObjIso_hom_restrict (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ I.gluedTo ∣_ ↑U = I.glueDataObjι U := by
  rw [← cancel_mono U.1.ι]; simp

private instance : IsPreimmersion I.gluedTo := by
  rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @IsPreimmersion) _ (iSup_affineOpens_eq_top X)]
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion (I.glueDataObjIso U).hom,
    glueDataObjIso_hom_restrict]
  infer_instance

private instance : QuasiCompact I.gluedTo :=
  ⟨fun _ _ ↦ (Topology.IsClosedEmbedding.isProperMap
    ⟨I.gluedTo.isEmbedding, I.range_gluedTo ▸ I.isClosed_support⟩).isCompact_preimage⟩

/-- (Implementation) The underlying space of `Spec(𝒪ₓ/I)` is homeomorphic to the support of `I`. -/
private noncomputable
def gluedHomeo : I.glueData.glued ≃ₜ I.support :=
  .trans (.ofIsEmbedding _ I.gluedTo.isEmbedding) (.setCongr I.range_gluedTo)

/-- The subscheme associated to an ideal sheaf. -/
noncomputable
def subscheme : Scheme :=
  I.glueData.glued.restrict
    (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding

/-- (Implementation) The isomorphism between the subscheme and the glued scheme. -/
private noncomputable
def subschemeIso : I.subscheme ≅ I.glueData.glued :=
  letI F := I.glueData.glued.ofRestrict (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding
  have : Epi F.base := ConcreteCategory.epi_of_surjective _ I.gluedHomeo.symm.surjective
  letI := IsOpenImmersion.to_iso F
  asIso F

/-- The inclusion from the subscheme associated to an ideal sheaf. -/
noncomputable
def subschemeι : I.subscheme ⟶ X :=
    (I.subschemeIso.hom ≫ I.gluedTo).copyBase Subtype.val <| by
  ext x
  show (I.gluedHomeo (I.gluedHomeo.symm x)).1 = x.1
  rw [I.gluedHomeo.apply_symm_apply]

lemma subschemeι_apply (x : I.subscheme) : I.subschemeι.base x = x.1 := rfl

private lemma subschemeι_def : I.subschemeι = I.subschemeIso.hom ≫ I.gluedTo :=
  Scheme.Hom.copyBase_eq _ _ _

instance : IsPreimmersion I.subschemeι := by
  rw [subschemeι_def]
  infer_instance

instance : QuasiCompact I.subschemeι := by
  rw [subschemeι_def]
  infer_instance

@[simp]
lemma range_subschemeι : Set.range I.subschemeι.base = I.support := by
  rw [← range_gluedTo, I.subschemeι_def]
  have : Set.range I.subschemeIso.hom.base = .univ :=
    Set.range_eq_univ.mpr I.subschemeIso.hom.homeomorph.surjective
  simp [Set.range_comp, this]

private lemma opensRange_glueData_ι_subschemeIso_inv (U : X.affineOpens) :
    (I.glueData.ι U ≫ I.subschemeIso.inv).opensRange = I.subschemeι ⁻¹ᵁ U := by
  ext1
  simp only [glueData_U, Hom.coe_opensRange, comp_coeBase, TopCat.hom_comp, ContinuousMap.coe_comp,
    TopologicalSpace.Opens.map_coe, Set.range_comp, I.range_glueData_ι]
  show (Scheme.homeoOfIso I.subschemeIso).toEquiv.symm '' _ = _
  rw [← Set.preimage_equiv_eq_image_symm, subschemeι_def]
  rfl

/-- The subscheme associated to an ideal sheaf `I` is covered by `Spec(Γ(X, U)/I)`. -/
noncomputable
def subschemeCover : I.subscheme.AffineOpenCover where
  J := X.affineOpens
  obj U := .of <| Γ(X, U) ⧸ I.ideal U
  map U := I.glueData.ι U ≫ I.subschemeIso.inv
  f x := (X.openCoverOfISupEqTop _ (iSup_affineOpens_eq_top X)).f x.1
  covers x := by
    let U := (X.openCoverOfISupEqTop _ (iSup_affineOpens_eq_top X)).f x.1
    obtain ⟨⟨y, hy : y ∈ U.1⟩, rfl : y = x.1⟩ :=
      (X.openCoverOfISupEqTop _ (iSup_affineOpens_eq_top X)).covers x.1
    exact (I.opensRange_glueData_ι_subschemeIso_inv U).ge hy

@[simp]
lemma opensRange_subschemeCover_map (U : X.affineOpens) :
    (I.subschemeCover.map U).opensRange = I.subschemeι ⁻¹ᵁ U :=
  I.opensRange_glueData_ι_subschemeIso_inv U

@[simp]
lemma subschemeCover_map_subschemeι (U : X.affineOpens) :
    I.subschemeCover.map U ≫ I.subschemeι = I.glueDataObjι U ≫ U.1.ι := by
  simp [subschemeCover, subschemeι_def]

lemma subschemeι_app (U : X.affineOpens) : I.subschemeι.app U =
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫
    (Scheme.ΓSpecIso (.of (Γ(X, U) ⧸ I.ideal U))).inv ≫ ((I.subschemeCover.map U).appIso _).inv ≫
      I.subscheme.presheaf.map (eqToHom (by simp)).op := by
  have := I.subschemeCover_map_subschemeι U
  simp only [glueDataObjι, Category.assoc, IsAffineOpen.isoSpec_inv_ι] at this
  replace this := Scheme.congr_app this U
  simp only [comp_coeBase, TopologicalSpace.Opens.map_comp_obj, comp_app, eqToHom_op,
    Category.assoc] at this
  rw [IsAffineOpen.fromSpec_app_self] at this
  simp only [Category.assoc, Hom.naturality_assoc, TopologicalSpace.Opens.map_top,
    Quiver.Hom.unop_op, ← ΓSpecIso_inv_naturality_assoc] at this
  simp_rw [← Category.assoc, ← IsIso.comp_inv_eq] at this
  rw [← this]
  simp only [← Functor.map_inv, inv_eqToHom, Category.assoc, ← Functor.map_comp, IsIso.Iso.inv_inv,
    eqToHom_op, Iso.hom_inv_id_assoc, Hom.appIso_inv_naturality_assoc, Functor.op_obj,
    Functor.op_map, unop_comp, unop_inv, Quiver.Hom.unop_op, eqToHom_unop, Hom.app_appIso_inv_assoc,
    TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.map_coe, homOfLE_leOfHom]
  convert (Category.comp_id _).symm
  exact CategoryTheory.Functor.map_id _ _

lemma ker_subschemeι_app (U : X.affineOpens) :
    RingHom.ker (I.subschemeι.app U).hom = I.ideal U := by
  rw [subschemeι_app]
  let e : CommRingCat.of (Γ(X, U) ⧸ I.ideal U) ≅ Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso _).symm ≪≫ ((I.subschemeCover.map U).appIso _).symm ≪≫
      I.subscheme.presheaf.mapIso (eqToIso (by simp)).op
  show RingHom.ker (e.commRingCatIsoToRingEquiv.toRingHom.comp
    (Ideal.Quotient.mk (I.ideal U))) = _
  rw [RingHom.ker_equiv_comp, Ideal.mk_ker]

@[simp]
lemma ker_subschemeι : I.subschemeι.ker = I := by
  ext; simp [ker_subschemeι_app]

/-- Given `I ≤ J`, this is the map `Spec(Γ(X, U)/J(U)) ⟶ Spec(Γ(X, U)/I(U))`. -/
noncomputable
def glueDataObjHom {I J : IdealSheafData X} (h : I ≤ J) (U) :
    J.glueDataObj U ⟶ I.glueDataObj U :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h U)))

@[reassoc (attr := simp)]
lemma glueDataObjHom_ι {I J : IdealSheafData X} (h : I ≤ J) (U) :
    glueDataObjHom h U ≫ I.glueDataObjι U = J.glueDataObjι U := by
  rw [glueDataObjHom, glueDataObjι, glueDataObjι, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]

@[simp]
lemma glueDataObjHom_id {I : IdealSheafData X} (U) :
    glueDataObjHom (le_refl I) U = 𝟙 _ := by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

@[reassoc (attr := simp)]
lemma glueDataObjHom_comp {I J K : IdealSheafData X} (hIJ : I ≤ J) (hJK : J ≤ K) (U) :
    glueDataObjHom hJK U ≫ glueDataObjHom hIJ U = glueDataObjHom (hIJ.trans hJK) U := by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

/-- The inclusion of ideal sheaf induces an inclusion of subschemes -/
noncomputable
def inclusion {I J : IdealSheafData X} (h : I ≤ J) :
    J.subscheme ⟶ I.subscheme :=
  J.subschemeCover.openCover.glueMorphisms (fun U ↦ glueDataObjHom h U ≫ I.subschemeCover.map U)
  (by
    intro U V
    rw [← cancel_mono I.subschemeι]
    simp only [AffineOpenCover.openCover_obj, AffineOpenCover.openCover_map, Category.assoc,
      subschemeCover_map_subschemeι, glueDataObjHom_ι_assoc]
    rw [← subschemeCover_map_subschemeι, pullback.condition_assoc, subschemeCover_map_subschemeι])

@[reassoc (attr := simp)]
lemma subSchemeCover_map_inclusion {I J : IdealSheafData X} (h : I ≤ J) (U) :
    J.subschemeCover.map U ≫ inclusion h = glueDataObjHom h U ≫ I.subschemeCover.map U :=
  J.subschemeCover.openCover.ι_glueMorphisms _ _ _

@[reassoc (attr := simp)]
lemma inclusion_subschemeι {I J : IdealSheafData X} (h : I ≤ J) :
    inclusion h ≫ I.subschemeι = J.subschemeι :=
  J.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

@[reassoc (attr := simp)]
lemma inclusion_id (I : IdealSheafData X) :
    inclusion le_rfl = 𝟙 I.subscheme :=
  I.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

@[reassoc (attr := simp)]
lemma inclusion_comp {I J K : IdealSheafData X} (h₁ : I ≤ J) (h₂ : J ≤ K) :
    inclusion h₂ ≫ inclusion h₁ = inclusion (h₁.trans h₂) :=
  K.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

end IdealSheafData

end subscheme

end Scheme

end AlgebraicGeometry
