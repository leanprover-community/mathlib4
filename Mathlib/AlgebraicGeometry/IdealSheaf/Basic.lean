/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Properties

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

## Main results
* `AlgebraicGeometry.Scheme.IdealSheafData.gc`:
  `support` and `vanishingIdeal` forms a Galois connection.
* `AlgebraicGeometry.Scheme.Hom.support_ker`: The support of a kernel of a quasi-compact morphism
  is the closure of the range.

## Implementation detail

Ideal sheaves are not yet defined in this file as actual subsheaves of `𝒪ₓ`.
Instead, for the ease of development and application,
we define the structure `IdealSheafData` containing all necessary data to uniquely define an
ideal sheaf. This should be refactored as a constructor for ideal sheaves once they are introduced
into mathlib.

-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/--
A structure that contains the data to uniquely define an ideal sheaf, consisting of
1. an ideal `I(U) ≤ Γ(X, U)` for every affine open `U`
2. a proof that `I(D(f)) = I(U)_f` for every affine open `U` and every section `f : Γ(X, U)`
3. a subset of `X` equal to the support.

Also see `Scheme.IdealSheafData.mkOfMemSupportIff` for a constructor with the condition on the
support being (usually) easier to prove.
-/
structure IdealSheafData (X : Scheme.{u}) : Type u where
  /-- The component of an ideal sheaf at an affine open. -/
  ideal : ∀ U : X.affineOpens, Ideal Γ(X, U)
  /-- Also see `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal` -/
  map_ideal_basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)),
    (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
      ideal (X.affineBasicOpen f)
  /-- The support of an ideal sheaf. Use `IdealSheafData.support` instead for most occasions. -/
  supportSet : Set X := ⋂ U, X.zeroLocus (U := U.1) (ideal U)
  supportSet_eq_iInter_zeroLocus : supportSet = ⋂ U, X.zeroLocus (U := U.1) (ideal U) := by rfl

namespace IdealSheafData

@[ext]
protected lemma ext {I J : X.IdealSheafData} (h : I.ideal = J.ideal) : I = J := by
  obtain ⟨i, _, s, hs⟩ := I
  obtain ⟨j, _, t, ht⟩ := J
  subst h
  congr
  rw [hs, ht]

section Order

instance : PartialOrder (IdealSheafData X) := PartialOrder.lift ideal fun _ _ ↦ IdealSheafData.ext

lemma le_def {I J : IdealSheafData X} : I ≤ J ↔ ∀ U, I.ideal U ≤ J.ideal U := .rfl

instance : CompleteSemilatticeSup (IdealSheafData X) where
  sSup s :=
  { ideal := sSup (ideal '' s),
    map_ideal_basicOpen := by
      have : sSup (ideal '' s) = ⨆ i : s, ideal i.1 := by
        conv_lhs => rw [← Subtype.range_val (s := s), ← Set.range_comp]
        rfl
      simp only [this, iSup_apply, Ideal.map_iSup, map_ideal_basicOpen, implies_true] }
  le_sSup s x hxs := le_sSup (s := ideal '' s) ⟨_, hxs, rfl⟩
  sSup_le s i hi := sSup_le (s := ideal '' s) (Set.forall_mem_image.mpr hi)

/-- The largest ideal sheaf contained in a family of ideals. -/
def ofIdeals (I : ∀ U : X.affineOpens, Ideal Γ(X, U)) : IdealSheafData X :=
  sSup { J : IdealSheafData X | J.ideal ≤ I }

lemma ideal_ofIdeals_le (I : ∀ U : X.affineOpens, Ideal Γ(X, U)) :
    (ofIdeals I).ideal ≤ I :=
  sSup_le (Set.forall_mem_image.mpr fun _ ↦ id)

/-- The Galois coinsertion between ideal sheaves and arbitrary families of ideals. -/
protected def gci : GaloisCoinsertion ideal (ofIdeals (X := X)) where
  choice I hI :=
  { ideal := I
    map_ideal_basicOpen U f :=
      (ideal_ofIdeals_le I).antisymm hI ▸ (ofIdeals I).map_ideal_basicOpen U f }
  gc _ _ := ⟨(le_sSup ·), (le_trans · (ideal_ofIdeals_le _))⟩
  u_l_le _ := sSup_le fun _ ↦ id
  choice_eq I hI := IdealSheafData.ext (hI.antisymm (ideal_ofIdeals_le I))

lemma strictMono_ideal : StrictMono (ideal (X := X)) := IdealSheafData.gci.strictMono_l
lemma ideal_mono : Monotone (ideal (X := X)) := strictMono_ideal.monotone
lemma ofIdeals_mono : Monotone (ofIdeals (X := X)) := IdealSheafData.gci.gc.monotone_u
lemma ofIdeals_ideal (I : IdealSheafData X) : ofIdeals I.ideal = I := IdealSheafData.gci.u_l_eq _
lemma le_ofIdeals_iff {I : IdealSheafData X} {J} : I ≤ ofIdeals J ↔ I.ideal ≤ J :=
  IdealSheafData.gci.gc.le_iff_le.symm

instance : OrderTop (IdealSheafData X) where
  top.ideal := ⊤
  top.map_ideal_basicOpen := by simp [Ideal.map_top]
  top.supportSet := ⊥
  top.supportSet_eq_iInter_zeroLocus := by
    ext x
    simpa using X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  le_top I U := le_top

instance : OrderBot (IdealSheafData X) where
  bot.ideal := ⊥
  bot.map_ideal_basicOpen := by simp
  bot.supportSet := ⊤
  bot.supportSet_eq_iInter_zeroLocus := by ext; simp
  bot_le I U := bot_le

instance : SemilatticeInf (IdealSheafData X) where
  min I J :=
  { ideal := I.ideal ⊓ J.ideal
    map_ideal_basicOpen U f := by
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
      · rw [pow_add, mul_assoc]; exact Ideal.mul_mem_left _ _ h₂ }
  inf_le_left I J U := inf_le_left
  inf_le_right I J U := inf_le_right
  le_inf I J K hIJ hIK U := le_inf (hIJ U) (hIK U)

instance : CompleteLattice (IdealSheafData X) where
  __ := inferInstanceAs (OrderTop (IdealSheafData X))
  __ := inferInstanceAs (OrderBot (IdealSheafData X))
  __ := inferInstanceAs (SemilatticeInf (IdealSheafData X))
  __ := inferInstanceAs (CompleteSemilatticeSup (IdealSheafData X))
  __ := IdealSheafData.gci.liftCompleteLattice

@[simp]
lemma ideal_top : ideal (X := X) ⊤ = ⊤ := rfl

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
lemma ideal_inf {I J : IdealSheafData X} : (I ⊓ J).ideal = I.ideal ⊓ J.ideal := rfl

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
  simp only [Ideal.map_map, ← CommRingCat.hom_comp, affineBasicOpen_coe, X.presheaf.germ_res]
    at this ⊢
  simp only [homOfLE_leOfHom, TopCat.Presheaf.germ_res', this]

/-- A form of `map_ideal` that is easier to rewrite with. -/
lemma map_ideal' {U V : X.affineOpens} (h : Opposite.op V.1 ⟶ .op U.1) :
    (I.ideal V).map (X.presheaf.map h).hom = I.ideal U :=
  map_ideal _ _

lemma ideal_le_comap_ideal {U V : X.affineOpens} (h : U ≤ V) :
    I.ideal V ≤ (I.ideal U).comap (X.presheaf.map (homOfLE h).op).hom := by
  rw [← Ideal.map_le_iff_le_comap, ← I.map_ideal h]

end map_ideal

section support

lemma mem_supportSet_iff {I : IdealSheafData X} {x} :
    x ∈ I.supportSet ↔ ∀ U, x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

lemma supportSet_subset_zeroLocus (I : IdealSheafData X) (U : X.affineOpens) :
    I.supportSet ⊆ X.zeroLocus (U := U.1) (I.ideal U) :=
  I.supportSet_eq_iInter_zeroLocus.trans_subset (Set.iInter_subset _ _)

lemma zeroLocus_inter_subset_supportSet (I : IdealSheafData X) (U : X.affineOpens) :
    X.zeroLocus (U := U.1) (I.ideal U) ∩ U ⊆ I.supportSet := by
  rw [I.supportSet_eq_iInter_zeroLocus]
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

lemma mem_supportSet_iff_of_mem {I : IdealSheafData X} {x} {U : X.affineOpens} (hxU : x ∈ U.1) :
    x ∈ I.supportSet ↔ x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  ⟨I.supportSet_eq_iInter_zeroLocus ▸ fun h ↦ Set.iInter_subset _ U h,
    fun h ↦ I.zeroLocus_inter_subset_supportSet U ⟨h, hxU⟩⟩

lemma supportSet_inter (I : IdealSheafData X) (U : X.affineOpens) :
    I.supportSet ∩ U = X.zeroLocus (U := U.1) (I.ideal U) ∩ U := by
  ext x
  by_cases hxU : x ∈ U.1
  · simp [hxU, mem_supportSet_iff_of_mem hxU]
  · simp [hxU]

lemma isClosed_supportSet (I : IdealSheafData X) : IsClosed I.supportSet := by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top X)]
  intro U
  refine ⟨(X.zeroLocus (U := U.1) (I.ideal U))ᶜ, (X.zeroLocus_isClosed _).isOpen_compl, ?_⟩
  simp only [Set.preimage_compl, compl_inj_iff]
  apply Subtype.val_injective.image_injective
  simp [Set.image_preimage_eq_inter_range, I.supportSet_inter]

/-- The support of an ideal sheaf. Also see `IdealSheafData.mem_support_iff_of_mem`. -/
def support : Closeds X := ⟨I.supportSet, I.isClosed_supportSet⟩

lemma coe_support_eq_eq_iInter_zeroLocus :
    (I.support : Set X) = ⋂ U, X.zeroLocus (U := U.1) (I.ideal U) :=
  I.supportSet_eq_iInter_zeroLocus

lemma mem_support_iff {I : IdealSheafData X} {x} :
    x ∈ I.support ↔ ∀ U, x ∈ X.zeroLocus (U := U.1) (I.ideal U) :=
  (Set.ext_iff.mp I.supportSet_eq_iInter_zeroLocus _).trans Set.mem_iInter

lemma mem_support_iff_of_mem {I : IdealSheafData X} {x : X} {U : X.affineOpens} (h : x ∈ U.1) :
    x ∈ I.support ↔ x ∈ X.zeroLocus (U := U.1) (I.ideal U) := by
  simpa [-mem_zeroLocus_iff, h] using congr(x ∈ $(I.supportSet_inter U))

lemma coe_support_inter (I : IdealSheafData X) (U : X.affineOpens) :
    (I.support : Set X) ∩ U = X.zeroLocus (U := U.1) (I.ideal U) ∩ U :=
  I.supportSet_inter U

/-- Custom simps projection for `IdealSheafData`. -/
def Simps.coe_support : Set X := I.support

initialize_simps_projections IdealSheafData (supportSet → coe_support, as_prefix coe_support)

/-- A useful constructor of `IdealSheafData`
with the condition on `supportSet` being easier to check. -/
@[simps ideal coe_support]
def mkOfMemSupportIff
    (ideal : ∀ U : X.affineOpens, Ideal Γ(X, U))
    (map_ideal_basicOpen : ∀ (U : X.affineOpens) (f : Γ(X, U)),
      (ideal U).map (X.presheaf.map (homOfLE <| X.basicOpen_le f).op).hom =
        ideal (X.affineBasicOpen f))
    (supportSet : Set X)
    (supportSet_inter :
      ∀ U : X.affineOpens, ∀ x ∈ U.1, x ∈ supportSet ↔ x ∈ X.zeroLocus (U := U.1) (ideal U)) :
    X.IdealSheafData where
  ideal := ideal
  map_ideal_basicOpen := map_ideal_basicOpen
  supportSet := supportSet
  supportSet_eq_iInter_zeroLocus := by
    let I' : X.IdealSheafData := { ideal := ideal, map_ideal_basicOpen := map_ideal_basicOpen }
    change supportSet = I'.supportSet
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (supportSet_inter ⟨U, hU⟩ x hxU).trans
      (I'.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).symm

@[simp]
lemma support_top : support (X := X) ⊤ = ⊥ := rfl

@[simp]
lemma support_bot : support (X := X) ⊥ = ⊤ := rfl

lemma support_antitone : Antitone (support (X := X)) := by
  intro I J h
  rw [← SetLike.coe_subset_coe, I.coe_support_eq_eq_iInter_zeroLocus,
    J.coe_support_eq_eq_iInter_zeroLocus]
  exact Set.iInter_mono fun U ↦ X.zeroLocus_mono (h U)

@[simp]
lemma support_eq_bot_iff : support I = ⊥ ↔ I = ⊤ := by
  refine ⟨fun H ↦ top_le_iff.mp fun U ↦ ?_, by simp +contextual⟩
  have := (U.2.fromSpec_image_zeroLocus _).trans_subset
    ((zeroLocus_inter_subset_supportSet I U).trans H.le)
  simp only [Set.subset_empty_iff, Set.image_eq_empty, Closeds.coe_bot] at this
  simp [PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp this]

end support

section IsAffine

/-- The ideal sheaf induced by an ideal of the global sections. -/
@[simps! ideal coe_support]
def ofIdealTop (I : Ideal Γ(X, ⊤)) : IdealSheafData X :=
  mkOfMemSupportIff
    (fun U ↦ I.map (X.presheaf.map (homOfLE le_top).op).hom)
    (fun U f ↦ by rw [Ideal.map_map, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl)
    (X.zeroLocus (U := ⊤) I)
    (fun U x hxU ↦ by
      simp only [Ideal.map, zeroLocus_span, zeroLocus_map, Set.mem_union, Set.mem_compl_iff,
        SetLike.mem_coe, hxU, not_true_eq_false, iff_self_or, IsEmpty.forall_iff])

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
def equivOfIsAffine [IsAffine X] : IdealSheafData X ≃o Ideal Γ(X, ⊤) where
  toFun := (ideal · ⟨⊤, isAffineOpen_top X⟩)
  invFun := ofIdealTop
  left_inv I := ext_of_isAffine (by simp)
  right_inv I := by simp
  map_rel_iff' {I J} := ⟨le_of_isAffine, (· _)⟩

end IsAffine

section ofIsClosed

open _root_.PrimeSpectrum TopologicalSpace

@[deprecated (since := "2025-08-10")] alias Scheme.zeroLocus_radical :=
  AlgebraicGeometry.Scheme.zeroLocus_radical

/-- The radical of a ideal sheaf. -/
@[simps! ideal]
def radical (I : IdealSheafData X) : IdealSheafData X :=
  mkOfMemSupportIff
  (fun U ↦ (I.ideal U).radical)
  (fun U f ↦
    letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_of_eq_basicOpen _ _ rfl
    (IsLocalization.map_radical (.powers f) Γ(X, X.basicOpen f) (I.ideal U)).trans
      congr($(I.map_ideal_basicOpen U f).radical))
  I.supportSet
  (fun U x hx ↦ by
    simp only [mem_supportSet_iff_of_mem hx, AlgebraicGeometry.Scheme.zeroLocus_radical])

@[simp]
lemma support_radical (I : IdealSheafData X) : I.radical.support = I.support := rfl

/-- The nilradical of a scheme. -/
def _root_.AlgebraicGeometry.Scheme.nilradical (X : Scheme.{u}) : IdealSheafData X :=
  .radical ⊥

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.support_nilradical (X : Scheme.{u}) :
    X.nilradical.support = ⊤ := rfl

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

/-- The vanishing ideal sheaf of a closed set,
which is the largest ideal sheaf whose support is equal to it.
The reduced induced scheme structure on the closed set is the quotient of this ideal. -/
@[simps! ideal coe_support]
nonrec def vanishingIdeal (Z : Closeds X) : IdealSheafData X :=
  mkOfMemSupportIff
    (fun U ↦ vanishingIdeal (U.2.fromSpec.base ⁻¹' Z))
    (fun U f ↦ by
      let F := X.presheaf.map (homOfLE (X.basicOpen_le f)).op
      apply le_antisymm
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        suffices ∀ p, (X.affineBasicOpen f).2.fromSpec.base p ∈ Z → F.hom x ∈ p.asIdeal by
          simpa [PrimeSpectrum.mem_vanishingIdeal] using this
        intro x hxZ
        refine (PrimeSpectrum.mem_vanishingIdeal _ _).mp hx
          ((Spec.map (X.presheaf.map (homOfLE _).op)).base x) ?_
        rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply,
          IsAffineOpen.map_fromSpec _ (X.affineBasicOpen f).2]
      · letI : Algebra Γ(X, U) Γ(X, X.affineBasicOpen f) := F.hom.toAlgebra
        have : IsLocalization.Away f Γ(X, X.basicOpen f) :=
          U.2.isLocalization_of_eq_basicOpen _ _ rfl
        intro x hx
        dsimp only at hx ⊢
        have : Topology.IsOpenEmbedding (Spec.map F).base :=
          localization_away_isOpenEmbedding Γ(X, X.basicOpen f) f
        rw [← U.2.map_fromSpec (X.affineBasicOpen f).2 (homOfLE (X.basicOpen_le f)).op,
          Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hx
        generalize U.2.fromSpec.base ⁻¹' Z = Z' at hx ⊢
        replace hx : x ∈ vanishingIdeal ((Spec.map F).base ⁻¹' Z') := hx
        obtain ⟨I, hI, e⟩ :=
          (isClosed_iff_zeroLocus_radical_ideal _).mp (isClosed_closure (s := Z'))
        rw [← vanishingIdeal_closure,
          ← this.isOpenMap.preimage_closure_eq_closure_preimage this.continuous, e] at hx
        rw [← vanishingIdeal_closure, e]
        erw [preimage_comap_zeroLocus] at hx
        rwa [← PrimeSpectrum.zeroLocus_span, ← Ideal.map, vanishingIdeal_zeroLocus_eq_radical,
          ← RingHom.algebraMap_toAlgebra (X.presheaf.map _).hom,
          ← IsLocalization.map_radical (.powers f), ← vanishingIdeal_zeroLocus_eq_radical] at hx)
    Z
    (fun U x hxU ↦ by
      trans x ∈ X.zeroLocus (U := U.1) (vanishingIdeal (U.2.fromSpec.base.hom ⁻¹' Z)) ∩ U.1
      · rw [← U.2.fromSpec_image_zeroLocus, zeroLocus_vanishingIdeal_eq_closure,
          ← U.2.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
            U.2.fromSpec.base.1.2,
          Set.image_preimage_eq_inter_range, Z.isClosed.closure_eq, IsAffineOpen.range_fromSpec]
        simp [hxU]
      · simp [hxU])

lemma le_support_iff_le_vanishingIdeal {I : X.IdealSheafData} {Z : Closeds X} :
    Z ≤ I.support ↔ I ≤ vanishingIdeal Z := by
  simp only [le_def, vanishingIdeal_ideal, ← PrimeSpectrum.subset_zeroLocus_iff_le_vanishingIdeal]
  trans ∀ U : X.affineOpens, (Z : Set X) ∩ U ⊆ I.support ∩ U
  · refine ⟨fun H U x hx ↦ ⟨H hx.1, hx.2⟩, fun H x hx ↦ ?_⟩
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact (H ⟨U, hU⟩ ⟨hx, hxU⟩).1
  refine forall_congr' fun U ↦ ?_
  rw [coe_support_inter, ← Set.image_subset_image_iff U.2.fromSpec.isOpenEmbedding.injective,
    Set.image_preimage_eq_inter_range, IsAffineOpen.fromSpec_image_zeroLocus,
    IsAffineOpen.range_fromSpec]

@[deprecated (since := "2025-05-16")]
alias subset_support_iff_le_vanishingIdeal := le_support_iff_le_vanishingIdeal

/-- `support` and `vanishingIdeal` forms a Galois connection.
This is the global version of `PrimeSpectrum.gc`. -/
lemma gc : @GaloisConnection X.IdealSheafData (Closeds X)ᵒᵈ _ _ (support ·) (vanishingIdeal ·) :=
  fun _ _ ↦ le_support_iff_le_vanishingIdeal

lemma vanishingIdeal_antimono {S T : Closeds X} (h : S ≤ T) : vanishingIdeal T ≤ vanishingIdeal S :=
  gc.monotone_u h

lemma vanishingIdeal_support {I : IdealSheafData X} :
    vanishingIdeal I.support = I.radical := by
  ext U : 2
  dsimp
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  congr 1
  apply U.2.fromSpec.isOpenEmbedding.injective.image_injective
  rw [Set.image_preimage_eq_inter_range, IsAffineOpen.range_fromSpec,
    IsAffineOpen.fromSpec_image_zeroLocus, coe_support_inter]

@[simp] lemma vanishingIdeal_bot : vanishingIdeal (X := X) ⊥ = ⊤ := gc.u_top

@[simp] lemma vanishingIdeal_top : vanishingIdeal (X := X) ⊤ = X.nilradical := by
  rw [← support_bot, vanishingIdeal_support, nilradical]

@[simp] lemma vanishingIdeal_iSup {ι : Sort*} (Z : ι → Closeds X) :
    vanishingIdeal (iSup Z) = ⨅ i, vanishingIdeal (Z i) := gc.u_iInf

@[simp] lemma vanishingIdeal_sSup (Z : Set (Closeds X)) :
    vanishingIdeal (sSup Z) = ⨅ z ∈ Z, vanishingIdeal z := gc.u_sInf

@[simp] lemma vanishingIdeal_sup (Z Z' : TopologicalSpace.Closeds X) :
    vanishingIdeal (Z ⊔ Z') = vanishingIdeal Z ⊓ vanishingIdeal Z' := gc.u_inf

@[simp] lemma support_sup (I J : X.IdealSheafData) :
    (I ⊔ J).support = I.support ⊓ J.support := gc.l_sup

@[simp] lemma support_iSup {ι : Sort*} (I : ι → X.IdealSheafData) :
    (iSup I).support = ⨅ i, (I i).support := gc.l_iSup

@[simp] lemma support_sSup (I : Set X.IdealSheafData) :
    (sSup I).support = ⨅ i ∈ I, i.support := gc.l_sSup

end ofIsClosed

end IdealSheafData

section IsReduced

lemma nilradical_eq_bot [IsReduced X] : X.nilradical = ⊥ := by
  ext; simp [nilradical, Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot)]

lemma IdealSheafData.support_eq_top_iff [IsReduced X] {I : X.IdealSheafData} :
    I.support = ⊤ ↔ I = ⊥ := by
  rw [← top_le_iff, le_support_iff_le_vanishingIdeal,
    vanishingIdeal_top, nilradical_eq_bot, le_bot_iff]

end IsReduced

section ker

open IdealSheafData

variable {Y Z : Scheme.{u}}

/-- The kernel of a morphism,
defined as the largest (quasi-coherent) ideal sheaf contained in the component-wise kernel.
This is usually only well-behaved when `f` is quasi-compact. -/
def Hom.ker (f : X.Hom Y) : IdealSheafData Y :=
  ofIdeals fun U ↦ RingHom.ker (f.app U).hom

lemma Hom.ideal_ker_le (f : X.Hom Y) (U : Y.affineOpens) :
    f.ker.ideal U ≤ RingHom.ker (f.app U).hom :=
  ideal_ofIdeals_le _ _

@[simp]
lemma Hom.ker_apply (f : X.Hom Y) [QuasiCompact f] (U : Y.affineOpens) :
    f.ker.ideal U = RingHom.ker (f.app U).hom := by
  let I : IdealSheafData Y := ⟨fun U ↦ RingHom.ker (f.app U).hom, ?_, _, rfl⟩
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
  rw [Scheme.Hom.comp_app f g U, CommRingCat.hom_comp, ← RingHom.comap_ker]
  exact Ideal.ker_le_comap _

lemma ker_eq_top_of_isEmpty (f : X.Hom Y) [IsEmpty X] : f.ker = ⊤ :=
  top_le_iff.mp (le_ofIdeals_iff.mpr fun U x _ ↦ by simpa using Subsingleton.elim _ _)

@[simp]
lemma Hom.ker_eq_bot_of_isIso (f : X ⟶ Y) [IsIso f] : f.ker = ⊥ := by
  ext U
  simp [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (f.app U)).1]

lemma Hom.ker_comp_of_isIso (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : (f ≫ g).ker = g.ker :=
  (f.le_ker_comp g).antisymm' (((inv f).le_ker_comp _).trans (by simp))

lemma ker_of_isAffine {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    f.ker = ofIdealTop (RingHom.ker f.appTop.hom) := by
  refine (le_of_isAffine ((f.ideal_ker_le _).trans (by simp))).antisymm
    (le_ofIdeals_iff.mpr fun U ↦ ?_)
  simp only [ofIdealTop_ideal, homOfLE_leOfHom, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
    ← CommRingCat.hom_comp, f.naturality]
  intro x
  simp +contextual

lemma Hom.range_subset_ker_support (f : X.Hom Y) :
    Set.range f.base ⊆ f.ker.support := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  refine ((coe_support_inter f.ker ⟨U, hU⟩).ge ⟨?_, hxU⟩).1
  simp only [Scheme.mem_zeroLocus_iff, SetLike.mem_coe]
  intro s hs hxs
  have : x ∈ f ⁻¹ᵁ Y.basicOpen s := hxs
  rwa [Scheme.preimage_basicOpen, RingHom.mem_ker.mp (f.ideal_ker_le _ hs),
    Scheme.basicOpen_zero] at this

lemma Hom.ker_eq_top_iff_isEmpty (f : X.Hom Y) : f.ker = ⊤ ↔ IsEmpty X :=
  ⟨fun H ↦ by simpa [H] using f.range_subset_ker_support, fun _ ↦ ker_eq_top_of_isEmpty f⟩

lemma Hom.iInf_ker_openCover_map_comp_apply
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) (U : Y.affineOpens) :
    ⨅ i, (𝒰.f i ≫ f).ker.ideal U = f.ker.ideal U := by
  refine le_antisymm ?_ (le_iInf fun i ↦ (𝒰.f i).le_ker_comp f U)
  intro s hs
  simp only [Hom.ker_apply, RingHom.mem_ker]
  apply X.IsSheaf.section_ext
  rintro x hxU
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
  simp only [homOfLE_leOfHom, map_zero, exists_and_left]
  refine ⟨𝒰.f i ''ᵁ 𝒰.f i ⁻¹ᵁ f ⁻¹ᵁ U.1, ⟨_, hxU, rfl⟩,
    Set.image_preimage_subset (𝒰.f i).base (f ⁻¹ᵁ U), ?_⟩
  apply ((𝒰.f i).appIso _).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_toRingHom,
    Scheme.Hom.appIso_hom']
  simp only [homOfLE_leOfHom, Scheme.Hom.app_eq_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
  simpa [Scheme.Hom.appLE] using ideal_ker_le _ _ (Ideal.mem_iInf.mp hs i)

lemma Hom.iInf_ker_openCover_map_comp (f : X ⟶ Y) [QuasiCompact f] (𝒰 : X.OpenCover) :
    ⨅ i, (𝒰.f i ≫ f).ker = f.ker := by
  refine le_antisymm ?_ (le_iInf fun i ↦ (𝒰.f i).le_ker_comp f)
  refine iInf_le_iff.mpr fun I hI U ↦ ?_
  rw [← f.iInf_ker_openCover_map_comp_apply 𝒰, le_iInf_iff]
  exact fun i ↦ hI i U

lemma Hom.iUnion_support_ker_openCover_map_comp
    (f : X.Hom Y) [QuasiCompact f] (𝒰 : X.OpenCover) [Finite 𝒰.I₀] :
    ⋃ i, ((𝒰.f i ≫ f).ker.support : Set Y) = f.ker.support := by
  cases isEmpty_or_nonempty 𝒰.I₀
  · have : IsEmpty X := Function.isEmpty 𝒰.idx
    simp [ker_eq_top_of_isEmpty]
  suffices ∀ U : Y.affineOpens,
      (⋃ i, (𝒰.f i ≫ f).ker.support) ∩ U = (f.ker.support ∩ U : Set Y) by
    ext x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    simpa [hxU] using congr(x ∈ $(this ⟨U, hU⟩))
  intro U
  simp only [Set.iUnion_inter, coe_support_inter, ← f.iInf_ker_openCover_map_comp_apply 𝒰,
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
      eqToHom_op, Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, e, Scheme.Hom.appLE_comp_appLE, H.w]
  simp only [Scheme.Hom.ker_apply, RingHom.mem_ker, Ideal.mem_comap, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, this]
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
        ((coe_support_inter _ ⟨⊤, isAffineOpen_top _⟩).ge ⟨?_, Set.mem_univ x⟩).1
      · have := image_closure_subset_closure_image (f := (𝒰.f i).base)
          (𝒰.f i).base.1.2 (Set.mem_image_of_mem _ this)
        rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, 𝒰.pullbackHom_map] at this
        exact closure_mono (Set.range_comp_subset_range _ _) this
      · rw [← (𝒰.f i).isOpenEmbedding.injective.mem_set_image, Scheme.image_zeroLocus,
          ker_ideal_of_isPullback_of_isOpenImmersion f (𝒰.pullbackHom f i)
            ((𝒰.pullback₁ f).f i) (𝒰.f i),
          Ideal.coe_comap, Set.image_preimage_eq]
        · exact ⟨((coe_support_inter _ _).le ⟨hx, by simp⟩).1, ⟨_, rfl⟩⟩
        · exact (ConcreteCategory.bijective_of_isIso ((𝒰.f i).appIso ⊤).inv).2
        · exact (IsPullback.of_hasPullback _ _).flip
    obtain ⟨S, rfl⟩ := hY
    wlog hX : ∃ R, X = Spec R generalizing X S
    · intro x hx
      have inst : CompactSpace X := HasAffineProperty.iff_of_isAffine.mp ‹QuasiCompact f›
      let 𝒰 := X.affineCover.finiteSubcover
      obtain ⟨_, ⟨i, rfl⟩, hx⟩ := (f.iUnion_support_ker_openCover_map_comp 𝒰).ge hx
      have inst : QuasiCompact (𝒰.f i ≫ f) := HasAffineProperty.iff_of_isAffine.mpr
        (by change CompactSpace (Spec _); infer_instance)
      exact closure_mono (Set.range_comp_subset_range _ _) (this S (𝒰.f i ≫ f) ⟨_, rfl⟩ hx)
    obtain ⟨R, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    rw [ker_of_isAffine, coe_support_ofIdealTop, Spec_zeroLocus, ← Ideal.coe_comap,
      RingHom.comap_ker, ← PrimeSpectrum.closure_range_comap, ← CommRingCat.hom_comp,
      ← Scheme.ΓSpecIso_inv_naturality]
    simp only [CommRingCat.hom_comp, PrimeSpectrum.comap_comp, ContinuousMap.coe_comp]
    exact closure_mono (Set.range_comp_subset_range _ (Spec.map φ).base)
  · rw [(support _).isClosed.closure_subset_iff]
    exact f.range_subset_ker_support

/-- The functor taking a morphism into `Y` to its kernel as an ideal sheaf on `Y`. -/
@[simps]
def kerFunctor (Y : Scheme.{u}) : (Over Y)ᵒᵖ ⥤ IdealSheafData Y where
  obj f := f.unop.hom.ker
  map {f g} hfg := homOfLE <| by simpa only [Functor.id_obj, Functor.const_obj_obj,
    OrderDual.toDual_le_toDual, ← Over.w hfg.unop] using hfg.unop.left.le_ker_comp f.unop.hom
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

end ker

end Scheme

end AlgebraicGeometry
