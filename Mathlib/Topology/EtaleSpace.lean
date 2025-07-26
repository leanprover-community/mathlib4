/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
import Mathlib.Topology.Covering
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# Étalé spaces of local predicates and presheaves

The traditional approach to étalé spaces starts from a (pre)sheaf on a base space and
directly constructs the associated étalé space with a local homeomorphism to the base space.
We instead construct a local homeomorphism from an arbitrary type family (over the base space)
with a predicate on sections (over open sets of the base space) specifying the "admissible"
sections, provided that the type family behaves like the family of stalks of the presheaf
of admissible sections (i.e., satisfies the conditions `IsStalkInj` and `IsStalkSurj`).

The passage between (pre)sheaves and (pre)local predicates was already established during
the development of sheafification (see `TopCat.LocalPredicate` and the file
``Mathlib.Topology.Sheaves.Sheafify`), and we obtain the étalé space of a (pre)sheaf by
combining both steps. But our theory can also be applied to situations where the type family
is not (definitionally) the stalks of a presheaf: for example it can be a family of Hom types
in the fundamental groupoid when constructing the universal cover, or a constant family
when constructing the primitive of a holomorphic function and integrating it along a path.

In this file we will adopt the sheaf-theoretic terminology and refer to the types in the type
family as "stalks" and their elements as "germs".

## Main definitions

* `EtaleSpace`: The étalé space associated to a set of admissible sections given in the form of
  a predicate. It is endowed with the strongest topology making every admissible section continuous.
  `EtaleSpace.mk` is its constructor and `EtaleSpace.proj` is the continuous projection to the
  base space.

## Main results

Some results below requires the type family satisfies the injectivity and/or surjectivity criteria
to behave like the family of stalks of the admissible sections.

* `EtaleSpace.isOpenEmbedding_restrict_proj`: the projection from the étalé space
  to the base space is an open embedding on the range of every admissible section.

* `EtaleSpace.isOpenEmbedding_section`: every admissible section is an open embedding
  (requires injectivity criterion).

* `EtaleSpace.isLocalHomeomorph_proj`: the projection from the étalé space to the base space
  is a local homeomorphism (requires both criteria).

* `EtaleSpace.isOpen_range_section_iff_of_isOpen`: the range of a section is open if and only if
  it is the range of a continuous section over an open set (requires both criteria).

* `EtaleSpace.continuous_cod_iff`: a function to the étalé space is continuous if and only if
  it agrees with an admissible section around each point (requires both criteria).

* `EtaleSpace.continuous_section_iff`: a section is continuous if and only if it is admissible
  according to the sheafified predicate, i.e., it locally agrees with admissible sections
  (requires both criteria and that the predicate is pre-local).

* `EtaleSpace.isTopologicalBasis`: the étalé space has a basis consisting of
  the ranges of admissible sections (with the same requirements as the above).

## References
* https://ncatlab.org/nlab/show/%C3%A9tale+space
* https://nforum.ncatlab.org/discussion/11283/etale-space/
-/

open CategoryTheory Topology TopologicalSpace Opposite Set

universe u v

namespace TopCat

variable {B : TopCat.{u}} {F : B → Type v} {X : Type*} [TopologicalSpace X]

set_option linter.unusedVariables false in
/-- The underlying type of the étalé space associated to a predicate on sections of a type family
is simply the `Sigma` type. -/
@[nolint unusedArguments]
def EtaleSpace (P : Π ⦃U : Opens B⦄, (Π b : U, F b) → Prop) : Type _ := Σ b, F b

variable {P : Π ⦃U : Opens B⦄, (Π b : U, F b) → Prop}

namespace EtaleSpace

/-- Constructor for points in the étalé space. -/
@[simps] def mk {b : B} (x : F b) : EtaleSpace P := ⟨b, x⟩

/-- The étalé space is endowed with the strongest topology
making every admissible section continuous. -/
instance : TopologicalSpace (EtaleSpace P) :=
  ⨆ (U : Opens B) (s : Π b : U, F b) (_ : P s), coinduced (mk <| s ·) inferInstance

lemma isOpen_iff {V : Set (EtaleSpace P)} :
    IsOpen V ↔
    ∀ (U : Opens B) (s : Π b : U, F b), P s → IsOpen ((mk <| s ·) ⁻¹' V) := by
  simp_rw [isOpen_iSup_iff, isOpen_coinduced]

lemma continuous_dom_iff {X} [TopologicalSpace X] {f : EtaleSpace P → X} :
    Continuous f ↔
    ∀ (U : Opens B) (s : Π b : U, F b), P s → Continuous (f <| mk <| s ·) := by
  simp_rw [continuous_def, isOpen_iff, preimage_preimage,
    ← forall_comm (α := Set X), ← forall_comm (α := IsOpen _)]

variable (P) in
/-- The projection from the étalé space down to the base is continuous. -/
def proj : C(EtaleSpace P, B) where
  toFun := Sigma.fst
  continuous_toFun := continuous_dom_iff.mpr fun _ _ _ ↦ continuous_subtype_val

section Section

theorem exists_eq_mk_of_comp_eq_id (f : B → EtaleSpace P) (hf : proj P ∘ f = id) :
    ∃! s : Π b, F b, f = (mk <| s ·) := by
  convert ← (Equiv.piEquivSubtypeSigma ..).bijective.existsUnique ⟨f, congr_fun hf⟩
  exact eq_comm.trans Subtype.ext_iff

theorem exists_eq_mk_of_comp_eq_val {U : Set B} (f : U → EtaleSpace P) (hf : proj P ∘ f = (↑)) :
    ∃! s : Π b : U, F b, f = (mk <| s ·) := by
  convert ← (Equiv.piSubtypeEquivSubtypeSigma ..).bijective.existsUnique ⟨f, hf⟩
  exact eq_comm.trans Subtype.ext_iff

variable {U : Opens B} {s : Π b : U, F b} (hs : P s)

section

include hs

lemma continuous_section : Continuous fun b ↦ (mk (s b) : EtaleSpace P) :=
  continuous_iff_coinduced_le.mpr (le_iSup₂_of_le U s <| le_iSup_of_le hs le_rfl)

/-- The domain of any section is homeomorphic to its range. -/
def homeomorphRangeSection : U ≃ₜ range fun b ↦ (mk (s b) : EtaleSpace P) where
  toFun b := ⟨_, b, rfl⟩
  invFun x := ⟨proj P x, by obtain ⟨_, b, rfl⟩ := x; exact b.2⟩
  right_inv := by rintro ⟨_, _, rfl⟩; rfl
  continuous_toFun := (continuous_section hs).subtype_mk _
  continuous_invFun := ((proj P).continuous.comp continuous_subtype_val).subtype_mk <| by
    rintro ⟨_, b, rfl⟩; exact b.2

theorem isOpenEmbedding_restrict_proj :
    IsOpenEmbedding ((range (mk <| s ·)).restrict (proj P)) :=
  U.2.isOpenEmbedding_subtypeVal.comp (homeomorphRangeSection hs).symm.isOpenEmbedding

theorem isOpen_preimage_inter_range_section {U' : Opens B} (inj : ∀ b ∈ U', IsStalkInj P b) :
    IsOpen (proj P ⁻¹' U'.1 ∩ range fun b ↦ (mk (s b) : EtaleSpace P)) :=
  isOpen_iff.mpr fun V t ht ↦ isOpen_iff_mem_nhds.mpr fun ⟨v, hv⟩ ⟨h', ⟨u, hu⟩, he⟩ ↦ by
    cases congr($he.1)
    have ⟨W, iU, iV, eq⟩ := inj v h' ⟨U, hu⟩ ⟨V, hv⟩ _ _ hs ht congr($he.2)
    exact Filter.mem_of_superset (((U'.2.inter W.1.2).preimage continuous_subtype_val).mem_nhds
      ⟨h', W.2⟩) fun v hv ↦ ⟨hv.1, _, congr(mk $(eq ⟨v, hv.2⟩))⟩

theorem isOpen_range_section (inj : ∀ b ∈ U, IsStalkInj P b) :
    IsOpen (range fun b ↦ (mk (s b) : EtaleSpace P)) := by
  convert isOpen_preimage_inter_range_section hs inj
  rw [inter_eq_right.mpr (by rintro _ ⟨b, rfl⟩; exact b.2)]

theorem isOpenEmbedding_section (inj : ∀ b ∈ U, IsStalkInj P b) :
    IsOpenEmbedding fun b ↦ (mk (s b) : EtaleSpace P) := by
  rw [isOpenEmbedding_iff, isEmbedding_iff, and_assoc]
  exact ⟨.of_comp (continuous_section hs) (proj P).continuous .subtypeVal,
    fun _ _ eq ↦ Subtype.ext congr(proj P $eq), isOpen_range_section hs inj⟩

end

theorem isLocalHomeomorphOn_proj (inj : ∀ b ∈ U, IsStalkInj P b) (surj : ∀ b ∈ U, IsStalkSurj P b) :
    IsLocalHomeomorphOn (proj P) (proj P ⁻¹' U.1) :=
  isLocalHomeomorphOn_iff_isOpenEmbedding_restrict.mpr fun x hx ↦
    have ⟨_V, _s, hs, eq⟩ := surj _ hx x.2
    have ho := isOpen_preimage_inter_range_section hs inj
    ⟨_, ho.mem_nhds ⟨hx, _, congr(mk $eq)⟩, (isOpenEmbedding_restrict_proj hs).comp
      (.inclusion inter_subset_right <| ho.preimage continuous_subtype_val)⟩

variable (P) in
/-- A map from a topological space `X` to an étalé space locally agrees with sections if every
point of `X` has a neighborhood on which the map is determined by an admissible section. -/
def LocallyEqSection (f : X → EtaleSpace P) : Prop :=
  ∀ x, ∃ (U : OpenNhds (f x).1) (s : Π b : U.1, F b),
    P s ∧ ∃ V ∈ 𝓝 x, ∀ x' (h' : (f x').1 ∈ U.1), x' ∈ V → s ⟨_, h'⟩ = (f x').2

theorem section_locallyEqSection_iff {P : PrelocalPredicate F} :
    LocallyEqSection P.pred (mk <| s ·) ↔ Sheafify P.pred s := by
  constructor <;> intro h x
  · have ⟨W, t, ht, V, hV, eq⟩ := h x
    have ⟨V', hV', hV, hxV⟩ := mem_nhds_iff.mp hV
    refine ⟨W.1 ⊓ ⟨_, U.2.isOpenMap_subtype_val _ hV⟩,
      ⟨W.2, _, hxV, rfl⟩, Opens.infLERight .. ≫ image_val_subset.hom, ?_⟩
    convert ← P.res (Opens.infLELeft ..) _ ht with ⟨_, hW, x, hxV, rfl⟩
    exact eq _ _ (hV' hxV)
  · have ⟨V, hV, i, hs⟩ := h x
    exact ⟨⟨V, hV⟩, _, hs, _, (V.2.preimage continuous_subtype_val).mem_nhds hV, fun _ _ _ ↦ rfl⟩

theorem continuous_cod {f : X → EtaleSpace P} (cont : Continuous (proj P ∘ f))
    (eq : LocallyEqSection P f) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x ↦
    have ⟨U, s, hs, V, hV, eq⟩ := eq x
    (continuousOn_iff_continuous_restrict.mpr <| ((continuous_section hs).comp
      (f := (⟨_, ·.2.1⟩)) <| (cont.comp continuous_subtype_val).subtype_mk _).congr
        fun x ↦ by exact congr(mk $(eq x x.2.1 x.2.2))).continuousAt
      (Filter.inter_mem (cont.continuousAt.preimage_mem_nhds (U.1.2.mem_nhds U.2)) hV)

theorem continuous_sheafify_section (hs : Sheafify P s) :
    Continuous (fun b ↦ (mk (s b) : EtaleSpace P)) :=
  continuous_cod continuous_subtype_val fun x ↦
    have ⟨V, hV, _, hs⟩ := hs x
    ⟨⟨V, hV⟩, _, hs, _, (V.2.preimage continuous_subtype_val).mem_nhds hV, fun _ _ _ ↦ rfl⟩

theorem continuous_cod_iff_of_opens {f : X → EtaleSpace P}
    (hU : ∀ x, (f x).1 ∈ U) (inj : ∀ b ∈ U, IsStalkInj P b) (surj : ∀ x, IsStalkSurj P (f x).1) :
    Continuous f ↔ Continuous (proj P ∘ f) ∧ LocallyEqSection P f := by
  refine ⟨fun cont ↦ ⟨(proj P).continuous.comp cont, fun x ↦ ?_⟩, fun h ↦ continuous_cod h.1 h.2⟩
  have ⟨U', s, hs, eq⟩ := surj _ (f x).2
  refine ⟨U', s, hs, _, ((isOpen_preimage_inter_range_section hs inj).preimage cont).mem_nhds
    ⟨hU x, _, congr(mk $eq)⟩, fun x hx ⟨_, b, eq⟩ ↦ ?_⟩
  set y := f x with hy; clear_value y
  have : s ⟨y.1, hx⟩ = y.2 := by cases eq; rfl
  cases hy; exact this

theorem continuous_cod_iff {f : X → EtaleSpace P}
    (inj : ∀ b, IsStalkInj P b) (surj : ∀ x, IsStalkSurj P (f x).1) :
    Continuous f ↔ Continuous (proj P ∘ f) ∧ LocallyEqSection P f :=
  continuous_cod_iff_of_opens (fun _ ↦ Opens.mem_top _) (fun _ _ ↦ inj _) surj

theorem continuous_section_iff {P : PrelocalPredicate F}
    (inj : ∀ b ∈ U, IsStalkInj P.pred b) (surj : ∀ b ∈ U, IsStalkSurj P.pred b) :
    Continuous (fun b ↦ (mk (s b) : EtaleSpace P.pred)) ↔ P.sheafify.pred s := by
  rw [continuous_cod_iff_of_opens (·.2) inj fun b : U ↦ surj b b.2,
    and_iff_right (by exact continuous_subtype_val), section_locallyEqSection_iff]
  rfl

section InjSurj

variable (inj : ∀ b, IsStalkInj P b) (surj : ∀ b, IsStalkSurj P b)
include inj surj

theorem isLocalHomeomorph_proj : IsLocalHomeomorph (proj P) :=
  isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun x ↦ have ⟨_U, _s, hs, eq⟩ := surj _ x.2
    ⟨_, (isOpen_range_section hs fun _ _ ↦ inj _).mem_nhds ⟨_, congr(mk $eq)⟩,
      isOpenEmbedding_restrict_proj hs⟩

theorem isOpen_injOn_iff_exists_continuous_section {V : Set (EtaleSpace P)} :
    IsOpen V ∧ V.InjOn (proj P) ↔ letI U := proj P '' V
    IsOpen U ∧ ∃ s : Π b : U, F b, letI sec b : EtaleSpace P := mk (s b)
      Continuous sec ∧ range sec = V := by
  rw [((isLocalHomeomorph_proj inj surj).isOpen_injOn_tfae V).out 0 3 rfl]
  refine and_congr .rfl (.trans ?_ Equiv.piSubtypeEquivSubtypeSigma.exists_congr_left.symm)
  simp_rw [show mk = Sigma.mk _ from rfl, Equiv.mk_piSubtypeEquivSubtypeSigma]
  exact ⟨fun ⟨s, hs, hsV⟩ ↦ ⟨⟨s, hs⟩, s.continuous, hsV⟩, fun ⟨s, hs, hsV⟩ ↦ ⟨⟨s.1, hs⟩, s.2, hsV⟩⟩

theorem isOpen_range_section_iff {U : Set B} {s : Π b : U, F b} :
    letI sec b : EtaleSpace P := mk (s b)
    IsOpen (range sec) ↔ IsOpen U ∧ Continuous sec :=
  (isLocalHomeomorph_proj inj surj).isOpen_range_section_iff U rfl

theorem isOpen_range_section_opens_iff :
    letI sec b : EtaleSpace P := mk (s b)
    IsOpen (range sec) ↔ Continuous sec :=
  (isOpen_range_section_iff inj surj).trans <| and_iff_right U.2

end InjSurj

theorem isTopologicalBasis {P : PrelocalPredicate F}
    (inj : ∀ b, IsStalkInj P.pred b) (surj : ∀ b, IsStalkSurj P.pred b) :
    IsTopologicalBasis {V : Set (EtaleSpace P.pred) |
      ∃ (U : Opens B) (s : Π b : U, F b), P.pred s ∧ V = range (mk <| s ·)} :=
  isTopologicalBasis_of_isOpen_of_nhds
    (by rintro _ ⟨U, s, hs, rfl⟩; exact isOpen_range_section hs fun _ _ ↦ inj _)
      fun ⟨b, x⟩ V hx hV ↦ by
      have ⟨U, s, hs, eq⟩ := surj _ x
      let W : Opens B := ⟨_, U.1.2.isOpenMap_subtype_val _ (isOpen_iff.mp hV _ s hs)⟩
      refine ⟨_, ⟨W, _, P.res image_val_subset.hom s hs, rfl⟩,
        ⟨⟨b, ⟨b, U.2⟩, by rwa [mem_preimage, eq], rfl⟩, congr(mk $eq)⟩, ?_⟩
      rintro _ ⟨⟨_, b, hb, rfl⟩, rfl⟩
      exact hb

end Section

theorem isSeparatedMap_proj (sep : ∀ b, IsSeparated P b) (inj : ∀ b, IsStalkInj P b) :
    IsSeparatedMap (proj P) :=
  fun x y eq ne ↦ by
    have ⟨U, s, t, hs, ht, hsx, hty, ne⟩ := sep (proj P x) x.2 (eq ▸ y.2)
      fun eq2 ↦ ne <| Sigma.ext eq (by simp [eq2])
    refine ⟨_, _, isOpen_range_section hs fun _ _ ↦ inj _, isOpen_range_section ht fun _ _ ↦ inj _,
      ⟨_, congr(mk $hsx)⟩, ⟨_, congr(mk $hty).trans <| Sigma.ext eq <| by simp⟩,
      disjoint_iff_forall_ne.mpr ?_⟩
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩ eq
    cases Subtype.ext congr(proj P $eq)
    exact ne b congr($eq.2)

/-- The adjunction between predicates on sections and topological spaces over a base space. -/
def adjunction {X : Type*} [TopologicalSpace X] {p : X → B} :
    {f : C(EtaleSpace P, X) // p ∘ f = proj P} ≃
    {f : Π b, F b → p ⁻¹' {b} // P ≤ Pullback f (isContinuousSection p).pred} where
  toFun f := ⟨fun _b x ↦ ⟨f.1 (mk x), congr_fun f.2 _⟩,
    fun _U _s hs ↦ f.1.continuous.comp (continuous_section hs)⟩
  invFun f := ⟨⟨fun x ↦ f.1 _ x.2, continuous_dom_iff.mpr f.2⟩, funext fun x ↦ (f.1 _ x.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end EtaleSpace

open EtaleSpace

namespace TrivializationOn

variable {U : Opens B} {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
variable (t : TrivializationOn P U ι) (inj : ∀ b ∈ U, IsStalkInj P b)

/-- The étalé space of a set of sections with a trivialization on `U` evenly covers `U` via
the projection map. -/
noncomputable def homeomorph : proj P ⁻¹' U ≃ₜ U × ι where
  __ := t.equiv
  continuous_toFun := (proj P).continuous.restrictPreimage.prodMk <| continuous_discrete_rng.2 <| by
    convert fun i ↦ (isOpen_range_section (t.pred i) inj).preimage continuous_subtype_val
    exact t.preimage_snd_comp_equiv _
  continuous_invFun := continuous_prod_of_discrete_right.mpr
    fun i ↦ (continuous_section (t.pred i)).subtype_mk _

include t inj in
theorem isEvenlyCovered {b : B} (hb : b ∈ U) : IsEvenlyCovered (proj P) b ι :=
  ⟨‹_›, U, hb, U.2, U.2.preimage (proj P).continuous, t.homeomorph inj, fun _ ↦ rfl⟩

include t inj in
theorem isCoveringMapOn : IsCoveringMapOn (proj P) U :=
  fun _b hb ↦ (t.isEvenlyCovered inj hb).to_isEvenlyCovered_preimage

end TrivializationOn

theorem isCoveringMapOn_of_isLocallyConstant {P : PrelocalPredicate F} {U : Opens B}
    (h : ∀ b ∈ U, IsLocallyConstant P.pred b) : IsCoveringMapOn (proj P.pred) U := fun b hb ↦
  have ⟨V, hVU, hV⟩ := h b hb ⟨U, hb⟩
  let _ : TopologicalSpace (F (⟨b, V.2⟩ : V.1)) := ⊥
  have := discreteTopology_bot
  hV.trivializationOn ⟨b, V.2⟩ |>.isEvenlyCovered
    (fun b hb ↦ (h b <| hVU hb).hasIdentityPrinciple.isStalkInj) V.2 |>.to_isEvenlyCovered_preimage

theorem isCoveringMap_of_isLocallyConstant {P : PrelocalPredicate F}
    (h : ∀ b, IsLocallyConstant P.pred b) : IsCoveringMap (proj P.pred) :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <|
    isCoveringMapOn_of_isLocallyConstant (U := ⊤) fun _ _ ↦ h _

end TopCat

section ContinuousSection

open TopCat

variable {B : TopCat.{u}} {X : Type*} [TopologicalSpace X] {p : X → B}

theorem IsLocallyInjective.isStalkInj (inj : IsLocallyInjective p) (b : B) :
    IsStalkInj (F := (p ⁻¹' {·})) (isContinuousSection p).pred b :=
  PrelocalPredicate.isStalkInj_iff.mpr fun U s t hs ht eq ↦ by
    have ⟨V, hV, hsV, inj⟩ := inj (s ⟨b, U.2⟩)
    refine ⟨⟨⟨_, U.1.2.isOpenMap_subtype_val _ ((hV.preimage hs).inter (hV.preimage ht))⟩,
      ⟨_, ⟨hsV, by apply eq ▸ hsV⟩, rfl⟩⟩, image_val_subset.hom, ?_⟩
    rintro ⟨_, b, h, rfl⟩
    exact Subtype.ext (inj h.1 h.2 <| (s _).2.trans (t _).2.symm)

theorem IsLocalHomeomorph.isStalkSurj (hp : IsLocalHomeomorph p) (b : B) :
    IsStalkSurj (F := (p ⁻¹' {·})) (isContinuousSection p).pred b := by
  rintro ⟨x, rfl⟩
  have ⟨U, hU, s, hs, hxU, eq⟩ := hp.exists_section x
  exact ⟨⟨⟨U, hU⟩, hxU⟩, fun b ↦ ⟨s b, congr_fun hs b⟩, s.continuous, Subtype.ext eq⟩

theorem IsLocalHomeomorph.isSeparated_of_isSeparatedMap (hp : IsLocalHomeomorph p)
    (sep : IsSeparatedMap p) (b : B) :
    IsSeparated (F := (p ⁻¹' {·})) (isContinuousSection p).pred b := by
  rintro ⟨x, eq⟩ ⟨y, rfl⟩ ne
  have ⟨U, V, hU, hV, hxU, hyV, disj⟩ := sep x y eq (Subtype.coe_ne_coe.mpr ne)
  have ⟨U', hU', s, hs, hxU', hsx⟩ := hp.exists_section x
  have ⟨V', hV', t, ht, hxV', hty⟩ := hp.exists_section y
  exact ⟨⟨⟨_, (hU'.isOpenMap_subtype_val _ (hU.preimage s.continuous)).inter
      (hV'.isOpenMap_subtype_val _ (hV.preimage t.continuous))⟩,
    ⟨_, hsx ▸ hxU, by exact eq⟩, _, hty ▸ hyV, rfl⟩,
    fun b ↦ ⟨s ⟨b, image_val_subset b.2.1⟩, congr_fun hs _⟩,
    fun b ↦ ⟨t ⟨b, image_val_subset b.2.2⟩, congr_fun ht _⟩,
    s.continuous.comp (by fun_prop), t.continuous.comp (by fun_prop),
    Subtype.ext ((congr_arg s <| Subtype.ext eq.symm).trans hsx),
    Subtype.ext hty, fun b ↦ Subtype.coe_ne_coe.mp <| disjoint_iff_forall_ne.mp disj
      (mem_of_mem_image_val b.2.1) (mem_of_mem_image_val b.2.2)⟩

end ContinuousSection
