import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence

universe v u
noncomputable section

@[simp]
lemma QuotientGroup.mk'_comp_subtype {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (mk' N).comp N.subtype = 1 := by ext; simp

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R] (S : ShortComplex (ModuleCat.{v} R))

def moduleCatOpcyclesIso : S.opcycles ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  S.opcyclesIsoCokernel ≪≫ ModuleCat.cokernelIsoRangeQuotient _

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem pOpcycles_comp_moduleCatOpcyclesIso_hom :
    S.pOpcycles ≫ S.moduleCatOpcyclesIso.hom = ModuleCat.ofHom (Submodule.mkQ _) := sorry

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem moduleCatOpcyclesIso_inv_comp_fromOpcycles :
    S.moduleCatOpcyclesIso.inv ≫ S.fromOpcycles = ModuleCat.ofHom (Submodule.liftQ _ S.g.hom sorry) := sorry

theorem moduleCat_pOpcycles_eq_iff (x y : S.X₂) :
    S.pOpcycles x = S.pOpcycles y ↔ x - y ∈ LinearMap.range S.f.hom := by
  rw [← Submodule.Quotient.eq]
  constructor
  · intro h
    replace h := congr(S.moduleCatOpcyclesIso.hom $h)
    simp_all
  · intro h
    apply_fun S.moduleCatOpcyclesIso.hom using (ModuleCat.mono_iff_injective _).1 inferInstance
    simp_all

def moduleCatRightHomologyData : S.RightHomologyData where
  Q := ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom)
  H := ModuleCat.of R <| LinearMap.ker
    (Submodule.liftQ (LinearMap.range S.f.hom) S.g.hom sorry)
  p := ModuleCat.ofHom <| Submodule.mkQ _
  ι := ModuleCat.ofHom <| Submodule.subtype _
  wp := sorry
  hp := sorry
  wι := sorry
  hι := sorry

end CategoryTheory.ShortComplex
namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
noncomputable def ofQuotientGroup [IsTrivial (ρ.comp S.subtype)] :
    Representation k (G ⧸ S) V :=
  (QuotientGroup.con S).lift ρ <| by
    rintro x y ⟨⟨z, hz⟩, rfl⟩
    ext w
    have : ρ y (ρ z.unop _) = _ :=
      congr((ρ y) ($(IsTrivial.out (ρ := ρ.comp S.subtype) (⟨z.unop, hz⟩)) w))
    simpa [← LinearMap.mul_apply, ← map_mul] using this

@[simp]
lemma ofQuotientGroup_coe_apply [IsTrivial (ρ.comp S.subtype)] (g : G) (x : V) :
    ofQuotientGroup ρ S (g : G ⧸ S) x = ρ g x :=
  rfl

section QuotientGroup

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
@[simps]
noncomputable def toInvariantsOfNormal :
    Representation k G (invariants (ρ.comp S.subtype)) where
  toFun g := ((ρ g).comp (Submodule.subtype _)).codRestrict _ (fun ⟨x, hx⟩ ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩)))
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

instance wtf : IsTrivial ((toInvariantsOfNormal ρ S).comp S.subtype) where
  out g := LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext <| by
    simpa using (hx g)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
noncomputable abbrev quotientGroupToInvariants :
    Representation k (G ⧸ S) (invariants (ρ.comp S.subtype)) :=
  ofQuotientGroup (toInvariantsOfNormal ρ S) S

@[simp]
lemma mk_ρ_apply_eq_mk (g : G) (x : V) :
    Submodule.Quotient.mk (p := augmentationSubmodule ρ) (ρ g x) = Submodule.Quotient.mk x :=
  (Submodule.Quotient.eq _).2 <| mem_augmentationSubmodule_of_eq g x _ rfl

lemma augmentationSubmodule_eq_comap_ρ_of_normal (g : G) :
    (augmentationSubmodule <| ρ.comp S.subtype).comap (ρ g) =
      augmentationSubmodule (ρ.comp S.subtype) := by
  have H : ∀ g, augmentationSubmodule (ρ.comp S.subtype) ≤
      (augmentationSubmodule <| ρ.comp S.subtype).comap (ρ g) :=
    fun g => Submodule.span_le.2 fun y ⟨⟨s, x⟩, hs⟩ => by
      simpa [← hs] using mem_augmentationSubmodule_of_eq
        ⟨g * s * g⁻¹, Subgroup.Normal.conj_mem ‹_› s.1 s.2 g⟩ (ρ g x) _ <| by simp
  refine le_antisymm ?_ (H g)
  simpa [← Submodule.comap_comp, ← LinearMap.mul_eq_comp, ← map_mul] using
    Submodule.comap_mono (f := ρ g) (H g⁻¹)

lemma mk_ρ_eq_zero_of_normal_iff (g : G) (x : V) :
    Submodule.Quotient.mk (p := augmentationSubmodule (ρ.comp S.subtype)) (ρ g x) = 0 ↔
      Submodule.Quotient.mk (p := augmentationSubmodule (ρ.comp S.subtype)) x = 0 := by
  simp_rw [Submodule.Quotient.mk_eq_zero]
  nth_rw 2 [← augmentationSubmodule_eq_comap_ρ_of_normal ρ S g]
  rfl

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the augmentation submodule of `ρ|_S`. -/
@[simps]
noncomputable def toAugmentationSubmoduleOfNormal :
    Representation k G (augmentationSubmodule <| ρ.comp S.subtype) where
  toFun g := LinearMap.restrict (ρ g) <| le_of_eq
    (augmentationSubmodule_eq_comap_ρ_of_normal ρ S g).symm
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G`-representation on the
coinvariants of `ρ|_S`. -/
@[simps]
noncomputable def toCoinvariantsOfNormal :
    Representation k G (coinvariants (ρ.comp S.subtype)) where
  toFun g := coinvariantsLift (ρ.comp S.subtype) ((augmentationSubmodule _).mkQ ∘ₗ ρ g)
    fun ⟨s, hs⟩ => by
      ext x
      simpa [Submodule.Quotient.eq] using mem_augmentationSubmodule_of_eq
        (ρ := ρ.comp S.subtype) ⟨g * s * g⁻¹, Subgroup.Normal.conj_mem ‹_› s hs g⟩ (ρ g x)
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

instance : IsTrivial ((toCoinvariantsOfNormal ρ S).comp S.subtype) where
  out g := Submodule.linearMap_qext _ <| by
    ext x
    simpa [Submodule.Quotient.eq] using mem_augmentationSubmodule_of_eq g x _ rfl

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
noncomputable abbrev quotientGroupToCoinvariants :
    Representation k (G ⧸ S) (coinvariants (ρ.comp S.subtype)) :=
  ofQuotientGroup (toCoinvariantsOfNormal ρ S) S

end QuotientGroup

end Representation

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

open CategoryTheory
namespace Rep

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
noncomputable abbrev ofQuotientGroup [Representation.IsTrivial (A.ρ.comp S.subtype)] :
    Rep k (G ⧸ S) := Rep.of (A.ρ.ofQuotientGroup S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
abbrev quotientGroupToInvariants (S : Subgroup G) [S.Normal] :=
  Rep.of (A.ρ.quotientGroupToInvariants S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the augmentation submodule of `ρ|_S`. -/
abbrev toAugmentationSubmoduleOfNormal :=
  Rep.of (A.ρ.toAugmentationSubmoduleOfNormal S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G`-representation on the
coinvariants of `ρ|_S`. -/
abbrev toCoinvariantsOfNormal :=
  Rep.of (A.ρ.toCoinvariantsOfNormal S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `A` induces a short exact sequence of
`G`-representations `0 ⟶ (I_S)A ⟶ A ⟶ A_S ⟶ 0` where `(I_S)A` is the submodule of `A`
generated by elements of the form `ρ(s)(x) - x` for `s ∈ S, x ∈ A`. -/
@[simps]
def coinvariantsShortComplex : ShortComplex (Rep k G) where
  X₁ := toAugmentationSubmoduleOfNormal A S
  X₂ := A
  X₃ := toCoinvariantsOfNormal A S
  f := ⟨ModuleCat.ofHom (Submodule.subtype _), fun _ => rfl⟩
  g := ⟨ModuleCat.ofHom (Submodule.mkQ _), fun _ => rfl⟩
  zero := by ext x; exact (Submodule.Quotient.mk_eq_zero _).2 x.2

lemma coinvariantsShortComplex_shortExact : (coinvariantsShortComplex A S).ShortExact where
  exact := (forget₂ _ (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2
      fun x hx => ⟨(⟨x, (Submodule.Quotient.mk_eq_zero _).1 hx⟩ :
      Representation.augmentationSubmodule <| A.ρ.comp S.subtype), rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  epi_g := (Rep.epi_iff_surjective _).2 <| Submodule.mkQ_surjective _

instance : IsTrivial ((Action.res _ S.subtype).obj (A.toCoinvariantsOfNormal S)) where
  out g := Submodule.linearMap_qext _ <| LinearMap.ext fun x => (Submodule.Quotient.eq _).2 <|
    Representation.mem_augmentationSubmodule_of_eq (k := k) g x _ rfl

instance : Representation.IsTrivial (MonoidHom.comp (A.toCoinvariantsOfNormal S).ρ S.subtype) where
  out g := Submodule.linearMap_qext _ <| LinearMap.ext fun x => (Submodule.Quotient.eq _).2 <|
    Representation.mem_augmentationSubmodule_of_eq (k := k) g x _ rfl

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
abbrev quotientGroupToCoinvariants :=
  ofQuotientGroup (toCoinvariantsOfNormal A S) S

end Rep
namespace groupCohomology
open Rep ShortComplex

theorem congr {H : Type u} [Monoid H] {A : Rep k H} {B : Rep k G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : (Action.res _ f₁).obj A ⟶ B} {T : Type*}
    (F : (f : G →* H) → (φ : (Action.res _ f).obj A ⟶ B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

@[simp]
theorem mapOneCocycles_one {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : (Action.res _ 1).obj A ⟶ B) :
    mapOneCocycles 1 φ = 0 := by
  rw [mapOneCocycles, ← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i,
    ShortComplex.cyclesMap'_i]
  refine ModuleCat.hom_ext (LinearMap.ext fun _ ↦ funext fun _ => ?_)
  show _ = 0
  simp [mapShortComplexH1, shortComplexH1]

@[simp]
theorem H1Map_one {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : (Action.res _ 1).obj A ⟶ B) :
    H1Map 1 φ = 0 := by
  simp [← cancel_epi (H1π _)]

@[simps X₁ X₂ X₃ f g]
def H1InfRes₁ (A : Rep k G) (H : Subgroup G) [H.Normal] :
     ShortComplex (ModuleCat k) where
  X₁ := H1 (A.quotientGroupToInvariants H)
  X₂ := H1 A
  X₃ := H1 ((Action.res _ H.subtype).obj A)
  f := H1Map (QuotientGroup.mk' H) ⟨ModuleCat.ofHom (Submodule.subtype _), fun _ => rfl⟩
  g := H1Map H.subtype (𝟙 _)
  zero := by rw [← H1Map_comp, Category.comp_id,
    congr (QuotientGroup.mk'_comp_subtype H) H1Map, H1Map_one]

@[simp]
lemma _root_.QuotientGroup.coe_subtype {G : Type*} [Group G] {S : Subgroup G} [S.Normal]
    (x : S) : (x : G ⧸ S) = 1 := by simp

instance : Mono (H1InfRes₁ A S).f := by
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro x hx
  induction' x using Quotient.inductionOn' with x
  simp_all only [H1InfRes₁_X₂, H1InfRes₁_X₁, H1InfRes₁_f, Submodule.Quotient.mk''_eq_mk,
    H1π_comp_H1Map_apply (QuotientGroup.mk' S), Submodule.Quotient.mk_eq_zero]
  rcases hx with ⟨y, hy⟩
  refine ⟨⟨y, fun s => ?_⟩, Subtype.ext <| funext fun g => Quotient.inductionOn' g
    fun g => Subtype.ext <| congr_fun (Subtype.ext_iff.1 hy) g⟩
  replace hy := congr_fun (Subtype.ext_iff.1 hy) s.1
  simp_all [sub_eq_zero, shortComplexH1, moduleCatToCycles]

instance : (H1InfRes₁ A S).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x
  refine Quotient.inductionOn' x fun x hx => ?_
  simp_all only [H1InfRes₁_X₂, H1InfRes₁_X₃, H1InfRes₁_g, Submodule.Quotient.mk''_eq_mk,
    LinearMap.mem_ker, H1π_comp_H1Map_apply S.subtype, Submodule.Quotient.mk_eq_zero,
    H1InfRes₁_X₁, H1InfRes₁_f]
  rcases hx with ⟨y, hy⟩
  have h1 := (mem_oneCocycles_iff x.1).1 x.2
  have h2 : ∀ s ∈ S, x.1 s = (A.ρ s y - · : A → A) y :=
    fun s hs  => (groupCohomology.oneCocycles_ext_iff.1 hy ⟨s, hs⟩).symm
  refine ⟨H1π _ ⟨fun g => Quotient.liftOn' g
    (fun g => ⟨(x.1 g - A.ρ g y + · : A → A) y, ?_⟩) ?_, ?_⟩, ?_⟩
  · intro s
    simp_all only [MonoidHom.coe_comp, Subgroup.coeSubtype, Function.comp_apply, map_add, map_sub]
    rw [eq_add_of_sub_eq (h2 s s.2).symm, eq_sub_of_add_eq (h1 s g).symm,
      eq_sub_of_add_eq' (h1 g (g⁻¹ * s * g)).symm,
      h2 (g⁻¹ * s * g) (Subgroup.Normal.conj_mem' ‹_› _ s.2 _)]
    simp only [mul_assoc, mul_inv_cancel_left, map_mul, LinearMap.mul_apply, map_sub,
      Representation.ρ_self_inv_apply]
    abel
  · intro g h hgh
    have := congr(A.ρ g $(h2 (g⁻¹ * h) <| QuotientGroup.leftRel_apply.1 hgh))
    rw [h1] at this
    simp_all [← sub_eq_add_neg, sub_eq_sub_iff_sub_eq_sub]
  · rw [mem_oneCocycles_iff]
    intro g h
    induction' g using QuotientGroup.induction_on with g
    induction' h using QuotientGroup.induction_on with h
    apply Subtype.ext
    simp [-oneCocycles.val_eq_coe, coe_of, ← QuotientGroup.mk_mul, h1 g h, sub_add_eq_add_sub,
      add_assoc]
  · symm
    simp only [ModuleCat.hom_ofHom, oneCocycles.val_eq_coe, Submodule.mkQ_apply,
      H1π_comp_H1Map_apply, Submodule.Quotient.eq, LinearMap.mem_range]
    use y
    simp_rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', sub_add]
    rfl -- I can't seem to close this without abusing defeq rn

end groupCohomology
namespace groupHomology
open Rep ShortComplex

noncomputable section
open Representation hiding leftRegular
open CategoryTheory groupHomology Rep Finsupp Limits Finset

variable [DecidableEq G]

section NotMap

theorem congr {H : Type u} [Monoid H] {A : Rep k G} {B : Rep k H}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : A ⟶ (Action.res _ f₁).obj B} {T : Type*}
    (F : (f : G →* H) → (φ : A ⟶ (Action.res _ f).obj B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

lemma Representation.ρ_eq_of_coe_eq_of_comp_subtype_isTrivial {k G V : Type*} [CommRing k]
    [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (S : Subgroup G) [IsTrivial (ρ.comp S.subtype)] (g h : G) (hgh : (g : G ⧸ S) = h) :
    ρ g = ρ h := by
  ext x
  apply (Representation.ρ_apply_bijective ρ g⁻¹).1
  simpa [← LinearMap.mul_apply, ← map_mul, -isTrivial_def] using
    (congr($(isTrivial_def (ρ.comp S.subtype) ⟨g⁻¹ * h, QuotientGroup.eq.1 hgh⟩) x)).symm

omit [DecidableEq G] [S.Normal] in
lemma ρ_eq_of_coe_eq_of_comp_subtype_isTrivial
    [IsTrivial (A.ρ.comp S.subtype)] (g h : G) (hgh : (g : G ⧸ S) = h) :
    A.ρ g = A.ρ h := by
  ext x
  apply (Representation.ρ_apply_bijective A.ρ g⁻¹).1
  simpa [← LinearMap.mul_apply, ← map_mul, -isTrivial_def] using
    (congr($(isTrivial_def (A.ρ.comp S.subtype) ⟨g⁻¹ * h, QuotientGroup.eq.1 hgh⟩) x)).symm

def augmentationSubmoduleToFinsupp {k G V : Type*} [CommRing k]
    [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (x : augmentationSubmodule ρ) :
    G →₀ V :=
  let T := Classical.choose <| Finsupp.mem_span_range_iff_exists_finsupp.1 x.2
  mapRange.linearMap (R := k) (linearCombination k id) <|
    lmapDomain _ k (fun g => g⁻¹) T.curry

omit [DecidableEq G] in
theorem dZero_augmentationSubmoduleToFinsupp
    (x : augmentationSubmodule A.ρ) :
    dZero A (augmentationSubmoduleToFinsupp A.ρ x) = x.1 := by
  unfold augmentationSubmoduleToFinsupp dZero linearCombination
  have hT := Classical.choose_spec <| Finsupp.mem_span_range_iff_exists_finsupp.1 x.2
  set T := Classical.choose <| Finsupp.mem_span_range_iff_exists_finsupp.1 x.2
  simp [sum_mapRange_index, map_finsupp_sum, sum_mapDomain_index_inj inv_injective,
    sum_curry_index, add_smul, ← hT, sum_sub, smul_sub]

@[simps]
def toResMkOfQuotientGroup [IsTrivial (A.ρ.comp S.subtype)] :
    A ⟶ (Action.res _ (QuotientGroup.mk' S)).obj (A.ofQuotientGroup S) where
  hom := 𝟙 _
  comm _ := rfl

@[simp]
lemma H1Map_one {G H : Type u} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
    {A : Rep k G} {B : Rep k H} (φ : A ⟶ (Action.res _ (1 : G →* H)).obj B) :
    H1Map (1 : G →* H) φ = 0 := by
  simp only [← cancel_epi (H1π A), H1π_comp_H1Map, Limits.comp_zero]
  ext x
  refine (H1π_eq_zero_iff _).2 ?_
  show Subtype.val ((ConcreteCategory.hom (mapOneCycles 1 φ)) x) ∈ _
  simp
  rw [← mapDomain_mapRange]
  apply Submodule.finsupp_sum_mem
  · intros
    exact single_one_mem_oneBoundaries _
  · simp

@[simps]
def coinvariantsMkQHom : A ⟶ toCoinvariantsOfNormal A S where
  hom := ModuleCat.ofHom <| Submodule.mkQ _

@[simps]
def resCoinvariantsMkQHom :
    A ⟶ (Action.res _ (QuotientGroup.mk' S)).obj (Rep.quotientGroupToCoinvariants A S) where
  hom := ModuleCat.ofHom <| Submodule.mkQ _

abbrev corestriction₁ :
    H1 ((Action.res _ S.subtype).obj A) ⟶ H1 A := H1Map S.subtype (𝟙 _)

abbrev coinflation₁ [DecidableEq (G ⧸ S)] :
    H1 A ⟶ H1 (quotientGroupToCoinvariants A S) :=
  H1Map (QuotientGroup.mk' S) (resCoinvariantsMkQHom A S)

@[simps X₁ X₂ X₃ f g]
def corestrictionCoinflation₁ [DecidableEq (G ⧸ S)] :
    ShortComplex (ModuleCat k) where
  X₁ := H1 ((Action.res _ S.subtype).obj A)
  X₂ := H1 A
  X₃ := H1 (quotientGroupToCoinvariants A S)
  f := corestriction₁ A S
  g := coinflation₁ A S
  zero := by rw [← H1Map_comp, congr (QuotientGroup.mk'_comp_subtype S) H1Map, H1Map_one]

@[simps X₁ X₂ X₃ f g]
def H1ResToOfQuotientGroup [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    ShortComplex (ModuleCat k) where
  X₁ := H1 ((Action.res _ S.subtype).obj A)
  X₂ := H1 A
  X₃ := H1 (ofQuotientGroup A S)
  f := corestriction₁ A S
  g := H1Map (QuotientGroup.mk' S) <| toResMkOfQuotientGroup A S
  zero := by rw [← H1Map_comp, congr (QuotientGroup.mk'_comp_subtype S) H1Map, H1Map_one]

instance mapOneCycles_toResMkOfQuotientGroup_epi
    [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    Epi (mapOneCycles (QuotientGroup.mk' S) (toResMkOfQuotientGroup A S)) := by
  rw [ModuleCat.epi_iff_surjective]
  rintro ⟨x, hx⟩
  choose! s hs using QuotientGroup.mk_surjective (s := S)
  have hs₁ : QuotientGroup.mk ∘ s = id := funext hs
  refine ⟨⟨mapDomain s x, ?_⟩, Subtype.ext <| by
    simp_all [mapOneCycles_comp_subtype_apply, ← mapDomain_comp]⟩
  simpa [ModuleCat.of_coe, mem_oneCycles_iff, of_ρ, ← (mem_oneCycles_iff _).1 hx,
      sum_mapDomain_index_inj (f := s) (fun x y h => by rw [← hs x, ← hs y, h])]
    using Finsupp.sum_congr fun a b => QuotientGroup.induction_on a fun a => by
      simp [← QuotientGroup.mk_inv, ρ_eq_of_coe_eq_of_comp_subtype_isTrivial A S (s a)⁻¹ a⁻¹
        (by simp [hs])]

instance H1Map_toResMkOfQuotientGroup_epi [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    Epi (H1Map (QuotientGroup.mk' S) (toResMkOfQuotientGroup A S)) := by
  convert epi_of_epi (H1π A) _
  rw [H1π_comp_H1Map]
  exact @epi_comp _ _ _ _ _ _ (mapOneCycles_toResMkOfQuotientGroup_epi A S) (H1π _) inferInstance

instance H1ResToOfQuotientGroup_g_epi
    [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    Epi (H1ResToOfQuotientGroup A S).g :=
  inferInstanceAs <| Epi (H1Map _ _)

theorem H1ResToOfQuotientGroup_exact [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    (H1ResToOfQuotientGroup A S).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
/- Denote `C(i) : C(S, A) ⟶ C(G, A), C(π) : C(G, A) ⟶ C(G ⧸ S, A)`. -/
/- Let `x : Z₁(G, A)` map to 0 in `H₁(G ⧸ S, A)`. -/
  induction' x using Quotient.inductionOn' with x
  rcases x with ⟨(x : G →₀ A), (hxc : x ∈ oneCycles A)⟩
  simp_all only [H1ResToOfQuotientGroup_X₂, H1ResToOfQuotientGroup_X₃, H1ResToOfQuotientGroup_g,
    Submodule.Quotient.mk''_eq_mk, LinearMap.mem_ker, H1π_comp_H1Map_apply (QuotientGroup.mk' S)
    (toResMkOfQuotientGroup A S)]
/- Choose `y := ∑ y(σ, τ)·(σ, τ) ∈ C₂(G ⧸ S, A)` such that `C₁(π)(x) = d(y)`. -/
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
/- Let `s : G ⧸ S → G` be a section of the quotient map. -/
  choose! s hs using QuotientGroup.mk'_surjective S
  have hs₁ : QuotientGroup.mk (s := S) ∘ s = id := funext hs
  have hs₂ : s.Injective := fun x y hxy => by rw [← hs x, ← hs y, hxy]
/- Let `z := ∑ y(σ, τ)·(s(σ), s(τ))`. -/
  let z : G × G →₀ A := lmapDomain _ k (Prod.map s s) y
/- We have that `C₂(π)(z) = y`: -/
  have hz : lmapDomain _ k (QuotientGroup.mk' S) (dOne A z) = dOne (A.ofQuotientGroup S) y := by
    have := congr($((mapShortComplexH1 (QuotientGroup.mk' S)
      (toResMkOfQuotientGroup A S)).comm₁₂.symm) z)
    simp_all [shortComplexH1, toResMkOfQuotientGroup, z, ← mapDomain_comp, Prod.map_comp_map]
  let v := x - dOne _ z
/- We have `C₁(s ∘ π)(v) = ∑ v(g)·s(π(g)) = 0`, since `C₁(π)(v) = dC₁(π)(z) - C₁(π)(dz) = 0` by
  previous assumptions. -/
  have hv : mapDomain (s ∘ QuotientGroup.mk) v = 0 := by
    rw [mapDomain_comp]
    simp_all [v, mapDomain, sum_sub_index]
/- The map sending `g ↦ (s(π(g)), s(π(g))⁻¹g)`. -/
  let e : G → G × G := fun (g : G) => (s (g : G ⧸ S), (s (g : G ⧸ S))⁻¹ * g)
  have he : e.Injective := fun x y hxy => by
    obtain ⟨(h₁ : s _ = s _), (h₂ : _ * _ = _ * _)⟩ := Prod.ext_iff.1 hxy
    exact (mul_right_inj _).1 (h₁ ▸ h₂)
/- Let `ve := ∑ v(g)·(s(π(g)), s(π(g))⁻¹g)`. -/
  let ve : G × G →₀ A := mapDomain e v
  have hS : (v + dOne _ ve).support.toSet ⊆ S := by
  /- We have `d(ve) = ∑ ρ(s(π(g))⁻¹)(v(g))·s(π(g))⁻¹g - ∑ v(g)·g + ∑ v(g)·s(π(g))`.
    The second sum is `v`, so cancels: -/
    simp only [dOne, coe_lsum, he, ve, sum_mapDomain_index_inj, mul_inv_cancel_left,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      lsingle_apply, sum_add, sum_sub, sum_single, ← add_assoc, add_sub_cancel, e]
    intro w hw
    · obtain (hl | hr) := Finset.mem_union.1 (support_add hw)
    /- The first sum clearly has support in `S`: -/
      · obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 (support_sum hl)
        apply support_single_subset at ht
        simp_all [← QuotientGroup.eq, hs]
    /- The third sum is 0, by `hv`. -/
      · simp_all [mapDomain]
  /- Now `(v + d(ve))|_S` has support in `S` and agrees with `x` in `H₁(G, A)`: -/
  use H1π _ ⟨comapDomain Subtype.val (v + dOne _ ve) <|
    Set.injOn_of_injective Subtype.val_injective, ?_⟩
  · simp only [H1ResToOfQuotientGroup_X₁, H1ResToOfQuotientGroup_f, Action.res_obj_V,
      ModuleCat.hom_ofHom, Submodule.mkQ_apply, H1π_comp_H1Map_apply]
    refine (H1π_eq_iff _ _).2 ?_
    /- Indeed, `(v + d(ve))|_S` is just `v + d(ve)` by `hS`, and
    `v + d(ve) - x = d(ve - z) ∈ B₁(G, A)`, since `v := x - dz`. -/
    use ve - z
    have := mapOneCycles_comp_subtype_apply (B := A) S.subtype (𝟙 _)
    have := mapDomain_comapDomain (α := S) Subtype.val Subtype.val_injective
      (v + dOne A ve) (fun x hx => ⟨⟨x, hS hx⟩, rfl⟩)
    simp_all [-mapOneCycles_comp_subtype_apply, v, add_sub_assoc, sub_add_sub_cancel']
    /- And `v + d(ve) := x - dz + d(ve)` is a 1-cycle because `x` is. -/
  · have : v + dOne _ ve ∈ oneCycles A := Submodule.add_mem _
      (Submodule.sub_mem _ hxc <| dOne_apply_mem_oneCycles _) (dOne_apply_mem_oneCycles _)
    rw [mem_oneCycles_iff] at this ⊢
    rwa [← sum_comapDomain, ← sum_comapDomain (g := fun _ a => a)] at this <;>
    exact ⟨Set.mapsTo_preimage _ _, Set.injOn_of_injective Subtype.val_injective,
      fun x hx => ⟨⟨x, hS hx⟩, hx, rfl⟩⟩

set_option maxHeartbeats 320000
/-- The image of `C₁(G, ℐ(S)A)` in `C₁(G, A)⧸B₁(G, A)` is contained in the image of `C₁(S, A)`. -/
theorem a_long_name :
    Submodule.comap ((mapShortComplexH1 (MonoidHom.id G) (coinvariantsShortComplex A S).f).τ₂ ≫
      (shortComplexH1 _).pOpcycles).hom (LinearMap.range ((mapShortComplexH1 S.subtype (𝟙 _)).τ₂ ≫
      (shortComplexH1 _).pOpcycles).hom) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  choose! t ht using fun i : augmentationSubmodule (A.ρ.comp S.subtype) =>
    Finsupp.mem_span_range_iff_exists_finsupp.1 i.2
  let t' := fun i => (t i).curry
/- Let `x = ∑ xᵢ·gᵢ ∈ C₁(G, ℐ(S)A)` and choose representatives `∑ rᵢⱼ(ρ(sᵢⱼ)(aᵢⱼ - aᵢⱼ)` for
`rᵢⱼ ∈ k, sᵢⱼ ∈ S, aᵢⱼ ∈ A` for each `xᵢ`. -/
  let T : G →₀ S →₀ A →₀ k := (mapRange (fun i => t' i - t' 0) (sub_self _) x)
/- Prove that `x = ∑(∑ rᵢⱼ(ρ(sᵢⱼ)(aᵢⱼ) - aᵢⱼ)·gᵢ`: -/
  have : x = T.sum fun a b => single a ((linearCombination k (fun (y : S × A) =>
      (⟨A.ρ.comp S.subtype y.1 y.2 - y.2, mem_augmentationSubmodule_of_eq y.1 y.2 _ rfl⟩)) ∘ₗ
      (finsuppProdLEquiv k).symm.toLinearMap) b) := by
    apply_fun mapRange.linearMap (Submodule.subtype _) using
      mapRange_injective Subtype.val rfl Subtype.val_injective
    rw [← sum_single x]
    simp only [map_finsupp_sum, mapRange.linearMap_apply, mapRange_single, LinearMap.coe_comp,
      map_sub, map_zero, LinearEquiv.coe_coe, Function.comp_apply, single_zero, implies_true,
      sum_mapRange_index, T]
    simp only [linearCombination_apply, finsuppProdLEquiv, finsuppProdEquiv,
      LinearEquiv.coe_symm_mk, Finsupp.uncurry, single_zero, implies_true, single_add,
      sum_curry_index, map_finsupp_sum, t']
    simp_all
/- Define `Y : C₁(S, A)` to be `∑ rᵢⱼρ(gᵢ⁻¹)(aᵢⱼ)·gᵢ⁻¹sᵢⱼ⁻¹gᵢ - ∑ rᵢⱼaᵢⱼ·sᵢⱼ⁻¹`. -/
  let Y : S →₀ A := sum T fun g x => mapRange.linearMap (linearCombination k (A.ρ g⁻¹))
      (lmapDomain _ k (fun s => MulAut.conjNormal g⁻¹ s⁻¹) x) -
    mapRange.linearMap (linearCombination k id) (lmapDomain _ k (fun s => s⁻¹) x)
/- Define `Z : C₂(G, A)` to be `∑ rᵢⱼaᵢⱼ·(gᵢ, gᵢ⁻¹sᵢⱼ⁻¹gᵢ) - ∑ rᵢⱼaᵢⱼ·(sᵢⱼ⁻¹, gᵢ)`. -/
  let Z : G × G →₀ A := sum T fun g x => mapRange.linearMap (linearCombination k id)
      (lmapDomain _ k (fun s => (g, g⁻¹ * s.1⁻¹ * g)) x) -
    mapRange.linearMap (linearCombination k id) (lmapDomain _ k (fun s => (s.1⁻¹, g)) x)
  use Y
  apply (moduleCat_pOpcycles_eq_iff _ _ _).2 ⟨Z, ?_⟩
  show (dOne A) Z = mapRange id rfl (lmapDomain _ k Subtype.val Y) -
    mapRange.linearMap (Submodule.subtype _) (mapDomain id x)
/- Then a computation shows that `dZ = Y - x` as required. -/
  simp only [mapRange_id, mapDomain_id, sum_sub, linearCombination, map_finsupp_sum,
    lmapDomain_apply, mapDomain, single_sum, mapRange.linearMap_apply, coe_lsum,
    LinearMap.coe_smulRight, mapRange_single, map_sub, this, sum_single_index, Function.comp_apply,
    finsuppProdLEquiv, finsuppProdEquiv, Finsupp.uncurry, LinearMap.coe_comp, SetLike.mk_smul_mk,
    LinearEquiv.coe_coe, LinearEquiv.coe_symm_mk, dOne, map_zero, LinearMap.add_apply,
    LinearMap.sub_apply, sum_add, Y, Z]
  simpa [smul_sub, sub_add_eq_add_sub, sub_sub_sub_eq, sum_sum_index, sum_add_index', add_smul,
    sub_smul, smul_add, smul_sub, mul_assoc] using add_comm _ _
-- ^ this simpa is to blame for the heartbeat bump... I'll squeeze it if I must

instance {k G V : Type u} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) [IsTrivial ρ] : IsTrivial (Rep.of ρ).ρ where

instance : Representation.IsTrivial ((A.toCoinvariantsOfNormal S).ρ.comp S.subtype) where
  out g := Submodule.linearMap_qext _ <| LinearMap.ext fun _ => by simp

@[elab_as_elim]
theorem H1_induction_on {C : H1 A → Prop}
    (h : ∀ x : oneCycles A, C (Submodule.Quotient.mk x)) (x : H1 A) :
    C x := Quotient.inductionOn' x h

instance [DecidableEq (G ⧸ S)] : (corestrictionCoinflation₁ A S).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction' x using H1_induction_on with x
/- Let `x : Z₁(G, A)` map to 0 in `H₁(G, ⧸ S, A_S)`. -/
  simp only [corestrictionCoinflation₁_X₂, corestrictionCoinflation₁_X₃, LinearMap.mem_ker,
    corestrictionCoinflation₁_g, H1π_comp_H1Map_apply (QuotientGroup.mk' S)] at hx
/- Pick `y : C₂(G ⧸ S, A_S)` such that `d(y)` agrees with `Z₁(π, π)(x) : Z₁(G ⧸ S, A_S)`. -/
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
/- Then `Z₁(π, Id)(π) : Z₁(G, A_S)` maps to 0 in `H₁(G ⧸ S, A_S)`, so since `S` acts trivially on
`A_S`, we can choose `z : Z₁(S, A_S)` with the same homology class as `Z₁(π, Id)(π)` in
`H₁(G, A_S)`. -/
  rcases @(ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (H1ResToOfQuotientGroup_exact (toCoinvariantsOfNormal A S) S)
    (H1π _ <| mapOneCycles (MonoidHom.id G) (coinvariantsMkQHom A S) x) (by
      simpa [H1π_comp_H1Map_apply (QuotientGroup.mk' S), ← ConcreteCategory.comp_apply,
        ← cyclesMap'_comp, ← mapShortComplexH1_comp, congr (MonoidHom.comp_id _) mapShortComplexH1,
        -Submodule.Quotient.mk_eq_zero] using hx) with ⟨z, hz⟩
  induction' z using H1_induction_on with z
  simp [H1ResToOfQuotientGroup_X₂, H1ResToOfQuotientGroup_X₁,
    H1π_comp_H1Map_apply S.subtype] at hz
/- Choose `w : C₂(G, A_S)` such that `d(w) = Z₁(i, Id)(z) - Z₁(Id, π)(x)`. -/
  rcases (H1π_eq_iff _ _).1 hz with ⟨w, hzw⟩
/- Choose `Z : C₁(S, A)` mapping to `z`, and `W : C₂(G, A)` mapping to `w`. -/
  rcases mapRange_surjective (coinvariantsMkQ _) (map_zero _)
    (Submodule.Quotient.mk_surjective _) z.1 with ⟨Z, hZ⟩
  rcases mapRange_surjective (coinvariantsMkQ _) (map_zero _)
    (Submodule.Quotient.mk_surjective _) w with ⟨W, hW⟩
/- Let `b : C₁(G, A)` denote `x + d(W) - C₁(i, Id)(z)`. -/
  let b : G →₀ A := (x.1 : G →₀ A) + dOne A W - lmapDomain _ k S.subtype Z
/- Then `b` has coefficients in `ℐ(S)A`, since `C₁(Id, π)(b) = 0`. -/
  have hb : ∀ g, b g ∈ augmentationSubmodule (A.ρ.comp S.subtype) :=
    fun g => (Submodule.Quotient.eq _).1 <| by
      show mapRange.linearMap (coinvariantsMkQ _) _ _ = mapRange.linearMap (coinvariantsMkQ _) _ _
      have := Finsupp.ext_iff.1 (congr($((mapShortComplexH1 (B := toCoinvariantsOfNormal A S)
        (MonoidHom.id G) (coinvariantsMkQHom A S)).comm₁₂.symm) W)) g
      simpa [← mapDomain_mapRange, hZ, shortComplexH1, hW, hzw, eq_sub_iff_add_eq',
        mapOneCycles_comp_subtype_apply (B := toCoinvariantsOfNormal A S)] using this
/- Let `β` be `b` considered as an element of `C₁(G, ℐ(S)(A))`, so that `C₁(Id, i)(β) = b`. -/
  let β : G →₀ augmentationSubmodule (A.ρ.comp S.subtype) :=
    mapRange (Function.invFun <| (augmentationSubmodule (A.ρ.comp S.subtype)).subtype)
    (Function.leftInverse_invFun Subtype.val_injective (0 : augmentationSubmodule _)) b
  have hβb : mapRange Subtype.val rfl β = b := Finsupp.ext fun g => Subtype.ext_iff.1 <|
    Function.leftInverse_invFun Subtype.val_injective ⟨b g, hb g⟩
/- Then, since the image of `C₁(G, ℐ(S)A)` in `C₁(G, A)⧸B₁(G, A)` is contained in the image of
`C₁(S, A)`, we can choose `α : C₁(S, A)`, `δ : C₂(G, A)` such that
`d(δ) = Z₁(i, Id)(α) - Z₁(Id, i)(β)`. -/
  rcases eq_top_iff.1 (a_long_name A S) (by trivial : β ∈ ⊤) with ⟨(α : S →₀ A), hα⟩
  dsimp only [ModuleCat.hom_comp] at hα
  rcases (moduleCat_pOpcycles_eq_iff _ _ _).1 hα with ⟨(δ : G × G →₀ A), hβ⟩
/- Then by assumption, `d(W + δ) = C₁(i, Id)(α + Z) - x`. -/
  have hαZ : dOne A (W + δ) = mapDomain Subtype.val (α + Z) - x := by
    simp_all [shortComplexH1, mapDomain_add, b, ← hβ, ← sub_add, sub_add_eq_add_sub, ← sub_sub,
      add_sub_cancel]
/- So we claim that `α + Z` is an element of `Z₁(S, A)` which differs from `x` by a boundary in
`Z₁(G, A)`. -/
  use H1π _ ⟨α + Z, ?_⟩
/- Indeed, by `hαZ`, `d(W + δ)` is the desired boundary: -/
  · simp only [corestrictionCoinflation₁_X₂, corestrictionCoinflation₁_X₁, Submodule.mkQ_apply,
      corestrictionCoinflation₁_f, ModuleCat.hom_ofHom, H1π_comp_H1Map_apply, b]
    refine (H1π_eq_iff _ _).2 ⟨W + δ, ?_⟩
    have := mapOneCycles_comp_subtype_apply (B := A) S.subtype (𝟙 _)
    simp_all [hαZ]
/- And `α + Z` is a cycle, since `d(W + δ) + x` is. -/
  · rw [mem_oneCycles_iff]
    have : x + dOne A (W + δ) ∈ oneCycles A := Submodule.add_mem _ x.2 (dOne_apply_mem_oneCycles _)
    rwa [eq_sub_iff_add_eq'.1 hαZ, mem_oneCycles_iff, sum_mapDomain_index_inj
      Subtype.val_injective, sum_mapDomain_index_inj Subtype.val_injective] at this


@[simp]
lemma _root_.Rep.res_obj_ρ {H : Type u} [Monoid H] (f : G →* H) (A : Rep k H) (g : G) :
    DFunLike.coe (F := G →* (A →ₗ[k] A)) (ρ ((Action.res _ f).obj A)) g = A.ρ (f g) := rfl


instance mapOneCycles_mk'_id_epi [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    Epi (mapOneCycles (B := A.ofQuotientGroup S) (QuotientGroup.mk' S) (𝟙 _)) := by
  rw [ModuleCat.epi_iff_surjective]
  rintro ⟨x, hx⟩
  choose! s hs using QuotientGroup.mk_surjective (s := S)
  refine ⟨⟨mapDomain s x, ?_⟩, Subtype.ext ?_⟩
  · simp_all [mem_oneCycles_iff, sum_mapDomain_index_inj (f := s)
      (fun x y h => by rw [← hs x, ← hs y, h]), Rep.res_obj_ρ]
  · rw [mapOneCycles_comp_subtype_apply]
    simp_all [mapDomain, sum_sum_index]

instance H1Map_mk'_id_epi [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    Epi (H1Map (QuotientGroup.mk' S) (𝟙 (Action.res (ModuleCat k) (QuotientGroup.mk' S)).obj
      (A.ofQuotientGroup S))) := by
  convert epi_of_epi (H1π A) _
  rw [H1π_comp_H1Map]
  exact @epi_comp _ _ _ _ _ _ (mapOneCycles_mk'_id_epi A S) (H1π _) inferInstance

instance [DecidableEq (G ⧸ S)] :
    Epi (coinflation₁ A S) := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  induction' x using Quotient.inductionOn' with x
  rcases (ModuleCat.epi_iff_surjective _).1
    (mapOneCycles_mk'_id_epi (A.toCoinvariantsOfNormal S) S) x with ⟨⟨y, hdy⟩, hy⟩
  rcases mapRange_surjective _ (map_zero _) (Submodule.mkQ_surjective
    (augmentationSubmodule (A.ρ.comp S.subtype))) y with ⟨Y, hY⟩
  have hdY : coinvariantsMkQ _ (dZero _ Y) =
      dZero (A.toCoinvariantsOfNormal S) (mapRange (Submodule.mkQ _) (map_zero _) Y) := by
    simp [dZero, map_finsupp_sum, sum_mapRange_index]
  have : dZero _ Y ∈ augmentationSubmodule (A.ρ.comp S.subtype) := by
    simp only [← Submodule.Quotient.mk_eq_zero, Submodule.mkQ_apply,
      mapRange.linearMap_apply] at hdY ⊢
    simpa [hdY, hY] using hdy
  have H : dZero A (Y - mapDomain S.subtype
      (augmentationSubmoduleToFinsupp _ ⟨dZero _ Y, this⟩)) = 0 := by
    rw [map_sub, sub_eq_zero]
    refine (dZero_augmentationSubmoduleToFinsupp (Rep.of <| A.ρ.comp S.subtype)
      ⟨dZero A Y, this⟩).symm.trans ?_
    simp [- LinearMap.sub_apply, dZero, sum_mapDomain_index_inj, Subtype.val_injective]
  use H1π A ⟨Y - mapDomain S.subtype (augmentationSubmoduleToFinsupp _ ⟨dZero _ Y, this⟩), H⟩
  show (H1π A ≫ H1Map _ _) _ = _
  rw [H1π_comp_H1Map]
  refine (H1π_eq_iff _ _).2 ?_
  sorry
/-
  rw [← hy, mapOneCycles_comp_subtype_apply, coe_mapOneCycles, fOne, map_sub, sub_sub, add_comm, ← sub_sub]
  convert Submodule.sub_mem _ (Submodule.zero_mem _) _
  · simp [fOne, moduleCat_simps, hY, ← mapDomain_mapRange]
  · simpa [← mapDomain_comp, ← mapDomain_mapRange, Function.comp_def,
      (QuotientGroup.eq_one_iff _).2 (Subtype.prop _)]
      using Submodule.finsupp_sum_mem _ _ _ (fun _ _ => single_one_mem_oneBoundaries _)
-/

end groupHomology
