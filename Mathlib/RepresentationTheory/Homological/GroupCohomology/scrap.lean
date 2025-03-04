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

/-- Given a short complex `S` of modules, this is the isomorphism between the abstract `S.opcycles`
of the homology API and the more concrete description as `S.X₂ ⧸ LinearMap.range S.f.hom`. -/
def moduleCatOpcyclesIso : S.opcycles ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  S.opcyclesIsoCokernel ≪≫ ModuleCat.cokernelIsoRangeQuotient _

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem pOpcycles_comp_moduleCatOpcyclesIso_hom :
    S.pOpcycles ≫ S.moduleCatOpcyclesIso.hom = ModuleCat.ofHom (Submodule.mkQ _) := by
  simp [moduleCatOpcyclesIso]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem moduleCatOpcyclesIso_inv_comp_fromOpcycles :
    S.moduleCatOpcyclesIso.inv ≫ S.fromOpcycles = ModuleCat.ofHom (Submodule.liftQ
      (LinearMap.range S.f.hom) S.g.hom <|
      LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.1 S.zero) := by
  have : Epi (ModuleCat.ofHom <| Submodule.mkQ (LinearMap.range S.f.hom)) :=
    (ModuleCat.epi_iff_surjective _).2 <| Submodule.Quotient.mk_surjective _
  simp only [← cancel_epi (ModuleCat.ofHom <| Submodule.mkQ <| LinearMap.range S.f.hom),
    moduleCatOpcyclesIso, Iso.trans_inv, ← Category.assoc]
  simp [← ModuleCat.ofHom_comp, Submodule.liftQ_mkQ]

theorem moduleCat_pOpcycles_eq_iff (x y : S.X₂) :
    S.pOpcycles x = S.pOpcycles y ↔ x - y ∈ LinearMap.range S.f.hom :=
  Iff.trans ⟨fun h => by simpa using congr(S.moduleCatOpcyclesIso.hom $h),
    fun h => (ModuleCat.mono_iff_injective S.moduleCatOpcyclesIso.hom).1 inferInstance (by simpa)⟩
    (Submodule.Quotient.eq _)

end CategoryTheory.ShortComplex
namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (S : Subgroup G) [S.Normal]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
noncomputable def ofQuotient [IsTrivial (ρ.comp S.subtype)] :
    Representation k (G ⧸ S) V :=
  (QuotientGroup.con S).lift ρ <| by
    rintro x y ⟨⟨z, hz⟩, rfl⟩
    ext w
    have : ρ y (ρ z.unop _) = _ :=
      congr(ρ y ($(IsTrivial.out (ρ := ρ.comp S.subtype) ⟨z.unop, hz⟩) w))
    simpa [← LinearMap.mul_apply, ← map_mul] using this

@[simp]
lemma ofQuotient_coe_apply [IsTrivial (ρ.comp S.subtype)] (g : G) (x : V) :
    ofQuotient ρ S (g : G ⧸ S) x = ρ g x :=
  rfl

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
@[simps]
def subrepresentation (W : Submodule k V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    Representation k G W where
  toFun g := (ρ g).restrict <| le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`. -/
@[simps]
def quotient (W : Submodule k V) (le_comap : ∀ g, W ≤ W.comap (ρ g)) :
    Representation k G (V ⧸ W) where
  toFun g := Submodule.mapQ _ _ (ρ g) <| le_comap g
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

section QuotientGroup

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
noncomputable abbrev toInvariants :
    Representation k G (invariants (ρ.comp S.subtype)) :=
  subrepresentation ρ _ fun g x hx ⟨s, hs⟩ => by
    simpa using congr(ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩))

instance : IsTrivial ((toInvariants ρ S).comp S.subtype) where
  out g := LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext <| by simpa using (hx g)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
noncomputable abbrev quotientToInvariants :
    Representation k (G ⧸ S) (invariants (ρ.comp S.subtype)) :=
  ofQuotient (toInvariants ρ S) S

lemma le_comap_augmentationSubmodule (g : G) :
    augmentationSubmodule (ρ.comp S.subtype) ≤
      (augmentationSubmodule <| ρ.comp S.subtype).comap (ρ g) :=
  Submodule.span_le.2 fun y ⟨⟨s, x⟩, hs⟩ => by
    simpa [← hs] using mem_augmentationSubmodule_of_eq
      ⟨g * s * g⁻¹, Subgroup.Normal.conj_mem ‹_› s.1 s.2 g⟩ (ρ g x) _ <| by simp

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the augmentation submodule of `ρ|_S`. -/
noncomputable abbrev toAugmentationSubmodule :=
  subrepresentation ρ (augmentationSubmodule <| ρ.comp S.subtype)
    fun g => le_comap_augmentationSubmodule ρ S g

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G`-representation on the
coinvariants of `ρ|_S`. -/
noncomputable abbrev toCoinvariants :=
  quotient ρ (augmentationSubmodule <| ρ.comp S.subtype)
    fun g => le_comap_augmentationSubmodule ρ S g

instance : IsTrivial ((toCoinvariants ρ S).comp S.subtype) where
  out g := Submodule.linearMap_qext _ <| by
    ext x
    simpa [Submodule.Quotient.eq] using mem_augmentationSubmodule_of_eq g x _ rfl

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
noncomputable abbrev quotientToCoinvariants :
    Representation k (G ⧸ S) (coinvariants (ρ.comp S.subtype)) :=
  ofQuotient (toCoinvariants ρ S) S

end QuotientGroup

end Representation

variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

open CategoryTheory
open Representation (IsTrivial)
namespace Rep

instance {H V : Type u} [Group H] [AddCommGroup V] [Module k V] (ρ : Representation k H V)
    (f : G →* H) [Representation.IsTrivial (ρ.comp f)] :
    Representation.IsTrivial ((Rep.of ρ).ρ.comp f) := ‹_›

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
noncomputable abbrev ofQuotient [Representation.IsTrivial (A.ρ.comp S.subtype)] :
    Rep k (G ⧸ S) := Rep.of (A.ρ.ofQuotient S)

/-- Given a `k`-linear `G`-representation `(V, ρ)`, this is the representation defined by
restricting `ρ` to a `G`-invariant `k`-submodule of `V`. -/
noncomputable abbrev subrepresentation (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    Rep k G :=
  Rep.of (A.ρ.subrepresentation W le_comap)

/-- The natural inclusion of a subrepresentation into the ambient representation. -/
@[simps]
def subtype (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    subrepresentation A W le_comap ⟶ A where
  hom := ModuleCat.ofHom W.subtype
  comm _ := rfl

/-- Given a `k`-linear `G`-representation `(V, ρ)` and a `G`-invariant `k`-submodule `W ≤ V`, this
is the representation induced on `V ⧸ W` by `ρ`.-/
noncomputable abbrev quotient (W) (le_comap) :=
  Rep.of (A.ρ.quotient W le_comap)

/-- The natural projection from a representation to its quotient by a subrepresentation. -/
@[simps]
def mkQ (W : Submodule k A) (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) :
    A ⟶ quotient A W le_comap where
  hom := ModuleCat.ofHom <| Submodule.mkQ _
  comm _ := rfl

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the invariants of `ρ|_S`. -/
noncomputable abbrev toInvariants :
    Rep k G := Rep.of <| A.ρ.toInvariants S

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the invariants of `ρ|_S`. -/
abbrev quotientToInvariants (S : Subgroup G) [S.Normal] :=
  Rep.of (A.ρ.quotientToInvariants S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` restricts to a `G`-representation on
the augmentation submodule of `ρ|_S`. -/
abbrev toAugmentationSubmodule :=
  Rep.of (A.ρ.toAugmentationSubmodule S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G`-representation on the
coinvariants of `ρ|_S`. -/
abbrev toCoinvariants :=
  Rep.of (A.ρ.toCoinvariants S)

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `A` induces a short exact sequence of
`G`-representations `0 ⟶ ℐ(S)A ⟶ A ⟶ A_S ⟶ 0` where `ℐ(S)A` is the submodule of `A`
generated by elements of the form `ρ(s)(x) - x` for `s : S, x : A`. -/
@[simps X₁ X₂ X₃ f g]
def coinvariantsShortComplex : ShortComplex (Rep k G) where
  X₁ := toAugmentationSubmodule A S
  X₂ := A
  X₃ := toCoinvariants A S
  f := subtype ..
  g := mkQ ..
  zero := by ext x; exact (Submodule.Quotient.mk_eq_zero _).2 x.2

lemma coinvariantsShortComplex_shortExact : (coinvariantsShortComplex A S).ShortExact where
  exact := (forget₂ _ (ModuleCat k)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2
      fun x hx => ⟨(⟨x, (Submodule.Quotient.mk_eq_zero _).1 hx⟩ :
      Representation.augmentationSubmodule <| A.ρ.comp S.subtype), rfl⟩
  mono_f := (Rep.mono_iff_injective _).2 fun _ _ h => Subtype.ext h
  epi_g := (Rep.epi_iff_surjective _).2 <| Submodule.mkQ_surjective _

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` induces a `G ⧸ S`-representation on
the coinvariants of `ρ|_S`. -/
abbrev quotientToCoinvariants :=
  ofQuotient (toCoinvariants A S) S

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
    (φ : (Action.res _ 1).obj A ⟶ B) : mapOneCocycles 1 φ = 0 := by
  rw [mapOneCocycles, ← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i,
    ShortComplex.cyclesMap'_i]
  refine ModuleCat.hom_ext (LinearMap.ext fun _ ↦ funext fun y => ?_)
  simp [mapShortComplexH1, shortComplexH1, moduleCatMk, Pi.zero_apply y]

@[simp]
theorem H1Map_one {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : (Action.res _ 1).obj A ⟶ B) :
    H1Map 1 φ = 0 := by
  simp [← cancel_epi (H1π _)]

/-- The short complex `H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)`. -/
@[simps X₁ X₂ X₃ f g]
def H1InfRes (A : Rep k G) (S : Subgroup G) [S.Normal] :
     ShortComplex (ModuleCat k) where
  X₁ := H1 (A.quotientToInvariants S)
  X₂ := H1 A
  X₃ := H1 ((Action.res _ S.subtype).obj A)
  f := H1Map (QuotientGroup.mk' S) (subtype ..)
  g := H1Map S.subtype (𝟙 _)
  zero := by
    rw [← H1Map_comp, Category.comp_id,
      congr (QuotientGroup.mk'_comp_subtype S) H1Map, H1Map_one]
    rintro g x hx ⟨s, hs⟩
    simpa using congr(A.ρ g $(hx ⟨(g⁻¹ * s * g), Subgroup.Normal.conj_mem' ‹_› s hs g⟩))

@[elab_as_elim]
theorem H1_induction_on {C : H1 A → Prop}
    (h : ∀ x : oneCocycles A, C (Submodule.Quotient.mk x)) (x : H1 A) :
    C x := Quotient.inductionOn' x h

@[simp]
lemma _root_.QuotientGroup.coe_subtype {G : Type*} [Group G] {S : Subgroup G} [S.Normal]
    (x : S) : (x : G ⧸ S) = 1 := by simp

/-- The inflation map `H¹(G ⧸ S, A^S) ⟶ H¹(G, A)` is a monomorphism. -/
instance : Mono (H1InfRes A S).f := by
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro x hx
  induction' x using H1_induction_on with x
  simp_all only [H1InfRes_X₂, H1InfRes_X₁, H1InfRes_f, H1π_comp_H1Map_apply (QuotientGroup.mk' S),
    Submodule.Quotient.mk_eq_zero]
  rcases hx with ⟨y, hy⟩
  refine ⟨⟨y, fun s => ?_⟩, Subtype.ext <| funext fun g => Quotient.inductionOn' g
    fun g => Subtype.ext <| congr_fun (Subtype.ext_iff.1 hy) g⟩
  simpa [sub_eq_zero, shortComplexH1, moduleCatToCycles] using congr_fun (Subtype.ext_iff.1 hy) s.1

/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, the short complex
`H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)` is exact. -/
instance : (H1InfRes A S).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction' x using H1_induction_on with x
  simp_all only [H1InfRes_X₂, H1InfRes_X₃, H1InfRes_g, Submodule.Quotient.mk''_eq_mk, H1InfRes_X₁,
    LinearMap.mem_ker, H1π_comp_H1Map_apply S.subtype, Submodule.Quotient.mk_eq_zero, H1InfRes_f]
  rcases hx with ⟨(y : A), hy⟩
  have h1 := (mem_oneCocycles_iff x).1 x.2
  have h2 : ∀ s ∈ S, x s = A.ρ s y - y :=
    fun s hs => (groupCohomology.oneCocycles_ext_iff.1 hy ⟨s, hs⟩).symm
  refine ⟨H1π _ ⟨fun g => Quotient.liftOn' g (fun g => ⟨x.1 g - A.ρ g y + y, ?_⟩) ?_, ?_⟩, ?_⟩
  · intro s
    calc
      _ = x (s * g) - x s - A.ρ s (A.ρ g y) + (x s + y) := by
        simp [add_eq_of_eq_sub (h2 s s.2), sub_eq_of_eq_add (h1 s g)]
      _ = x (g * (g⁻¹ * s * g)) - A.ρ g (A.ρ (g⁻¹ * s * g) y - y) - A.ρ g y + y := by
        simp only [mul_assoc, mul_inv_cancel_left, map_mul, LinearMap.mul_apply, map_sub,
          Representation.ρ_self_inv_apply]
        abel
      _ = x g - A.ρ g y + y := by
        simp [eq_sub_of_add_eq' (h1 g (g⁻¹ * s * g)).symm,
          h2 (g⁻¹ * s * g) (Subgroup.Normal.conj_mem' ‹_› _ s.2 _)]
  · intro g h hgh
    have := congr(A.ρ g $(h2 (g⁻¹ * h) <| QuotientGroup.leftRel_apply.1 hgh))
    simp_all [h1, ← sub_eq_add_neg, sub_eq_sub_iff_sub_eq_sub]
  · rw [mem_oneCocycles_iff]
    intro g h
    induction' g using QuotientGroup.induction_on with g
    induction' h using QuotientGroup.induction_on with h
    apply Subtype.ext
    simp [← QuotientGroup.mk_mul, h1 g h, sub_add_eq_add_sub, add_assoc]
  · symm
    simp only [ModuleCat.hom_ofHom, oneCocycles.val_eq_coe, Submodule.mkQ_apply,
      H1π_comp_H1Map_apply, Submodule.Quotient.eq]
    use y
    refine Subtype.ext <| funext fun g => ?_
    simp only [moduleCatToCycles_apply_coe, AddSubgroupClass.coe_sub]
    simp [mapOneCocycles_comp_subtype_apply (A := A.quotientToInvariants S) (QuotientGroup.mk' S),
      shortComplexH1, oneCocycles.coe_mk (A := A.quotientToInvariants S), ← sub_sub]

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

lemma Representation.ρ_eq_of_coe_eq {k G V : Type*} [CommRing k]
    [Group G] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (S : Subgroup G) [IsTrivial (ρ.comp S.subtype)] (g h : G) (hgh : (g : G ⧸ S) = h) :
    ρ g = ρ h := by
  ext x
  apply (ρ.ρ_apply_bijective g⁻¹).1
  simpa [← LinearMap.mul_apply, ← map_mul, -isTrivial_def] using
    (congr($(isTrivial_def (ρ.comp S.subtype) ⟨g⁻¹ * h, QuotientGroup.eq.1 hgh⟩) x)).symm

omit [DecidableEq G] [S.Normal] in
lemma ρ_eq_of_coe_eq
    [IsTrivial (A.ρ.comp S.subtype)] (g h : G) (hgh : (g : G ⧸ S) = h) :
    A.ρ g = A.ρ h := by
  ext x
  apply (A.ρ.ρ_apply_bijective g⁻¹).1
  simpa [← LinearMap.mul_apply, ← map_mul, -isTrivial_def] using
    (congr($(isTrivial_def (A.ρ.comp S.subtype) ⟨g⁻¹ * h, QuotientGroup.eq.1 hgh⟩) x)).symm

/-- A `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially induces a
`G ⧸ S`-representation on `A`, and composing this with the quotient map `G → G ⧸ S` gives the
original representation by definition. Useful for typechecking. -/
abbrev resOfQuotientIso [IsTrivial (A.ρ.comp S.subtype)] :
    (Action.res _ (QuotientGroup.mk' S)).obj (A.ofQuotient S) ≅ A := Iso.refl _

@[simp]
lemma H1Map_one {G H : Type u} [Group G] [Group H] [DecidableEq G] [DecidableEq H]
    {A : Rep k G} {B : Rep k H} (φ : A ⟶ (Action.res _ (1 : G →* H)).obj B) :
    H1Map (1 : G →* H) φ = 0 := by
  simp only [← cancel_epi (H1π A), H1π_comp_H1Map, Limits.comp_zero]
  ext x
  rw [ModuleCat.hom_comp]
  refine (H1π_eq_zero_iff _).2 ?_
  simpa [← mapDomain_mapRange] using
    Submodule.finsupp_sum_mem _ _ _ _ fun _ _ => single_one_mem_oneBoundaries _

/-- The short complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A_S)`. -/
@[simps X₁ X₂ X₃ f g]
def H1CoresCoinf [DecidableEq (G ⧸ S)] :
    ShortComplex (ModuleCat k) where
  X₁ := H1 ((Action.res _ S.subtype).obj A)
  X₂ := H1 A
  X₃ := H1 (quotientToCoinvariants A S)
  f := H1Map S.subtype (𝟙 _)
  g := H1Map (QuotientGroup.mk' S) (mkQ _ _ fun _ => le_comap_augmentationSubmodule _ _ _)
  zero := by rw [← H1Map_comp, congr (QuotientGroup.mk'_comp_subtype S) H1Map, H1Map_one]

/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, this is the
short complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A)`. -/
@[simps X₁ X₂ X₃ f g]
def H1CoresCoinfOfTrivial [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    ShortComplex (ModuleCat k) where
  X₁ := H1 ((Action.res _ S.subtype).obj A)
  X₂ := H1 A
  X₃ := H1 (ofQuotient A S)
  f := H1Map S.subtype (𝟙 _)
  g := H1Map (QuotientGroup.mk' S) <| (resOfQuotientIso A S).inv
  zero := by rw [← H1Map_comp, congr (QuotientGroup.mk'_comp_subtype S) H1Map, H1Map_one]

instance mapOneCycles_quotientGroupMk'_epi
    [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    Epi (mapOneCycles (QuotientGroup.mk' S) (resOfQuotientIso A S).inv) := by
  rw [ModuleCat.epi_iff_surjective]
  rintro ⟨x, hx⟩
  choose! s hs using QuotientGroup.mk_surjective (s := S)
  have hs₁ : QuotientGroup.mk ∘ s = id := funext hs
  refine ⟨⟨mapDomain s x, ?_⟩, Subtype.ext <| by
    rw [mapOneCycles_comp_subtype_apply]; simp [← mapDomain_comp, hs₁]⟩
  simpa [mem_oneCycles_iff, ← (mem_oneCycles_iff _).1 hx, sum_mapDomain_index_inj (f := s)
      (fun x y h => by rw [← hs x, ← hs y, h])]
    using Finsupp.sum_congr fun a b => QuotientGroup.induction_on a fun a => by
      simp [← QuotientGroup.mk_inv, ρ_eq_of_coe_eq A S (s a)⁻¹ a⁻¹ (by simp [hs])]

instance H1Map_quotientGroupMk'_epi [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    Epi (H1Map (QuotientGroup.mk' S) (resOfQuotientIso A S).inv) := by
  convert epi_of_epi (H1π A) _
  rw [H1π_comp_H1Map]
  exact @epi_comp _ _ _ _ _ _ (mapOneCycles_quotientGroupMk'_epi A S) (H1π _) inferInstance

/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, the
induced map `H₁(G, A) ⟶ H₁(G ⧸ S, A)` is an epimorphism. -/
instance H1CoresCoinfOfTrivial_g_epi
    [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    Epi (H1CoresCoinfOfTrivial A S).g :=
  inferInstanceAs <| Epi (H1Map _ _)

/-- Given a `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially, the short
complex `H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A)` is exact. -/
theorem H1CoresCoinfOfTrivial_exact [DecidableEq (G ⧸ S)] [IsTrivial (A.ρ.comp S.subtype)] :
    (H1CoresCoinfOfTrivial A S).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
/- Denote `C(i) : C(S, A) ⟶ C(G, A), C(π) : C(G, A) ⟶ C(G ⧸ S, A)` and let `x : Z₁(G, A)` map to
0 in `H₁(G ⧸ S, A)`. -/
  induction' x using Quotient.inductionOn' with x
  rcases x with ⟨(x : G →₀ A), (hxc : x ∈ oneCycles A)⟩
  simp_all only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₃, H1CoresCoinfOfTrivial_g,
    Submodule.Quotient.mk''_eq_mk, LinearMap.mem_ker, H1π_comp_H1Map_apply (QuotientGroup.mk' S)]
/- Choose `y := ∑ y(σ, τ)·(σ, τ) ∈ C₂(G ⧸ S, A)` such that `C₁(π)(x) = d(y)`. -/
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
/- Let `s : G ⧸ S → G` be a section of the quotient map. -/
  choose! s hs using QuotientGroup.mk'_surjective S
  have hs₁ : QuotientGroup.mk (s := S) ∘ s = id := funext hs
  have hs₂ : s.Injective := fun x y hxy => by rw [← hs x, ← hs y, hxy]
/- Let `z := ∑ y(σ, τ)·(s(σ), s(τ))`. -/
  let z : G × G →₀ A := lmapDomain _ k (Prod.map s s) y
/- We have that `C₂(π)(z) = y`. -/
  have hz : lmapDomain _ k (QuotientGroup.mk' S) (dOne A z) = dOne (A.ofQuotient S) y := by
    have := congr($((mapShortComplexH1 (QuotientGroup.mk' S)
      (resOfQuotientIso A S).inv).comm₁₂.symm) z)
    simp_all [shortComplexH1, z, ← mapDomain_comp, Prod.map_comp_map]
  let v := x - dOne _ z
/- We have `C₁(s ∘ π)(v) = ∑ v(g)·s(π(g)) = 0`, since `C₁(π)(v) = dC₁(π)(z) - C₁(π)(dz) = 0` by
previous assumptions. -/
  have hv : mapDomain (s ∘ QuotientGroup.mk) v = 0 := by
    rw [mapDomain_comp]
    simp_all [v, mapDomain, sum_sub_index]
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
  /- Now `v + d(ve)` has support in `S` and agrees with `x` in `H₁(G, A)`: -/
  use H1π _ ⟨comapDomain Subtype.val (v + dOne _ ve) <|
    Set.injOn_of_injective Subtype.val_injective, ?_⟩
  · simp only [H1CoresCoinfOfTrivial_X₁, H1CoresCoinfOfTrivial_f, Action.res_obj_V,
      ModuleCat.hom_ofHom, Submodule.mkQ_apply, H1π_comp_H1Map_apply]
    refine (H1π_eq_iff _ _).2 ?_
  /- Indeed, `v + d(ve) - x = d(ve - z) ∈ B₁(G, A)`, since `v := x - dz`. -/
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

lemma oneChainsToAugmentationSubmodule_surjective :
    Function.Surjective (oneChainsToAugmentationSubmodule A) := by
  rintro ⟨x, hx⟩
  rcases range_dZero_eq_augmentationSubmodule A ▸ hx with ⟨y, hy⟩
  use y, Subtype.ext hy

/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, let `I(S)A` denote the submodule
of `A` spanned by elements of the form `ρ(s)(a) - a` for `s : S, a : A`. Then the image of
`C₁(G, I(S)A)` in `C₁(G, A)⧸B₁(G, A)` is contained in the image of `C₁(S, A)`. -/
theorem comap_augmentationSubmodule_pOpcycles_range_subtype_pOpcycles_eq_top :
    Submodule.comap ((mapShortComplexH1 (MonoidHom.id G) (coinvariantsShortComplex A S).f).τ₂ ≫
      (shortComplexH1 _).pOpcycles).hom (LinearMap.range ((mapShortComplexH1 S.subtype (𝟙 _)).τ₂ ≫
      (shortComplexH1 _).pOpcycles).hom) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rcases mapRange_surjective _ (map_zero _) (oneChainsToAugmentationSubmodule_surjective
    ((Action.res _ S.subtype).obj A)) x with ⟨(X : G →₀ S →₀ A), hX⟩
  let Y : S →₀ A := X.sum fun g f =>
    mapRange.linearMap (A.ρ g⁻¹) (lmapDomain _ k (fun s => MulAut.conjNormal g⁻¹ s) f) - f
  let Z : G × G →₀ A := X.sum fun g f =>
    lmapDomain _ k (fun s => (g, g⁻¹ * s.1 * g)) f - lmapDomain _ k (fun s => (s.1, g)) f
  use Y
  apply (moduleCat_pOpcycles_eq_iff _ _ _).2 ⟨Z, ?_⟩
  show dOne A Z = mapRange id rfl (lmapDomain _ k Subtype.val Y) -
    mapRange.linearMap (Submodule.subtype _) (mapDomain id x)
  simpa [map_finsupp_sum, mapDomain, map_sub, ← hX, sum_single_index, finsuppProdLEquiv,
    finsuppProdEquiv, Finsupp.uncurry, dOne, Y, Z, sum_mapRange_index,
    oneChainsToAugmentationSubmodule, dZero, single_sum, mul_assoc, sub_add_eq_add_sub,
    sum_sum_index, add_smul, sub_sub_sub_eq, lsingle, singleAddHom] using add_comm _ _

@[elab_as_elim]
theorem H1_induction_on {C : H1 A → Prop}
    (h : ∀ x : oneCycles A, C (Submodule.Quotient.mk x)) (x : H1 A) :
    C x := Quotient.inductionOn' x h

-- not sure why this is so slow even after I squeezed all the simps :(
set_option maxHeartbeats 320000 in
/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, the short complex
`H₁(S, A) ⟶ H₁(G, A) ⟶ H₁(G ⧸ S, A_S)` is exact. -/
instance [DecidableEq (G ⧸ S)] :
    (H1CoresCoinf A S).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction' x using H1_induction_on with x
  simp only [H1CoresCoinf_X₂, H1CoresCoinf_X₃, LinearMap.mem_ker, H1CoresCoinf_g,
    H1π_comp_H1Map_apply (QuotientGroup.mk' S)] at hx
/- Let `x : Z₁(G, A)` map to 0 in `H₁(G, ⧸ S, A_S)`. Pick `y : C₂(G ⧸ S, A_S)` such that `d(y)`
equals `Z₁(π, π)(x) : Z₁(G ⧸ S, A_S)`. -/
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
/- Then `Z₁(π, Id)(x) : Z₁(G, A_S)` maps to 0 in `H₁(G ⧸ S, A_S)`. We know
`H₁(S, A_S) ⟶ H₁(G, A_S) ⟶ H₁(G ⧸ S, A_S)` is exact by `H1CoresCoinfOfTrivial_exact`, since
`S` acts trivially on `A_S`. So we can choose `z : Z₁(S, A_S)` with the same homology class as
`Z₁(π, Id)(π)` in `H₁(G, A_S)`. -/
  rcases @(ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (H1CoresCoinfOfTrivial_exact (toCoinvariants A S) S)
    (H1π _ <| mapOneCycles (MonoidHom.id G) (mkQ _ _ _) x) (by
      simpa only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₃, H1CoresCoinfOfTrivial_g,
        Iso.refl_inv, ModuleCat.hom_ofHom, Submodule.mkQ_apply, LinearMap.mem_ker,
        H1π_comp_H1Map_apply (QuotientGroup.mk' S), ← ConcreteCategory.comp_apply,
        ← cyclesMap'_comp, ← mapShortComplexH1_comp,
        congr (MonoidHom.comp_id _) mapShortComplexH1] using hx) with ⟨z, hz⟩
  induction' z using H1_induction_on with z
  simp only [H1CoresCoinfOfTrivial_X₂, H1CoresCoinfOfTrivial_X₁, H1CoresCoinfOfTrivial_f,
    H1π_comp_H1Map_apply S.subtype, Action.res_obj_V, ModuleCat.hom_ofHom,
    Submodule.mkQ_apply] at hz
/- Choose `w : C₂(G, A_S)` such that `d(w) = Z₁(i, Id)(z) - Z₁(Id, π)(x)`. -/
  rcases (H1π_eq_iff _ _).1 hz with ⟨w, hzw⟩
/- Choose `Z : C₁(S, A)` mapping to `z : C₁(S, A_S)`, and `W : C₂(G, A)` mapping to
`w : C₂(G, A_S)`. -/
  rcases mapRange_surjective (coinvariantsMkQ _) (map_zero _)
    (Submodule.Quotient.mk_surjective _) z.1 with ⟨Z, hZ⟩
  rcases mapRange_surjective (coinvariantsMkQ _) (map_zero _)
    (Submodule.Quotient.mk_surjective _) w with ⟨W, hW⟩
/- Let `b : C₁(G, A)` denote `x + d(W) - C₁(i, Id)(z)`. -/
  let b : G →₀ A := (x.1 : G →₀ A) + dOne A W - lmapDomain _ k S.subtype Z
/- Then `b` has coefficients in `I(S)A := ⟨{ρ(s)(a) - a | s ∈ S, a ∈ A}⟩`, since
`C₁(G, I(S)(A)) ⟶ C₁(G, A) ⟶ C₁(G, A_S)` is exact, and `b` is in the kernel of the second map. -/
  have hb : ∀ g, b g ∈ augmentationSubmodule (A.ρ.comp S.subtype) :=
    fun g => (Submodule.Quotient.eq _).1 <| by
      show mapRange.linearMap (coinvariantsMkQ _) _ _ = mapRange.linearMap (coinvariantsMkQ _) _ _
      have := Finsupp.ext_iff.1 (congr($((mapShortComplexH1 (B := toCoinvariants A S)
        (MonoidHom.id G) (mkQ _ _ _)).comm₁₂.symm) W)) g
      simpa only [mapRange.linearMap_apply, mapRange_apply, Finsupp.coe_add, Pi.add_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_add, Subgroup.coeSubtype, lmapDomain_apply,
        implies_true, ← mapDomain_mapRange, hZ, Action.res_obj_V, shortComplexH1,
        moduleCatMk_X₁_carrier, moduleCatMk_X₂_carrier, moduleCatMk_f, mapShortComplexH1_τ₂,
        ModuleCat.ofHom_comp, MonoidHom.coe_id, lmapDomain_id, ModuleCat.ofHom_id, mkQ_hom,
        ModuleCat.hom_ofHom, Category.id_comp, mapShortComplexH1_τ₁, Prod.map_id,
        ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, hW, hzw,
        mapOneCycles_comp_subtype_apply (B := toCoinvariants A S), mapDomain_id, Finsupp.coe_sub,
        Pi.sub_apply, eq_sub_iff_add_eq'] using this
/- Let `β` be `b` considered as an element of `C₁(G, I(S)(A))`, so that `C₁(Id, i)(β) = b`. -/
  let β : G →₀ augmentationSubmodule (A.ρ.comp S.subtype) :=
    mapRange (Function.invFun <| (augmentationSubmodule (A.ρ.comp S.subtype)).subtype)
    (Function.leftInverse_invFun Subtype.val_injective (0 : augmentationSubmodule _)) b
  have hβb : mapRange Subtype.val rfl β = b := Finsupp.ext fun g => Subtype.ext_iff.1 <|
    Function.leftInverse_invFun Subtype.val_injective ⟨b g, hb g⟩
/- Then, since the image of `C₁(G, I(S)A)` in `C₁(G, A)⧸B₁(G, A)` is contained in the image of
`C₁(S, A)` by `comap_augmentationSubmodule_pOpcycles_range_subtype_pOpcycles_eq_top`, we can choose
`α : C₁(S, A)`, `δ : C₂(G, A)` such that `d(δ) = Z₁(i, Id)(α) - Z₁(Id, i)(β)`. -/
  rcases eq_top_iff.1 (comap_augmentationSubmodule_pOpcycles_range_subtype_pOpcycles_eq_top A S)
    (by trivial : β ∈ ⊤) with ⟨(α : S →₀ A), hα⟩
  dsimp only [ModuleCat.hom_comp] at hα
  rcases (moduleCat_pOpcycles_eq_iff _ _ _).1 hα with ⟨(δ : G × G →₀ A), hβ⟩
/- Then, by assumption, `d(W + δ) = C₁(i, Id)(α + Z) - x`. -/
  have hαZ : dOne A (W + δ) = mapDomain Subtype.val (α + Z) - x := by
    simp_all only [shortComplexH1, moduleCatMk_X₂_carrier, moduleCatMk_X₃_carrier,
      moduleCatMk_g, ModuleCat.hom_ofHom, moduleCatMk_X₁_carrier, Submodule.Quotient.mk_eq_zero,
      LinearMap.mem_range, Action.res_obj_V, Subgroup.coeSubtype, lmapDomain_apply, Finsupp.coe_sub,
      Finsupp.coe_add, Pi.sub_apply, Pi.add_apply, mapShortComplexH1_τ₂, ModuleCat.ofHom_comp,
      Action.id_hom, ModuleCat.hom_id, mapRange.linearMap_id, ModuleCat.ofHom_id, Category.comp_id,
      LinearMap.coe_comp, Function.comp_apply, coinvariantsShortComplex_X₁, Submodule.coe_subtype,
      coinvariantsShortComplex_f, MonoidHom.coe_id, lmapDomain_id, subtype_hom, Category.id_comp,
      mapRange.linearMap_apply, map_sub, map_add, moduleCatMk_f, ← sub_add, ← sub_sub,
      sub_add_eq_add_sub, add_sub_cancel, mapDomain_add, b]
/- So we claim that `α + Z` is an element of `Z₁(S, A)` which differs from `x` by a boundary in
`Z₁(G, A)`. -/
  use H1π _ ⟨α + Z, ?_⟩
/- Indeed, by `hαZ`, `d(W + δ)` is the desired boundary: -/
  · simp only [H1CoresCoinf_X₂, H1CoresCoinf_X₁, Submodule.mkQ_apply, H1CoresCoinf_f,
      ModuleCat.hom_ofHom, H1π_comp_H1Map_apply, b]
    refine (H1π_eq_iff _ _).2 ⟨W + δ, ?_⟩
    have := mapOneCycles_comp_subtype_apply (B := A) S.subtype (𝟙 _)
    simp_all only [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range, Action.res_obj_V,
      mapShortComplexH1_τ₂, ModuleCat.ofHom_comp, Subgroup.coeSubtype, Action.id_hom,
      ModuleCat.hom_id, mapRange.linearMap_id, ModuleCat.ofHom_id, Category.comp_id,
      ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply, coinvariantsShortComplex_f,
      coinvariantsShortComplex_X₁, MonoidHom.coe_id, lmapDomain_id, subtype_hom, Category.id_comp,
      map_add, LinearMap.id_coe, mapRange_id, b]
/- And `α + Z` is a cycle, since `d(W + δ) + x` is. -/
  · rw [mem_oneCycles_iff]
    have : x + dOne A (W + δ) ∈ oneCycles A := Submodule.add_mem _ x.2 (dOne_apply_mem_oneCycles _)
    rwa [eq_sub_iff_add_eq'.1 hαZ, mem_oneCycles_iff, sum_mapDomain_index_inj
      Subtype.val_injective, sum_mapDomain_index_inj Subtype.val_injective] at this

@[simp]
lemma _root_.Rep.res_obj_ρ {H : Type u} [Monoid H] (f : G →* H) (A : Rep k H) (g : G) :
    DFunLike.coe (F := G →* (A →ₗ[k] A)) (ρ ((Action.res _ f).obj A)) g = A.ρ (f g) := rfl

/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, the map
`H₁(G, A) ⟶ H₁(G ⧸ S, A_S)` is an epimorphism. -/
instance [DecidableEq (G ⧸ S)] :
    Epi (H1CoresCoinf A S).g := by
  rw [ModuleCat.epi_iff_surjective]
  intro x
  induction' x using H1_induction_on with x
/- Let `x : Z₁(G ⧸ S, A_S)`. We know `Z₁(G, A_S) ⟶ Z₁(G ⧸ S, A_S)` is surjective, so pick
`y : Z₁(G, A_S)` in the preimage of `x`. -/
  rcases (ModuleCat.epi_iff_surjective _).1
    (mapOneCycles_quotientGroupMk'_epi (A.toCoinvariants S) S) x with ⟨y, hy⟩
/- We know `C₁(G, A) ⟶ C₁(G, A_S)` is surjective, so pick `Y` in the preimage of `y`. -/
  rcases mapRange_surjective _ (map_zero _) (Submodule.mkQ_surjective
    (augmentationSubmodule (A.ρ.comp S.subtype))) y.1 with ⟨Y, hY⟩
/- Then `d(Y) ∈ I(S)A,` since `d(y) = 0`. -/
  have : dZero _ Y ∈ augmentationSubmodule (A.ρ.comp S.subtype) := by
    have h' := congr($((mapShortComplexH1 (B := toCoinvariants A S)
      (MonoidHom.id G) (mkQ _ _ _)).comm₂₃) Y)
    simp_all [shortComplexH1, ← Submodule.Quotient.mk_eq_zero]
  /- Thus we can pick a representation of `d(Y)` as a sum `∑ ρ(sᵢ⁻¹)(aᵢ) - aᵢ`, `sᵢ ∈ S, aᵢ ∈ A`,
and `Y - ∑ aᵢ·sᵢ` is a cycle. -/
  rcases oneChainsToAugmentationSubmodule_surjective
    ((Action.res _ S.subtype).obj A) ⟨dZero A Y, this⟩ with ⟨(Z : S →₀ A), hZ⟩
  have H : dZero A (Y - mapDomain S.subtype Z) = 0 := by
    simpa [map_sub, sub_eq_zero, oneChainsToAugmentationSubmodule, - LinearMap.sub_apply, dZero,
      sum_mapDomain_index_inj] using Subtype.ext_iff.1 hZ.symm
  use H1π A ⟨Y - mapDomain S.subtype Z, H⟩
  simp only [H1CoresCoinf_X₃, H1CoresCoinf_X₂, H1CoresCoinf_g, ModuleCat.hom_ofHom,
    Subgroup.coeSubtype, Submodule.mkQ_apply, H1π_comp_H1Map_apply]
/- Moreover, the image of `Y - ∑ aᵢ·sᵢ` in `Z₁(G ⧸ S, A_S)` is `x - ∑ aᵢ·1`, and hence differs from
`x` by a boundary, since `aᵢ·1 = d(aᵢ·(1, 1))`. -/
  refine (H1π_eq_iff _ _).2 ?_
  rw [← hy, mapOneCycles_comp_subtype_apply, mapOneCycles_comp_subtype_apply,
    ← lmapDomain_apply _ k]
  simpa [map_sub, mapRange_sub, hY, ← mapDomain_comp, ← mapDomain_mapRange, Function.comp_def]
      using Submodule.finsupp_sum_mem _ _ _ _ fun _ _ => single_one_mem_oneBoundaries _

end NotMap
end
end groupHomology
