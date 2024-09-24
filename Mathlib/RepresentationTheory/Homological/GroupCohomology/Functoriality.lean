import Mathlib.CategoryTheory.Grothendieck
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
universe v u
variable (n : ℕ)

open CategoryTheory

lemma Fin.comp_contractNth {G H : Type*} [MulOneClass G] [MulOneClass H] (f : G →* H)
    (j : Fin (n + 1)) (g : Fin (n + 1) → G) :
    f ∘ Fin.contractNth j (· * ·) g = Fin.contractNth j (· * ·) (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : ℕ) j with (h|h|h)
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_eq, h, f.map_mul]
  · simp only [Function.comp_apply, Fin.contractNth_apply_of_gt, h]

namespace ModuleCat

variable (R : Type u) [Ring R]

lemma ofHom_comp {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    ofHom (g ∘ₗ f) = ofHom f ≫ ofHom g := rfl

end ModuleCat
namespace Rep

open Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H] (f : G →* H) (A : Rep k G)

lemma res_obj_ρ (A : Rep k H) :
    ((Action.res _ f).obj A).ρ = A.ρ.comp f := rfl

lemma res_map_hom {A B : Rep k H} (φ : A ⟶ B) :
    hom ((Action.res _ f).map φ) = hom φ := rfl

variable (k) in
def resFunctor : Grpᵒᵖ ⥤ Cat where
  obj := fun G ↦ Cat.of (Rep k G.unop)
  map := fun f ↦ Action.res (ModuleCat k) f.unop

@[simps]
noncomputable def invariantsFunctor : Rep k G ⥤ ModuleCat.{u} k where
  obj A := ModuleCat.of k A.ρ.invariants
  map {A B} f := ModuleCat.ofHom ((hom f ∘ₗ A.ρ.invariants.subtype).codRestrict
    B.ρ.invariants fun ⟨c, hc⟩ g => by simp [← hom_comm_apply'', hc g])

variable (S : Subgroup G)

@[simps]
noncomputable def invariantsOfNormal [h1 : S.Normal] :
    Representation k G (invariants (A.ρ.comp S.subtype)) where
  toFun := fun g => ((A.ρ g).comp (Submodule.subtype _)).codRestrict _
    (fun ⟨x, hx⟩ ⟨s, hs⟩ => by
      simpa using congr(A.ρ g $(hx ⟨(g⁻¹ * s * g), h1.conj_mem' s hs g⟩)))
  map_one' := by ext; simp
  map_mul' := fun x y => by ext; simp

noncomputable def inf [S.Normal] : Rep k (G ⧸ S) :=
Rep.of <| (QuotientGroup.con S).lift (invariantsOfNormal A S)
  fun x y ⟨⟨z, hz⟩, h⟩ => LinearMap.ext fun ⟨w, hw⟩ => Subtype.ext <| by
  simpa [← h] using congr(A.ρ y $(hw ⟨z.unop, hz⟩))

variable {A S} in
lemma inf_apply [S.Normal] (g : G) (x : invariants (A.ρ.comp S.subtype)) :
  ((inf A S).ρ (g : G ⧸ S) x).1 = A.ρ g x :=
rfl

@[simps]
noncomputable def infMap [S.Normal] {A B : Rep k G} (φ : A ⟶ B) :
    inf A S ⟶ inf B S where
  hom := invariantsFunctor.map ((Action.res _ S.subtype).map φ)
  comm := fun g => QuotientGroup.induction_on g (fun g => LinearMap.ext
    fun x => Subtype.ext (Rep.hom_comm_apply φ g x.1))

@[simps]
noncomputable def infFunctor [S.Normal] : Rep k G ⥤ Rep k (G ⧸ S) :=
{ obj := fun A => inf A S
  map := fun f => infMap S f }

end Rep
namespace groupCohomology
open Rep
/-def resFunctor2 (k : Type u) [CommRing k] : GroupCatᵒᵖ ⥤ Cat where
  obj := fun G ↦ Cat.of (Rep k G.unop)ᵒᵖ
  map := fun f ↦ (Action.res (ModuleCat k) f.unop).op-/

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
-- could be monoids for a while ig but I cbf generalising the invariants file
  (A : Rep k G) (B : Rep k H) (f : G →* H) (φ : B →ₗ[k] A) (n : ℕ)

class IsPairMap : Prop where
  compatible : ∀ (g : G), φ ∘ₗ B.ρ (f g) = A.ρ g ∘ₗ φ

namespace IsPairMap
open Representation

variable {A B f φ} (S : Subgroup G)

lemma compatible_apply [IsPairMap A B f φ] (g : G) (x : B) :
    φ (B.ρ (f g) x) = A.ρ g (φ x) :=
  congr($(compatible g) x)

instance comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    (A : Rep k G) (B : Rep k H) (C : Rep k K) (f : G →* H) (g : H →* K) (φ : B →ₗ[k] A)
    (ψ : C →ₗ[k] B) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    IsPairMap A C (g.comp f) (φ.comp ψ) where
  compatible x := by
    ext y
    have := congr($(compatible (A := A) (B := B) (f := f) (φ := φ) x) (ψ y))
    have := congr($(compatible (A := B) (B := C) (f := g) (φ := ψ) (f x)) y)
    simp_all

instance instInf [S.Normal] : IsPairMap A (inf A S) (QuotientGroup.mk' S)
    (invariants (A.ρ.comp S.subtype)).subtype where
  compatible := by intros; rfl

instance instRes : IsPairMap ((Action.res _ f).obj B) B f LinearMap.id where
  compatible := by intros; rfl

instance instHom {A B : Rep k G} (f : A ⟶ B) : IsPairMap B A (MonoidHom.id G) f.hom where
  compatible := f.comm

variable [IsPairMap A B f φ]

variable (A B f φ) in
@[simps (config := .lemmasOnly)]
noncomputable def cochainsMap :
    inhomogeneousCochains B ⟶ inhomogeneousCochains A where
  f i := φ.compLeft (Fin i → G) ∘ₗ LinearMap.funLeft k B (fun x : Fin i → G => (f ∘ x))
  comm' i j (hij : _ = _) := by
    subst hij
    ext x
    funext g
    simp only [CochainComplex.of_x, inhomogeneousCochains.d_def, ModuleCat.coe_comp,
      Function.comp_apply]
    simpa [ModuleCat.coe_of, ModuleCat.hom_def, Fin.comp_contractNth]
      using (compatible_apply _ _).symm

@[simp]
lemma cochainsMap_f_apply (n : ℕ) (x : (inhomogeneousCochains B).X n) (g : Fin n → G) :
    (cochainsMap A B f φ).f n x g = φ (x (f ∘ g)) :=
  rfl

lemma cochainsMap_comp {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]
    (A : Rep k G) (B : Rep k H) (C : Rep k K) (f : G →* H) (g : H →* K) (φ : B →ₗ[k] A)
    (ψ : C →ₗ[k] B) [IsPairMap A B f φ] [IsPairMap B C g ψ] :
    cochainsMap A C (g.comp f) (φ.comp ψ) = (cochainsMap B C g ψ) ≫ (cochainsMap A B f φ) := by
  rfl

variable (A B f φ)
noncomputable abbrev cocyclesMap (n : ℕ) :
    groupCohomology.cocycles B n ⟶ groupCohomology.cocycles A n :=
  HomologicalComplex.cyclesMap (cochainsMap A B f φ) n

noncomputable abbrev cohomologyMap (n : ℕ) :
  groupCohomology B n ⟶ groupCohomology A n :=
HomologicalComplex.homologyMap (cochainsMap A B f φ) n

@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupCohomology A n
  map {A B} φ :=
    letI : IsPairMap B A (MonoidHom.id _) φ.hom := instHom φ
    cohomologyMap B A (MonoidHom.id _) φ.hom n
  map_id A := HomologicalComplex.homologyMap_id _ _
  map_comp f g := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

abbrev fOne : (H → B) →ₗ[k] (G → A) :=
  φ.compLeft G ∘ₗ LinearMap.funLeft k B f

abbrev fTwo : (H × H → B) →ₗ[k] (G × G → A) :=
  φ.compLeft (G × G) ∘ₗ LinearMap.funLeft k B (Prod.map f f)

abbrev fThree : (H × H × H → B) →ₗ[k] (G × G × G → A) :=
  φ.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k B (Prod.map f (Prod.map f f))

@[reassoc (attr := simp)]
lemma cochainsMap_zero_comp_zeroCochainsLEquiv :
    (cochainsMap A B f φ).f 0 ≫ (zeroCochainsLequiv A : (inhomogeneousCochains A).X 0 →ₗ[k] A)
      = (zeroCochainsLequiv B : (inhomogeneousCochains B).X 0 →ₗ[k] B) ≫ φ := by
  ext x
  simp only [Action.forget_obj, CochainComplex.of_x, cochainsMap_f, ModuleCat.coe_comp,
    Function.comp_apply, Unique.eq_default (f ∘ _)]
  rfl

@[simps]
noncomputable def mapShortComplexH0 :
    shortComplexH0 B ⟶ shortComplexH0 A where
  τ₁ := (isoH0 B).inv ≫ cohomologyMap A B f φ 0 ≫ (isoH0 A).hom
  τ₂ := φ
  τ₃ := φ.compLeft G ∘ₗ LinearMap.funLeft k B f
  comm₁₂ := by
    simp [shortComplexH0, ModuleCat.ofHom, Iso.inv_comp_eq, ← cancel_epi (groupCohomologyπ _ _)]
  comm₂₃ := by
    ext (x : B)
    funext g
    dsimp [shortComplexH0]
    simp [dZero, ModuleCat.coe_of, ModuleCat.hom_def, compatible_apply]

noncomputable def mapH0 :
    ModuleCat.of k (H0 B) ⟶ ModuleCat.of k (H0 A) :=
  (isoH0 B).inv ≫ cohomologyMap A B f φ 0 ≫ (isoH0 A).hom

@[simps]
def mapShortComplexH1 :
    shortComplexH1 B ⟶ shortComplexH1 A where
  τ₁ := φ
  τ₂ := fOne A B f φ
  τ₃ := fTwo A B f φ
  comm₁₂ := by
    ext x
    funext g
    dsimp [shortComplexH1, dZero, fOne]
    simp [ModuleCat.coe_of, ModuleCat.hom_def, compatible_apply]
  comm₂₃ := by
    ext x
    funext g
    dsimp [shortComplexH1, fOne, dOne, fTwo]
    simp [ModuleCat.coe_of, ModuleCat.hom_def, compatible_apply]

@[simps]
def mapShortComplexH2 :
    shortComplexH2 B ⟶ shortComplexH2 A where
  τ₁ := fOne A B f φ
  τ₂ := fTwo A B f φ
  τ₃ := fThree A B f φ
  comm₁₂ := by
    ext x
    funext g
    dsimp [shortComplexH2, dOne, fTwo]
    simp [ModuleCat.coe_of, ModuleCat.hom_def, compatible_apply]
  comm₂₃ := by
    ext x
    funext g
    dsimp [shortComplexH2, fTwo, dTwo, fThree]
    simp [ModuleCat.coe_of, ModuleCat.hom_def, compatible_apply]

open HomologicalComplex

noncomputable def mapShortComplexH1Iso :
    Arrow.mk ((shortComplexFunctor' _ _ 0 1 2).map (cochainsMap A B f φ))
      ≅ Arrow.mk (mapShortComplexH1 A B f φ) :=
  Arrow.isoMk' _ _ (shortComplexH1Iso B) (shortComplexH1Iso A) <| by
    ext x
    · show φ _ = φ _
      simp only [Unique.eq_default (f ∘ _)]
      congr
    · rfl
    · funext ⟨g₁, g₂⟩
      show φ (x _) = φ (x (f ∘ _))
      rcongr x
      exact Fin.cases (by simp) (fun j => by simp [Fin.fin_one_eq_zero]) x

noncomputable def mapShortComplexH2Iso :
    Arrow.mk ((shortComplexFunctor' _ _ 1 2 3).map (cochainsMap A B f φ))
      ≅ Arrow.mk (mapShortComplexH2 A B f φ) :=
  Arrow.isoMk' _ _ (shortComplexH2Iso B) (shortComplexH2Iso A) <| by
    ext x
    · funext g
      show φ _ = φ _
      congr
    · funext ⟨g₁, g₂⟩
      show φ (x _) = φ (x _)
      rcongr x
      fin_cases x <;> rfl
    · funext ⟨g₁, g₂, g₃⟩
      show φ (x _) = φ (x _)
      rcongr x
      fin_cases x <;> rfl
