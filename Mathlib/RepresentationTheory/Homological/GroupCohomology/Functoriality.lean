/-
Copyright (c) 2025 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Functoriality of group cohomology

Given a commutative ring `k`, a group homomorphism `f : G →* H`, a `k`-linear `H`-representation
`A`, a `k`-linear `G`-representation `B`, and a representation morphism `Res(f)(A) ⟶ B`, we get
a cochain map `inhomogeneousCochains A ⟶ inhomogeneousCochains B` and hence maps on
cohomology `Hⁿ(H, A) ⟶ Hⁿ(G, B)`.
We also provide extra API for these maps in degrees 0, 1, 2.

## Main definitions

* `groupCohomology.cochainsMap f φ` is the map `inhomogeneousCochains A ⟶ inhomogeneousCochains B`
  induced by a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.map f φ n` is the map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` induced by a group
  homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`.
* `groupCohomology.H1InfRes A S` is the short complex `H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)` for
  a normal subgroup `S ≤ G` and a `G`-representation `A`.

-/

universe v u

namespace groupCohomology
open Rep CategoryTheory Representation

variable {k G H : Type u} [CommRing k] [Group G] [Group H]
  {A : Rep k H} {B : Rep k G} (f : G →* H) (φ : (Action.res _ f).obj A ⟶ B) (n : ℕ)

section

theorem congr {f₁ f₂ : G →* H} (h : f₁ = f₂) {φ : (Action.res _ f₁).obj A ⟶ B} {T : Type*}
    (F : (f : G →* H) → (φ : (Action.res _ f).obj A ⟶ B) → T) :
    F f₁ φ = F f₂ (h ▸ φ) := by
  subst h
  rfl

variable [DecidableEq G] [DecidableEq H]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the chain map sending `x : Hⁿ → A` to `(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
@[simps! -isSimp f f_hom]
noncomputable def cochainsMap :
    inhomogeneousCochains A ⟶ inhomogeneousCochains B where
  f i := ModuleCat.ofHom <|
    φ.hom.hom.compLeft (Fin i → G) ∘ₗ LinearMap.funLeft k A (fun x : Fin i → G => (f ∘ x))
  comm' i j (hij : _ = _) := by
    subst hij
    ext
    simpa [inhomogeneousCochains.d_hom_apply, Fin.comp_contractNth]
      using (hom_comm_apply φ _ _).symm

@[simp]
lemma cochainsMap_id :
    cochainsMap (MonoidHom.id _) (𝟙 A) = 𝟙 (inhomogeneousCochains A) := by
  rfl

@[simp]
lemma cochainsMap_id_f_hom_eq_compLeft {A B : Rep k G} (f : A ⟶ B) (i : ℕ) :
    ((cochainsMap (MonoidHom.id G) f).f i).hom = f.hom.hom.compLeft _ := by
  ext
  rfl

@[deprecated (since := "2025-06-11")]
alias cochainsMap_id_f_eq_compLeft := cochainsMap_id_f_hom_eq_compLeft

@[reassoc]
lemma cochainsMap_comp {G H K : Type u} [Group G] [DecidableEq G] [Group H] [DecidableEq H]
    [Group K] [DecidableEq K] {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    cochainsMap (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      cochainsMap f φ ≫ cochainsMap g ψ := by
  rfl

@[reassoc]
lemma cochainsMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    cochainsMap (MonoidHom.id G) (φ ≫ ψ) =
      cochainsMap (MonoidHom.id G) φ ≫ cochainsMap (MonoidHom.id G) ψ := by
  rfl

@[simp]
lemma cochainsMap_zero : cochainsMap (A := A) (B := B) f 0 = 0 := by rfl

lemma cochainsMap_f_map_mono (hf : Function.Surjective f) [Mono φ] (i : ℕ) :
    Mono ((cochainsMap f φ).f i) := by
  simpa [ModuleCat.mono_iff_injective] using
    ((Rep.mono_iff_injective φ).1 inferInstance).comp_left.comp <|
    LinearMap.funLeft_injective_of_surjective k A _ hf.comp_left

instance cochainsMap_id_f_map_mono {A B : Rep k G} (φ : A ⟶ B) [Mono φ] (i : ℕ) :
    Mono ((cochainsMap (MonoidHom.id G) φ).f i) :=
  cochainsMap_f_map_mono (MonoidHom.id G) φ (fun x => ⟨x, rfl⟩) i

lemma cochainsMap_f_map_epi (hf : Function.Injective f) [Epi φ] (i : ℕ) :
    Epi ((cochainsMap f φ).f i) := by
  simpa [ModuleCat.epi_iff_surjective] using
    ((Rep.epi_iff_surjective φ).1 inferInstance).comp_left.comp <|
    LinearMap.funLeft_surjective_of_injective k A _ hf.comp_left

instance cochainsMap_id_f_map_epi {A B : Rep k G} (φ : A ⟶ B) [Epi φ] (i : ℕ) :
    Epi ((cochainsMap (MonoidHom.id G) φ).f i) :=
  cochainsMap_f_map_epi (MonoidHom.id G) φ (fun _ _ h => h) i

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map `Zⁿ(H, A) ⟶ Zⁿ(G, B)` sending `x : Hⁿ → A` to
`(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
noncomputable abbrev cocyclesMap (n : ℕ) :
    groupCohomology.cocycles A n ⟶ groupCohomology.cocycles B n :=
  HomologicalComplex.cyclesMap (cochainsMap f φ) n

@[simp]
lemma cocyclesMap_id : cocyclesMap (MonoidHom.id G) (𝟙 B) n = 𝟙 _ :=
  HomologicalComplex.cyclesMap_id _ _

@[reassoc]
lemma cocyclesMap_comp {G H K : Type u} [Group G] [DecidableEq G] [Group H] [DecidableEq H]
    [Group K] [DecidableEq K] {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) (n : ℕ) :
    cocyclesMap (f.comp g) ((Action.res _ g).map φ ≫ ψ) n =
      cocyclesMap f φ n ≫ cocyclesMap g ψ n := by
  simp [cocyclesMap, ← HomologicalComplex.cyclesMap_comp, ← cochainsMap_comp]

@[reassoc]
theorem cocyclesMap_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    cocyclesMap (MonoidHom.id G) (φ ≫ ψ) n =
      cocyclesMap (MonoidHom.id G) φ n ≫ cocyclesMap (MonoidHom.id G) ψ n := by
  simp [cocyclesMap, cochainsMap_id_comp, HomologicalComplex.cyclesMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map `Hⁿ(H, A) ⟶ Hⁿ(G, B)` sending `x : Hⁿ → A` to
`(g : Gⁿ) ↦ φ (x (f ∘ g))`. -/
noncomputable abbrev map (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology B n :=
  HomologicalComplex.homologyMap (cochainsMap f φ) n

@[reassoc, elementwise]
theorem π_map (n : ℕ) :
    π A n ≫ map f φ n = cocyclesMap f φ n ≫ π B n := by
  simp [map, cocyclesMap]

@[simp]
lemma map_id : map (MonoidHom.id G) (𝟙 B) n = 𝟙 _ := HomologicalComplex.homologyMap_id _ _

@[reassoc]
lemma map_comp {G H K : Type u} [Group G] [DecidableEq G] [Group H] [DecidableEq H]
    [Group K] [DecidableEq K] {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) (n : ℕ) :
    map (f.comp g) ((Action.res _ g).map φ ≫ ψ) n = map f φ n ≫ map g ψ n := by
  simp [map, ← HomologicalComplex.homologyMap_comp, ← cochainsMap_comp]

@[reassoc]
theorem map_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    map (MonoidHom.id G) (φ ≫ ψ) n =
      map (MonoidHom.id G) φ n ≫ map (MonoidHom.id G) ψ n := by
  rw [map, cochainsMap_id_comp, HomologicalComplex.homologyMap_comp]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H → A` to `(g : G) ↦ φ (x (f g))`. -/
noncomputable abbrev fOne :
    ModuleCat.of k (H → A) ⟶ ModuleCat.of k (G → B) :=
  ModuleCat.ofHom <| φ.hom.hom.compLeft G ∘ₗ LinearMap.funLeft k A f

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H → A` to `(g₁, g₂ : G × G) ↦ φ (x (f g₁, f g₂))`. -/
noncomputable abbrev fTwo :
    ModuleCat.of k (H × H → A) ⟶ ModuleCat.of k (G × G → B) :=
  ModuleCat.ofHom <| φ.hom.hom.compLeft (G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f f)

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map sending `x : H × H × H → A` to
`(g₁, g₂, g₃ : G × G × G) ↦ φ (x (f g₁, f g₂, f g₃))`. -/
noncomputable abbrev fThree :
    ModuleCat.of k (H × H × H → A) ⟶ ModuleCat.of k (G × G × G → B) :=
  ModuleCat.ofHom <|
    φ.hom.hom.compLeft (G × G × G) ∘ₗ LinearMap.funLeft k A (Prod.map f (Prod.map f f))

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cochainsMap_f_0_comp_zeroCochainsIso :
    (cochainsMap f φ).f 0 ≫ (zeroCochainsIso B).hom = (zeroCochainsIso A).hom ≫ φ.hom := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[deprecated (since := "2025-05-09")]
alias cochainsMap_f_0_comp_zeroCochainsLequiv := cochainsMap_f_0_comp_zeroCochainsIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cochainsMap_f_1_comp_oneCochainsIso :
    (cochainsMap f φ).f 1 ≫ (oneCochainsIso B).hom = (oneCochainsIso A).hom ≫ fOne f φ := by
  ext x
  simp only [cochainsMap_f, Unique.eq_default (f ∘ _)]
  rfl

@[deprecated (since := "2025-05-09")]
alias cochainsMap_f_1_comp_oneCochainsLequiv := cochainsMap_f_1_comp_oneCochainsIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cochainsMap_f_2_comp_twoCochainsIso :
    (cochainsMap f φ).f 2 ≫ (twoCochainsIso B).hom = (twoCochainsIso A).hom ≫ fTwo f φ := by
  ext x g
  show φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

@[deprecated (since := "2025-05-09")]
alias cochainsMap_f_2_comp_twoCochainsLequiv := cochainsMap_f_2_comp_twoCochainsIso

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cochainsMap_f_3_comp_threeCochainsIso :
    (cochainsMap f φ).f 3 ≫ (threeCochainsIso B).hom = (threeCochainsIso A).hom ≫ fThree f φ := by
  ext x g
  show φ.hom (x _) = φ.hom (x _)
  rcongr x
  fin_cases x <;> rfl

@[deprecated (since := "2025-05-09")]
alias cochainsMap_f_3_comp_threeCochainsLequiv := cochainsMap_f_3_comp_threeCochainsIso

end

open ShortComplex

section H0

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Aᴴ ⟶ Bᴳ`. -/
@[deprecated (since := "2025-06-09")]
alias H0Map := map

@[deprecated (since := "2025-06-09")]
alias H0Map_id := map_id

@[deprecated (since := "2025-06-09")]
alias H0Map_comp := map_comp

@[deprecated (since := "2025-06-09")]
alias H0Map_id_comp := map_id_comp

variable [DecidableEq G] [DecidableEq H]

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem map_H0Iso_hom_f :
    map f φ 0 ≫ (H0Iso B).hom ≫ (shortComplexH0 B).f =
      (H0Iso A).hom ≫ (shortComplexH0 A).f ≫ φ.hom := by
  simp [← cancel_epi (π _ _)]

@[deprecated (since := "2025-06-09")]
alias H0Map_comp_f := map_H0Iso_hom_f

@[reassoc (attr := simp), elementwise (attr := simp)]
theorem map_id_comp_H0Iso_hom {A B : Rep k G} (f : A ⟶ B) :
    map (MonoidHom.id G) f 0 ≫ (H0Iso B).hom = (H0Iso A).hom ≫ (invariantsFunctor k G).map f := by
  simp only [← cancel_mono (shortComplexH0 B).f, Category.assoc, map_H0Iso_hom_f]
  rfl

@[deprecated (since := "2025-06-09")]
alias H0Map_id_eq_invariantsFunctor_map := map_id_comp_H0Iso_hom

instance mono_map_0_of_mono {A B : Rep k G} (f : A ⟶ B) [Mono f] :
    Mono (map (MonoidHom.id G) f 0) where
  right_cancellation g h hgh := by
    simp only [← cancel_mono (H0Iso B).hom, Category.assoc, map_id_comp_H0Iso_hom] at hgh
    simp_all [cancel_mono]

@[deprecated (since := "2025-06-09")]
alias mono_H0Map_of_mono := mono_map_0_of_mono

@[reassoc, elementwise]
theorem cocyclesMap_zeroIsoCocycles_hom_f :
    cocyclesMap f φ 0 ≫ (zeroCocyclesIso B).hom ≫ (shortComplexH0 B).f =
      (zeroCocyclesIso A).hom ≫ (shortComplexH0 A).f ≫ φ.hom := by
  simp

@[deprecated (since := "2025-06-12")]
alias cocyclesMap_comp_isoZeroCocycles_hom := cocyclesMap_zeroIsoCocycles_hom_f

end H0
section H1

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex `A --dZero--> Fun(H, A) --dOne--> Fun(H × H, A)`
to `B --dZero--> Fun(G, B) --dOne--> Fun(G × G, B)`. -/
@[simps]
noncomputable def mapShortComplexH1 :
    shortComplexH1 A ⟶ shortComplexH1 B where
  τ₁ := φ.hom
  τ₂ := fOne f φ
  τ₃ := fTwo f φ
  comm₁₂ := by
    ext x
    funext g
    simpa [shortComplexH1, dZero, fOne] using (hom_comm_apply φ g x).symm
  comm₂₃ := by
    ext x
    funext g
    simpa [shortComplexH1, dOne, fOne, fTwo] using (hom_comm_apply φ _ _).symm

@[simp]
theorem mapShortComplexH1_zero :
    mapShortComplexH1 (A := A) (B := B) f 0 = 0 := by
  rfl

@[simp]
theorem mapShortComplexH1_id :
    mapShortComplexH1 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[reassoc]
theorem mapShortComplexH1_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapShortComplexH1 (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      mapShortComplexH1 f φ ≫ mapShortComplexH1 g ψ := rfl

@[reassoc]
theorem mapShortComplexH1_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH1 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH1 (MonoidHom.id G) φ ≫ mapShortComplexH1 (MonoidHom.id G) ψ := rfl

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Z¹(H, A) ⟶ Z¹(G, B)`. -/
noncomputable abbrev mapOneCocycles :
    ModuleCat.of k (oneCocycles A) ⟶ ModuleCat.of k (oneCocycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH1 f φ) (shortComplexH1 A).moduleCatLeftHomologyData
    (shortComplexH1 B).moduleCatLeftHomologyData

@[reassoc, elementwise]
lemma mapOneCocycles_comp_i :
    mapOneCocycles f φ ≫ (shortComplexH1 B).moduleCatLeftHomologyData.i =
      (shortComplexH1 A).moduleCatLeftHomologyData.i ≫ fOne f φ := by
  simp

@[simp]
lemma coe_mapOneCocycles (x) :
    ⇑(mapOneCocycles f φ x) = fOne f φ x := rfl

@[deprecated (since := "2025-05-09")]
alias mapOneCocycles_comp_subtype := mapOneCocycles_comp_i

variable [DecidableEq G] [DecidableEq H] in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cocyclesMap_comp_isoOneCocycles_hom :
    cocyclesMap f φ 1 ≫ (isoOneCocycles B).hom = (isoOneCocycles A).hom ≫ mapOneCocycles f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, mapShortComplexH1,
    cochainsMap_f_1_comp_oneCochainsIso f]

@[simp]
theorem mapOneCocycles_one (φ : (Action.res _ 1).obj A ⟶ B) :
    mapOneCocycles 1 φ = 0 := by
  rw [← cancel_mono (moduleCatLeftHomologyData (shortComplexH1 B)).i, cyclesMap'_i]
  refine ModuleCat.hom_ext (LinearMap.ext fun _ ↦ funext fun y => ?_)
  simp [mapShortComplexH1, shortComplexH1, moduleCatMk, Pi.zero_apply y]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `H¹(H, A) ⟶ H¹(G, B)`. -/
@[deprecated (since := "2025-06-09")]
alias H1Map := map

@[deprecated (since := "2025-6-09")]
alias H1Map_id := map_id

@[deprecated (since := "2025-06-09")]
alias H1Map_comp := map_comp

@[deprecated (since := "2025-06-09")]
alias H1Map_id_comp := map_id_comp

variable [DecidableEq G] [DecidableEq H]

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H1π_comp_map :
    H1π A ≫ map f φ 1 = mapOneCocycles f φ ≫ H1π B := by
  simp [H1π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoOneCocycles_hom_assoc]

@[deprecated (since := "2025-06-12")]
alias H1π_comp_H1Map := H1π_comp_map

@[simp]
theorem map_1_one (φ : (Action.res _ 1).obj A ⟶ B) :
    map 1 φ 1 = 0 := by
  simp [← cancel_epi (H1π _)]

@[deprecated (since := "2025-06-09")]
alias H1Map_one := map_1_one

section InfRes

variable (A : Rep k G) (S : Subgroup G) [S.Normal] [DecidableEq (G ⧸ S)]

/-- The short complex `H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)`. -/
@[simps X₁ X₂ X₃ f g]
noncomputable def H1InfRes :
    ShortComplex (ModuleCat k) where
  X₁ := groupCohomology (A.quotientToInvariants S) 1
  X₂ := groupCohomology A 1
  X₃ := groupCohomology ((Action.res _ S.subtype).obj A) 1
  f := map (QuotientGroup.mk' S) (subtype _ _ <| le_comap_invariants A.ρ S) 1
  g := map S.subtype (𝟙 _) 1
  zero := by rw [← map_comp, Category.comp_id, congr (QuotientGroup.mk'_comp_subtype S)
    (fun f φ => map f φ 1), map_1_one]

/-- The inflation map `H¹(G ⧸ S, A^S) ⟶ H¹(G, A)` is a monomorphism. -/
instance : Mono (H1InfRes A S).f := by
  rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₁, H1InfRes_f, H1π_comp_map_apply (QuotientGroup.mk' S)]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨y, hy⟩
  refine (H1π_eq_zero_iff _).2 ⟨⟨y, fun s => ?_⟩, funext fun g => QuotientGroup.induction_on g
    fun g => Subtype.ext <| by simpa [-SetLike.coe_eq_coe] using congr_fun hy g⟩
  simpa [coe_mapOneCocycles (x := x), sub_eq_zero, (QuotientGroup.eq_one_iff s.1).2 s.2] using
    congr_fun hy s.1

/-- Given a `G`-representation `A` and a normal subgroup `S ≤ G`, the short complex
`H¹(G ⧸ S, A^S) ⟶ H¹(G, A) ⟶ H¹(S, A)` is exact. -/
lemma H1InfRes_exact : (H1InfRes A S).Exact := by
  rw [moduleCat_exact_iff_ker_sub_range]
  intro x hx
  induction x using H1_induction_on with | @h x =>
  simp_all only [H1InfRes_X₂, H1InfRes_X₃, H1InfRes_g, H1InfRes_X₁, LinearMap.mem_ker,
    H1π_comp_map_apply S.subtype, H1InfRes_f]
  rcases (H1π_eq_zero_iff _).1 hx with ⟨(y : A), hy⟩
  have h1 := (mem_oneCocycles_iff x).1 x.2
  have h2 : ∀ s ∈ S, x s = A.ρ s y - y :=
    fun s hs => funext_iff.1 hy.symm ⟨s, hs⟩
  refine ⟨H1π _ ⟨fun g => Quotient.liftOn' g (fun g => ⟨x.1 g - A.ρ g y + y, ?_⟩) ?_, ?_⟩, ?_⟩
  · intro s
    calc
      _ = x (s * g) - x s - A.ρ s (A.ρ g y) + (x s + y) := by
        simp [add_eq_of_eq_sub (h2 s s.2), sub_eq_of_eq_add (h1 s g)]
      _ = x (g * (g⁻¹ * s * g)) - A.ρ g (A.ρ (g⁻¹ * s * g) y - y) - A.ρ g y + y := by
        simp only [mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply, map_sub,
          Representation.self_inv_apply]
        abel
      _ = x g - A.ρ g y + y := by
        simp [eq_sub_of_add_eq' (h1 g (g⁻¹ * s * g)).symm,
          h2 (g⁻¹ * s * g) (Subgroup.Normal.conj_mem' ‹_› _ s.2 _)]
  · intro g h hgh
    have := congr(A.ρ g $(h2 (g⁻¹ * h) <| QuotientGroup.leftRel_apply.1 hgh))
    simp_all [← sub_eq_add_neg, sub_eq_sub_iff_sub_eq_sub]
  · rw [mem_oneCocycles_iff]
    intro g h
    induction g using QuotientGroup.induction_on with | @H g =>
    induction h using QuotientGroup.induction_on with | @H h =>
    apply Subtype.ext
    simp [← QuotientGroup.mk_mul, h1 g h, sub_add_eq_add_sub, add_assoc]
  · symm
    simp only [H1π_comp_map_apply, H1π_eq_iff (A := A)]
    use y
    ext g
    simp [coe_mapOneCocycles (QuotientGroup.mk' S),
      oneCocycles.coe_mk (A := A.quotientToInvariants S), ← sub_sub]

end InfRes
end H1
section H2

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is the induced map from the short complex
`Fun(H, A) --dOne--> Fun(H × H, A) --dTwo--> Fun(H × H × H, A)` to
`Fun(G, B) --dOne--> Fun(G × G, B) --dTwo--> Fun(G × G × G, B)`. -/
@[simps]
noncomputable def mapShortComplexH2 :
    shortComplexH2 A ⟶ shortComplexH2 B where
  τ₁ := fOne f φ
  τ₂ := fTwo f φ
  τ₃ := fThree f φ
  comm₁₂ := by
    ext x
    funext g
    simpa [shortComplexH2, dOne, fOne, fTwo] using (hom_comm_apply φ _ _).symm
  comm₂₃ := by
    ext x
    funext g
    simpa [shortComplexH2, dTwo, fTwo, fThree] using (hom_comm_apply φ _ _).symm

@[simp]
theorem mapShortComplexH2_zero :
    mapShortComplexH2 (A := A) (B := B) f 0 = 0 := rfl

@[simp]
theorem mapShortComplexH2_id :
    mapShortComplexH2 (MonoidHom.id _) (𝟙 A) = 𝟙 _ := by
  rfl

@[reassoc]
theorem mapShortComplexH2_comp {G H K : Type u} [Group G] [Group H] [Group K]
    {A : Rep k K} {B : Rep k H} {C : Rep k G} (f : H →* K) (g : G →* H)
    (φ : (Action.res _ f).obj A ⟶ B) (ψ : (Action.res _ g).obj B ⟶ C) :
    mapShortComplexH2 (f.comp g) ((Action.res _ g).map φ ≫ ψ) =
      mapShortComplexH2 f φ ≫ mapShortComplexH2 g ψ := rfl

@[reassoc]
theorem mapShortComplexH2_id_comp {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) :
    mapShortComplexH2 (MonoidHom.id G) (φ ≫ ψ) =
      mapShortComplexH2 (MonoidHom.id G) φ ≫ mapShortComplexH2 (MonoidHom.id G) ψ := rfl

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `Z²(H, A) ⟶ Z²(G, B)`. -/
noncomputable abbrev mapTwoCocycles :
    ModuleCat.of k (twoCocycles A) ⟶ ModuleCat.of k (twoCocycles B) :=
  ShortComplex.cyclesMap' (mapShortComplexH2 f φ) (shortComplexH2 A).moduleCatLeftHomologyData
    (shortComplexH2 B).moduleCatLeftHomologyData

@[reassoc, elementwise]
lemma mapTwoCocycles_comp_i :
    mapTwoCocycles f φ ≫ (shortComplexH2 B).moduleCatLeftHomologyData.i =
      (shortComplexH2 A).moduleCatLeftHomologyData.i ≫ fTwo f φ := by
  simp

@[simp]
lemma coe_mapTwoCocycles (x) :
    ⇑(mapTwoCocycles f φ x) = fTwo f φ x := rfl

@[deprecated (since := "2025-05-09")]
alias mapTwoCocycles_comp_subtype := mapTwoCocycles_comp_i

variable [DecidableEq G] [DecidableEq H] in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma cocyclesMap_comp_isoTwoCocycles_hom :
    cocyclesMap f φ 2 ≫ (isoTwoCocycles B).hom = (isoTwoCocycles A).hom ≫ mapTwoCocycles f φ := by
  simp [← cancel_mono (moduleCatLeftHomologyData (shortComplexH2 B)).i, mapShortComplexH2,
    cochainsMap_f_2_comp_twoCochainsIso f]

/-- Given a group homomorphism `f : G →* H` and a representation morphism `φ : Res(f)(A) ⟶ B`,
this is induced map `H²(H, A) ⟶ H²(G, B)`. -/
@[deprecated (since := "2025-06-09")]
alias H2Map := map

@[deprecated (since := "2025-06-09")]
alias H2Map_id := map_id

@[deprecated (since := "2025-06-09")]
alias H2Map_comp := map_comp

@[deprecated (since := "2025-06-09")]
alias H2Map_id_comp := map_id_comp

variable [DecidableEq G] [DecidableEq H] in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma H2π_comp_map :
    H2π A ≫ map f φ 2 = mapTwoCocycles f φ ≫ H2π B := by
  simp [H2π, Iso.inv_comp_eq, ← cocyclesMap_comp_isoTwoCocycles_hom_assoc]

@[deprecated (since := "2025-06-12")]
alias H2π_comp_H2Map := H2π_comp_map

end H2

variable [DecidableEq G]

variable (k G) in
/-- The functor sending a representation to its complex of inhomogeneous cochains. -/
@[simps]
noncomputable def cochainsFunctor : Rep k G ⥤ CochainComplex (ModuleCat k) ℕ where
  obj A := inhomogeneousCochains A
  map f := cochainsMap (MonoidHom.id _) f
  map_id _ := cochainsMap_id
  map_comp φ ψ := cochainsMap_comp (MonoidHom.id G) (MonoidHom.id G) φ ψ

instance : (cochainsFunctor k G).PreservesZeroMorphisms where
instance : (cochainsFunctor k G).Additive where

variable (k G) in
/-- The functor sending a `G`-representation `A` to `Hⁿ(G, A)`. -/
@[simps]
noncomputable def functor (n : ℕ) : Rep k G ⥤ ModuleCat k where
  obj A := groupCohomology A n
  map φ := map (MonoidHom.id _) φ n
  map_id _ := HomologicalComplex.homologyMap_id _ _
  map_comp _ _ := by
    simp only [← HomologicalComplex.homologyMap_comp]
    rfl

instance (n : ℕ) : (functor k G n).PreservesZeroMorphisms where
  map_zero _ _ := by simp [map]

end groupCohomology
