import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Skyscraper
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Testing
import Mathlib.Topology.Sheaves.LocallySurjective

--set_option backward.isDefEq.respectTransparency false

/-!
# Twisted closed subscheme exact sequence

In this file we define the following exact sequence on a curve:
`0 → 𝒪ₓ(D - P) → 𝒪ₓ(D) → k(P) → 0` where `k(P)` is the skyscraper
at `P` for some closed point `P`.
-/
universe u

open Function.locallyFinsuppWithin

open AlgebraicGeometry AlgebraicCycle Sheaf Opposite Order

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (p : X)

namespace AlgebraicCycle
namespace Sheaf

/-
If `f` is a section of `𝒪ₓ(D)`, then it is also a section of `𝒪ₓ(D + D')` for effective `D'`.
-/
lemma extend_prop {D D' : AlgebraicCycle X ℤ} (h : D' ≥ 0) (U : (TopologicalSpace.Opens ↥X)ᵒᵖ)
    {f : X.functionField} (hf : f ∈ carrier D U.unop) : f ∈ carrier (D + D') U.unop := by
  simp only [carrier, ne_eq, Scheme.Opens.nonempty_iff, ge_iff_le, Set.mem_setOf_eq] at hf ⊢
  intro fnez
  specialize hf fnez
  constructor
  · exact hf.1
  intro hx
  apply le_trans hf.2
  simp only [add_le_add_iff_left]
  intro z
  simp [restrict_apply]
  split_ifs
  · simpa using h z
  · rfl

variable [IsRegularInCodimensionOne X]

/--
The inclusion mapping `𝒪ₓ(D) ⟶ 𝒪ₓ(D + D')`, defined by `h ↦ h`.
-/
noncomputable
def extend (D D' : AlgebraicCycle X ℤ) (h : D' ≥ 0) :
    D.sheaf ⟶ (D + D').sheaf where
  val := {
    app U :=
      ModuleCat.ofHom
        {
          toFun := fun m ↦ ⟨m.val, extend_prop h U m.prop⟩
          map_add' := by
            intro a b
            --apply Subtype.ext
            rfl
          map_smul' := by
            intro r x
            --apply Subtype.ext
            --simp only [RingHom.id_apply]
            rfl
        }
    naturality {U V} f := by
      apply ModuleCat.hom_ext
      ext ⟨v, hv⟩
      apply Subtype.ext

      -- Both paths: extend then restrict, or restrict then extend
      -- Both preserve the underlying value v

      simp [Sheaf.map, mapFun, presheaf, sheaf]
      sorry
      --split_ifs <;> rfl
  }

open CategoryTheory

/--
The inclusion morphism `𝒪ₓ(D) ⟶ 𝒪ₓ(D + D')` is a monomorphism
-/
lemma extend_mono (D D' : AlgebraicCycle X ℤ) (h : D' ≥ 0) :
    Mono <| extend D D' h := by
  suffices ∀ (U : (TopologicalSpace.Opens ↥X)ᵒᵖ), Function.Injective <|
    (extend D D' h).val.app U by
    suffices Mono <| (SheafOfModules.toSheaf X.ringCatSheaf).map <|
      extend D D' h by cat_disch
    exact
      Sheaf.mono_of_injective
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (extend D D' h)) this
  intro U
  simp [extend]
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  change (AddHom.toFun _) (⟨x, hx⟩ : ↑((D.sheaf).val.obj U)) =
         (AddHom.toFun _) (⟨y, hy⟩ : ↑((D.sheaf).val.obj U)) at h
  --change (ModuleCat.ofHom _) _ = (ModuleCat.ofHom _) _ at h
  simp at h

  --simp [-AddHom.toFun_eq_coe, -LinearMap.toFun_eq_coe] at h
  --change (fun (x : ↑(carrier D (unop U))) ↦ ⟨↑x, extend._proof_1 D D' U ↑x⟩) ⟨x, hx⟩ = (fun x ↦ ⟨↑x, _⟩) ⟨y, hy⟩ at h
  -- Modified by Claude Opus 4.6: replaced broken grind
  have hxy : x = y := by
    have := congr_arg Subtype.val h
    sorry
    --simpa using this
  exact Subtype.ext hxy

open Function.locallyFinsuppWithin
omit [IsRegularInCodimensionOne X] in
open Classical in
/--
A cycle supported at a single point with a positive coefficient is effective.
-/
lemma _root_.AlgebraicCycle.single_effective (x : X) (c : ℤ) (hc : c ≥ 0) : single x c ≥ 0 := by
  intro z
  simp [single_apply]
  by_cases o : x = z
  all_goals grind


variable (D : AlgebraicCycle X ℤ)
open Classical in
/--
On open sets away from a point `P`, `extend` is surjective (and hence bijective, and hence
an isomorphism of modules)
-/
lemma extend_surjective (U : X.Opensᵒᵖ) (hU : p ∉ U.1) :
    Function.Surjective <| ((extend (D - single p 1) (single p 1)
    (single_effective p 1 (by simp))).val.app U).hom := by
  intro ⟨f, hf⟩
  refine ⟨⟨f, ?_⟩, ?_⟩
  · simp only [carrier] at hf ⊢
    intro fnez
    specialize hf fnez
    refine ⟨hf.1, ?_⟩
    apply le_trans hf.2
    intro z
    simp [restrict_apply]
    split_ifs with hz
    · have hzp : z ≠ p := fun h => hU (h ▸ hz)
      simp [hzp]
    · rfl
  · apply Subtype.ext
    rfl

noncomputable
def toSkyscraperFun {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) (hp' : p ∈ U) :
    letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
    (D.sheaf).val.obj (op U) →ₗ[Γ(X, U)] ↑(X.residueField p) :=
  let f1 := germModuleHom (D.sheaf) U p hp'
  let _ : Module ↑Γ(X, U) ↑(X.presheaf.stalk p) := (X.presheaf.germ U p hp').hom.toModule
  let _ : Module ↑(X.presheaf.stalk p) ↑(X.residueField p) := (X.residue p).hom.toModule
  letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
  have : IsScalarTower Γ(X, U) ↑(X.presheaf.stalk p) ↑(X.residueField p) := sorry
  let : Module ↑Γ(X, U) ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p) := l (D.sheaf) U p hp'
  have : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk p) ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p) := sorry
  have : LinearMap.CompatibleSMul ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p) ↑(X.presheaf.stalk p) ↑Γ(X, U)
    ↑(X.presheaf.stalk p) := sorry
  let f2 := (stalkEquiv D hD p hp ϖ hϖ).restrictScalars Γ(X, U)
  let f3 := (Module.compHom.toLinearMap (X.residue p).hom).restrictScalars Γ(X, U)
  f3 ∘ₗ f2 ∘ₗ f1

/-
This precisely says that the kernel is all those sections of 𝒪ₓ(D) which are also sections
of 𝒪ₓ(P)

ker (f3 ∘ f2 ∘ f1) = Submodule.comap (f3 ∘ f2) (ker f1)
-/
lemma toSkyscraperFun_ker {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) (hp' : p ∈ U) :
    letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
  (toSkyscraperFun p D hD ϖ hϖ hp hp').ker.carrier = {f : Γ(D.sheaf, U) | X.ord f.1 p ≥ 1 - D p} := by
  simp [toSkyscraperFun, LinearMap.ker_comp, Set.preimage_comp, Scheme.residue]
  have := IsLocalRing.ker_residue (R := X.presheaf.stalk p)
  suffices ⇑(germModuleHom D.sheaf U p hp') ⁻¹'
    ⇑(D.stalkEquiv hD p hp ϖ hϖ) ⁻¹' IsLocalRing.maximalIdeal ↑(X.presheaf.stalk p) by sorry

  --[IsLocalRing.ker_residue]
  #check IsLocalRing.residue_eq_zero_iff
  #check IsLocalRing.ker_residue

  sorry
#check TopCat.Presheaf.isLocallySurjective_iff
/-
For this local surjectivity proof, we want to say that given a section s of k(X) over U, for any
x ∈ U there is always a neighbourhood V of x such that the restriction of s to V is in the image of
a section of Oₓ(D).


-/









/-
We should be able to use the following lemmas to show that the kernel is what we expect

+ We should have that f3 has no kernel, so we can get rid of it from considerations
+ We should have that the things mapping to the maximal ideal under f2 are just the
  multiples of ϖ^(D p)
Then we win
-/
#check IsLocalRing.residue_eq_zero_iff
#check LinearMap.ker_comp
#check LinearEquiv.ker_comp

/-
We want that toSkyscraperFun has kernel ⟨ϖ^(-D p)⟩, and then we should be able to
prove exactness quite easily
-/


/--
Map from `𝒪ₓ(D)` to the skyscraper sheaf at a point `p` on an open set U.

NOTE: It is very annoying to work with this stupid if then else notion. I think we
should define the map on sets containing and not containing p separately.

PLAN: Ignore this nonsense for now, define all the maps without the sheaf machinery
and just show all of the exactness and such there
-/
noncomputable
def toSkyscraper {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) :
    (D.sheaf).val.obj (op U) ⟶ (skyscraperSheafOfModules p).val.obj (op U) := by
  by_cases o : p ∈ U
  · classical
    refine ModuleCat.ofHom (X := D.sheaf.val.obj (op U))
        (Y := (skyscraperSheafOfModules p).val.obj (op U)) ?_
    let f1 := germModuleHom (D.sheaf) U p o
    let _ : Module ↑Γ(X, U) ↑(X.presheaf.stalk p) := (X.presheaf.germ U p o).hom.toModule
    let _ : Module ↑(X.presheaf.stalk p) ↑(X.residueField p) := (X.residue p).hom.toModule
    letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p o).hom.toModule
    have : IsScalarTower Γ(X, U) ↑(X.presheaf.stalk p) ↑(X.residueField p) := sorry
    let : Module ↑Γ(X, U) ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p) := l (D.sheaf) U p o
    have : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk p) ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p) := sorry
    have : LinearMap.CompatibleSMul ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p) ↑(X.presheaf.stalk p) ↑Γ(X, U)
      ↑(X.presheaf.stalk p) := sorry
    let f2 := (stalkEquiv D hD p hp ϖ hϖ).toLinearMap.restrictScalars Γ(X, U)
    let f3 := (Module.compHom.toLinearMap (X.residue p).hom).restrictScalars Γ(X, U)
    let f : ↑Γ(D.sheaf, U) →ₗ[Γ(X, U)] X.residueField p := f3 ∘ₗ f2 ∘ₗ f1
    simp [skyscraperSheafOfModules, skyscraperPresheafOfModules,
      skyscraperAb]
    simp_rw [← PresheafOfModules.presheaf_obj_coe]
    #check TopCat.Sheaf.presheaf
    have := skyscraperSheaf_obj_obj p (X.residueField p)
    dsimp [skyscraperSheaf, skyscraperPresheaf]



    /-
    TODO: Write some API for skyscraperSheafOfModules that makes this easy
    -/
    sorry
  exact 0

instance (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1)
    (hD : ∀ z : X, coheight z ≠ 1 → D z ≥ 0)
    (pClosed : ∀ x : X, x ≤ p → x = p) :
    CategoryTheory.Sheaf.IsLocallySurjective <|
    (SheafOfModules.toSheaf X.ringCatSheaf).map <| toSkyscraper p D ϖ hϖ hp := by
  -- Add Mathlib.Topology.Sheaves.LocallySurjective
  #check TopCat.Presheaf.isLocallySurjective_iff
  sorry

open Classical in
noncomputable
def twistedClosedSubschemeComplex (hD : support D ⊆ {x | coheight x = 1}) (ϖ : X.presheaf.stalk p)
    (hϖ : Irreducible ϖ) (hp : coheight p = 1) :
  ShortComplex X.Modules where
  X₁ := (D - single p 1).sheaf
  X₂ := D.sheaf
  X₃ := skyscraperSheafOfModules p
  f := sorry
  g := sorry --toSkyscraper p D hD ϖ hϖ hp
  zero := sorry

/-
This should be no work at all with the above definitons (at least that's the hope).
-/
lemma twistedClosedSubschemeComplex_exact (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ)
    (hp : coheight p = 1)
    (PClosed : ∀ x : X, x ≤ p → x = p) : (twistedClosedSubschemeComplex p D hD ϖ hϖ hp).Exact :=
    sorry

end Sheaf
end AlgebraicCycle
