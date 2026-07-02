import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Skyscraper
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Testing
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Twisted closed subscheme exact sequence

In this file we define the following exact sequence on a curve:
`0 → 𝒪ₓ(D - P) → 𝒪ₓ(D) → k(P) → 0` where `k(P)` is the skyscraper
at `P` for some closed point `P`.

Notes: the way this is constructed is mildly idiosyncratic, mainly for the purposes of avoiding
tensor products of sheaves of modules like the plague. Nevertheless, this has some "practical"
implications. Namely, nowhere do we ever assume here that the variety we're working on is a curve,
which means regular in codimension one does not necessarily imply regular. In particular we do not
assume that `𝒪ₓ(D)` is invertible, and so we cannot assume tensoring by `𝒪ₓ(D)` is exact.
So, technically speaking this is a more general exact sequence than the one constructed
in, say, Hartshorne by tensoring the closed subscheme exact sequence with `𝒪ₓ(D)`.
-/
universe u

open Function.locallyFinsuppWithin

open AlgebraicGeometry AlgebraicCycle Sheaf Opposite Order CategoryTheory

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable (p : X)

namespace AlgebraicCycle
namespace Sheaf

open Function.locallyFinsuppWithin
open Classical in
/--
A cycle supported at a single point with a positive coefficient is effective.
-/
lemma _root_.AlgebraicCycle.single_effective (x : X) (c : ℤ) (hc : c ≥ 0) : single x c ≥ 0 := by
  intro z
  simp [single_apply]
  by_cases o : x = z
  all_goals grind


variable (D : AlgebraicCycle X ℤ) [IsRegularInCodimensionOne X]

noncomputable
def toSkyscraperFun {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) (hp' : p ∈ U) :
    letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
    (D.sheaf).val.obj (op U) →ₗ[Γ(X, U)] ↑(X.residueField p) :=
  let f1 := germModuleHom (D.sheaf) U p hp'
  let _ : Module ↑Γ(X, U) ↑(X.presheaf.stalk p) := (X.presheaf.germ U p hp').hom.toModule
  let _ : Module ↑(X.presheaf.stalk p) ↑(X.residueField p) := (X.residue p).hom.toModule
  letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
  have : IsScalarTower Γ(X, U) ↑(X.presheaf.stalk p) ↑(X.residueField p) := by
    constructor
    intro r s t
    change (X.residue p).hom ((X.presheaf.germ U p hp').hom r * s) * t =
      (X.evaluation U p hp').hom r * ((X.residue p).hom s * t)
    rw [map_mul, mul_assoc]
    rfl
  let : Module ↑Γ(X, U) ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p) := l (D.sheaf) U p hp'
  -- The action of `Γ(X, U)` on the stalk of `𝒪ₓ(D)` (given by `l`, via the `RingCat`-valued
  -- germ) agrees with acting by the germ in `X.presheaf.stalk p`.
  have key : ∀ (r : ↑Γ(X, U)) (m : ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p)),
      r • m = (X.presheaf.germ U p hp' r : ↑(X.presheaf.stalk p)) • m := by
    intro r m
    obtain ⟨W, hpW, m', rfl⟩ := TopCat.Presheaf.exists_germ_eq D.sheaf.val.presheaf m
    have hpΩ : p ∈ U ⊓ W := ⟨hp', hpW⟩
    change TopCat.Presheaf.germ X.ringCatSheaf.presheaf U p hp' r •
      TopCat.Presheaf.germ D.sheaf.val.presheaf W p hpW m' = _
    rw [← TopCat.Presheaf.germ_res_apply D.sheaf.val.presheaf
        (homOfLE (inf_le_right : U ⊓ W ≤ W)) p hpΩ m',
      ← TopCat.Presheaf.germ_res_apply X.ringCatSheaf.presheaf
        (homOfLE (inf_le_left : U ⊓ W ≤ U)) p hpΩ r,
      ← TopCat.Presheaf.germ_res_apply X.presheaf
        (homOfLE (inf_le_left : U ⊓ W ≤ U)) p hpΩ r,
      ← PresheafOfModules.germ_ringCat_smul (M := D.sheaf.val) p (U ⊓ W) hpΩ]
    exact PresheafOfModules.germ_smul (R := X.presheaf) (M := D.sheaf.val) p (U ⊓ W) hpΩ _ _
  have : IsScalarTower ↑Γ(X, U) ↑(X.presheaf.stalk p)
    ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p) := by
    constructor
    intro r s m
    rw [key r (s • m)]
    change ((X.presheaf.germ U p hp' r : ↑(X.presheaf.stalk p)) * s) • m = _
    rw [mul_smul]
  have : LinearMap.CompatibleSMul ↑(TopCat.Presheaf.stalk D.sheaf.val.presheaf p)
    ↑(X.presheaf.stalk p) ↑Γ(X, U)
    ↑(X.presheaf.stalk p) := by
    constructor
    intro f r m
    rw [key r m, map_smul]
    rfl
  let f2 := (stalkEquiv D hD p hp ϖ hϖ).restrictScalars Γ(X, U)
  let f3 := (Module.compHom.toLinearMap (X.residue p).hom).restrictScalars Γ(X, U)
  f3 ∘ₗ f2 ∘ₗ f1

open Classical in
lemma toSkyscraperFun_ker {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) (hp' : p ∈ U) :
    letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
    (toSkyscraperFun p D hD ϖ hϖ hp hp').ker.carrier =
    {f : Γ(D.sheaf, U) | f.1 ∈ carrier (D - single p 1) U} := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
    IsRegularInCodimensionOne.stalk_dvr p hp
  ext s
  simp only [Submodule.mem_carrier, SetLike.mem_coe, LinearMap.mem_ker]
  set a := stalkEquiv D hD p hp ϖ hϖ (germModuleHom D.sheaf U p hp' s) with ha_def
  -- The function field realization of the stalk element associated to `s` is `ϖ ^ D p * s`.
  have hspec : algebraMap (X.presheaf.stalk p) X.functionField a =
      (algebraMap (X.presheaf.stalk p) X.functionField ϖ) ^ (D p) * s.1 := by
    rw [ha_def, algebraMap_stalkEquiv_apply]
    congr 1
    exact stalkToFunctionField_germ D p U hp' s
  -- Kernel membership is membership of the stalk element in the maximal ideal.
  have hker : toSkyscraperFun p D hD ϖ hϖ hp hp' s = 0 ↔
      a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) :=
    IsLocalRing.residue_eq_zero_iff a
  rw [hker]
  by_cases hs : (s.1 : X.functionField) = 0
  · -- Both sides hold for the zero section.
    constructor
    · intro _ hne
      exact absurd hs hne
    · intro _
      have ha0 : a = 0 := by
        have h0 := hspec
        rw [hs, mul_zero] at h0
        exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mp h0
      rw [ha0]
      exact zero_mem _
  · -- The interesting case: compare orders of vanishing at `p`.
    have hϖK : algebraMap (X.presheaf.stalk p) X.functionField ϖ ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
      exact hϖ.ne_zero
    have hKa : algebraMap (X.presheaf.stalk p) X.functionField a ≠ 0 := by
      rw [hspec]
      exact mul_ne_zero (zpow_ne_zero _ hϖK) hs
    have hane : a ≠ 0 := fun h => hKa (by rw [h, map_zero])
    have hord : X.ord (algebraMap (X.presheaf.stalk p) X.functionField a) p =
        D p + X.ord s.1 p := by
      rw [hspec, X.ord_mul hp (zpow_ne_zero _ hϖK) hs, ord_zpow_algebraMap_irreducible hp hϖ]
    rw [mem_maximalIdeal_iff_one_le_ord hp hane, hord]
    constructor
    · -- The order bound at `p` gives the section condition for `D - single p 1`.
      intro hle hne
      refine ⟨⟨⟨p, hp'⟩⟩, ?_⟩
      intro z
      simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
        Function.locallyFinsuppWithin.coe_add, Pi.add_apply, restrict_apply]
      split_ifs with hzU
      · simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, single_apply,
          div_eq_ord]
        by_cases hzp : z = p
        · subst hzp
          omega
        · simp only [if_neg hzp, sub_zero]
          have h2 := (s.2 hne).2 z
          simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
            Function.locallyFinsuppWithin.coe_add, Pi.add_apply, restrict_apply, if_pos hzU,
            div_eq_ord] at h2
          omega
      · simp
    · -- Conversely, evaluate the section condition at `p`.
      intro hcar
      have h2 := (hcar hs).2 p
      simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
        Function.locallyFinsuppWithin.coe_add, Pi.add_apply, restrict_eq_of_mem _ _ _ hp',
        Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, single_apply, if_true,
        div_eq_ord] at h2
      omega

open Classical in
/--
Every element of the residue field at `p` is hit by `toSkyscraperFun` applied to a section of
`𝒪ₓ(D)` over some neighbourhood `V` of `p`: lift `y` to a unit `a` of the local ring and use
the rational function `ϖ ^ (-D p) * a`, which is a section of `𝒪ₓ(D)` after shrinking `V` so
that the only point of `V` where `ϖ ^ (-D p) * a` or `D` is supported is `p` itself.

Note: an earlier version of this statement asked for `V` to contain an additional arbitrary
point `x` as well; that statement is too strong (the section `ϖ ^ (-D p) * a` can acquire
poles away from `p`, and a section over a large `V` must satisfy the divisor condition
everywhere on `V`). For local surjectivity of `toSkyscraperHom` at a closed point `p` only
the present statement is needed: at points `x ≠ p` one can choose `V` avoiding `p`, where the
skyscraper has no sections.
-/
lemma toSkyscraperFun_isLocallySurjective (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) :
    ∀ (y : X.residueField p), ∃ (V : X.Opens) (hpV : p ∈ V),
    ∃ s : Γ(D.sheaf, V), toSkyscraperFun p D hD ϖ hϖ hp hpV s = y := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
    IsRegularInCodimensionOne.stalk_dvr p hp
  intro y
  by_cases hy : y = 0
  · exact ⟨⊤, trivial, 0, by subst hy; exact map_zero _⟩
  -- Lift `y` to the local ring; since `y ≠ 0` the lift is a unit.
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := X.presheaf.stalk p) y
  have haU : IsUnit a := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, ha]
    exact hy
  have ha0 : a ≠ 0 := haU.ne_zero
  have hϖK : algebraMap (X.presheaf.stalk p) X.functionField ϖ ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    exact hϖ.ne_zero
  have hKa : algebraMap (X.presheaf.stalk p) X.functionField a ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)]
    exact ha0
  -- The candidate rational function.
  set h : X.functionField := (algebraMap (X.presheaf.stalk p) X.functionField ϖ) ^ (-(D p)) *
    algebraMap (X.presheaf.stalk p) X.functionField a with hh_def
  have hne : h ≠ 0 := mul_ne_zero (zpow_ne_zero _ hϖK) hKa
  -- Units have order zero, so `h` has order exactly `-D p` at `p`.
  have ha_ord : X.ord (algebraMap (X.presheaf.stalk p) X.functionField a) p = 0 := by
    have h1 : ¬ (1 ≤ X.ord (algebraMap (X.presheaf.stalk p) X.functionField a) p) := by
      rw [← mem_maximalIdeal_iff_one_le_ord hp ha0, IsLocalRing.mem_maximalIdeal,
        mem_nonunits_iff, not_not]
      exact haU
    have h2 := ord_algebraMap_nonneg hp ha0
    omega
  have hh_ord : X.ord h p = -(D p) := by
    rw [hh_def, X.ord_mul hp (zpow_ne_zero _ hϖK) hKa,
      ord_zpow_algebraMap_irreducible hp hϖ, ha_ord, add_zero]
  -- Choose a neighbourhood of `p` where the only supported point specializing into it is `p`.
  obtain ⟨Uh, hUh1, hUh2, hUh3⟩ :=
    Function.locallyFinsupp.exists_nhd_mem_support_implies_specializes (div h) p
  obtain ⟨UD, hUD1, hUD2, hUD3⟩ :=
    Function.locallyFinsupp.exists_nhd_mem_support_implies_specializes D p
  set V : X.Opens := ⟨Uh ∩ UD, hUh1.inter hUD1⟩ with hV_def
  have hpV : p ∈ V := ⟨hUh2, hUD2⟩
  have spec_eq : ∀ (z : X), coheight z = 1 → z ⤳ p → z = p := by
    intro z hz hspec
    have hxz : p ≤ z := hspec
    by_cases hzx : z ≤ p
    · exact (Specializes.antisymm hspec (hzx : p ⤳ z)).eq
    · have hbound := Order.coheight_add_one_le <| lt_of_le_not_ge hxz hzx
      rw [hz, hp] at hbound
      norm_num at hbound
  -- `h` is a section of `𝒪ₓ(D)` over `V`.
  have hcar : h ∈ carrier D V := by
    intro _
    refine ⟨⟨⟨p, hpV⟩⟩, ?_⟩
    intro z
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
      Function.locallyFinsuppWithin.coe_add, Pi.add_apply, restrict_apply]
    split_ifs with hzV
    · by_cases hzp : z = p
      · subst hzp
        simp only [div_eq_ord, hh_ord]
        omega
      · have hdiv_z : (div h) z = 0 := by
          by_cases hzcoh : coheight z = 1
          · by_contra hord
            exact hzp (spec_eq z hzcoh (hUh3 z ⟨hzV.1, hord⟩))
          · simp [div_eq_ord, Scheme.ord_eq_zero_of_coheight_neq_one hzcoh]
        have hD_z : D z = 0 := by
          by_contra hD'
          have hzcoh : coheight z = 1 := hD hD'
          exact hzp (spec_eq z hzcoh (hUD3 z ⟨hzV.2, hD'⟩))
        rw [hdiv_z, hD_z]
        simp
    · simp
  refine ⟨V, hpV, ⟨h, hcar⟩, ?_⟩
  -- The stalk element associated to `h` is `a`, whose residue is `y`.
  have hstalk : stalkEquiv D hD p hp ϖ hϖ (germModuleHom D.sheaf V p hpV ⟨h, hcar⟩) = a := by
    apply FaithfulSMul.algebraMap_injective (X.presheaf.stalk p) X.functionField
    rw [algebraMap_stalkEquiv_apply]
    have hgerm : D.stalkToFunctionFieldLinearMap p (germModuleHom D.sheaf V p hpV ⟨h, hcar⟩) =
        h := stalkToFunctionField_germ D p V hpV ⟨h, hcar⟩
    rw [hgerm, hh_def, ← mul_assoc, ← zpow_add₀ hϖK, add_neg_cancel, zpow_zero, one_mul]
  change (X.residue p).hom (stalkEquiv D hD p hp ϖ hϖ
    (germModuleHom D.sheaf V p hpV ⟨h, hcar⟩)) = y
  rw [hstalk]
  exact ha

open Classical in
/--
`toSkyscraperFun` is also semilinear for the module structure on the residue field through
the `RingCat`-valued stalk: both scalar actions are multiplication by the evaluation at `p`,
by `residueField_compHom_smul_eq`.
-/
lemma toSkyscraperFun_compHom_smul {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) (hp' : p ∈ U)
    (a : ↑Γ(X, U)) (t : ↑((D.sheaf).val.obj (op U))) :
    letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
    toSkyscraperFun p D hD ϖ hϖ hp hp' (a • t) =
      (letI : Module ↑Γ(X, U) ↑(X.residueField p) :=
        Module.compHom ↑(X.residueField p) (X.ringCatSheaf.presheaf.germ U p hp').hom
       a • toSkyscraperFun p D hD ϖ hϖ hp hp' t) := by
  erw [residueField_compHom_smul_eq p hp' a]
  letI : Module ↑Γ(X, U) ↑(X.residueField p) := (X.evaluation U p hp').hom.toModule
  exact (toSkyscraperFun p D hD ϖ hϖ hp hp').map_smul' a t

open Classical in
/--
`toSkyscraperFun` as a linear map into the residue field equipped with its module structure
through the `RingCat`-valued stalk (as used by the skyscraper presheaf of modules).
-/
noncomputable
def toSkyscraperFun' {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) (hp' : p ∈ U) :
    letI : Module ↑Γ(X, U) ↑(X.residueField p) :=
      Module.compHom ↑(X.residueField p) (X.ringCatSheaf.presheaf.germ U p hp').hom
    (D.sheaf).val.obj (op U) →ₗ[Γ(X, U)] ↑(X.residueField p) :=
  letI : Module ↑Γ(X, U) ↑(X.residueField p) :=
    Module.compHom ↑(X.residueField p) (X.ringCatSheaf.presheaf.germ U p hp').hom
  { toFun := toSkyscraperFun p D hD ϖ hϖ hp hp'
    map_add' := fun a b => map_add _ a b
    map_smul' := fun a t => toSkyscraperFun_compHom_smul p D hD ϖ hϖ hp hp' a t }

/--
Map from `𝒪ₓ(D)` to the skyscraper sheaf at a point `p` on an open set U.
-/
noncomputable
def toSkyscraper {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) :
    (D.sheaf).val.obj (op U) ⟶
      (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)).val.obj (op U) :=
  open Classical in
  if hp' : p ∈ U then
    letI : Module ↑Γ(X, U) ↑(X.residueField p) :=
      Module.compHom ↑(X.residueField p) (X.ringCatSheaf.presheaf.germ U p hp').hom
    ModuleCat.ofHom (X := ↑(D.sheaf.val.obj (op U))) (Y := ↑(X.residueField p))
      (toSkyscraperFun' p D hD ϖ hϖ hp hp') ≫
      eqToHom (skyscraperPresheafOfModulesObj_pos p X.ringCatSheaf
        ↑(X.residueField p) hp').symm
  else 0

open Classical in
lemma toSkyscraper_pos {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) (hp' : p ∈ U) :
    toSkyscraper p D (U := U) hD ϖ hϖ hp =
      (letI : Module ↑Γ(X, U) ↑(X.residueField p) :=
        Module.compHom ↑(X.residueField p) (X.ringCatSheaf.presheaf.germ U p hp').hom;
        ModuleCat.ofHom (X := ↑(D.sheaf.val.obj (op U))) (Y := ↑(X.residueField p))
          (toSkyscraperFun' p D hD ϖ hϖ hp hp')) ≫
      eqToHom (skyscraperPresheafOfModulesObj_pos p X.ringCatSheaf
        ↑(X.residueField p) hp').symm :=
  dif_pos hp'

open Classical in
lemma toSkyscraper_neg {U : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) (hp' : p ∉ U) :
    toSkyscraper p D (U := U) hD ϖ hϖ hp = 0 :=
  dif_neg hp'

/--
`toSkyscraperFun` is compatible with restriction of sections: both are computed from the
germ at `p`, and the germ is unchanged by restriction.
-/
lemma toSkyscraperFun_res {U V : X.Opens} (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1)
    (i : V ≤ U) (hpV : p ∈ V) (s : ↑((D.sheaf).val.obj (op U))) :
    toSkyscraperFun p D hD ϖ hϖ hp hpV (mapFun D i s) =
      toSkyscraperFun p D hD ϖ hϖ hp (i hpV) s :=
  congrArg (fun z => (X.residue p).hom ((stalkEquiv D hD p hp ϖ hϖ) z))
    (TopCat.Presheaf.germ_res_apply D.sheaf.val.presheaf (homOfLE i) p hpV s)

/--
The morphism of sheaves of modules `𝒪ₓ(D) ⟶ k(p)` to the skyscraper sheaf at `p`, given on
opens containing `p` by evaluating `ϖ ^ D p * f` at `p`.
-/
noncomputable
def toSkyscraperHom (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) :
    D.sheaf ⟶ skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p) where
  val := {
    app U := toSkyscraper p D (U := unop U) hD ϖ hϖ hp
    naturality {U V} f := by
      rw [show (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)).val.map f =
        skyscraperPresheafOfModulesMap p X.ringCatSheaf ↑(X.residueField p) f from rfl]
      have hobj := fun (W : (TopologicalSpace.Opens ↥X)ᵒᵖ) (hw : p ∈ unop W) =>
        skyscraperPresheafOfModulesObj_pos p X.ringCatSheaf ↑(X.residueField p)
          (U := W) hw
      by_cases h : p ∈ unop V
      · have hU : p ∈ unop U := f.unop.le h
        rw [skyscraperPresheafOfModulesMap_pos p X.ringCatSheaf ↑(X.residueField p) f h,
          toSkyscraper_pos p D hD ϖ hϖ hp h, toSkyscraper_pos p D hD ϖ hϖ hp hU]
        -- Elementwise, both sides are casts of the same residue: the underlying maps agree by
        -- `toSkyscraperFun_res`, and all the `eqToHom`s and the restriction are identities.
        apply ModuleCat.hom_ext
        ext s
        apply eq_of_heq
        have h1 : toSkyscraperFun p D hD ϖ hϖ hp h (mapFun D f.unop.le s) =
            toSkyscraperFun p D hD ϖ hϖ hp hU s :=
          toSkyscraperFun_res p D hD ϖ hϖ hp f.unop.le h s
        refine HEq.trans (b := toSkyscraperFun p D hD ϖ hϖ hp h (mapFun D f.unop.le s)) ?_ ?_
        · exact heq_eqToHom_apply_moduleCat (hobj V h).symm _
        · rw [h1]
          exact ((heq_eqToHom_apply_moduleCat (hobj V h).symm _).trans
            ((heq_eqToHom_apply_moduleCat (hobj U (f.unop.le h)) _).trans
              (heq_eqToHom_apply_moduleCat (hobj U hU).symm _))).symm
      · rw [toSkyscraper_neg p D hD ϖ hϖ hp h]
        exact ((ModuleCat.restrictScalars _).map_isZero
          (skyscraperPresheafOfModulesObj_isZero_of_neg p X.ringCatSheaf
            ↑(X.residueField p) h)).eq_of_tgt _ _
  }

open Classical in
/--
TODO: Make this proof a bit more sensible - namely, this should really just be a wrapper around
`toSkyscraperFun_isLocallySurjective`
-/
lemma toSkyscraperHom_isLocallySurjective (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ)
    (hp : coheight p = 1) (pClosed : ∀ x : X, x ≤ p → x = p) :
    CategoryTheory.Sheaf.IsLocallySurjective <|
    (SheafOfModules.toSheaf X.ringCatSheaf).map <| toSkyscraperHom p D hD ϖ hϖ hp := by
  refine (TopCat.Presheaf.isLocallySurjective_iff _).mpr ?_
  intro U t x hxU
  have hobj := fun {W : X.Opens} (hw : p ∈ W) =>
    skyscraperPresheafOfModulesObj_pos p X.ringCatSheaf ↑(X.residueField p)
      (U := op W) hw
  by_cases hxp : x = p
  · -- At `p` itself, use `toSkyscraperFun_isLocallySurjective` for the value of `t`.
    have hpU : p ∈ U := hxp ▸ hxU
    obtain ⟨V₀, hpV₀, s₀, hs₀⟩ := toSkyscraperFun_isLocallySurjective p D hD ϖ hϖ hp
      ((eqToHom (hobj hpU)).hom t)
    have hpV : p ∈ V₀ ⊓ U := ⟨hpV₀, hpU⟩
    letI : Module ↑Γ(X, V₀ ⊓ U) ↑(X.residueField p) :=
      (X.evaluation (V₀ ⊓ U) p hpV).hom.toModule
    refine ⟨V₀ ⊓ U, inf_le_right, ⟨mapFun D inf_le_left s₀, ?_⟩, by rw [hxp]; exact hpV⟩
    -- The value of the candidate section under `toSkyscraperFun`.
    have hL : toSkyscraperFun p D hD ϖ hϖ hp hpV (mapFun D inf_le_left s₀) =
        (eqToHom (hobj hpU)).hom t :=
      (toSkyscraperFun_res p D hD ϖ hϖ hp inf_le_left hpV s₀).trans hs₀
    -- Reduce the left hand side through `toSkyscraper_pos`.
    have hT : (ConcreteCategory.hom
        (((SheafOfModules.toSheaf X.ringCatSheaf).map (toSkyscraperHom p D hD ϖ hϖ hp)).hom.app
          (op (V₀ ⊓ U)))) (mapFun D inf_le_left s₀) =
        (eqToHom (hobj hpV).symm).hom
          (toSkyscraperFun p D hD ϖ hϖ hp hpV (mapFun D inf_le_left s₀)) := by
      change ((toSkyscraper p D (U := V₀ ⊓ U) hD ϖ hϖ hp).hom (mapFun D inf_le_left s₀) : _) = _
      rw [toSkyscraper_pos p D hD ϖ hϖ hp hpV]
      rfl
    -- Reduce the right hand side through `skyscraperPresheafOfModulesMap_pos`.
    have hRest : TopCat.Presheaf.restrictOpen t (V₀ ⊓ U) inf_le_right =
        (eqToHom (hobj hpV).symm).hom
          ((skyscraperPresheafOfModulesRestriction p X.ringCatSheaf ↑(X.residueField p)
            (homOfLE (inf_le_right : V₀ ⊓ U ≤ U)).op hpV).hom
          ((eqToHom (hobj hpU)).hom t)) := by
      change (skyscraperPresheafOfModulesMap p X.ringCatSheaf ↑(X.residueField p)
        (homOfLE (inf_le_right : V₀ ⊓ U ≤ U)).op).hom t = _
      rw [skyscraperPresheafOfModulesMap_pos p X.ringCatSheaf ↑(X.residueField p)
        (homOfLE (inf_le_right : V₀ ⊓ U ≤ U)).op hpV]
      rfl
    rw [hT, hRest, hL]
    -- Both sides are casts of the same element of the residue field.
    apply eq_of_heq
    refine HEq.trans (heq_eqToHom_apply_moduleCat (hobj hpV).symm _) ?_
    exact (heq_eqToHom_apply_moduleCat (hobj hpU) t).trans
      ((heq_eqToHom_apply_moduleCat (hobj hpV).symm _).trans
        (heq_eqToHom_apply_moduleCat (hobj hpU) t)).symm
  · -- Away from `p`, shrink to a neighbourhood avoiding `p`, where the skyscraper is zero.
    have hxc : x ∉ closure ({p} : Set X) := fun hmem =>
      hxp (pClosed x (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hmem)))
    refine ⟨U ⊓ ⟨(closure ({p} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩, inf_le_left,
      ⟨0, ?_⟩, ⟨hxU, hxc⟩⟩
    have hpV : p ∉ (U ⊓ ⟨(closure ({p} : Set X))ᶜ, isClosed_closure.isOpen_compl⟩ : X.Opens) :=
      fun hpv => hpv.2 (subset_closure rfl)
    exact @Subsingleton.elim _
      (AddCommGrpCat.subsingleton_of_isZero
        (skyscraperPresheafOfModules_presheaf_obj_isZero p X.ringCatSheaf
          ↑(X.residueField p) hpV)) _ _

omit [IsRegularInCodimensionOne X] in
/--
If `D₁ ≤ D₂` then sections of `𝒪ₓ(D₁)` are sections of `𝒪ₓ(D₂)`.
-/
lemma carrier_mono {D₁ D₂ : AlgebraicCycle X ℤ} (h : D₁ ≤ D₂)
    (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) {f : X.functionField}
    (hf : f ∈ carrier D₁ U.unop) : f ∈ carrier D₂ U.unop := by
  simp only [carrier, ne_eq, Scheme.Opens.nonempty_iff, ge_iff_le, Set.mem_setOf_eq] at hf ⊢
  intro fnez
  obtain ⟨h1, h2⟩ := hf fnez
  refine ⟨h1, le_trans h2 ?_⟩
  intro z
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply, restrict_apply]
  split_ifs
  · exact add_le_add le_rfl (h z)
  · exact le_refl _

/--
The inclusion mapping `𝒪ₓ(D₁) ⟶ 𝒪ₓ(D₂)` for `D₁ ≤ D₂`, defined by `h ↦ h`. Compared with
`extend`, this avoids an `eqToHom` when the target divisor is not literally of the form
`D₁ + D'`.
-/
noncomputable
def extendLe {D₁ D₂ : AlgebraicCycle X ℤ} (h : D₁ ≤ D₂) :
    D₁.sheaf ⟶ D₂.sheaf where
  val := {
    app U := ModuleCat.ofHom
      { toFun := fun m ↦ ⟨m.val, carrier_mono h U m.prop⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    naturality {U V} f := by
      apply ModuleCat.hom_ext
      ext ⟨v, hv⟩
      apply Subtype.ext
      change (mapFun D₁ f.unop.le ⟨v, hv⟩).1 =
        (mapFun D₂ f.unop.le ⟨v, carrier_mono h U hv⟩).1
      simp only [mapFun]
      split_ifs <;> rfl
  }

open Classical in
noncomputable
def twistedClosedSubschemeComplex (hD : support D ⊆ {x | coheight x = 1}) (ϖ : X.presheaf.stalk p)
    (hϖ : Irreducible ϖ) (hp : coheight p = 1) :
  ShortComplex X.Modules where
  X₁ := (D - single p 1).sheaf
  X₂ := D.sheaf
  X₃ := skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)
  f := extendLe (sub_le_self D (single_effective p 1 (by simp)))
  g := toSkyscraperHom p D hD ϖ hϖ hp
  zero := by
    apply SheafOfModules.Hom.ext
    apply PresheafOfModules.hom_ext
    intro U
    have hcomp : (extendLe (sub_le_self D (single_effective p 1 (by simp))) ≫
        toSkyscraperHom p D hD ϖ hϖ hp).val.app U =
        (extendLe (sub_le_self D (single_effective p 1 (by simp)))).val.app U ≫
        toSkyscraper p D (U := unop U) hD ϖ hϖ hp := rfl
    rw [hcomp]
    by_cases hp' : p ∈ unop U
    · letI : Module ↑Γ(X, unop U) ↑(X.residueField p) :=
        (X.evaluation (unop U) p hp').hom.toModule
      rw [toSkyscraper_pos p D hD ϖ hϖ hp hp']
      apply ModuleCat.hom_ext
      ext s
      -- The image of `s` is a section of `𝒪ₓ(D)` which is also a section of `𝒪ₓ(D - p)`,
      -- so it lies in the kernel of `toSkyscraperFun` by `toSkyscraperFun_ker`.
      set t : ↑(D.sheaf.val.obj U) :=
        (⟨s.1, carrier_mono (sub_le_self D (single_effective p 1 (by simp))) U s.2⟩ :
          ↑(D.sheaf.val.obj U)) with ht
      have hmem : t ∈ LinearMap.ker (toSkyscraperFun p D hD ϖ hϖ hp hp') := by
        have hset := Set.ext_iff.mp (toSkyscraperFun_ker p D hD ϖ hϖ hp hp') t
        exact hset.mpr s.2
      have hzero := LinearMap.mem_ker.mp hmem
      change (eqToHom (skyscraperPresheafOfModulesObj_pos p X.ringCatSheaf
        ↑(X.residueField p) hp').symm).hom
        (toSkyscraperFun p D hD ϖ hϖ hp hp' t) = 0
      rw [hzero]
      exact map_zero _
    · -- Away from `p` the skyscraper component vanishes.
      rw [toSkyscraper_neg p D hD ϖ hϖ hp hp', Limits.comp_zero]
      rfl


omit [IsRegularInCodimensionOne X] in
open Classical in
/--
Away from `p`, a section of `𝒪ₓ(D)` is also a section of `𝒪ₓ(D - p)`.
-/
lemma mem_carrier_sub_single {U : X.Opens} (hU : p ∉ U) {f : X.functionField}
    (hf : f ∈ carrier D U) : f ∈ carrier (D - single p 1) U := by
  intro hne
  obtain ⟨h1, h2⟩ := hf hne
  refine ⟨h1, ?_⟩
  intro z
  have h3 := h2 z
  simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply, restrict_apply] at h3 ⊢
  split_ifs at h3 ⊢ with hz
  · have hzp : z ≠ p := fun h => hU (h ▸ hz)
    simp only [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, single_apply,
      if_neg hzp, sub_zero]
    exact h3
  · exact le_refl _

open Classical in
/--
If `k : A ⟶ 𝒪ₓ(D)` composes to zero with the map to the skyscraper sheaf at `p`, then all
values of `k` are sections of `𝒪ₓ(D - p)`.
-/
lemma mem_carrier_of_comp_toSkyscraperHom_eq_zero (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) {A : X.Modules}
    (k : A ⟶ D.sheaf) (hk : k ≫ toSkyscraperHom p D hD ϖ hϖ hp = 0)
    (U : (TopologicalSpace.Opens ↥X)ᵒᵖ) (t : ↑(A.val.obj U)) :
    ((k.val.app U) t).1 ∈ carrier (D - single p 1) (unop U) := by
  by_cases hp' : p ∈ unop U
  · letI : Module ↑Γ(X, unop U) ↑(X.residueField p) :=
      (X.evaluation (unop U) p hp').hom.toModule
    -- Componentwise, `k` composed with `toSkyscraper` is zero.
    have h1 : k.val.app U ≫ toSkyscraper p D (U := unop U) hD ϖ hϖ hp = 0 :=
      congrArg (fun (ψ : A ⟶ skyscraperSheafOfModules p X.ringCatSheaf
        ↑(X.residueField p)) => ψ.val.app U) hk
    rw [toSkyscraper_pos p D hD ϖ hϖ hp hp'] at h1
    have h2' := ConcreteCategory.congr_hom h1 t
    -- Cancel the (injective) `eqToHom` to get the statement about `toSkyscraperFun`.
    have hinj : Function.Injective (eqToHom (skyscraperPresheafOfModulesObj_pos
        p X.ringCatSheaf ↑(X.residueField p) hp').symm).hom :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    have h2 : toSkyscraperFun p D hD ϖ hϖ hp hp' ((k.val.app U) t) = 0 := by
      apply hinj
      rw [map_zero]
      exact h2'
    exact (Set.ext_iff.mp (toSkyscraperFun_ker p D hD ϖ hϖ hp hp') ((k.val.app U) t)).mp
      (LinearMap.mem_ker.mpr h2)
  · exact mem_carrier_sub_single p D hp' ((k.val.app U) t).2

open Classical in
/--
The lift through `𝒪ₓ(D - p) ⟶ 𝒪ₓ(D)` of a morphism `k : A ⟶ 𝒪ₓ(D)` which composes to zero
with the map to the skyscraper sheaf at `p`.
-/
noncomputable def toSkyscraperKernelLift (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ) (hp : coheight p = 1) {A : X.Modules}
    (k : A ⟶ D.sheaf) (hk : k ≫ toSkyscraperHom p D hD ϖ hϖ hp = 0) :
    A ⟶ (D - single p 1).sheaf where
  val := {
    app U :=
      letI : Module ↑(X.ringCatSheaf.obj.obj U) ↑(carrier (D - single p 1) (unop U)) :=
        instModuleCarrier
      ModuleCat.ofHom
      { toFun := fun t => ⟨((k.val.app U) t).1,
          mem_carrier_of_comp_toSkyscraperHom_eq_zero p D hD ϖ hϖ hp k hk U t⟩
        map_add' := fun a b => by
          apply Subtype.ext
          have h := congrArg Subtype.val (map_add (k.val.app U).hom a b)
          exact h
        map_smul' := fun r t => by
          apply Subtype.ext
          have h := congrArg Subtype.val (map_smul (k.val.app U).hom r t)
          exact h }
    naturality {U V} i := by
      apply ModuleCat.hom_ext
      ext t
      apply Subtype.ext
      have hnat := PresheafOfModules.naturality_apply k.val i t
      change ((k.val.app V) ((A.val.map i) t)).1 =
        (mapFun (D - single p 1) i.unop.le
          ⟨((k.val.app U) t).1,
            mem_carrier_of_comp_toSkyscraperHom_eq_zero p D hD ϖ hϖ hp k hk U t⟩).1
      rw [hnat]
      change (mapFun D i.unop.le ((k.val.app U) t)).1 = _
      simp only [mapFun]
      split_ifs <;> rfl
  }

/--
The inclusion `𝒪ₓ(D₁) ⟶ 𝒪ₓ(D₂)` for `D₁ ≤ D₂` is a monomorphism.
-/
lemma extendLe_mono {D₁ D₂ : AlgebraicCycle X ℤ} (h : D₁ ≤ D₂) : Mono (extendLe h) := by
  suffices ∀ (U : (TopologicalSpace.Opens ↥X)ᵒᵖ), Function.Injective <|
    (extendLe h).val.app U by
    suffices Mono <| (SheafOfModules.toSheaf X.ringCatSheaf).map <| extendLe h by cat_disch
    exact Sheaf.mono_of_injective ((SheafOfModules.toSheaf X.ringCatSheaf).map (extendLe h)) this
  intro U a b hab
  have hval := Subtype.ext_iff.mp hab
  exact Subtype.ext hval

open Limits in
/--
The sequence `0 ⟶ 𝒪ₓ(D - p) ⟶ 𝒪ₓ(D) ⟶ k(p)` is exact: by `toSkyscraperFun_ker`, the
inclusion `𝒪ₓ(D - p) ⟶ 𝒪ₓ(D)` is precisely a kernel of the map to the skyscraper sheaf.
-/
lemma twistedClosedSubschemeComplex_exact (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ)
    (hp : coheight p = 1) : (twistedClosedSubschemeComplex p D hD ϖ hϖ hp).Exact := by
  haveI : Mono (twistedClosedSubschemeComplex p D hD ϖ hϖ hp).f :=
    extendLe_mono (sub_le_self D (single_effective p 1 (by simp)))
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι' _ _ (fun {A} k hk =>
    ⟨toSkyscraperKernelLift p D hD ϖ hϖ hp k hk, by
      apply SheafOfModules.Hom.ext
      apply PresheafOfModules.hom_ext
      intro U
      apply ModuleCat.hom_ext
      ext t
      rfl⟩)

lemma twistedClosedSubschemeComplex_shortExact (hD : support D ⊆ {x | coheight x = 1})
    (ϖ : X.presheaf.stalk p) (hϖ : Irreducible ϖ)
    (hp : coheight p = 1)
    (pClosed : ∀ x : X, x ≤ p → x = p) :
    (twistedClosedSubschemeComplex p D hD ϖ hϖ hp).ShortExact where
  exact := twistedClosedSubschemeComplex_exact p D hD ϖ hϖ hp
  mono_f := extendLe_mono (sub_le_self D (single_effective p 1 (by simp)))
  epi_g := by
    -- The map to the skyscraper sheaf is locally surjective, hence an epimorphism of
    -- sheaves of abelian groups, and `toSheaf` is faithful so it reflects epimorphisms.
    have h : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map
        (toSkyscraperHom p D hD ϖ hϖ hp)) :=
      (Sheaf.isLocallySurjective_iff_epi' (φ := (SheafOfModules.toSheaf X.ringCatSheaf).map
        (toSkyscraperHom p D hD ϖ hϖ hp))).mp
        (toSkyscraperHom_isLocallySurjective p D hD ϖ hϖ hp pClosed)
    exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map h

/-
Two reparametrisations of `twistedClosedSubschemeComplex`. Rather than writing the smaller divisor
literally as `D - single p 1`, these take it as a free variable (`D'`/`D`) related to the larger
one by a hypothesis. This keeps `X₁`/`X₂` definitionally equal to the sheaves one actually wants in
applications (e.g. `E.sheaf` rather than `((E + single p 1) - single p 1).sheaf`), avoiding casts.
Both are definitionally equal to `twistedClosedSubschemeComplex` applied to the larger divisor, so
their structure (in particular the `zero`/exactness proofs) is inherited from it.
-/

open Classical in
/-- `0 ⟶ 𝒪ₓ(D') ⟶ 𝒪ₓ(D) ⟶ k(p)` where `D - D' = single p 1`; the skyscraper sits on the larger
divisor `D`. Definitionally `twistedClosedSubschemeComplex` at `D`. -/
noncomputable
def twistedClosedSubschemeComplex₁
    {D D' : AlgebraicCycle X ℤ}
    (hD : support D ⊆ {x | coheight x = 1}) (ϖ : X.presheaf.stalk p)
    (hϖ : Irreducible ϖ) (hp : coheight p = 1)
    (hD' : D - D' = single p 1)
    : ShortComplex X.Modules where
  X₁ := D'.sheaf
  X₂ := D.sheaf
  X₃ := skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)
  f := extendLe (by rw [← sub_nonneg, hD']; exact single_effective p 1 (by simp))
  g := toSkyscraperHom p D hD ϖ hϖ hp
  zero := by
    obtain rfl : D' = D - single p 1 := by rw [← hD']; abel
    exact (twistedClosedSubschemeComplex p D hD ϖ hϖ hp).zero

open Classical in
/-- `twistedClosedSubschemeComplex₁` is short exact, inherited from
`twistedClosedSubschemeComplex_shortExact`. -/
lemma twistedClosedSubschemeComplex₁_shortExact
    {D D' : AlgebraicCycle X ℤ}
    (hD : support D ⊆ {x | coheight x = 1}) (ϖ : X.presheaf.stalk p)
    (hϖ : Irreducible ϖ) (hp : coheight p = 1)
    (hD' : D - D' = single p 1)
    (pClosed : ∀ x : X, x ≤ p → x = p) :
    (twistedClosedSubschemeComplex₁ p hD ϖ hϖ hp hD').ShortExact := by
  obtain rfl : D' = D - single p 1 := by rw [← hD']; abel
  exact twistedClosedSubschemeComplex_shortExact p D hD ϖ hϖ hp pClosed

open Classical in
/-- `0 ⟶ 𝒪ₓ(D) ⟶ 𝒪ₓ(D') ⟶ k(p)` where `D' - D = single p 1`; the skyscraper sits on the larger
divisor `D'`. Definitionally `twistedClosedSubschemeComplex` at `D'`. -/
noncomputable
def twistedClosedSubschemeComplex₂
    {D D' : AlgebraicCycle X ℤ}
    (hD : support D ⊆ {x | coheight x = 1}) (ϖ : X.presheaf.stalk p)
    (hϖ : Irreducible ϖ) (hp : coheight p = 1)
    (hD' : D' - D = single p 1)
    : ShortComplex X.Modules where
  X₁ := D.sheaf
  X₂ := D'.sheaf
  X₃ := skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)
  f := extendLe (by rw [← sub_nonneg, hD']; exact single_effective p 1 (by simp))
  g :=
    have hsupp : support D' ⊆ {x | coheight x = 1} := by
      intro x hx
      by_cases hxp : x = p
      · exact hxp ▸ hp
      · refine hD ?_
        have heq : D' = D + single p 1 := by rw [← hD']; abel
        have hx' : D'.toFun x ≠ 0 := hx
        rw [heq] at hx'
        simpa [Function.mem_support, single_apply, hxp] using hx'
    toSkyscraperHom p D' hsupp ϖ hϖ hp
  zero := by
    have hsupp : support D' ⊆ {x | coheight x = 1} := by
      intro x hx
      by_cases hxp : x = p
      · exact hxp ▸ hp
      · refine hD ?_
        have heq : D' = D + single p 1 := by rw [← hD']; abel
        have hx' : D'.toFun x ≠ 0 := hx
        rw [heq] at hx'
        simpa [Function.mem_support, single_apply, hxp] using hx'
    obtain rfl : D = D' - single p 1 := by rw [← hD']; abel
    exact (twistedClosedSubschemeComplex p D' hsupp ϖ hϖ hp).zero

open Classical in
/-- `twistedClosedSubschemeComplex₂` is short exact, inherited from
`twistedClosedSubschemeComplex_shortExact`. -/
lemma twistedClosedSubschemeComplex₂_shortExact
    {D D' : AlgebraicCycle X ℤ}
    (hD : support D ⊆ {x | coheight x = 1}) (ϖ : X.presheaf.stalk p)
    (hϖ : Irreducible ϖ) (hp : coheight p = 1)
    (hD' : D' - D = single p 1)
    (pClosed : ∀ x : X, x ≤ p → x = p) :
    (twistedClosedSubschemeComplex₂ p hD ϖ hϖ hp hD').ShortExact := by
  have hsupp : support D' ⊆ {x | coheight x = 1} := by
    intro x hx
    by_cases hxp : x = p
    · exact hxp ▸ hp
    · refine hD ?_
      have heq : D' = D + single p 1 := by rw [← hD']; abel
      have hx' : D'.toFun x ≠ 0 := hx
      rw [heq] at hx'
      simpa [Function.mem_support, single_apply, hxp] using hx'
  obtain rfl : D = D' - single p 1 := by rw [← hD']; abel
  exact twistedClosedSubschemeComplex_shortExact p D' hsupp ϖ hϖ hp pClosed

end Sheaf
end AlgebraicCycle
