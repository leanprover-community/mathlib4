import Mathlib.AlgebraicGeometry.AlgebraicCycle.EulerCharAdditive
import Mathlib.AlgebraicGeometry.AlgebraicCycle.ExactSequence
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Skyscraper
import Mathlib.Topology.Sheaves.Flasque

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat Opposite

universe u

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
    (p : X) (M : Type u) [AddCommGroup M]
    [Module (↑(X.ringCatSheaf.presheaf.stalk p)) M]

/-- The residue field at `p` is a `k`-module via the structure map `k → Γ(X, ⊤) → κ(p)`. -/
noncomputable instance : Module k ↑(X.residueField p) :=
  Module.compHom (↑(X.residueField p))
    ((X.Γevaluation p).hom.comp (globalSec (X := X) (R := CommRingCat.of k)))

/-- The scalar endomorphism `smulEnd r` evaluated at `U` on a section is `r • ·`. -/
lemma smulEnd_hom_app_apply {Y : Scheme.{u}} {R : CommRingCat.{u}} [Y.Over (Spec R)]
    (G : Y.Modules) (r : R) (U : (TopologicalSpace.Opens Y)ᵒᵖ) (y : Γ(G, U.unop)) :
    (smulEnd G r).hom.app U y = r • y := rfl

/-- Higher cohomology of the skyscraper sheaf vanishes, because it is flasque. -/
lemma skyscraper_h {n : ℕ} (h : n > 0) :
    Scheme.Modules.h k (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) n = 0 := by
  haveI := subsingleton_H_skyscraper_of_pos p h
  exact Module.finrank_zero_of_subsingleton

/-- The degree-zero cohomology of the skyscraper sheaf is its space of global sections, the residue
field; in particular it has dimension `finrank k (residue field)`.

The proof builds a `k`-linear equivalence `H⁰ ≃ₗ[k] κ(p)`: as an additive equivalence it is
`H.equiv₀` (`H⁰ ≅ Γ(⊤)`) composed with the skyscraper identification `Γ(⊤) = κ(p)`; `k`-linearity
follows from `equiv₀`'s naturality applied to the scalar endomorphism `smulEnd`, modulo the
geometric fact `key` that `smulEnd r` acts at `⊤` as the residue-field scalar `r •`. -/
lemma skyscraper_h_zero :
    Scheme.Modules.h k (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) 0
      = Module.finrank k (X.residueField p) := by
  set F : X.Modules := skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p) with hF
  set F' := (SheafOfModules.toSheaf X.ringCatSheaf).obj F with hF'
  have hobj : F'.obj.obj (op ⊤) = AddCommGrpCat.of ↑(X.residueField p) :=
    skyscraperPresheafOfModules_presheaf_obj_pos p X.ringCatSheaf ↑(X.residueField p) trivial
  -- identification `Γ(⊤) = κ(p)` and the equivalence `H⁰ ≅ Γ(⊤)`.
  let c : ↑(F'.obj.obj (op ⊤)) ≃+ ↑(X.residueField p) :=
    (eqToIso hobj).addCommGroupIsoToAddEquiv
  let e₀ : ↑(lesH (CommRingCat.of k) F 0) ≃+ ↑(F'.obj.obj (op ⊤)) :=
    Sheaf.H.equiv₀ F' isTerminalTop
  -- The geometric content: `smulEnd r` acts at `⊤` (on `Γ(⊤) = κ(p)`) as the residue-field
  -- scalar `r •`. (Unfolds the skyscraper module structure and the stalk-to-residue-field action.)
  have key_action : ∀ (r : k) (y : ↑(F'.obj.obj (op ⊤))),
      c ((smulEnd (R := CommRingCat.of k) F r).hom.app (op ⊤) y) = r • c y := by
    intro r y
    rw [smulEnd_hom_app_apply (R := CommRingCat.of k) F r (op ⊤) y]
    -- The residue-field scalar `r • c y` is multiplication by `Γevaluation p (globalSec r)`.
    have rhsval : r • c y
        = X.Γevaluation p (globalSec (X := X) (R := CommRingCat.of k) r) * c y := rfl
    rw [rhsval]
    -- `c` is the underlying additive map of the `ModuleCat`-linear skyscraper identification
    -- `eqToHom hposM`, hence semilinear for the section ring.
    have hposM := skyscraperPresheafOfModulesObj_pos p X.ringCatSheaf ↑(X.residueField p)
      (U := op (⊤ : X.Opens)) trivial
    have hA : ∀ z : ↑(F'.obj.obj (op ⊤)), c z = (eqToHom hposM).hom z := fun z =>
      eq_of_heq ((heq_eqToHom_apply_ab hobj z).trans
        (heq_eqToHom_apply_moduleCat hposM z).symm)
    have hsg : structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r
        = globalSec (X := X) (R := CommRingCat.of k) r := by
      rw [structureRingHom_apply, Subsingleton.elim (⊤ : X.Opens).leTop.op (𝟙 _)]
      simp
    -- The section-ring (`RingCat`) action on `κ(p)`, as used by the skyscraper at `⊤`.
    letI : Module ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) ↑(X.residueField p) :=
      Module.compHom ↑(X.residueField p) (X.ringCatSheaf.presheaf.germ (⊤ : X.Opens) p trivial).hom
    simp only [hA]
    -- `r • y` (`Module R` via `compHom structureRingHom`) is, definitionally, the section-ring
    -- (`RingCat`) action by `structureRingHom ⊤ r`. Push it through the linear map `eqToHom hposM`
    -- (`map_smul`), then evaluate the section-ring action on `κ(p)`.
    erw [(eqToHom hposM).hom.map_smul, residueField_compHom_smul_eq p (U := ⊤) trivial
      (structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r) ((eqToHom hposM).hom y)]
    rw [hsg]
  -- `k`-linearity of `e₀` composed with `Γ(⊤) = κ(p)`, via `equiv₀`-naturality.
  have key : ∀ (r : k) (x : ↑(lesH (CommRingCat.of k) F 0)),
      c (e₀ (CategoryTheory.Sheaf.H.map (smulEnd (R := CommRingCat.of k) F r) 0 x))
        = r • c (e₀ x) := by
    intro r x
    rw [show e₀ (CategoryTheory.Sheaf.H.map (smulEnd (R := CommRingCat.of k) F r) 0 x)
        = (smulEnd (R := CommRingCat.of k) F r).hom.app (op ⊤) (e₀ x) from
      (CategoryTheory.Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
        (f := smulEnd (R := CommRingCat.of k) F r) x).symm]
    exact key_action r (e₀ x)
  rw [Scheme.Modules.h]
  refine LinearEquiv.finrank_eq (AddEquiv.toLinearEquiv (e₀.trans c) (fun r x => ?_))
  -- `r • x` is by definition `H.map (smulEnd r) 0 x`.
  exact key r x

/-- The Euler characteristic of the skyscraper sheaf at `p` equals the dimension of the residue
field: all higher cohomology vanishes (flasqueness), so only `H⁰` contributes. -/
lemma eulerChar_skyscraper : Scheme.Modules.eulerChar k
    (skyscraperSheafOfModules p X.ringCatSheaf (X.residueField p)) =
    Module.finrank k (X.residueField p) := by
  rw [Scheme.Modules.eulerChar,
    finsum_eq_single _ 0 (fun n hn => by simp [skyscraper_h k p (Nat.pos_of_ne_zero hn)])]
  simp only [pow_zero, one_mul]
  rw [skyscraper_h_zero]

open AlgebraicGeometry.AlgebraicCycle AlgebraicGeometry.AlgebraicCycle.Sheaf Order
  Function.locallyFinsuppWithin in
/--
Under the cohomological finiteness hypothesis `hf₁`, the cohomology of the skyscraper sheaf at a
codimension-one point `p` is finite dimensional over `k`. In degree zero it is trapped between the
finite-dimensional `H⁰(𝒪ₓ(p))` and `H¹(𝒪ₓ)` in the long exact sequence of
`0 ⟶ 𝒪ₓ ⟶ 𝒪ₓ(p) ⟶ k(p) ⟶ 0`; in positive degrees it is subsingleton.
-/
lemma finite_H_skyscraper [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]
    (hf₁ : ∀ (D : AlgebraicCycle X ℤ), ∀ n, Module.Finite k (D.sheaf.H n))
    (hX : ∀ x : X, coheight x = 1 → ∀ y, y ≤ x → y = x)
    {p : X} (hp : coheight p = 1) (n : ℕ) :
    Module.Finite k (Scheme.Modules.H
      (skyscraperSheafOfModules p X.ringCatSheaf (X.residueField p)) n) := by
  classical
  rcases n with _ | m
  · haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
      IsRegularInCodimensionOne.stalk_dvr p hp
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p)
    let o := twistedClosedSubschemeComplex₂ (D := 0) (D' := single p 1) p
      (by simp) ϖ hϖ hp (by simp)
    have hS : (o.map (Modules.toSheafAb X)).ShortExact :=
      shortExact_map_toSheaf (twistedClosedSubschemeComplex₂_shortExact _ _ _ _ _ _ (hX p hp))
    -- Positions 1, 2, 3 of the spliced LES are `H⁰(𝒪ₓ(p)) →f H⁰(k(p)) →g H¹(𝒪ₓ)`; the outer
    -- terms are Noetherian, so `isNoetherian_of_range_eq_ker` traps the middle.
    have hex := dAux_exact (CommRingCat.of k) o hS 0 1
    haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o 0 1) :=
      IsNoetherian.iff_fg.mpr (hf₁ (single p 1) 0)
    haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o 0 3) :=
      IsNoetherian.iff_fg.mpr (hf₁ 0 1)
    haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o 0 2) :=
      isNoetherian_of_range_eq_ker _ _ hex.moduleCat_range_eq_ker
    exact IsNoetherian.iff_fg.mp ‹_›
  · haveI := subsingleton_H_skyscraper p m
    infer_instance
