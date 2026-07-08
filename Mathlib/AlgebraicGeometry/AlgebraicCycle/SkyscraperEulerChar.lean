/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.EulerCharAdditive
import Mathlib.AlgebraicGeometry.AlgebraicCycle.ResidueFieldModule
import Mathlib.AlgebraicGeometry.AlgebraicCycle.ExactSequence
import Mathlib.Topology.Sheaves.Flasque

/-!
# The Euler characteristic of the canonical cokernel `Q_p(D)`

For a codimension-one point `p` of an integral scheme over a field `k`, we compute the
cohomology of the canonical cokernel `Q_p(D)` of `𝒪ₓ(D - p) ⟶ 𝒪ₓ(D)` (the skyscraper valued
in the line `L_p(D)`, `residueLineSheaf`):

* `subsingleton_H_residueLineSheaf_of_pos`: positive-degree cohomology vanishes, by
  flasqueness of the skyscraper — no trivialization of the line is needed;
* `h_residueLineSheaf_zero` and `eulerChar_residueLineSheaf`:
  `χ(Q_p(D)) = dim_k κ(p)`, by transporting the computation for the residue-field skyscraper
  along the trivialization `residueLineSheafIso` (whose choice of uniformizer is harmless
  here, since Euler characteristics are isomorphism-invariant);
* `finite_H_residueLineSheaf`: under the cohomological finiteness hypothesis on the divisor
  sheaves, the cohomology of `Q_p(D)` is finite-dimensional: in degree zero it is trapped
  between `H⁰(𝒪ₓ(p))` and `H¹(𝒪ₓ)` in the long exact sequence of
  `0 ⟶ 𝒪ₓ ⟶ 𝒪ₓ(p) ⟶ Q_p(p) ⟶ 0`, and transported to general `D` along the
  trivializations.

Along the way we provide two pieces of reusable API:

* `hLinearEquivOfIso`/`h_eq_of_iso`/`eulerChar_eq_of_iso`: an isomorphism of sheaves of
  modules induces `k`-linear isomorphisms on cohomology, so `hⁿ` and `χ` are
  isomorphism-invariant (TODO: move next to `Scheme.Modules.eulerChar` in
  `Mathlib.AlgebraicGeometry.AlgebraicCycle.EulerCharAdditive`);
* `skyscraperSectionsAddEquiv`: the sections of a skyscraper presheaf over an open containing
  the point are its value (TODO: upstream to the skyscraper development).
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory CategoryTheory.Limits TopCat Opposite
  CategoryTheory.GrothendieckTopology TopologicalSpace Order
  Function.locallyFinsuppWithin

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

/-!
### Isomorphism invariance of cohomology dimensions

TODO: move next to `Scheme.Modules.eulerChar`.
-/

section IsoInvariance

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
  {F G : X.Modules}

/-- An isomorphism of sheaves of modules induces a `k`-linear isomorphism on cohomology. -/
noncomputable def hLinearEquivOfIso (e : F ≅ G) (n : ℕ) : F.H n ≃ₗ[k] G.H n :=
  AddEquiv.toLinearEquiv
    { toFun := HMapₗ (R := CommRingCat.of k) e.hom n
      invFun := HMapₗ (R := CommRingCat.of k) e.inv n
      left_inv := fun x =>
        ((CategoryTheory.Sheaf.H.map_comp_apply _ _ x).symm.trans
          (congrArg (fun ψ => CategoryTheory.Sheaf.H.map ψ n x)
            (((CategoryTheory.Functor.map_comp _ _ _).symm.trans
              (congrArg _ e.hom_inv_id)).trans (CategoryTheory.Functor.map_id _ _)))).trans
          (CategoryTheory.Sheaf.H.map_id_apply x)
      right_inv := fun x =>
        ((CategoryTheory.Sheaf.H.map_comp_apply _ _ x).symm.trans
          (congrArg (fun ψ => CategoryTheory.Sheaf.H.map ψ n x)
            (((CategoryTheory.Functor.map_comp _ _ _).symm.trans
              (congrArg _ e.inv_hom_id)).trans (CategoryTheory.Functor.map_id _ _)))).trans
          (CategoryTheory.Sheaf.H.map_id_apply x)
      map_add' := map_add _ }
    (fun r x => (HMapₗ (R := CommRingCat.of k) e.hom n).map_smul r x)

/-- `hⁿ` is invariant under isomorphism of sheaves of modules. -/
lemma h_eq_of_iso (e : F ≅ G) (n : ℕ) :
    Scheme.Modules.h k F n = Scheme.Modules.h k G n :=
  LinearEquiv.finrank_eq (hLinearEquivOfIso k e n)

/-- The Euler characteristic is invariant under isomorphism of sheaves of modules. -/
lemma eulerChar_eq_of_iso (e : F ≅ G) :
    Scheme.Modules.eulerChar k F = Scheme.Modules.eulerChar k G := by
  rw [Scheme.Modules.eulerChar, Scheme.Modules.eulerChar]
  exact finsum_congr fun n => by rw [h_eq_of_iso k e n]

end IsoInvariance

/-!
### Sections of a skyscraper presheaf over an open containing the point

TODO: upstream to the skyscraper development.
-/

section SectionsEquiv

variable {Y : TopCat.{u}} (q : ↑Y)

/-- Over an open containing the point (witnessed by `x`), the sections of the skyscraper
presheaf are its value: project at `x`, with inverse the constant tuple. -/
noncomputable def skyscraperSectionsAddEquiv (A : AddCommGrpCat.{u})
    {U : (TopologicalSpace.Opens ↑Y)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology q).fiber.obj (unop U)) :
    ↑(((Opens.pointGrothendieckTopology q).skyscraperPresheaf A).obj U) ≃+ ↑A where
  toFun := (Pi.π (fun _ => A) x).hom
  invFun := (Pi.lift fun _ => 𝟙 A).hom
  left_inv t := pi_ext _ fun x' => by
    obtain ⟨⟨hx⟩⟩ := x
    obtain ⟨⟨hx'⟩⟩ := x'
    rw [pi_lift_π_apply]
    exact congrArg (fun h => (Pi.π (fun _ => A) ((⟨⟨h⟩⟩ :
        (Opens.pointGrothendieckTopology q).fiber.obj (unop U)))).hom t)
      (Subsingleton.elim hx hx')
  right_inv y := (pi_lift_π_apply (fun _ => A) (fun _ => 𝟙 A) x y).trans rfl
  map_add' s t := map_add _ s t

end SectionsEquiv

/-!
### The cohomology of the residue-field skyscraper
-/

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))] (p : X)

/-- The value of a section of the residue-field skyscraper at a witness `p ∈ U`.
TODO: unify with `evalLine` (a single statement for any module over the stalk). -/
noncomputable def evalRes {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U))
    (t : ↑((skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)).val.obj U)) :
    ↑(X.residueField p) :=
  (Pi.π (fun _ => AddCommGrpCat.of ↑(X.residueField p)) x).hom t

/-- The scalar action of a section `a` of the structure sheaf on the residue-field skyscraper
is, on values, multiplication by the evaluation of `a` at `p`. -/
lemma evalRes_smul {U : (TopologicalSpace.Opens ↥X)ᵒᵖ}
    (x : (Opens.pointGrothendieckTopology p).fiber.obj (unop U))
    (a : ↑(X.ringCatSheaf.obj.obj U))
    (t : ↑((skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)).val.obj U)) :
    evalRes p x (a • t) = (X.evaluation (unop U) p x.down.down).hom a * evalRes p x t := by
  letI : Module ↑((Opens.pointGrothendieckTopology p).presheafFiber.obj
      X.ringCatSheaf.presheaf) ↑(X.residueField p) :=
    pointSheafFiberModule p X.ringCatSheaf ↑(X.residueField p)
  have h1 : evalRes p x (a • t) =
      ((Opens.pointGrothendieckTopology p).toPresheafFiber (unop U) x
        X.ringCatSheaf.presheaf).hom a • evalRes p x t := by
    refine (ConcreteCategory.congr_hom
      (Point.skyscraperSMul_π (Opens.pointGrothendieckTopology p)
        X.ringCatSheaf.presheaf (ModuleCat.of _ ↑(X.residueField p)) U a x) t).trans ?_
    exact Point.skyscraperSMulComponent_apply _ _ _ _ _ _ _
  rw [h1]
  have hfibsmul : ∀ (r : ↑((Opens.pointGrothendieckTopology p).presheafFiber.obj
      X.ringCatSheaf.presheaf)) (m : ↑(X.residueField p)),
      r • m = (pointPresheafFiberToStalk p X.ringCatSheaf).hom r • m := fun _ _ => rfl
  have hsmul : ∀ (s : ↑(X.ringCatSheaf.presheaf.stalk p)) (m : ↑(X.residueField p)),
      s • m = (RingCat.Hom.hom
        (colimit.post ((OpenNhds.inclusion p).op ⋙ X.presheaf) (forget₂ CommRingCat RingCat) ≫
          (forget₂ CommRingCat RingCat).map (X.residue p))) s * m := fun _ _ => rfl
  have hfib : (pointPresheafFiberToStalk p X.ringCatSheaf).hom
      (((Opens.pointGrothendieckTopology p).toPresheafFiber (unop U) x
        X.ringCatSheaf.presheaf).hom a) =
      (X.ringCatSheaf.presheaf.germ (unop U) p x.down.down).hom a :=
    ConcreteCategory.congr_hom
      (toPresheafFiber_pointPresheafFiberToStalk p X.ringCatSheaf (unop U) x.down.down) a
  have hpost : (RingCat.Hom.hom
      (colimit.post ((OpenNhds.inclusion p).op ⋙ X.presheaf) (forget₂ CommRingCat RingCat) ≫
        (forget₂ CommRingCat RingCat).map (X.residue p)))
      ((X.ringCatSheaf.presheaf.germ (unop U) p x.down.down).hom a) =
      (X.evaluation (unop U) p x.down.down).hom a := by
    have h := colimit.ι_post ((OpenNhds.inclusion p).op ⋙ X.presheaf)
      (forget₂ CommRingCat RingCat) (op ⟨unop U, x.down.down⟩)
    have h2 : (RingCat.Hom.hom (colimit.post ((OpenNhds.inclusion p).op ⋙ X.presheaf)
        (forget₂ CommRingCat RingCat)))
        ((X.ringCatSheaf.presheaf.germ (unop U) p x.down.down).hom a) =
        (X.presheaf.germ (unop U) p x.down.down).hom a :=
      congrArg (fun f => (RingCat.Hom.hom f) a) h
    exact congrArg (RingCat.Hom.hom ((forget₂ CommRingCat RingCat).map (X.residue p))) h2
  rw [hfibsmul, hsmul, hfib, hpost]

/-- Higher cohomology of the residue-field skyscraper vanishes, because it is flasque. -/
lemma skyscraper_h (n : ℕ) (h : 0 < n) :
    Scheme.Modules.h k (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) n
      = 0 := by
  haveI := subsingleton_H_skyscraper_of_pos p h
  exact Module.finrank_zero_of_subsingleton

/-- The degree-zero cohomology of the residue-field skyscraper is its space of global
sections, the residue field; in particular it has dimension `finrank k κ(p)`.

The proof builds a `k`-linear equivalence `H⁰ ≃ₗ[k] κ(p)`: as an additive equivalence it is
`H.equiv₀` (`H⁰ ≅ Γ(⊤)`) composed with the identification of the skyscraper's global sections
with its value (`skyscraperSectionsAddEquiv`); `k`-linearity follows from `equiv₀`'s
naturality applied to `smulEnd`, with the geometric content supplied by `evalRes_smul`. -/
noncomputable def skyscraperH0LinearEquiv :
    Scheme.Modules.H (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) 0 ≃ₗ[k]
      ↑(X.residueField p) := by
  set F : X.Modules := skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p) with hF
  set F' := (SheafOfModules.toSheaf X.ringCatSheaf).obj F with hF'
  -- identification `Γ(⊤) ≃+ κ(p)` and the equivalence `H⁰ ≃+ Γ(⊤)`.
  let c : ↑(F'.obj.obj (op ⊤)) ≃+ ↑(X.residueField p) :=
    skyscraperSectionsAddEquiv p (AddCommGrpCat.of ↑(X.residueField p))
      (⟨⟨TopologicalSpace.Opens.mem_top p⟩⟩ : (Opens.pointGrothendieckTopology p).fiber.obj (unop (op ⊤)))
  let e₀ : ↑(lesH (CommRingCat.of k) F 0) ≃+ ↑(F'.obj.obj (op ⊤)) :=
    Sheaf.H.equiv₀ F' isTerminalTop
  -- The geometric content: `smulEnd r` acts at `⊤` (on `Γ(⊤) = ∏ κ(p)`) as the
  -- residue-field scalar `r •` on values.
  have key_action : ∀ (r : k) (y : ↑(F'.obj.obj (op ⊤))),
      c ((smulEnd (R := CommRingCat.of k) F r).hom.app (op ⊤) y) = r • c y := by
    intro r y
    -- The `k`-action on sections acts through `structureRingHom ⊤ r`; on values this is
    -- multiplication by its evaluation at `p` (`evalRes_smul`).
    have h1 : c ((smulEnd (R := CommRingCat.of k) F r).hom.app (op ⊤) y) =
        (X.evaluation ⊤ p (TopologicalSpace.Opens.mem_top p)).hom
          (structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r) * c y :=
      evalRes_smul p ⟨⟨TopologicalSpace.Opens.mem_top p⟩⟩
        (structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r) y
    have hsg : structureRingHom (R := CommRingCat.of k) (⊤ : X.Opens) r
        = globalSec (X := X) (R := CommRingCat.of k) r := by
      rw [structureRingHom_apply, Subsingleton.elim (⊤ : X.Opens).leTop.op (𝟙 _)]
      simp
    rw [h1, hsg, residueField_smul_def]
  -- `k`-linearity of `e₀` composed with the sections identification, via `equiv₀`-naturality.
  have key : ∀ (r : k) (x : ↑(lesH (CommRingCat.of k) F 0)),
      c (e₀ (CategoryTheory.Sheaf.H.map (smulEnd (R := CommRingCat.of k) F r) 0 x))
        = r • c (e₀ x) := by
    intro r x
    rw [show e₀ (CategoryTheory.Sheaf.H.map (smulEnd (R := CommRingCat.of k) F r) 0 x)
        = (smulEnd (R := CommRingCat.of k) F r).hom.app (op ⊤) (e₀ x) from
      (CategoryTheory.Sheaf.H.equiv₀_naturality (hT := isTerminalTop)
        (f := smulEnd (R := CommRingCat.of k) F r) x).symm]
    exact key_action r (e₀ x)
  exact AddEquiv.toLinearEquiv (e₀.trans c) (fun r x => key r x)

/-- The degree-zero cohomology of the residue-field skyscraper has dimension
`finrank k κ(p)`. -/
lemma skyscraper_h_zero :
    Scheme.Modules.h k (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) 0
      = Module.finrank k (X.residueField p) := by
  rw [Scheme.Modules.h]
  exact LinearEquiv.finrank_eq (skyscraperH0LinearEquiv k p)

/-- If the residue field at `p` is finite dimensional over `k`, the residue-field skyscraper
has finite-dimensional cohomology in every degree: `H⁰` is `κ(p)` itself and the rest vanish
by flasqueness. -/
lemma finite_H_skyscraper_of_finite_residueField
    (hκ : Module.Finite k ↑(X.residueField p)) (n : ℕ) :
    Module.Finite k
      (Scheme.Modules.H (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) n) := by
  rcases n with _ | m
  · haveI := hκ
    exact Module.Finite.equiv (skyscraperH0LinearEquiv k p).symm
  · haveI := subsingleton_H_skyscraper_of_pos p (Nat.succ_pos m)
    infer_instance

/-- The Euler characteristic of the residue-field skyscraper at `p` equals the dimension of
the residue field: all higher cohomology vanishes (flasqueness), so only `H⁰` contributes. -/
lemma eulerChar_skyscraper :
    Scheme.Modules.eulerChar k
      (skyscraperSheafOfModules p X.ringCatSheaf ↑(X.residueField p)) =
    Module.finrank k (X.residueField p) := by
  rw [Scheme.Modules.eulerChar,
    finsum_eq_single _ 0 (fun n hn => by simp [skyscraper_h k p n (Nat.pos_of_ne_zero hn)])]
  simp only [pow_zero, one_mul]
  rw [skyscraper_h_zero]

/-!
### The cohomology of the canonical cokernel `Q_p(D)`
-/

variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]
variable {p} (hp : coheight p = 1) (D : AlgebraicCycle X ℤ)

/-- Positive-degree cohomology of `Q_p(D)` is subsingleton: the skyscraper is flasque, with no
trivialization of the line needed. -/
lemma subsingleton_H_residueLineSheaf_of_pos {n : ℕ} (hn : 0 < n) :
    Subsingleton ((residueLineSheaf hp D).H n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact inferInstanceAs (Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj
    (skyscraperSheafOfModules p X.ringCatSheaf (residueLine hp D))).H (m + 1)))

/-- Higher cohomology of `Q_p(D)` vanishes dimensionally. -/
lemma h_residueLineSheaf (n : ℕ) (h : 0 < n) :
    Scheme.Modules.h k (residueLineSheaf hp D) n = 0 := by
  haveI := subsingleton_H_residueLineSheaf_of_pos hp D h
  exact Module.finrank_zero_of_subsingleton

/-- The degree-zero cohomology of `Q_p(D)` has dimension `dim_k κ(p)`, by transport along the
trivialization of the line. -/
lemma h_residueLineSheaf_zero :
    Scheme.Modules.h k (residueLineSheaf hp D) 0 = Module.finrank k (X.residueField p) := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
    IsRegularInCodimensionOne.stalk_dvr p hp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p)
  rw [h_eq_of_iso k (residueLineSheafIso hp D hϖ) 0]
  exact skyscraper_h_zero k p

/-- **The Euler characteristic of the canonical cokernel.**
`χ(Q_p(D)) = dim_k κ(p)`: the cokernel of `𝒪ₓ(D - p) ⟶ 𝒪ₓ(D)` contributes the dimension of
the residue field, by transport along the (uniformizer-dependent, but χ-irrelevant)
trivialization `residueLineSheafIso`. -/
lemma eulerChar_residueLineSheaf :
    Scheme.Modules.eulerChar k (residueLineSheaf hp D) =
      Module.finrank k (X.residueField p) := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
    IsRegularInCodimensionOne.stalk_dvr p hp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p)
  rw [eulerChar_eq_of_iso k (residueLineSheafIso hp D hϖ)]
  exact eulerChar_skyscraper k p

open Classical in
/--
Under the cohomological finiteness hypothesis `hf₁`, the cohomology of `Q_p(D)` is finite
dimensional over `k`. In degree zero, `Q_p(p)` is trapped between the finite-dimensional
`H⁰(𝒪ₓ(p))` and `H¹(𝒪ₓ)` in the long exact sequence of `0 ⟶ 𝒪ₓ ⟶ 𝒪ₓ(p) ⟶ Q_p(p) ⟶ 0`, and
the general `Q_p(D)` is isomorphic to it through the trivializations of the lines; in positive
degrees the cohomology is subsingleton.
-/
lemma finite_H_residueLineSheaf
    (hf₁ : ∀ (E : AlgebraicCycle X ℤ) (n : ℕ), Module.Finite k ((sheaf E).H n))
    (pClosed : ∀ x : X, x ≤ p → x = p) (n : ℕ) :
    Module.Finite k ((residueLineSheaf hp D).H n) := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
    IsRegularInCodimensionOne.stalk_dvr p hp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p)
  rcases n with _ | m
  · -- Degree zero: trap `H⁰(Q_p(p))` in the long exact sequence, then transport to `D`.
    let o := twistedClosedSubschemeComplex₂ (D := 0) (D' := single p 1) hp (by simp)
    have hS : (o.map (Modules.toSheafAb X)).ShortExact :=
      shortExact_map_toSheaf (twistedClosedSubschemeComplex₂_shortExact
        (by simp) hp (by simp) pClosed)
    -- Positions 1, 2, 3 of the spliced LES are `H⁰(𝒪ₓ(p)) → H⁰(Q_p(p)) → H¹(𝒪ₓ)`; the outer
    -- terms are Noetherian, so `isNoetherian_of_range_eq_ker` traps the middle.
    have hex := dAux_exact (CommRingCat.of k) o hS 0 1
    haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o 0 1) :=
      IsNoetherian.iff_fg.mpr (hf₁ (single p 1) 0)
    haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o 0 3) :=
      IsNoetherian.iff_fg.mpr (hf₁ 0 1)
    haveI : _root_.IsNoetherian k (lesXAux (CommRingCat.of k) o 0 2) :=
      isNoetherian_of_range_eq_ker _ _ hex.moduleCat_range_eq_ker
    have h0 : Module.Finite k ((residueLineSheaf hp (single p 1)).H 0) :=
      IsNoetherian.iff_fg.mp ‹_›
    -- Transport across `Q_p(p) ≅ κ(p) ≅ Q_p(D)`.
    exact Module.Finite.equiv (hLinearEquivOfIso k
      ((residueLineSheafIso hp (single p 1) hϖ).trans (residueLineSheafIso hp D hϖ).symm) 0)
  · haveI := subsingleton_H_residueLineSheaf_of_pos hp D (Nat.succ_pos m)
    infer_instance

/-- If the residue field at `p` is finite dimensional over `k` (as holds at any closed point
of a scheme of finite type over `k`), the cohomology of `Q_p(D)` is finite dimensional in
every degree, with no hypothesis on the divisor sheaves: transport
`finite_H_skyscraper_of_finite_residueField` along the trivialization of the line. -/
lemma finite_H_residueLineSheaf_of_finite_residueField
    (hκ : Module.Finite k ↑(X.residueField p)) (n : ℕ) :
    Module.Finite k ((residueLineSheaf hp D).H n) := by
  haveI : IsDiscreteValuationRing (X.presheaf.stalk p) :=
    IsRegularInCodimensionOne.stalk_dvr p hp
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk p)
  haveI := finite_H_skyscraper_of_finite_residueField k p hκ n
  exact Module.Finite.equiv (hLinearEquivOfIso k (residueLineSheafIso hp D hϖ) n).symm

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
