module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.CohmologyModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Algebra.Homology.EulerPoincare

/-!
# Additivity of the Euler characteristic in short exact sequences

Given a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of sheaves of modules on a scheme `X`
over a field `k`, with finite-dimensional and eventually-vanishing cohomologies, we show that
`χ(F₂) = χ(F₁) + χ(F₃)` where `χ(F) = ∑ (-1)ⁿ dim_k Hⁿ(F)`.

The proof splices the long exact cohomology sequence into a single bounded exact complex of
`k`-modules and applies the Euler–Poincaré formula.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme Limits Abelian

variable {X : Scheme.{u}} {R : CommRingCat.{u}} [X.Over (Spec R)]


/--
The forgetful functor `𝒪ₓ-modules ⥤ abelian sheaves`, with its codomain pinned to
`Sheaf (Opens.grothendieckTopology X) AddCommGrpCat`.

This ascription is **load-bearing**: `Sheaf J AddCommGrpCat` carries two definitionally equal but
syntactically distinct `HasZeroMorphisms` instances (one via `Preadditive`, one via the
full-subcategory-of-presheaves structure that `ShortComplex.map` uses). Writing
`SheafOfModules.toSheaf X.ringCatSheaf` directly lets the two leak into different use sites, so the
`PreservesZeroMorphisms` instance found at a declaration fails to match the one required at a
`S.map …` site. Routing every `S.map` through this single pinned functor keeps them consistent.
-/
noncomputable abbrev Modules.toSheafAb (X : Scheme.{u}) :
    X.Modules ⥤ Sheaf (Opens.grothendieckTopology ↑X.toPresheafedSpace) AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

noncomputable instance : (Modules.toSheafAb X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

noncomputable instance : (Modules.toSheafAb X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- The forgetful functor `SheafOfModules R ⥤ Sheaf J AddCommGrpCat` preserves finite colimits: a
finite diagram `D` of sheaves of modules is (via the reflective counit) the sheafification of the
diagram of underlying presheaves, and `sheafification ⋙ toSheaf` preserves finite colimits (it is
`toPresheaf ⋙ presheafToSheaf`). Together with `PreservesFiniteLimits`, this makes `toSheaf` exact,
so it sends short exact sequences of sheaves of modules to short exact sequences of abelian sheaves. -/
noncomputable instance toSheaf_preservesFiniteColimits {C : Type*} [Category C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{u}]
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Limits.PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) := by
  have adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  haveI hcounit : IsIso adj.counit := inferInstance
  have ε := asIso adj.counit
  haveI : Limits.PreservesFiniteColimits
      (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ SheafOfModules.toSheaf R) :=
    Limits.preservesFiniteColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
  constructor
  intro K _ _
  constructor
  intro D
  have hiso : (D ⋙ SheafOfModules.forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj) ≅ D :=
    Functor.associator D (SheafOfModules.forget R) (PresheafOfModules.sheafification (𝟙 R.obj)) ≪≫
      Functor.isoWhiskerLeft D ε ≪≫ D.rightUnitor
  haveI : Limits.PreservesColimit
      ((D ⋙ SheafOfModules.forget R) ⋙ PresheafOfModules.sheafification (𝟙 R.obj))
      (SheafOfModules.toSheaf R) := by
    apply Limits.preservesColimit_of_preserves_colimit_cocone
      (Limits.isColimitOfPreserves (PresheafOfModules.sheafification (𝟙 R.obj))
        (Limits.colimit.isColimit (D ⋙ SheafOfModules.forget R)))
    exact Limits.isColimitOfPreserves
      (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ SheafOfModules.toSheaf R)
      (Limits.colimit.isColimit (D ⋙ SheafOfModules.forget R))
  exact Limits.preservesColimit_of_iso_diagram (SheafOfModules.toSheaf R) hiso

/-- `toSheaf` preserves finite limits (a thin restatement so the instance is resolved in a context
without an ambient `ShortExact` hypothesis, which otherwise derails synthesis). -/
lemma toSheaf_preservesFiniteLimits {Y : Scheme.{u}} :
    Limits.PreservesFiniteLimits (SheafOfModules.toSheaf.{u} Y.ringCatSheaf) := inferInstance

/-- Since `toSheaf` is exact (it preserves finite limits and, by `toSheaf_preservesFiniteColimits`,
finite colimits), a short exact sequence of sheaves of modules maps to a short exact sequence of
abelian sheaves. -/
lemma shortExact_map_toSheaf {Y : Scheme.{u}} {S : ShortComplex Y.Modules}
    (hSE : S.ShortExact) : (S.map (SheafOfModules.toSheaf.{u} Y.ringCatSheaf)).ShortExact :=
  @ShortComplex.ShortExact.map_of_exact Y.Modules _ _ _ _ _ S hSE
    (SheafOfModules.toSheaf.{u} Y.ringCatSheaf) inferInstance toSheaf_preservesFiniteLimits
    (toSheaf_preservesFiniteColimits Y.ringCatSheaf)

section LinearGlue

/--
The scalar action of `r : R` on sheaf cohomology is `H.map` applied to the
`smulEnd` endomorphism.
-/
lemma smul_eq_H_map (F : X.Modules) (r : R) (n : ℕ)
    (x : ((SheafOfModules.toSheaf _).obj F).H n) :
    r • x = Sheaf.H.map (smulEnd F r) n x := rfl

/--
Multiplication by `r : R` commutes with (the underlying abelian sheaf morphism of) any
morphism of sheaves of modules.
-/
lemma smulEnd_naturality {F G : X.Modules} (ψ : F ⟶ G) (r : R) :
    (smulEnd F r : (SheafOfModules.toSheaf X.ringCatSheaf).obj F ⟶ _) ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map ψ =
      (SheafOfModules.toSheaf X.ringCatSheaf).map ψ ≫ smulEnd G r := by
  apply Sheaf.hom_ext
  ext U x
  exact map_smul (ψ.val.app U).hom (structureRingHom U.unop r) (show Γ(F, U.unop) from x)

/--
The map induced on cohomology by a morphism of sheaves of modules, as an `R`-linear map.
-/
noncomputable def HMapₗ {F G : X.Modules} (ψ : F ⟶ G) (n : ℕ) :
    ((SheafOfModules.toSheaf _).obj F).H n →ₗ[R] ((SheafOfModules.toSheaf _).obj G).H n where
  toFun := Sheaf.H.map ((SheafOfModules.toSheaf _).map ψ) n
  map_add' := map_add _
  map_smul' r x := by
    change Sheaf.H.map _ n (r • x) = r • Sheaf.H.map _ n x
    rw [smul_eq_H_map, smul_eq_H_map, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply,
      smulEnd_naturality]

variable {S : ShortComplex X.Modules}

/--
The endomorphism of the short complex of abelian sheaves underlying `S` given by scalar
multiplication by `r : R` on each term.
-/
noncomputable def smulShortComplexEnd (S : ShortComplex X.Modules) (r : R) :
    S.map (Modules.toSheafAb X) ⟶ S.map (Modules.toSheafAb X) where
  τ₁ := smulEnd S.X₁ r
  τ₂ := smulEnd S.X₂ r
  τ₃ := smulEnd S.X₃ r
  comm₁₂ := smulEnd_naturality S.f r
  comm₂₃ := smulEnd_naturality S.g r

/--
The connecting homomorphism of the long exact cohomology sequence, as an `R`-linear map.
-/
noncomputable def δₗ (hS : (S.map (Modules.toSheafAb X)).ShortExact)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    ((SheafOfModules.toSheaf _).obj S.X₃).H n₀ →ₗ[R]
      ((SheafOfModules.toSheaf _).obj S.X₁).H n₁ where
  toFun := Sheaf.H.δ hS n₀ n₁ h
  map_add' := map_add _
  map_smul' r x :=
    -- Both scalar actions are `H.map` of the corresponding `smulEnd`, so this is exactly
    -- the naturality of the connecting homomorphism applied to the `smul` endomorphism of `S`.
    Sheaf.H.δ_naturality n₀ n₁ h hS hS (smulShortComplexEnd S r) x

end LinearGlue

section Splice

variable (R) (S : ShortComplex X.Modules)
    (hS : (S.map (Modules.toSheafAb X)).ShortExact)

/-- The cohomology `Hⁿ(F)` of a sheaf of modules `F`, as an object of `ModuleCat R`. The three
terms of the long exact sequence are `lesH R S.X₁`, `lesH R S.X₂`, `lesH R S.X₃`. -/
noncomputable def lesH (F : X.Modules) (n : ℕ) : ModuleCat R :=
  .of R (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H n)

/-- The map on cohomology in each degree induced by a morphism `ψ : F ⟶ G` of sheaves of modules.
The two non-connecting maps of the long exact sequence are `lesMap R S.f` and `lesMap R S.g`. -/
noncomputable def lesMap {F G : X.Modules} (ψ : F ⟶ G) (n : ℕ) : lesH R F n ⟶ lesH R G n :=
  ModuleCat.ofHom (HMapₗ (R := R) ψ n)

/-- The connecting map of the long exact sequence in each degree. -/
noncomputable def lesδ (n : ℕ) : lesH R S.X₃ n ⟶ lesH R S.X₁ (n + 1) :=
  ModuleCat.ofHom (δₗ (R := R) hS n (n + 1) rfl)

/--
The terms of the long exact sequence, with a shifted block parameter `s` so that the
period-three pattern is a structural recursion: `lesXAux s` lists
`Hˢ(X₁), Hˢ(X₂), Hˢ(X₃), Hˢ⁺¹(X₁), …`.
-/
noncomputable def lesXAux (s : ℕ) : ℕ → ModuleCat R
  | 0 => lesH R S.X₁ s
  | 1 => lesH R S.X₂ s
  | 2 => lesH R S.X₃ s
  | (m + 3) => lesXAux (s + 1) m

/-- The maps of the long exact sequence, in the indexing of `lesXAux`. The pattern of each block is
`Hˢ(X₁) →f Hˢ(X₂) →g Hˢ(X₃) →δ Hˢ⁺¹(X₁)`. -/
noncomputable def dAux (s : ℕ) :
    (m : ℕ) → (lesXAux R S s m ⟶ lesXAux R S s (m + 1))
  | 0 => lesMap R S.f s
  | 1 => lesMap R S.g s
  | 2 => lesδ R S hS s
  | (m + 3) => dAux (s + 1) m

include hS in
/-- Consecutive maps of the long exact sequence compose to zero. -/
lemma lesF_comp_lesG (n : ℕ) : lesMap R S.f n ≫ lesMap R S.g n = 0 := by
  have hzero : (SheafOfModules.toSheaf X.ringCatSheaf).map S.f ≫
      (SheafOfModules.toSheaf X.ringCatSheaf).map S.g = 0 :=
    (S.map (Modules.toSheafAb X)).zero
  ext x
  change Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map S.g) n
    (Sheaf.H.map ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f) n x) = 0
  rw [← Sheaf.H.map_comp_apply, hzero]
  change x.comp (Ext.mk₀ 0) (add_zero n) = 0
  rw [Ext.mk₀_zero, Ext.comp_zero]

/-- Consecutive maps of the long exact sequence compose to zero. -/
lemma lesG_comp_lesδ (n : ℕ) : lesMap R S.g n ≫ lesδ R S hS n = 0 := by
  have hzero : (Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map S.g)).comp
      hS.extClass (zero_add 1) = 0 := hS.comp_extClass
  ext x
  refine (Ext.comp_assoc_of_second_deg_zero x (Ext.mk₀ _) hS.extClass rfl).trans ?_
  exact (congrArg (fun e => x.comp e rfl) hzero).trans (Ext.comp_zero x _ 1 (n + 1) rfl)

/-- Consecutive maps of the long exact sequence compose to zero. -/
lemma lesδ_comp_lesF (n : ℕ) : lesδ R S hS n ≫ lesMap R S.f (n + 1) = 0 := by
  have hzero : hS.extClass.comp
      (Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f)) (add_zero 1) = 0 :=
    hS.extClass_comp
  ext x
  refine (Ext.comp_assoc_of_third_deg_zero x hS.extClass _ rfl).trans ?_
  exact (congrArg (fun e => x.comp e rfl) hzero).trans (Ext.comp_zero x _ 1 (n + 1) rfl)

/-- Consecutive maps in the `dAux` indexing compose to zero. -/
lemma dAux_comp (s : ℕ) : ∀ m, dAux R S hS s m ≫ dAux R S hS s (m + 1) = 0
  | 0 => lesF_comp_lesG R S hS s
  | 1 => lesG_comp_lesδ R S hS s
  | 2 => lesδ_comp_lesF R S hS s
  | (m + 3) => dAux_comp (s + 1) m

/-- The graded object underlying the spliced long exact sequence:
`Hⁿ(X₁), Hⁿ(X₂), Hⁿ(X₃)` are placed at positions `3n, 3n+1, 3n+2`. -/
noncomputable def lesX : ℕ → ModuleCat R := lesXAux R S 0

/-- The differentials of the spliced long exact sequence (a cochain complex on `ℕ`). -/
noncomputable def lesD : (i j : ℕ) → (lesX R S i ⟶ lesX R S j)
  | i, j =>
    if h : j = i + 1 then
      h ▸ (dAux R S hS 0 i : lesX R S i ⟶ lesX R S (i + 1))
    else 0

/-- The long exact sequence of cohomology of a short exact sequence of sheaves of modules,
spliced into a single `ℕ`-indexed cochain complex. -/
noncomputable def lesComplex : CochainComplex (ModuleCat R) ℕ where
  X := lesX R S
  d := lesD R S hS
  shape i j hij := by
    show lesD R S hS i j = 0
    rw [lesD, dif_neg]
    intro h
    exact hij (by rw [ComplexShape.up_Rel]; omega)
  d_comp_d' i j l hij hjl := by
    show lesD R S hS i j ≫ lesD R S hS j l = 0
    rw [lesD, lesD]
    split_ifs with h1 h2
    · subst h1; subst h2; exact dAux_comp R S hS 0 i
    · exact comp_zero ..
    · exact zero_comp ..
    · exact zero_comp ..

/-- The `dAux` windows of the long exact sequence are exact. This is exactly the exactness of
the long exact cohomology sequence, read off from `longSequence_exact₁/₂/₃`. -/
lemma dAux_exact (s : ℕ) : ∀ m, (ShortComplex.mk (dAux R S hS s m) (dAux R S hS s (m + 1))
    (dAux_comp R S hS s m)).Exact
  | 0 => by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    exact Sheaf.H.longSequence_exact₂ hS s x₂ hx₂
  | 1 => by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    exact Sheaf.H.longSequence_exact₃ hS s (s + 1) rfl x₂ hx₂
  | 2 => by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    exact Sheaf.H.longSequence_exact₁ hS s (s + 1) rfl x₂ hx₂
  | (m + 3) => dAux_exact (s + 1) m

/-- The differentials of the spliced complex are the `dAux` maps. The `dite` in `lesD`
does not reduce definitionally for symbolic `i` (since `Nat.decEq i i` is stuck), so this is
needed as a propositional rewrite. -/
lemma lesComplex_d (i : ℕ) :
    (lesComplex R S hS).d i (i + 1) = dAux R S hS 0 i := by
  simp [lesComplex, lesD]

/-- The spliced long exact sequence is exact everywhere. The interior windows are the exactness
of the long exact sequence; exactness at degree `0` is the injectivity of `H⁰(f)` (which holds
because `f` is a monomorphism). -/
lemma lesComplex_exactAt (i : ℕ) : (lesComplex R S hS).ExactAt i := by
  cases i with
  | zero =>
    -- the window `0 ⟶ H⁰(X₁) ⟶ H⁰(X₂)`: exactness is the injectivity of `H⁰(f)`.
    rw [HomologicalComplex.exactAt_iff'
      (lesComplex R S hS) 0 0 1
      ((ComplexShape.up ℕ).prev_eq_self 0 (by simp [ComplexShape.up_Rel]))
      ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk 0 1 rfl)),
      ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    refine ⟨0, ?_⟩
    rw [show (HomologicalComplex.sc' (lesComplex R S hS) 0 0 1).g = dAux R S hS 0 0
      from lesComplex_d R S hS 0] at hx₂
    have hx₂' : Sheaf.H.map ((S.map (Modules.toSheafAb X)).f) 0 x₂ = 0 := hx₂
    have h1 : Ext.addEquiv₀ x₂ ≫ (S.map (Modules.toSheafAb X)).f = 0 := by
      have e := Sheaf.H.addEquiv₀_map ((S.map (Modules.toSheafAb X)).f) x₂
      rw [hx₂', map_zero] at e
      exact e.symm
    have hmono : Mono ((S.map (Modules.toSheafAb X)).f) := hS.mono_f
    have h3 : Ext.addEquiv₀ x₂ = 0 :=
      hmono.right_cancellation (Ext.addEquiv₀ x₂) 0 (h1.trans (Limits.zero_comp).symm)
    have h2 : x₂ = 0 := (map_eq_zero_iff _ Ext.addEquiv₀.injective).mp h3
    rw [h2]
    rfl
  | succ m =>
    -- the interior windows are exactly the `dAux` windows
    rw [HomologicalComplex.exactAt_iff'
      (lesComplex R S hS) m (m + 1) (m + 2)
      ((ComplexShape.up ℕ).prev_eq' (ComplexShape.up_mk m (m + 1) rfl))
      ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk (m + 1) (m + 2) rfl)),
      ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    rw [show (HomologicalComplex.sc' (lesComplex R S hS) m (m + 1) (m + 2)).g =
      dAux R S hS 0 (m + 1) from lesComplex_d R S hS (m + 1)] at hx₂
    obtain ⟨x₁, hx₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp (dAux_exact R S hS 0 m) x₂ hx₂
    refine ⟨x₁, ?_⟩
    rw [show (HomologicalComplex.sc' (lesComplex R S hS) m (m + 1) (m + 2)).f = dAux R S hS 0 m
      from lesComplex_d R S hS m]
    exact hx₁

/-- The homology of the spliced long exact sequence vanishes. -/
lemma lesComplex_homology_isZero (i : ℕ) : IsZero ((lesComplex R S hS).homology i) :=
  (lesComplex_exactAt R S hS i).isZero_homology

/-- Structural value of `lesXAux` on multiples of `3`: `Hˢ⁺ᵗ(X₁)`. -/
lemma lesXAux_three_mul (s t : ℕ) : lesXAux R S s (3 * t) = lesH R S.X₁ (s + t) := by
  induction t generalizing s with
  | zero => simp [lesXAux]
  | succ t ih =>
    rw [show 3 * (t + 1) = 3 * t + 3 from by ring]
    show lesXAux R S (s + 1) (3 * t) = _
    rw [ih (s + 1), show s + 1 + t = s + (t + 1) from by omega]

/-- Structural value of `lesXAux` on `3t+1`: `Hˢ⁺ᵗ(X₂)`. -/
lemma lesXAux_three_mul_add_one (s t : ℕ) :
    lesXAux R S s (3 * t + 1) = lesH R S.X₂ (s + t) := by
  induction t generalizing s with
  | zero => simp [lesXAux]
  | succ t ih =>
    rw [show 3 * (t + 1) + 1 = (3 * t + 1) + 3 from by ring]
    show lesXAux R S (s + 1) (3 * t + 1) = _
    rw [ih (s + 1), show s + 1 + t = s + (t + 1) from by omega]

/-- Structural value of `lesXAux` on `3t+2`: `Hˢ⁺ᵗ(X₃)`. -/
lemma lesXAux_three_mul_add_two (s t : ℕ) :
    lesXAux R S s (3 * t + 2) = lesH R S.X₃ (s + t) := by
  induction t generalizing s with
  | zero => simp [lesXAux]
  | succ t ih =>
    rw [show 3 * (t + 1) + 2 = (3 * t + 2) + 3 from by ring]
    show lesXAux R S (s + 1) (3 * t + 2) = _
    rw [ih (s + 1), show s + 1 + t = s + (t + 1) from by omega]

/-- `Hⁿ(X₁)` sits at position `3n` of the spliced complex. -/
lemma lesX_three_mul (n : ℕ) : lesX R S (3 * n) = lesH R S.X₁ n := by
  show lesXAux R S 0 (3 * n) = _
  rw [lesXAux_three_mul, Nat.zero_add]

/-- `Hⁿ(X₂)` sits at position `3n+1` of the spliced complex. -/
lemma lesX_three_mul_add_one (n : ℕ) : lesX R S (3 * n + 1) = lesH R S.X₂ n := by
  show lesXAux R S 0 (3 * n + 1) = _
  rw [lesXAux_three_mul_add_one, Nat.zero_add]

/-- `Hⁿ(X₃)` sits at position `3n+2` of the spliced complex. -/
lemma lesX_three_mul_add_two (n : ℕ) : lesX R S (3 * n + 2) = lesH R S.X₃ n := by
  show lesXAux R S 0 (3 * n + 2) = _
  rw [lesXAux_three_mul_add_two, Nat.zero_add]

end Splice

section Field

open Finset

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
  (S : ShortComplex X.Modules)

/-- `dim_k Hⁿ(F)`, accessed through the spliced complex object `lesH` (a `ModuleCat`, so its
`k`-module structure is structural and finrank is well-behaved). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.h (F : X.Modules) (n : ℕ) : ℕ :=
  Module.finrank k (lesH (CommRingCat.of k) F n)

/-- The **Euler characteristic** of a sheaf of modules: `χ(F) = ∑ₙ (-1)ⁿ dim_k Hⁿ(F)`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.eulerChar (F : X.Modules) : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (F.h k n : ℤ)

variable (hS : (S.map (Modules.toSheafAb X)).ShortExact)

/-- Each term of the spliced complex is finite-dimensional, given finiteness of the cohomologies. -/
lemma lesXAux_finite
    (hf₁ : ∀ n, Module.Finite k (lesH (CommRingCat.of k) S.X₁ n))
    (hf₂ : ∀ n, Module.Finite k (lesH (CommRingCat.of k) S.X₂ n))
    (hf₃ : ∀ n, Module.Finite k (lesH (CommRingCat.of k) S.X₃ n)) :
    ∀ (m s : ℕ), Module.Finite k (lesXAux (CommRingCat.of k) S s m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => exact fun s => hf₁ s
    | 1, _ => exact fun s => hf₂ s
    | 2, _ => exact fun s => hf₃ s
    | (m + 3), ih => exact fun s => ih m (by omega) (s + 1)

/-- All objects of the spliced complex are finite-dimensional. -/
lemma lesComplex_X_finite
    (hf₁ : ∀ n, Module.Finite k (lesH (CommRingCat.of k) S.X₁ n))
    (hf₂ : ∀ n, Module.Finite k (lesH (CommRingCat.of k) S.X₂ n))
    (hf₃ : ∀ n, Module.Finite k (lesH (CommRingCat.of k) S.X₃ n)) :
    ∀ (i : ℕ), Module.Finite k ((lesComplex (CommRingCat.of k) S hS).X i) :=
  fun i => lesXAux_finite k S hf₁ hf₂ hf₃ i 0

/-- The homology Euler characteristic of the spliced complex is zero (it is exact). -/
lemma lesComplex_homologyEulerChar_zero :
    (lesComplex (CommRingCat.of k) S hS).homologyEulerChar = 0 := by
  rw [HomologicalComplex.homologyEulerChar, GradedObject.eulerChar]
  apply finsum_eq_zero_of_forall_eq_zero
  intro i
  haveI : Subsingleton ↑((lesComplex (CommRingCat.of k) S hS).homology i) :=
    ModuleCat.subsingleton_of_isZero (lesComplex_homology_isZero (CommRingCat.of k) S hS i)
  simp [Module.finrank_zero_of_subsingleton]

/-! ### Signs at the three position families -/

lemma neg_one_pow_three_mul (n : ℕ) : (-1 : ℤ) ^ (3 * n) = (-1) ^ n := by
  rw [pow_mul]; norm_num

lemma neg_one_pow_three_mul_add_one (n : ℕ) : (-1 : ℤ) ^ (3 * n + 1) = -((-1) ^ n) := by
  rw [pow_succ, neg_one_pow_three_mul]; ring

lemma neg_one_pow_three_mul_add_two (n : ℕ) : (-1 : ℤ) ^ (3 * n + 2) = (-1) ^ n := by
  rw [pow_add, neg_one_pow_three_mul]; norm_num

/-- The Euler-characteristic sign `(up ℕ).χ m`, coerced to `ℤ`, is `(-1)ᵐ`. -/
lemma chi_up_coe (m : ℕ) : ((ComplexShape.up ℕ).χ m : ℤ) = (-1 : ℤ) ^ m := by
  simp only [ComplexShape.eulerCharSignsUpNat_χ]
  rfl

lemma chi_up_three_mul (n : ℕ) : ((ComplexShape.up ℕ).χ (3 * n) : ℤ) = (-1) ^ n := by
  rw [chi_up_coe, neg_one_pow_three_mul]

lemma chi_up_three_mul_add_one (n : ℕ) :
    ((ComplexShape.up ℕ).χ (3 * n + 1) : ℤ) = -((-1) ^ n) := by
  rw [chi_up_coe, neg_one_pow_three_mul_add_one]

lemma chi_up_three_mul_add_two (n : ℕ) :
    ((ComplexShape.up ℕ).χ (3 * n + 2) : ℤ) = (-1) ^ n := by
  rw [chi_up_coe, neg_one_pow_three_mul_add_two]

/-! ### finrank at the three position families -/

lemma finrank_X_A (n : ℕ) :
    Module.finrank k ((lesComplex (CommRingCat.of k) S hS).X (3 * n)) = AlgebraicGeometry.Scheme.Modules.h k S.X₁ n := by
  rw [show (lesComplex (CommRingCat.of k) S hS).X (3 * n) = lesH (CommRingCat.of k) S.X₁ n
    from lesX_three_mul (CommRingCat.of k) S n]; rfl

lemma finrank_X_B (n : ℕ) :
    Module.finrank k ((lesComplex (CommRingCat.of k) S hS).X (3 * n + 1)) = AlgebraicGeometry.Scheme.Modules.h k S.X₂ n := by
  rw [show (lesComplex (CommRingCat.of k) S hS).X (3 * n + 1) = lesH (CommRingCat.of k) S.X₂ n
    from lesX_three_mul_add_one (CommRingCat.of k) S n]; rfl

lemma finrank_X_C (n : ℕ) :
    Module.finrank k ((lesComplex (CommRingCat.of k) S hS).X (3 * n + 2)) = AlgebraicGeometry.Scheme.Modules.h k S.X₃ n := by
  rw [show (lesComplex (CommRingCat.of k) S hS).X (3 * n + 2) = lesH (CommRingCat.of k) S.X₃ n
    from lesX_three_mul_add_two (CommRingCat.of k) S n]; rfl

/-! ### Vanishing outside a bounded window -/

variable {N : ℕ}

/-- If the cohomologies vanish above `N`, then so does the spliced stream beyond total index. -/
lemma lesXAux_isZero
    (hb₁ : ∀ n, N < n → IsZero (lesH (CommRingCat.of k) S.X₁ n))
    (hb₂ : ∀ n, N < n → IsZero (lesH (CommRingCat.of k) S.X₂ n))
    (hb₃ : ∀ n, N < n → IsZero (lesH (CommRingCat.of k) S.X₃ n)) :
    ∀ (m s : ℕ), 3 * N + 2 < 3 * s + m → IsZero (lesXAux (CommRingCat.of k) S s m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => exact fun s hs => hb₁ s (by omega)
    | 1, _ => exact fun s hs => hb₂ s (by omega)
    | 2, _ => exact fun s hs => hb₃ s (by omega)
    | (m + 3), ih => exact fun s hs => ih m (by omega) (s + 1) (by omega)

/-- Finite-sum form of an Euler characteristic finsum, given a vanishing bound. -/
lemma eulerChar_finsum_eq (d : ℕ → ℕ) (hd : ∀ n, N < n → d n = 0) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (d n : ℤ)) =
      ∑ n ∈ range (N + 1), (-1 : ℤ) ^ n * (d n : ℤ) := by
  rw [finsum_eq_finsetSum_of_support_subset]
  intro n hn
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hn
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hle
  exact hn.2 (by rw [hd n (by omega)]; simp)

include hS

/-- The `finrank`-support of the spliced complex is contained in the image of
`(n, p) ↦ 3n+p` over `range (N+1) ×ˢ range 3`. -/
lemma finrankSupport_subset
    (hb₁ : ∀ n, N < n → IsZero (lesH (CommRingCat.of k) S.X₁ n))
    (hb₂ : ∀ n, N < n → IsZero (lesH (CommRingCat.of k) S.X₂ n))
    (hb₃ : ∀ n, N < n → IsZero (lesH (CommRingCat.of k) S.X₃ n)) :
    GradedObject.finrankSupport (lesComplex (CommRingCat.of k) S hS).X ⊆
      ↑(((range (N + 1)) ×ˢ (range 3)).image (fun q : ℕ × ℕ => 3 * q.1 + q.2)) := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro i hi
  -- If `i ≤ 3N+2` then `i` is in the image, contradicting `hi`; so `i > 3N+2`, giving zero.
  have hi' : 3 * N + 2 < i := by
    by_contra hle
    refine hi ?_
    have hdm := Nat.div_add_mod i 3
    have hmod : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, mem_product, mem_range]
    exact ⟨(i / 3, i % 3), ⟨by omega, by omega⟩, by omega⟩
  haveI : Subsingleton ↑((lesComplex (CommRingCat.of k) S hS).X i) :=
    ModuleCat.subsingleton_of_isZero
      (lesXAux_isZero k S hb₁ hb₂ hb₃ i 0 (by omega))
  exact Module.finrank_zero_of_subsingleton

omit hS in
/-- **The Euler characteristic is additive in short exact sequences.** Given a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` of sheaves of modules over a field `k`, with finite-dimensional cohomology
vanishing above some degree `N`, the Euler characteristics satisfy `χ(X₂) = χ(X₁) + χ(X₃)`.

The proof splices the long exact cohomology sequence into one bounded exact `ℕ`-indexed cochain
complex of `k`-vector spaces and applies the Euler–Poincaré formula. -/
theorem eulerChar_additive (hSE : S.ShortExact)
    (hf₁ : ∀ n, Module.Finite k (lesH (CommRingCat.of k) S.X₁ n))
    (hf₂ : ∀ n, Module.Finite k (lesH (CommRingCat.of k) S.X₂ n))
    (hf₃ : ∀ n, Module.Finite k (lesH (CommRingCat.of k) S.X₃ n))
    (hb₁ : ∀ n, N < n → IsZero (lesH (CommRingCat.of k) S.X₁ n))
    (hb₂ : ∀ n, N < n → IsZero (lesH (CommRingCat.of k) S.X₂ n))
    (hb₃ : ∀ n, N < n → IsZero (lesH (CommRingCat.of k) S.X₃ n)) :
    S.X₂.eulerChar k = S.X₁.eulerChar k + S.X₃.eulerChar k := by
  -- `toSheaf` is exact, so the short exact sequence of sheaves of modules maps to one of abelian
  -- sheaves, which is what the long exact cohomology sequence is built from.
  have hS : (S.map (Modules.toSheafAb X)).ShortExact := shortExact_map_toSheaf hSE
  haveI : ∀ i, Module.Finite k ((lesComplex (CommRingCat.of k) S hS).X i) :=
    lesComplex_X_finite k S hS hf₁ hf₂ hf₃
  -- The dimensions vanish above `N`.
  have hbA : ∀ n, N < n → AlgebraicGeometry.Scheme.Modules.h k S.X₁ n = 0 := by
    intro n hn; haveI := ModuleCat.subsingleton_of_isZero (hb₁ n hn)
    exact Module.finrank_zero_of_subsingleton
  have hbB : ∀ n, N < n → AlgebraicGeometry.Scheme.Modules.h k S.X₂ n = 0 := by
    intro n hn; haveI := ModuleCat.subsingleton_of_isZero (hb₂ n hn)
    exact Module.finrank_zero_of_subsingleton
  have hbC : ∀ n, N < n → AlgebraicGeometry.Scheme.Modules.h k S.X₃ n = 0 := by
    intro n hn; haveI := ModuleCat.subsingleton_of_isZero (hb₃ n hn)
    exact Module.finrank_zero_of_subsingleton
  -- Euler–Poincaré: the alternating sum of dimensions equals the (vanishing) homology version.
  have hEP : (lesComplex (CommRingCat.of k) S hS).eulerChar = 0 := by
    rw [ChainComplex.eulerChar_eq_homologyEulerChar' (lesComplex (CommRingCat.of k) S hS)
      0 (3 * N + 2) (by omega) (fun i hi => absurd hi (Nat.not_lt_zero i)) ?_,
      lesComplex_homologyEulerChar_zero]
    intro i hi
    exact lesXAux_isZero k S hb₁ hb₂ hb₃ i 0 (by omega)
  -- The bridge: the spliced Euler characteristic equals `χ(X₁) - χ(X₂) + χ(X₃)`.
  have heA := eulerChar_finsum_eq (AlgebraicGeometry.Scheme.Modules.h k S.X₁) hbA
  have heB := eulerChar_finsum_eq (AlgebraicGeometry.Scheme.Modules.h k S.X₂) hbB
  have heC := eulerChar_finsum_eq (AlgebraicGeometry.Scheme.Modules.h k S.X₃) hbC
  have key : (lesComplex (CommRingCat.of k) S hS).eulerChar =
      AlgebraicGeometry.Scheme.Modules.eulerChar k S.X₁ - AlgebraicGeometry.Scheme.Modules.eulerChar k S.X₂ + AlgebraicGeometry.Scheme.Modules.eulerChar k S.X₃ := by
    rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset _ _
      (finrankSupport_subset k S hS hb₁ hb₂ hb₃),
      Finset.sum_image (by
        intro x hx y hy hxy
        have hx3 : x.2 < 3 := Finset.mem_range.mp (Finset.mem_product.mp hx).2
        have hy3 : y.2 < 3 := Finset.mem_range.mp (Finset.mem_product.mp hy).2
        have h : 3 * x.1 + x.2 = 3 * y.1 + y.2 := hxy
        exact Prod.ext (by omega) (by omega)),
      Finset.sum_product]
    rw [AlgebraicGeometry.Scheme.Modules.eulerChar, AlgebraicGeometry.Scheme.Modules.eulerChar, AlgebraicGeometry.Scheme.Modules.eulerChar, heA, heB, heC,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    simp only [Nat.add_zero]
    rw [chi_up_three_mul n, chi_up_three_mul_add_one n, chi_up_three_mul_add_two n,
      finrank_X_A k S hS n, finrank_X_B k S hS n, finrank_X_C k S hS n]
    ring
  -- Conclude.
  rw [key] at hEP
  linarith

end Field
