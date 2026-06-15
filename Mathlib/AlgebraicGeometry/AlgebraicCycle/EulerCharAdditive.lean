module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.CohmologyModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
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
The forgetful functor from `𝒪ₓ`-modules to sheaves of abelian groups, typed over the
category `X.Modules` (which carries its own category instance).
-/
noncomputable abbrev Modules.toSheafAb (X : Scheme.{u}) :
    X.Modules ⥤
      Sheaf (Opens.grothendieckTopology ↑X.toPresheafedSpace)
        AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

noncomputable instance : (Modules.toSheafAb X).Additive :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive

noncomputable instance : (Modules.toSheafAb X).PreservesZeroMorphisms :=
  inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).PreservesZeroMorphisms

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
    S.map (Modules.toSheafAb X) ⟶
      S.map (Modules.toSheafAb X) where
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

variable (R) (S : ShortComplex X.Modules) (hS : (S.map (Modules.toSheafAb X)).ShortExact)

/-- The cohomology of the first term, as an object of `ModuleCat R`. -/
noncomputable def lesA (n : ℕ) : ModuleCat R :=
  .of R (((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₁).H n)

/-- The cohomology of the second term, as an object of `ModuleCat R`. -/
noncomputable def lesB (n : ℕ) : ModuleCat R :=
  .of R (((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₂).H n)

/-- The cohomology of the third term, as an object of `ModuleCat R`. -/
noncomputable def lesC (n : ℕ) : ModuleCat R :=
  .of R (((SheafOfModules.toSheaf X.ringCatSheaf).obj S.X₃).H n)

/-- The first map of the long exact sequence in each degree. -/
noncomputable def lesF (n : ℕ) : lesA R S n ⟶ lesB R S n := ModuleCat.ofHom (HMapₗ (R := R) S.f n)

/-- The second map of the long exact sequence in each degree. -/
noncomputable def lesG (n : ℕ) : lesB R S n ⟶ lesC R S n := ModuleCat.ofHom (HMapₗ (R := R) S.g n)

/-- The connecting map of the long exact sequence in each degree. -/
noncomputable def lesδ (n : ℕ) : lesC R S n ⟶ lesA R S (n + 1) :=
  ModuleCat.ofHom (δₗ (R := R) hS n (n + 1) rfl)

/--
The terms of the long exact sequence below degree `0`, with a shifted block parameter `s` so
that the period-three pattern is a structural recursion: `negTermAux s` lists
`Hˢ(X₂), Hˢ(X₃), Hˢ⁺¹(X₁), Hˢ⁺¹(X₂), …`.
-/
noncomputable def negTermAux (s : ℕ) : ℕ → ModuleCat R
  | 0 => lesB R S s
  | 1 => lesC R S s
  | 2 => lesA R S (s + 1)
  | (m + 3) => negTermAux (s + 1) m

/-- The maps of the long exact sequence, in the indexing of `negTermAux`. -/
noncomputable def dAux (s : ℕ) :
    (m : ℕ) → (negTermAux R S s m ⟶ negTermAux R S s (m + 1))
  | 0 => lesG R S s
  | 1 => lesδ R S hS s
  | 2 => lesF R S (s + 1)
  | (m + 3) => dAux (s + 1) m

include hS in
/-- Consecutive maps of the long exact sequence compose to zero. -/
lemma lesF_comp_lesG (n : ℕ) : lesF R S n ≫ lesG R S n = 0 := by
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
lemma lesG_comp_lesδ (n : ℕ) : lesG R S n ≫ lesδ R S hS n = 0 := by
  have hzero : (Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map S.g)).comp
      hS.extClass (zero_add 1) = 0 := hS.comp_extClass
  ext x
  refine (Ext.comp_assoc_of_second_deg_zero x (Ext.mk₀ _) hS.extClass rfl).trans ?_
  exact (congrArg (fun e => x.comp e rfl) hzero).trans (Ext.comp_zero x _ 1 (n + 1) rfl)

/-- Consecutive maps of the long exact sequence compose to zero. -/
lemma lesδ_comp_lesF (n : ℕ) : lesδ R S hS n ≫ lesF R S (n + 1) = 0 := by
  have hzero : hS.extClass.comp
      (Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map S.f)) (add_zero 1) = 0 :=
    hS.extClass_comp
  ext x
  refine (Ext.comp_assoc_of_third_deg_zero x hS.extClass _ rfl).trans ?_
  exact (congrArg (fun e => x.comp e rfl) hzero).trans (Ext.comp_zero x _ 1 (n + 1) rfl)

/-- Consecutive maps in the `dAux` indexing compose to zero. -/
lemma dAux_comp (s : ℕ) : ∀ m, dAux R S hS s m ≫ dAux R S hS s (m + 1) = 0
  | 0 => lesG_comp_lesδ R S hS s
  | 1 => lesδ_comp_lesF R S hS s
  | 2 => lesF_comp_lesG R S hS (s + 1)
  | (m + 3) => dAux_comp (s + 1) m

/-- The graded object underlying the spliced long exact sequence:
`Hⁿ(X₁), Hⁿ(X₂), Hⁿ(X₃)` are placed at positions `-3n, -(3n+1), -(3n+2)`, with the zero module
at positive positions. -/
noncomputable def lesX : ℤ → ModuleCat R
  | .ofNat 0 => lesA R S 0
  | .ofNat (_ + 1) => ModuleCat.of R PUnit
  | .negSucc m => negTermAux R S 0 m

/-- The differentials of the spliced long exact sequence. -/
noncomputable def lesD : (i j : ℤ) → (lesX R S i ⟶ lesX R S j)
  | .ofNat 0, .negSucc 0 => lesF R S 0
  | .negSucc m, .negSucc n =>
    if h : n = m + 1 then
      h ▸ (dAux R S hS 0 m : lesX R S (Int.negSucc m) ⟶ lesX R S (Int.negSucc (m + 1)))
    else 0
  | _, _ => 0

/-- The long exact sequence of cohomology of a short exact sequence of sheaves of modules,
spliced into a single `ℤ`-indexed chain complex. -/
noncomputable def lesComplex : ChainComplex (ModuleCat R) ℤ where
  X := lesX R S
  d := lesD R S hS
  shape i j hij := by
    cases i with
    | ofNat k =>
      cases k with
      | zero =>
        cases j with
        | ofNat l => rfl
        | negSucc n =>
          cases n with
          | zero =>
            refine absurd ?_ hij
            rw [ComplexShape.down_Rel]
            decide
          | succ n => rfl
      | succ k => cases j <;> rfl
    | negSucc m =>
      cases j with
      | ofNat l => rfl
      | negSucc n =>
        simp only [lesD]
        rw [dif_neg]
        intro h
        refine hij ?_
        rw [ComplexShape.down_Rel]
        omega
  d_comp_d' i j l hij hjl := by
    cases i with
    | ofNat k =>
      cases k with
      | zero =>
        cases j with
        | ofNat l' => exact zero_comp ..
        | negSucc n =>
          cases n with
          | zero =>
            cases l with
            | ofNat l' => exact comp_zero ..
            | negSucc p =>
              simp only [lesD]
              split_ifs with h
              · subst h
                exact lesF_comp_lesG R S hS 0
              · exact comp_zero ..
          | succ n => exact zero_comp ..
      | succ k => cases j <;> exact zero_comp ..
    | negSucc m =>
      cases j with
      | ofNat l' => exact zero_comp ..
      | negSucc n =>
        cases l with
        | ofNat l' => exact comp_zero ..
        | negSucc p =>
          simp only [lesD]
          split_ifs with h1 h2
          · subst h1; subst h2
            exact dAux_comp R S hS 0 m
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
    exact Sheaf.H.longSequence_exact₃ hS s (s + 1) rfl x₂ hx₂
  | 1 => by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    exact Sheaf.H.longSequence_exact₁ hS s (s + 1) rfl x₂ hx₂
  | 2 => by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    exact Sheaf.H.longSequence_exact₂ hS (s + 1) x₂ hx₂
  | (m + 3) => dAux_exact (s + 1) m

/-- The positive part of the spliced complex is zero. -/
lemma lesX_isZero_ofNat_succ (k : ℕ) : IsZero ((lesComplex R S hS).X (Int.ofNat (k + 1))) :=
  ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)

/-- The negative differentials of the spliced complex are the `dAux` maps. The `dite` in `lesD`
does not reduce definitionally for symbolic `m` (since `Nat.decEq m m` is stuck), so this is
needed as a propositional rewrite. -/
lemma lesComplex_d_negSucc (m : ℕ) :
    (lesComplex R S hS).d (Int.negSucc m) (Int.negSucc (m + 1)) = dAux R S hS 0 m := by
  show lesD R S hS (Int.negSucc m) (Int.negSucc (m + 1)) = dAux R S hS 0 m
  simp only [lesD, ↓reduceDIte]

/-- The spliced long exact sequence is exact everywhere. The interior windows and the seam at
degrees `0` and `-1` are the exactness of the long exact sequence; exactness at degree `0` is the
injectivity of `H⁰(f)` (which holds because `f` is a monomorphism); positive degrees are zero. -/
lemma lesComplex_exactAt (i : ℤ) : (lesComplex R S hS).ExactAt i := by
  rcases i with k | m
  · cases k with
    | zero =>
      -- the window `0 ⟶ H⁰(X₁) ⟶ H⁰(X₂)`: exactness is the injectivity of `H⁰(f)`.
      show (lesComplex R S hS).ExactAt (0 : ℤ)
      rw [HomologicalComplex.exactAt_iff'
        (lesComplex R S hS) (1 : ℤ) (0 : ℤ) (-1 : ℤ)
        ((ComplexShape.down ℤ).prev_eq' (ComplexShape.down_mk (1 : ℤ) (0 : ℤ) (by omega)))
        ((ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk (0 : ℤ) (-1 : ℤ) (by omega))),
        ShortComplex.moduleCat_exact_iff]
      intro x₂ hx₂
      refine ⟨0, ?_⟩
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
    | succ k =>
      -- the complex vanishes in positive degrees
      exact HomologicalComplex.ExactAt.of_isZero (lesX_isZero_ofNat_succ R S hS k)
  · cases m with
    | zero =>
      -- the seam `H⁰(X₁) ⟶ H⁰(X₂) ⟶ H⁰(X₃)`
      show (lesComplex R S hS).ExactAt (-1 : ℤ)
      rw [HomologicalComplex.exactAt_iff'
        (lesComplex R S hS) (0 : ℤ) (-1 : ℤ) (-2 : ℤ)
        ((ComplexShape.down ℤ).prev_eq' (ComplexShape.down_mk (0 : ℤ) (-1 : ℤ) (by omega)))
        ((ComplexShape.down ℤ).next_eq' (ComplexShape.down_mk (-1 : ℤ) (-2 : ℤ) (by omega))),
        ShortComplex.moduleCat_exact_iff]
      intro x₂ hx₂
      rw [show (HomologicalComplex.sc' (lesComplex R S hS) (0 : ℤ) (-1 : ℤ) (-2 : ℤ)).g =
        dAux R S hS 0 0 from lesComplex_d_negSucc R S hS 0] at hx₂
      have hx₂' : Sheaf.H.map ((S.map (Modules.toSheafAb X)).g) 0 x₂ = 0 := hx₂
      obtain ⟨x₁, hx₁⟩ := Sheaf.H.longSequence_exact₂ hS 0 x₂ hx₂'
      exact ⟨x₁, hx₁⟩
    | succ m =>
      -- the interior windows are exactly the `dAux` windows
      rw [HomologicalComplex.exactAt_iff'
        (lesComplex R S hS) (Int.negSucc m) (Int.negSucc (m + 1)) (Int.negSucc (m + 2))
        ((ComplexShape.down ℤ).prev_eq'
          (ComplexShape.down_mk (Int.negSucc m) (Int.negSucc (m + 1)) (by omega)))
        ((ComplexShape.down ℤ).next_eq'
          (ComplexShape.down_mk (Int.negSucc (m + 1)) (Int.negSucc (m + 2)) (by omega))),
        ShortComplex.moduleCat_exact_iff]
      intro x₂ hx₂
      rw [show (HomologicalComplex.sc' (lesComplex R S hS) (Int.negSucc m) (Int.negSucc (m + 1))
        (Int.negSucc (m + 2))).g = dAux R S hS 0 (m + 1) from
        lesComplex_d_negSucc R S hS (m + 1)] at hx₂
      obtain ⟨x₁, hx₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp (dAux_exact R S hS 0 m) x₂ hx₂
      refine ⟨x₁, ?_⟩
      rw [show (HomologicalComplex.sc' (lesComplex R S hS) (Int.negSucc m) (Int.negSucc (m + 1))
        (Int.negSucc (m + 2))).f = dAux R S hS 0 m from lesComplex_d_negSucc R S hS m]
      exact hx₁

/-- The homology of the spliced long exact sequence vanishes. -/
lemma lesComplex_homology_isZero (i : ℤ) : IsZero ((lesComplex R S hS).homology i) :=
  (lesComplex_exactAt R S hS i).isZero_homology

/-- Structural value of `negTermAux` on multiples of `3`: `Hˢ⁺ᵗ(X₂)`. -/
lemma negTermAux_three_mul (s t : ℕ) : negTermAux R S s (3 * t) = lesB R S (s + t) := by
  induction t generalizing s with
  | zero => simp [negTermAux]
  | succ t ih =>
    rw [show 3 * (t + 1) = 3 * t + 3 from by ring]
    show negTermAux R S (s + 1) (3 * t) = _
    rw [ih (s + 1), show s + 1 + t = s + (t + 1) from by omega]

/-- Structural value of `negTermAux` on `3t+1`: `Hˢ⁺ᵗ(X₃)`. -/
lemma negTermAux_three_mul_add_one (s t : ℕ) :
    negTermAux R S s (3 * t + 1) = lesC R S (s + t) := by
  induction t generalizing s with
  | zero => simp [negTermAux]
  | succ t ih =>
    rw [show 3 * (t + 1) + 1 = (3 * t + 1) + 3 from by ring]
    show negTermAux R S (s + 1) (3 * t + 1) = _
    rw [ih (s + 1), show s + 1 + t = s + (t + 1) from by omega]

/-- Structural value of `negTermAux` on `3t+2`: `Hˢ⁺ᵗ⁺¹(X₁)`. -/
lemma negTermAux_three_mul_add_two (s t : ℕ) :
    negTermAux R S s (3 * t + 2) = lesA R S (s + t + 1) := by
  induction t generalizing s with
  | zero => simp [negTermAux]
  | succ t ih =>
    rw [show 3 * (t + 1) + 2 = (3 * t + 2) + 3 from by ring]
    show negTermAux R S (s + 1) (3 * t + 2) = _
    rw [ih (s + 1), show s + 1 + t + 1 = s + (t + 1) + 1 from by omega]

/-- `Hⁿ(X₁)` sits at position `-3n` of the spliced complex. -/
lemma lesX_neg_three_mul (n : ℕ) : lesX R S (-(3 * (n : ℤ))) = lesA R S n := by
  cases n with
  | zero => rfl
  | succ m =>
    have h : -(3 * ((m + 1 : ℕ) : ℤ)) = Int.negSucc (3 * m + 2) := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [h]
    show negTermAux R S 0 (3 * m + 2) = _
    rw [negTermAux_three_mul_add_two, Nat.zero_add]

/-- `Hⁿ(X₂)` sits at position `-(3n+1)` of the spliced complex. -/
lemma lesX_neg_three_mul_add_one (n : ℕ) :
    lesX R S (-(3 * (n : ℤ) + 1)) = lesB R S n := by
  have h : -(3 * (n : ℤ) + 1) = Int.negSucc (3 * n) := by
    rw [Int.negSucc_eq]; push_cast; ring
  rw [h]
  show negTermAux R S 0 (3 * n) = _
  rw [negTermAux_three_mul, Nat.zero_add]

/-- `Hⁿ(X₃)` sits at position `-(3n+2)` of the spliced complex. -/
lemma lesX_neg_three_mul_add_two (n : ℕ) :
    lesX R S (-(3 * (n : ℤ) + 2)) = lesC R S n := by
  have h : -(3 * (n : ℤ) + 2) = Int.negSucc (3 * n + 1) := by
    rw [Int.negSucc_eq]; push_cast; ring
  rw [h]
  show negTermAux R S 0 (3 * n + 1) = _
  rw [negTermAux_three_mul_add_one, Nat.zero_add]

end Splice

section Field

open Finset

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
  (S : ShortComplex X.Modules)

/-- `dim_k Hⁿ(X₁)`, accessed through the spliced complex object `lesA` (a `ModuleCat`, so its
`k`-module structure is structural and finrank is well-behaved). -/
noncomputable def dimA (n : ℕ) : ℕ :=
  Module.finrank k (lesA (CommRingCat.of k) S n)

/-- `dim_k Hⁿ(X₂)`. -/
noncomputable def dimB (n : ℕ) : ℕ :=
  Module.finrank k (lesB (CommRingCat.of k) S n)

/-- `dim_k Hⁿ(X₃)`. -/
noncomputable def dimC (n : ℕ) : ℕ :=
  Module.finrank k (lesC (CommRingCat.of k) S n)

/-- `χ(X₁) = ∑ₙ (-1)ⁿ dim_k Hⁿ(X₁)`. -/
noncomputable def eulerCharA : ℤ := ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (dimA k S n : ℤ)
/-- `χ(X₂) = ∑ₙ (-1)ⁿ dim_k Hⁿ(X₂)`. -/
noncomputable def eulerCharB : ℤ := ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (dimB k S n : ℤ)
/-- `χ(X₃) = ∑ₙ (-1)ⁿ dim_k Hⁿ(X₃)`. -/
noncomputable def eulerCharC : ℤ := ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (dimC k S n : ℤ)

variable (hS : (S.map (Modules.toSheafAb X)).ShortExact)

/-- Each term of the spliced complex is finite-dimensional, given finiteness of the cohomologies. -/
lemma negTermAux_finite
    (hf₁ : ∀ n, Module.Finite k (lesA (CommRingCat.of k) S n))
    (hf₂ : ∀ n, Module.Finite k (lesB (CommRingCat.of k) S n))
    (hf₃ : ∀ n, Module.Finite k (lesC (CommRingCat.of k) S n)) :
    ∀ (m s : ℕ), Module.Finite k (negTermAux (CommRingCat.of k) S s m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => exact fun s => hf₂ s
    | 1, _ => exact fun s => hf₃ s
    | 2, _ => exact fun s => hf₁ (s + 1)
    | (m + 3), ih => exact fun s => ih m (by omega) (s + 1)

/-- All objects of the spliced complex are finite-dimensional. -/
lemma lesComplex_X_finite
    (hf₁ : ∀ n, Module.Finite k (lesA (CommRingCat.of k) S n))
    (hf₂ : ∀ n, Module.Finite k (lesB (CommRingCat.of k) S n))
    (hf₃ : ∀ n, Module.Finite k (lesC (CommRingCat.of k) S n)) :
    ∀ (i : ℤ), Module.Finite k ((lesComplex (CommRingCat.of k) S hS).X i) := by
  rintro (k' | m)
  · cases k' with
    | zero => exact hf₁ 0
    | succ k' =>
      haveI : Subsingleton
          ↑((lesComplex (CommRingCat.of k) S hS).X (Int.ofNat (k' + 1))) :=
        ModuleCat.subsingleton_of_isZero (lesX_isZero_ofNat_succ (CommRingCat.of k) S hS k')
      haveI : Finite ↑((lesComplex (CommRingCat.of k) S hS).X (Int.ofNat (k' + 1))) :=
        Finite.of_subsingleton
      exact Module.Finite.of_finite
  · exact negTermAux_finite k S hf₁ hf₂ hf₃ m 0

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

lemma negOnePow_neg_three_mul (n : ℕ) :
    ((-(3 * (n : ℤ))).negOnePow : ℤ) = (-1 : ℤ) ^ n := by
  rw [Int.negOnePow_neg, show (3 * (n : ℤ)) = 2 * n + n from by ring, Int.negOnePow_add,
    Int.negOnePow_two_mul, one_mul]
  push_cast [Int.coe_negOnePow_natCast]
  ring

lemma negOnePow_neg_three_mul_add_one (n : ℕ) :
    ((-(3 * (n : ℤ) + 1)).negOnePow : ℤ) = -((-1 : ℤ) ^ n) := by
  rw [Int.negOnePow_neg, show (3 * (n : ℤ) + 1) = (2 * n + n) + 1 from by ring, Int.negOnePow_add,
    Int.negOnePow_add, Int.negOnePow_two_mul, one_mul, Int.negOnePow_one]
  push_cast [Int.coe_negOnePow_natCast]
  ring

lemma negOnePow_neg_three_mul_add_two (n : ℕ) :
    ((-(3 * (n : ℤ) + 2)).negOnePow : ℤ) = (-1 : ℤ) ^ n := by
  rw [Int.negOnePow_neg, show (3 * (n : ℤ) + 2) = (2 * n + n) + 2 * 1 from by ring,
    Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_two_mul, Int.negOnePow_two_mul, one_mul,
    mul_one]
  push_cast [Int.coe_negOnePow_natCast]
  ring

/-! ### finrank at the three position families -/

lemma finrank_X_A (n : ℕ) :
    Module.finrank k
      ((lesComplex (CommRingCat.of k) S hS).X (-(3 * (n : ℤ)))) = dimA k S n := by
  rw [show (lesComplex (CommRingCat.of k) S hS).X (-(3 * (n : ℤ))) = lesA (CommRingCat.of k) S n
    from lesX_neg_three_mul (CommRingCat.of k) S n]; rfl

lemma finrank_X_B (n : ℕ) :
    Module.finrank k
      ((lesComplex (CommRingCat.of k) S hS).X (-(3 * (n : ℤ) + 1))) = dimB k S n := by
  rw [show (lesComplex (CommRingCat.of k) S hS).X (-(3 * (n : ℤ) + 1)) = lesB (CommRingCat.of k) S n
    from lesX_neg_three_mul_add_one (CommRingCat.of k) S n]; rfl

lemma finrank_X_C (n : ℕ) :
    Module.finrank k
      ((lesComplex (CommRingCat.of k) S hS).X (-(3 * (n : ℤ) + 2))) = dimC k S n := by
  rw [show (lesComplex (CommRingCat.of k) S hS).X (-(3 * (n : ℤ) + 2)) = lesC (CommRingCat.of k) S n
    from lesX_neg_three_mul_add_two (CommRingCat.of k) S n]; rfl

/-! ### Vanishing outside a bounded window -/

variable {N : ℕ}

/-- If the cohomologies vanish above `N`, then so does the spliced stream beyond total index. -/
lemma negTermAux_isZero
    (hb₁ : ∀ n, N < n → IsZero (lesA (CommRingCat.of k) S n))
    (hb₂ : ∀ n, N < n → IsZero (lesB (CommRingCat.of k) S n))
    (hb₃ : ∀ n, N < n → IsZero (lesC (CommRingCat.of k) S n)) :
    ∀ (m s : ℕ), 3 * N + 2 ≤ 3 * s + m → IsZero (negTermAux (CommRingCat.of k) S s m) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, ih with
    | 0, _ => exact fun s hs => hb₂ s (by omega)
    | 1, _ => exact fun s hs => hb₃ s (by omega)
    | 2, _ => exact fun s hs => hb₁ (s + 1) (by omega)
    | (m + 3), ih => exact fun s hs => ih m (by omega) (s + 1) (by omega)

/-- Finite-sum form of an Euler characteristic finsum, given a vanishing bound. -/
lemma eulerChar_finsum_eq (d : ℕ → ℕ) (hd : ∀ n, N < n → d n = 0) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (d n : ℤ)) =
      ∑ n ∈ range (N + 1), (-1 : ℤ) ^ n * (d n : ℤ) := by
  rw [finsum_eq_finset_sum_of_support_subset]
  intro n hn
  simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hn
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hle
  exact hn.2 (by rw [hd n (by omega)]; simp)

include hS

/-- The `finrank`-support of the spliced complex is contained in the image of
`(n, p) ↦ -(3n+p)` over `range (N+1) ×ˢ range 3`. -/
lemma finrankSupport_subset
    (hb₁ : ∀ n, N < n → IsZero (lesA (CommRingCat.of k) S n))
    (hb₂ : ∀ n, N < n → IsZero (lesB (CommRingCat.of k) S n))
    (hb₃ : ∀ n, N < n → IsZero (lesC (CommRingCat.of k) S n)) :
    GradedObject.finrankSupport (lesComplex (CommRingCat.of k) S hS).X ⊆
      ↑(((range (N + 1)) ×ˢ (range 3)).image (fun q : ℕ × ℕ => -(3 * (q.1 : ℤ) + q.2))) := by
  rw [GradedObject.finrankSupport_subset_iff]
  intro i hi
  rcases i with j | m
  · -- `i = j ≥ 0`: `i = 0` is in the image (so `hi` is absurd); `i ≥ 1` gives a zero object.
    cases j with
    | zero =>
      refine absurd ?_ hi
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, mem_product, mem_range]
      exact ⟨(0, 0), ⟨by omega, by omega⟩, by simp⟩
    | succ j =>
      haveI := ModuleCat.subsingleton_of_isZero
        (lesX_isZero_ofNat_succ (CommRingCat.of k) S hS j)
      exact Module.finrank_zero_of_subsingleton
  · -- `i = -(m+1)`: if `m < 3N+2` then `i` is in the image (absurd), so `m ≥ 3N+2`, giving zero.
    have hm : 3 * N + 2 ≤ m := by
      by_contra hlt
      refine hi ?_
      have hdm := Nat.div_add_mod (m + 1) 3
      have hmod : (m + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, mem_product, mem_range]
      refine ⟨((m + 1) / 3, (m + 1) % 3), ⟨by omega, by omega⟩, ?_⟩
      rw [Int.negSucc_eq]
      push_cast
      omega
    haveI : Subsingleton ↑((lesComplex (CommRingCat.of k) S hS).X (Int.negSucc m)) :=
      ModuleCat.subsingleton_of_isZero
        (negTermAux_isZero k S hb₁ hb₂ hb₃ m 0 (by omega))
    exact Module.finrank_zero_of_subsingleton

/-- **The Euler characteristic is additive in short exact sequences.** Given a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` of sheaves of modules over a field `k`, with finite-dimensional cohomology
vanishing above some degree `N`, the Euler characteristics satisfy `χ(X₂) = χ(X₁) + χ(X₃)`.

The proof splices the long exact cohomology sequence into one bounded exact `ℤ`-complex of
`k`-vector spaces and applies the Euler–Poincaré formula. -/
theorem eulerChar_additive
    (hf₁ : ∀ n, Module.Finite k (lesA (CommRingCat.of k) S n))
    (hf₂ : ∀ n, Module.Finite k (lesB (CommRingCat.of k) S n))
    (hf₃ : ∀ n, Module.Finite k (lesC (CommRingCat.of k) S n))
    (hb₁ : ∀ n, N < n → IsZero (lesA (CommRingCat.of k) S n))
    (hb₂ : ∀ n, N < n → IsZero (lesB (CommRingCat.of k) S n))
    (hb₃ : ∀ n, N < n → IsZero (lesC (CommRingCat.of k) S n)) :
    eulerCharB k S = eulerCharA k S + eulerCharC k S := by
  haveI : ∀ i, Module.Finite k ((lesComplex (CommRingCat.of k) S hS).X i) :=
    lesComplex_X_finite k S hS hf₁ hf₂ hf₃
  -- The dimensions vanish above `N`.
  have hbA : ∀ n, N < n → dimA k S n = 0 := by
    intro n hn; haveI := ModuleCat.subsingleton_of_isZero (hb₁ n hn)
    exact Module.finrank_zero_of_subsingleton
  have hbB : ∀ n, N < n → dimB k S n = 0 := by
    intro n hn; haveI := ModuleCat.subsingleton_of_isZero (hb₂ n hn)
    exact Module.finrank_zero_of_subsingleton
  have hbC : ∀ n, N < n → dimC k S n = 0 := by
    intro n hn; haveI := ModuleCat.subsingleton_of_isZero (hb₃ n hn)
    exact Module.finrank_zero_of_subsingleton
  -- Euler–Poincaré: the alternating sum of dimensions equals the (vanishing) homology version.
  have hEP : (lesComplex (CommRingCat.of k) S hS).eulerChar = 0 := by
    rw [ChainComplex.eulerChar_eq_homologyEulerChar (lesComplex (CommRingCat.of k) S hS)
      (-(3 * (N : ℤ) + 2)) 0 (by omega) ?_ ?_, lesComplex_homologyEulerChar_zero]
    · rintro (j | m) hi
      · exact absurd hi (by simp only [Int.ofNat_eq_natCast]; omega)
      · exact negTermAux_isZero k S hb₁ hb₂ hb₃ m 0 (by rw [Int.negSucc_eq] at hi; omega)
    · rintro (j | m) hi
      · cases j with
        | zero => exact absurd hi (by decide)
        | succ j => exact lesX_isZero_ofNat_succ (CommRingCat.of k) S hS j
      · exact absurd hi (by simp only [Int.negSucc_eq]; omega)
  -- The bridge: the spliced Euler characteristic equals `χ(X₁) - χ(X₂) + χ(X₃)`.
  have heA := eulerChar_finsum_eq (dimA k S) hbA
  have heB := eulerChar_finsum_eq (dimB k S) hbB
  have heC := eulerChar_finsum_eq (dimC k S) hbC
  have key : (lesComplex (CommRingCat.of k) S hS).eulerChar =
      eulerCharA k S - eulerCharB k S + eulerCharC k S := by
    rw [HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset _ _
      (finrankSupport_subset k S hS hb₁ hb₂ hb₃),
      Finset.sum_image (by
        intro x hx y hy hxy
        have hx3 : x.2 < 3 := Finset.mem_range.mp (Finset.mem_product.mp hx).2
        have hy3 : y.2 < 3 := Finset.mem_range.mp (Finset.mem_product.mp hy).2
        have h : 3 * x.1 + x.2 = 3 * y.1 + y.2 := by
          have := neg_inj.mp hxy; push_cast at this; omega
        exact Prod.ext (by omega) (by omega)),
      Finset.sum_product]
    rw [eulerCharA, eulerCharB, eulerCharC, heA, heB, heC,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    simp only [ComplexShape.eulerCharSignsDownInt_χ]
    rw [show (-(3 * (n : ℤ) + ((0 : ℕ) : ℤ))) = -(3 * (n : ℤ)) from by push_cast; ring,
      show (-(3 * (n : ℤ) + ((1 : ℕ) : ℤ))) = -(3 * (n : ℤ) + 1) from by push_cast; ring,
      show (-(3 * (n : ℤ) + ((2 : ℕ) : ℤ))) = -(3 * (n : ℤ) + 2) from by push_cast; ring,
      finrank_X_A k S hS n, finrank_X_B k S hS n, finrank_X_C k S hS n,
      negOnePow_neg_three_mul n, negOnePow_neg_three_mul_add_one n,
      negOnePow_neg_three_mul_add_two n]
    ring
  -- Conclude.
  rw [key] at hEP
  linarith

end Field
