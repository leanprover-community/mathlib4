/-
Copyright (c) 2026 Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan, Yi Yuan, Yongle Hu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# Definition of Koszul complex
-/

@[expose] public section

universe u v

open CategoryTheory Category MonoidalCategory Limits Module ExteriorAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (φ : M →ₗ[R] R)

set_option backward.isDefEq.respectTransparency false in
noncomputable def koszulComplex_aux (n : ℕ) : ⋀[R]^(n + 1) M →ₗ[R] ⋀[R]^n M :=
  exteriorPower.alternatingMapLinearEquiv {
    toFun x := ∑ i : Fin (n + 1),
      ((-1) ^ i.1 * (φ (x i))) • exteriorPower.ιMulti R n (x ∘ i.succAbove)
    map_update_add' := by
      classical
      intro _ m p x y
      have hremove (v : Fin (n + 1) → M) (k : Fin (n + 1)) : v ∘ k.succAbove = k.removeNth v := rfl
      let term (v : Fin (n + 1) → M) (k : Fin (n + 1)) :=
        ((-1) ^ (k : ℕ) * φ (v k)) • exteriorPower.ιMulti R n (v ∘ k.succAbove)
      have hcalc :
          ∑ k, term (Function.update m p (x + y)) k =
            ∑ k, term (Function.update m p x) k + ∑ k, term (Function.update m p y) k := by
        calc
          ∑ k, term (Function.update m p (x + y)) k =
              ∑ k, (term (Function.update m p x) k + term (Function.update m p y) k) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                by_cases hk' : k = p
                · subst hk'
                  have hupdate (z : M) : k.removeNth (Function.update m k z) = k.removeNth m := by
                    ext i
                    simp [Fin.removeNth, Function.update, Fin.succAbove_ne]
                  simp [term, hremove, LinearMap.map_add, mul_add, add_smul, hupdate (x + y),
                    hupdate x, hupdate y]
                · rcases Fin.exists_succAbove_eq (x := p) (y := k) (by
                    simpa [ne_comm] using hk') with ⟨j, rfl⟩
                  have hupdate (z : M) :
                      k.removeNth (Function.update m (k.succAbove j) z) =
                        Function.update (k.removeNth m) j z := by
                    ext i
                    by_cases hi : i = j
                    · subst hi; simp [Fin.removeNth, Function.update]
                    · have hne : k.succAbove i ≠ k.succAbove j := by
                        exact fun h => hi (Fin.succAbove_right_inj.mp h)
                      simp [Fin.removeNth, Function.update, hi, hne]
                  simp [term, hremove, hupdate (x + y), hupdate x, hupdate y, smul_add]
          _ = ∑ k, term (Function.update m p x) k + ∑ k, term (Function.update m p y) k := by
              simp [Finset.sum_add_distrib]
      simpa [term] using hcalc
    map_update_smul' := by
      classical
      intro _ m p c x
      have hremove (v : Fin (n + 1) → M) (k : Fin (n + 1)) : v ∘ k.succAbove = k.removeNth v := rfl
      let term (v : Fin (n + 1) → M) (k : Fin (n + 1)) :=
        ((-1) ^ (k : ℕ) * φ (v k)) • exteriorPower.ιMulti R n (v ∘ k.succAbove)
      have hcalc :
          ∑ k, term (Function.update m p (c • x)) k =
            ∑ k, c • term (Function.update m p x) k := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        by_cases hk' : k = p
        · subst hk'
          have hupdate (z : M) : k.removeNth (Function.update m k z) = k.removeNth m := by
            ext i
            simp [Fin.removeNth, Function.update, Fin.succAbove_ne]
          simp [term, hremove, smul_smul, mul_left_comm, hupdate (c • x), hupdate x]
        · rcases Fin.exists_succAbove_eq (x := p) (y := k) (by
            simpa [ne_comm] using hk') with ⟨j, rfl⟩
          have hupdate (z : M) :
              k.removeNth (Function.update m (k.succAbove j) z) =
                Function.update (k.removeNth m) j z := by
            ext i
            by_cases hi : i = j
            · subst hi; simp [Fin.removeNth, Function.update]
            · have hne : k.succAbove i ≠ k.succAbove j := by
                exact fun h => hi (Fin.succAbove_right_inj.mp h)
              simp [Fin.removeNth, Function.update, hi, hne]
          simp [term, hremove, smul_smul, mul_comm, hupdate (c • x),
            hupdate x]
      have hcalc' :
          ∑ k, term (Function.update m p (c • x)) k =
            c • ∑ k, term (Function.update m p x) k := by
        calc
          ∑ k, term (Function.update m p (c • x)) k =
              ∑ k, c • term (Function.update m p x) k := hcalc
          _ = c • ∑ k, term (Function.update m p x) k := by
              simpa using (Finset.smul_sum (r := c) (f := fun k ↦ term (Function.update m p x) k)
                (s := Finset.univ)).symm
      simpa [term] using hcalc'
    map_eq_zero_of_eq' := by
      sorry
      -- classical
      -- intro v i j hvij hij
      -- have hremove (v : Fin (n + 1) → M) (k : Fin (n + 1)) : v ∘ k.succAbove = k.removeNth v := rfl
      -- let term (v : Fin (n + 1) → M) (k : Fin (n + 1)) :=
      --   ((-1) ^ (k : ℕ) * φ (v k)) • exteriorPower.ιMulti R n (v ∘ k.succAbove)
      -- have hsum : ∑ k, term v k = term v i + term v j := by
      --   refine Fintype.sum_eq_add i j hij ?_
      --   intro k hk
      --   rcases hk with ⟨hki, hkj⟩
      --   rcases Fin.exists_succAbove_eq (x := i) (y := k) hki.symm with ⟨i', hi'⟩
      --   rcases Fin.exists_succAbove_eq (x := j) (y := k) hkj.symm with ⟨j', hj'⟩
      --   have hij' : i' ≠ j' := by
      --     intro h
      --     apply hij
      --     have : k.succAbove i' = k.succAbove j' := by simpa [h]
      --     simpa [hi', hj'] using this
      --   have hzero : exteriorPower.ιMulti R n (v ∘ k.succAbove) = 0 := by
      --     refine (exteriorPower.ιMulti R n).map_eq_zero_of_eq (v := v ∘ k.succAbove) ?_ hij'
      --     simpa [Function.comp, hi', hj', hvij]
      --   simp [term, hzero]
      -- have hneg :
      --     (-1 : R) ^ (i : ℕ) • exteriorPower.ιMulti R n (i.removeNth v) +
      --         (-1 : R) ^ (j : ℕ) • exteriorPower.ιMulti R n (j.removeNth v) = 0 := by
      --   rcases Fin.exists_succAbove_eq hij with ⟨i', rfl⟩
      --   obtain ⟨m, rfl⟩ : ∃ m, m + 1 = n := by simp [i'.pos]
      --   rw [← (i'.predAbove j).insertNth_self_removeNth (Fin.removeNth _ _),
      --     ← Fin.removeNth_removeNth_eq_swap, Fin.removeNth, Fin.succAbove_succAbove_predAbove,
      --     AlternatingMap.map_insertNth, ← AlternatingMap.neg_one_pow_smul_map_insertNth,
      --     Fin.insertNth_removeNth, Function.update_eq_self_iff.2, smul_smul, ← pow_add,
      --     Fin.neg_one_pow_succAbove_add_predAbove, neg_smul, pow_add, mul_smul,
      --     smul_smul (_ ^ i'.val), ← sq, ← pow_mul, pow_mul', neg_one_pow_two, one_pow, one_smul,
      --     neg_add_cancel]
      --   exact hvij.symm
      -- have hcancel : term v i + term v j = 0 := by
      --   calc
      --     term v i + term v j =
      --         ((-1) ^ (i : ℕ) * φ (v j)) • exteriorPower.ιMulti R n (i.removeNth v) +
      --           ((-1) ^ (j : ℕ) * φ (v j)) • exteriorPower.ιMulti R n (j.removeNth v) := by
      --             simp [term, hremove, hvij, mul_comm, mul_left_comm, mul_assoc]
      --     _ =
      --         φ (v j) • ((-1 : R) ^ (i : ℕ) • exteriorPower.ιMulti R n (i.removeNth v)) +
      --           φ (v j) • ((-1 : R) ^ (j : ℕ) • exteriorPower.ιMulti R n (j.removeNth v)) := by
      --             have h1 :
      --                 ((-1 : R) ^ (i : ℕ) * φ (v j)) • exteriorPower.ιMulti R n (i.removeNth v) =
      --                   φ (v j) •
      --                     ((-1 : R) ^ (i : ℕ) • exteriorPower.ιMulti R n (i.removeNth v)) := by
      --               calc
      --                 ((-1 : R) ^ (i : ℕ) * φ (v j)) • exteriorPower.ιMulti R n (i.removeNth v) =
      --                     (φ (v j) * (-1 : R) ^ (i : ℕ)) •
      --                       exteriorPower.ιMulti R n (i.removeNth v) := by
      --                         simp [mul_comm, mul_left_comm, mul_assoc]
      --                 _ = φ (v j) •
      --                     ((-1 : R) ^ (i : ℕ) • exteriorPower.ιMulti R n (i.removeNth v)) := by
      --                       simpa using
      --                         (mul_smul (φ (v j)) ((-1 : R) ^ (i : ℕ))
      --                           (exteriorPower.ιMulti R n (i.removeNth v)))
      --             have h2 :
      --                 ((-1 : R) ^ (j : ℕ) * φ (v j)) • exteriorPower.ιMulti R n (j.removeNth v) =
      --                   φ (v j) •
      --                     ((-1 : R) ^ (j : ℕ) • exteriorPower.ιMulti R n (j.removeNth v)) := by
      --               calc
      --                 ((-1 : R) ^ (j : ℕ) * φ (v j)) • exteriorPower.ιMulti R n (j.removeNth v) =
      --                     (φ (v j) * (-1 : R) ^ (j : ℕ)) •
      --                       exteriorPower.ιMulti R n (j.removeNth v) := by
      --                         simp [mul_comm, mul_left_comm, mul_assoc]
      --                 _ = φ (v j) •
      --                     ((-1 : R) ^ (j : ℕ) • exteriorPower.ιMulti R n (j.removeNth v)) := by
      --                       simpa using
      --                         (mul_smul (φ (v j)) ((-1 : R) ^ (j : ℕ))
      --                           (exteriorPower.ιMulti R n (j.removeNth v)))
      --             rw [h1, h2]
      --     _ = φ (v j) •
      --         ((-1 : R) ^ (i : ℕ) • exteriorPower.ιMulti R n (i.removeNth v) +
      --           (-1 : R) ^ (j : ℕ) • exteriorPower.ιMulti R n (j.removeNth v)) := by
      --             simp [smul_add]
      --     _ = 0 := by simpa [hneg]
      -- calc
      --   ∑ k, term v k = term v i + term v j := hsum
      --   _ = 0 := hcancel
  }

lemma koszulComplex_aux_comp_eq_zero (n : ℕ) :
    koszulComplex_aux φ n ∘ₗ koszulComplex_aux φ (n + 1) = 0 := by
  -- ext x
  -- simp [koszulComplex_aux]
  -- classical
  -- have hremove (v : Fin (n + 2) → M) (k : Fin (n + 2)) : v ∘ k.succAbove = k.removeNth v := rfl
  -- have hremove' (v : Fin (n + 1) → M) (k : Fin (n + 1)) : v ∘ k.succAbove = k.removeNth v := rfl
  -- -- rewrite inner compositions using `removeNth`
  -- simp [hremove, hremove']
  -- let term : Fin (n + 2) → Fin (n + 1) → ⋀[R]^n M := fun i j =>
  --   ((-1) ^ (i : ℕ) * φ (x i)) •
  --     ((-1) ^ (j : ℕ) * φ (x (i.succAbove j))) •
  --       exteriorPower.ιMulti R n (j.removeNth (i.removeNth x))
  -- let f : Fin (n + 2) × Fin (n + 1) → ⋀[R]^n M := fun p => term p.1 p.2
  -- let g : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) :=
  --   fun p => (p.1.succAbove p.2, p.2.predAbove p.1)
  -- have hpair : ∀ p, f p + f (g p) = 0 := by
  --   intro p
  --   rcases p with ⟨i, j⟩
  --   have hswap :
  --       (j.predAbove i).removeNth ((i.succAbove j).removeNth x) = j.removeNth (i.removeNth x) := by
  --     simpa using (Fin.removeNth_removeNth_eq_swap (m := x) (i := j) (j := i)).symm
  --   have hsign :
  --       (-1 : R) ^ (i.succAbove j + j.predAbove i : ℕ) =
  --         -((-1 : R) ^ (i : ℕ) * (-1 : R) ^ (j : ℕ)) := by
  --     simpa [pow_add] using
  --       (Fin.neg_one_pow_succAbove_add_predAbove (R := R) (i := i) (j := j))
  --   have hsign' :
  --       (-1 : R) ^ (i.succAbove j : ℕ) * (-1 : R) ^ (j.predAbove i : ℕ) =
  --         -((-1 : R) ^ (i : ℕ) * (-1 : R) ^ (j : ℕ)) := by
  --     simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hsign
  --   let w : ⋀[R]^n M := exteriorPower.ιMulti R n (j.removeNth (i.removeNth x))
  --   have hw : w = exteriorPower.ιMulti R n (j.removeNth (i.removeNth x)) := rfl
  --   calc
  --     f ⟨i, j⟩ + f (g ⟨i, j⟩) =
  --         ( ((-1 : R) ^ (i : ℕ) * φ (x i) * ((-1 : R) ^ (j : ℕ) * φ (x (i.succAbove j))))
  --           + ((-1 : R) ^ (i.succAbove j : ℕ) * φ (x (i.succAbove j)) *
  --               ((-1 : R) ^ (j.predAbove i : ℕ) * φ (x i))) )
  --           • w := by
  --             simp [f, term, g, hswap, hw, Fin.succAbove_succAbove_predAbove, smul_smul,
  --               mul_comm, mul_left_comm, mul_assoc, add_smul]
  --     _ = 0 := by
  --       -- cancel by pairing the two terms using the sign lemma
  --       have hscalar :
  --           (-1 : R) ^ (i : ℕ) * φ (x i) * ((-1 : R) ^ (j : ℕ) * φ (x (i.succAbove j))) +
  --               (-1 : R) ^ (i.succAbove j : ℕ) * φ (x (i.succAbove j)) *
  --                 ((-1 : R) ^ (j.predAbove i : ℕ) * φ (x i)) = 0 := by
  --         calc
  --           _ = ((-1 : R) ^ (i : ℕ) * (-1 : R) ^ (j : ℕ) *
  --                 (φ (x i) * φ (x (i.succAbove j)))) +
  --               ((-1 : R) ^ (i.succAbove j : ℕ) * (-1 : R) ^ (j.predAbove i : ℕ) *
  --                 (φ (x i) * φ (x (i.succAbove j)))) := by
  --                   simp [mul_comm, mul_left_comm, mul_assoc]
  --           _ = ((-1 : R) ^ (i : ℕ) * (-1 : R) ^ (j : ℕ) *
  --                 (φ (x i) * φ (x (i.succAbove j)))) +
  --               (-((-1 : R) ^ (i : ℕ) * (-1 : R) ^ (j : ℕ)) *
  --                 (φ (x i) * φ (x (i.succAbove j)))) := by
  --                   simp [hsign', mul_comm, mul_left_comm, mul_assoc]
  --           _ = 0 := by ring
  --       simpa [hscalar]
  -- have hne : ∀ p, g p ≠ p := by
  --   intro p hp
  --   have : p.1.succAbove p.2 = p.1 := by simpa [g] using congrArg Prod.fst hp
  --   exact (Fin.succAbove_ne _ _) this
  -- have hinvol : ∀ p, g (g p) = p := by
  --   intro p
  --   rcases p with ⟨i, j⟩
  --   simp [g, Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
  -- have hsum : ∑ p : Fin (n + 2) × Fin (n + 1), f p = 0 := by
  --   simpa using
  --     (Finset.sum_ninvolution (s := Finset.univ) (f := f) (g := g) hpair
  --       (fun p _ => hne p) (by intro p; simp) hinvol)
  -- have hsum' :
  --     ∑ i, ∑ j, term i j = ∑ p : Fin (n + 2) × Fin (n + 1), f p := by
  --   simpa [f] using (Fintype.sum_prod_type' (f := term)).symm
  -- have hmain : ∑ i, ∑ j, term i j = 0 := by
  --   calc
  --     ∑ i, ∑ j, term i j = ∑ p : Fin (n + 2) × Fin (n + 1), f p := hsum'
  --     _ = 0 := hsum
  -- simpa [term, Finset.smul_sum] using hmain
  sorry

set_option backward.isDefEq.respectTransparency false in
noncomputable def koszulComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of
    (ModuleCat.of R M).exteriorPower
    (fun n ↦ ModuleCat.ofHom (koszulComplex_aux φ n))
    (fun n ↦ by simp [← ModuleCat.ofHom_comp, koszulComplex_aux_comp_eq_zero]; rfl)

section DifferentialGradedAlgebra

end DifferentialGradedAlgebra

namespace koszulComplex

variable {N : Type v} [AddCommGroup N] [Module R N]

noncomputable def ofList (l : List R) := koszulComplex (Fintype.linearCombination R l.get)

section functoriality

noncomputable def map (f : M →ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ⟶ koszulComplex φ' := sorry

noncomputable def isoOfEquiv (f : M ≃ₗ[R] N) (φ' : N →ₗ[R] R) (h : φ' ∘ₗ f = φ) :
    koszulComplex φ ≅ koszulComplex φ' := sorry

end functoriality

section specialX

noncomputable def XZeroLinearEquivRing : (koszulComplex φ).X 0 ≃ₗ[R] R :=
  exteriorPower.zeroEquiv R M

set_option backward.isDefEq.respectTransparency false in
lemma X_isZero_of_card_generators_le {ι : Type*} [Finite ι] (g : ι → M)
    (hg : Submodule.span R (Set.range g) = ⊤) (i : ℕ) (hi : Nat.card ι < i) :
    IsZero ((koszulComplex φ).X i) := by
  have hIsZero : IsZero (ModuleCat.of R (⋀[R]^i M)) := by
    apply ModuleCat.isZero_of_iff_subsingleton.mpr
    exact subsingleton_of_card_generators_le R M g hg i hi
  simpa [koszulComplex, ModuleCat.exteriorPower] using hIsZero

lemma ofList_X_isZero_of_length_le (l : List R) (i : ℕ) (hi : l.length < i) :
    IsZero ((ofList l).X i) := X_isZero_of_card_generators_le _
  (Pi.basisFun R (Fin l.length)) (Pi.basisFun R (Fin l.length)).span_eq i
  (by simpa [Nat.card_eq_fintype_card] using hi)

end specialX

section H0

noncomputable def zeroHomologyLinearEquiv (l : List R) :
    (ofList l).homology 0 ≃ₗ[R] R ⧸ Ideal.ofList l := sorry

end H0

section regular

open RingTheory.Sequence

lemma exactAt_of_isRegular (rs : List R) (reg : IsRegular R rs)
    (i : ℕ) (lt : i ≠ 0) : (ofList rs).ExactAt i := by
  sorry

end regular

section change_generators

lemma nonempty_linearEquiv_of_minimal_generators' (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (l l' : List R) (hl : Ideal.ofList l = I) (hl' : Ideal.ofList l' = I)
    (hl_min : l.length = I.spanFinrank) (hl'_min : l'.length = I.spanFinrank) :
  ∃ e : (Fin l.length → R) ≃ₗ[R] (Fin l'.length → R), e l.get = l'.get := sorry

theorem nonempty_iso_of_minimal_generators [IsLocalRing R]
    {I : Ideal R} {l l' : List R}
    (hl : Ideal.ofList l = I) (hl' : Ideal.ofList l' = I)
    (hl_min : l.length = I.spanFinrank) (hl'_min : l'.length = I.spanFinrank) :
    Nonempty <| ofList l ≅ ofList l' := by
  have hI : I ≤ Ring.jacobson R := sorry
  obtain ⟨e, h⟩ := nonempty_linearEquiv_of_minimal_generators' I hI l l' hl hl' hl_min hl'_min
  have h' : Fintype.linearCombination R l'.get ∘ₗ e = Fintype.linearCombination R l.get := by
    sorry
  exact ⟨isoOfEquiv _ e _ h'⟩

theorem nonempty_iso_of_minimal_generators'
    [IsNoetherianRing R] [IsLocalRing R] {I : Ideal R} {l : List R}
    (eq : Ideal.ofList l = I) (min : l.length = I.spanFinrank) :
    Nonempty <| ofList I.finite_generators_of_isNoetherian.toFinset.toList ≅ ofList l := by
  refine nonempty_iso_of_minimal_generators ?_ eq ?_ min
  · simp only [Ideal.ofList, Finset.mem_toList, Set.Finite.mem_toFinset, Set.setOf_mem_eq]
    exact I.span_generators
  · simp only [Finset.length_toList, ← Set.ncard_eq_toFinset_card _ _]
    exact Submodule.FG.generators_ncard Submodule.FG.of_finite

end change_generators

section basechange

variable (S : Type (max u v)) [CommRing S] (f : R →+* S)

instance (T : Type v) [CommRing T] (g : R →+* T) :
    (ModuleCat.extendScalars.{u, v, u} g).Additive where
  map_add {X Y a b} := by
    simp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
      ModuleCat.hom_add, LinearMap.baseChange_add]
    rfl

open TensorProduct in
noncomputable def baseChange_iso (l : List R) (l' : List S) (eqmap : l.map f = l') :
    ofList l' ≅ ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj (ofList l) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ LinearEquiv.toModuleIso ?_) (fun i j ↦ ?_)
  · sorry
  · sorry

end basechange

end koszulComplex
