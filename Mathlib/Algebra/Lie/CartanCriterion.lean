import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Killing

namespace LieSubalgebra

variable {k L V : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

#count_heartbeats in
open Module LieAlgebra LieModule in
lemma exists_weight_eq_mul_root [FiniteDimensional k V] [FiniteDimensional k L]
    (H : LieSubalgebra k L) [H.IsCartanSubalgebra] [IsTriangularizable k H V]
    (χ : Weight k H V) (α : Weight k H L) :
    ∃ r : ℚ, ∀ (e : rootSpace H α) (f : rootSpace H (-⇑α)) (h : H),
      ⁅(e : L), (f : L)⁆ = h → χ h = r * α h := by
  classical
  let ι := {n : ℤ // genWeightSpace V (χ + n • α : H → k) ≠ ⊥ ∧ ((α : H → k) = 0 → n = 0)}
  let w (n : ι) : Weight k H V := ⟨χ + n.1 • α, n.2.1⟩ 
  let W (n : ι) : LieSubmodule k H V := genWeightSpace V (w n)
  let U : Submodule k V := ⨆ i, ((fun i ↦ ↑(genWeightSpace V ⇑i)) ∘ w) i
  have hw : w.Injective := by
    intro m n hmn
    ext
    by_cases hα : (α : H → k) = 0
    · rw [m.2.2 hα, n.2.2 hα]
    obtain ⟨x, hx⟩ : ∃ x, α x ≠ 0 := by
      contrapose! hα
      ext
      apply hα
    rw [Weight.ext_iff] at hmn
    specialize hmn x
    simpa [w, hx] using hmn
  have : Fintype ι := Fintype.ofInjective w hw
  let N : ℤ := ∑ n : ι, finrank k (W n) * n.1
  let D : ℕ := ∑ n : ι, finrank k (W n)
  use - N / D
  intro e f h hh
  suffices D * χ h + N * α h = 0 by
    rw [mul_comm] at this
    have hD : (D : k) ≠ 0 := by
      simp only [ne_eq, Weight.coe_weight_mk, Nat.cast_eq_zero, Finset.sum_eq_zero_iff,
        Finset.mem_univ, forall_const, not_forall, Subtype.exists, zsmul_eq_mul,
        Weight.coe_eq_zero_iff, exists_prop, D, ι, w, W]
      use 0
      rw [← ne_eq, ← ne_eq, ← Nat.pos_iff_ne_zero, finrank_pos_iff,
        LieSubmodule.nontrivial_iff_ne_bot]
      simp only [Int.cast_zero, implies_true, and_true, zero_mul, add_zero, zero_smul, and_self]
      exact χ.2
    field_simp [eq_neg_iff_add_eq_zero, this]
  have aux := (LieSubmodule.iSupIndep_iff_toSubmodule.mp <| iSupIndep_genWeightSpace' k H V).comp hw
  have Hh' (i : ι) : Set.MapsTo (toEnd k H V h)
    ↑(genWeightSpace V (w i)) ↑(genWeightSpace V (w i)) := fun v hv ↦ LieSubmodule.lie_mem _ hv
  have Hh : Set.MapsTo (toEnd k L V h) U U := by
    simpa using LinearMap.mapsTo_biSup_of_mapsTo (.univ : Set ι) Hh'
  have key : (((toEnd k L V h).restrict Hh).trace k U) =
      ∑ n : ι, (((toEnd k H (W n) h)).trace k (W n)) :=
    LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup
      Finset.univ (aux.comp Subtype.coe_injective) (f := toEnd k L V h) Hh' U (by simp [U]) Hh
  suffices (((toEnd k L V h).restrict Hh).trace k U) = 0 by
    simp only [trace_toEnd_genWeightSpace, this, W] at key
    dsimp only [Weight.coe_weight_mk, Pi.add_apply, Pi.smul_apply, w] at key
    simp only [zsmul_eq_mul, smul_add, nsmul_eq_mul, Finset.sum_add_distrib,
      ← mul_assoc, ← Finset.sum_mul] at key
    simpa [this, D, N, w] using key.symm
  clear key
  have aux' (m : ℤ) (e : rootSpace H (m • ⇑α)) : Set.MapsTo (toEnd k L V e) U U := by
    show U ≤ U.comap (toEnd k L V e)
    simp only [Function.comp_apply, iSup_pos, iSup_le_iff, U]
    intro n v hv
    simp only [Submodule.mem_comap, toEnd_apply_apply]
    by_cases hev : ⁅(e:L), v⁆ = 0
    · rw [hev]
      exact Submodule.zero_mem _
    have hev_mem : ⁅(e:L), v⁆ ∈ genWeightSpace V (χ + (n.1 + m) • α : H → k) := by
      have := LieAlgebra.mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace k L H V _ (w n) e.2 hv
      suffices ⇑χ + (↑n + m) • ⇑α = m • ⇑α + ⇑(w n) by rwa [this]
      simp only [zsmul_eq_mul, Int.cast_add, Pi.intCast_def, Weight.coe_weight_mk, w]
      ring
    by_cases hα : (α : H → k) = 0
    · refine le_iSup (fun n ↦ (W n).toSubmodule) n ?_
      simpa [hα, W, w] using hev_mem
    have hn : genWeightSpace V (χ + (n.1 + m) • α : H → k) ≠ ⊥ := by
      rw [← LieSubmodule.nontrivial_iff_ne_bot]
      apply nontrivial_of_ne ⟨_, hev_mem⟩ 0
      rw [ne_eq, Subtype.ext_iff]
      exact hev
    let n' : ι := ⟨n.1 + m, ⟨hn, by simp [hα]⟩⟩
    exact le_iSup (fun n ↦ (W n).toSubmodule) n' hev_mem
  have He : Set.MapsTo (toEnd k L V e) U U := by
    specialize aux' 1
    simp only [Subtype.forall, one_smul] at aux'
    exact aux' e e.2
  have Hf : Set.MapsTo (toEnd k L V f) U U := by
    specialize aux' (-1)
    simp only [Int.reduceNeg, Subtype.forall, neg_smul, one_smul] at aux'
    exact aux' f f.2
  suffices (toEnd k L V h).restrict Hh =
      ⁅(toEnd k L V e).restrict He, (toEnd k L V f).restrict Hf⁆ by
    simp only [LinearMap.trace_lie, this]
  simp [← hh]
  rfl




    -- (fun n : ℤ ↦ (χ + n • α : H → k))
  -- obtain (rfl|h0) := eq_or_ne h 0
  -- · simp
  -- let W (n : ℤ) : LieSubmodule k H V := weightSpace V (χ + n • α : H → k)
  -- let U' : Submodule k V := ⨆ n : ℤ, W n
  -- let H' : LieSubalgebra k H := preserving U'
  -- have hhH' (v : V) (hv : v ∈ U') : ⁅h, v⁆ ∈ U' := by
  --   suffices U' ≤ U'.comap (toEnd k H V h) from this hv
  --   simp only [zsmul_eq_mul, Pi.intCast_def, iSup_le_iff, U']
  --   intro n v hv
  --   have := LieSubmodule.lie_mem _ (x := h) hv
  --   simpa only [Submodule.mem_comap, toEnd_apply_apply, coe_bracket_of_module, U'] using
  --     le_iSup (fun n ↦ (W n).toSubmodule) n this
  -- let h' : H' := ⟨h, hhH'⟩
  -- have : LieRing.IsNilpotent H' := by
  --   -- TODO: extract instance
  --   apply Function.Injective.lieAlgebra_isNilpotent (f := H'.incl)
  --   exact Subtype.coe_injective
  -- let U : LieSubmodule k H' V := { toSubmodule := U', lie_mem := by intro x; apply x.2 }
  -- have foobar := LieModule.traceForm_eq_sum_finrank_nsmul' k H' U
  -- have quux := traceForm_genWeightSpace_eq k H' U
  -- have xyzzy := @LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup ℤ k V
  -- classical
  -- have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  --   (LieSubmodule.iSupIndep_iff_toSubmodule.mp <| iSupIndep_genWeightSpace' k H' U)
  --   (LieSubmodule.iSup_eq_top_iff_toSubmodule.mp <| iSup_genWeightSpace_eq_top' k H' U)
  -- have aux (χ : Weight k H' U) :
  --     Set.MapsTo (toEnd k H' U h') (genWeightSpace U χ) (genWeightSpace U χ) :=
  --   fun m hm ↦ LieSubmodule.lie_mem _ hm
  -- replace aux := LinearMap.trace_eq_sum_trace_restrict hds aux
  -- have tr_h' : (LinearMap.trace k ↥U) ((toEnd k ↥H' ↥U) h') = 0 := by
  --   sorry
  -- rw [tr_h'] at aux
  -- simp only [LieSubmodule.toEnd_restrict_eq_toEnd, U'] at aux
  -- sorry

end LieSubalgebra

namespace LieAlgebra

variable {k L V : Type*} [Field k] [CharZero k] [LieRing L] [LieAlgebra k L]
variable [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

example [IsSemisimple k L] : HasTrivialRadical k L := by
  infer_instance

example [Module.Finite k L] [IsKilling k L] : IsSemisimple k L := by
  infer_instance

example [Module.Finite k L] [IsKilling k L] : HasTrivialRadical k L := by
  infer_instance

-- move this
instance [Subsingleton L] : IsSolvable k L := by
  constructor
  use 0
  ext x
  simp [Subsingleton.elim x 0]

-- move this
/-- The Killing form is symmetric. -/
lemma killingForm_symm (X Y : L) : killingForm k L X Y = killingForm k L Y X :=
  LieModule.traceForm_comm _ _ _ _ _

/-- The Killing form is symmetric. -/
lemma killingForm_isSymm : (killingForm k L).IsSymm :=
  LieModule.traceForm_isSymm _ _ _

private theorem isSolvable_iff_of_algClosed [Module.Finite k L] [IsAlgClosed k] :
    IsSolvable k L ↔ ∀ X Y : L, Y ∈ LieAlgebra.derivedSeries k L 1 → killingForm k L X Y = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial L
  · simp; infer_instance
  constructor
  · intro h
    obtain ⟨χ, hχ⟩ := LieModule.exists_forall_lie_eq_smul_of_isSolvable k L L
    obtain ⟨⟨Z, hZ⟩, hZ0⟩ := exists_ne (0 : LieModule.weightSpace L χ) 
    simp only [ne_eq, LieSubmodule.mk_eq_zero] at hZ0
    simp only [LieModule.mem_weightSpace] at hZ
    sorry
  · intro h
    sorry

theorem isSolvable_iff [Module.Finite k L] :
    IsSolvable k L ↔ ∀ X Y : L, Y ∈ LieAlgebra.derivedSeries k L 1 → killingForm k L X Y = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial L
  · simp; infer_instance
  constructor
  · intro h
    -- WLOG: k is algebraically closed
    -- have := LieModule.exists_forall_lie_eq_smul_of_isSolvable k L L
    sorry
  · intro h
    sorry

instance [Module.Finite k L] [HasTrivialRadical k L] : IsKilling k L := by
  constructor
  suffices IsSolvable k (LieIdeal.killingCompl k L ⊤) from HasTrivialRadical.eq_bot_of_isSolvable _
  rw [isSolvable_iff]
  intro X Y hY
  rw [LieIdeal.killingForm_eq]
  show killingForm k L X Y = 0
  have := X.2
  rw [LieIdeal.mem_killingCompl] at this
  rw [killingForm_symm]
  apply this
  simp

example [Module.Finite k L] [IsSemisimple k L] : IsKilling k L := by
  infer_instance

example [Module.Finite k L] [HasTrivialRadical k L] : IsSemisimple k L := by
  infer_instance

end LieAlgebra
