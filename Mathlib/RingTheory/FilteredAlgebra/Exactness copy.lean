/-
Copyright (c) 2025 Huanyu Zheng, Weichen Jiao, Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng, Weichen Jiao, Yi Yuan
-/
import Mathlib.RingTheory.FilteredAlgebra.Exactness
import Mathlib.Tactic.Linarith.Frontend

variable {R S T σR σS σT : Type*}

variable [Ring R] [SetLike σR R] [AddSubgroupClass σR R]

variable [Ring S] [SetLike σS S] [AddSubgroupClass σS S]

variable [Ring T] [SetLike σT T] [AddSubgroupClass σT T]

variable {FR : ℤ → σR} {FS : ℤ → σS} {FT : ℤ → σT}

variable [IsRingFiltration FS (fun n ↦ FS <| n - 1)]
         [IsRingFiltration FT (fun n ↦ FT <| n - 1)]

variable (f : FilteredRingHom FR (fun n ↦ FR <| n - 1) FS (fun n ↦ FS <| n - 1))
         (g : FilteredRingHom FS (fun n ↦ FS <| n - 1) FT (fun n ↦ FT <| n - 1))
         [hasGMul FR fun n ↦ FR (n - 1)]
         [hasGMul FT fun n ↦ FT (n - 1)] [hasGMul FS fun n ↦ FS (n - 1)]

open DirectSum DFinsupp FilteredRingHom






theorem strictness_under_exact_and_exhaustive (fg_exact : Function.Exact f.toRingHom g.toRingHom)
    (GfGg_exact : Function.Exact Gr[f] Gr[g])
    (Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS <| n - 1)) : g.IsStrict := by
  constructor
  · sorry
  · sorry



-- omit [AddSubgroupClass σS S] in
-- theorem exists_nonneg_x_in_filtration (Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS <| n - 1))
--  : ∃ s, s ≥ 0 ∧ (x : S) ∈ FS (p + s) := by
--   obtain ⟨s₀, xin⟩ : ∃ s, (x : S) ∈ FS s := by
--     apply Set.mem_iUnion.mp
--     rw[← IsExhaustiveFiltration.exhaustive (fun n ↦ FS <| n - 1) (F := FS) (A := S)]
--     trivial
--   rcases lt_or_le p s₀ with ch | ch
--   · exact ⟨s₀ - p, by simp only [ge_iff_le, sub_nonneg, add_sub_cancel, xin, and_true, le_of_lt ch]⟩
--   · exact ⟨0, by simp only [ge_iff_le, le_refl, add_zero, (IsFiltration.mono ch) xin, and_self]⟩



-- omit [IsRingFiltration FS fun n ↦ FS <| n - 1] in
-- lemma Gf_zero (hx : g.toRingHom x = y)(ch : p < k)(hy1 : y ∈ FT p) : Gr(k)[g] ⟦⟨x, xin⟩⟧ = 0 := by
--   simp only [FilteredAddGroupHom.AssociatedGradedRingHom_lift, QuotientAddGroup.eq_zero_iff]
--   show (g.toRingHom x) ∈ FT (k - 1)
--   rw[hx]
--   apply IsFiltration.mono (F := FT) (F_lt := (fun n ↦ FT <| n - 1)) (by linarith) hy1




-- omit [IsRingFiltration FS fun n ↦ FS <| n - 1] [IsRingFiltration FT fun n ↦ FT <| n - 1] in
-- theorem Gf_zero_iff_of_in_ker : Gr(i)[g] u = 0 ↔
--     (of (GradedPiece FS (fun n ↦ FS <| n - 1)) i u) ∈ Gr[g].ker := by
--   rw[Gof_eq_piece g i u]
--   constructor
--   · intro h
--     apply AssociatedGraded.ext_iff.mpr fun j ↦ ?_
--     by_cases ch : i = j
--     · rw[← ch, h, zero_apply]
--     · rw[G_to_Gf, of_eq_of_ne i j u ch, map_zero, DirectSum.zero_apply]
--   · exact fun h ↦
--     (AddSemiconjBy.eq_zero_iff ((Gr[g] ((of (GradedPiece FS fun n ↦ FS <| n - 1) i) u)) i)
--     (congrArg (HAdd.hAdd ((Gr[g] ((of (GradedPiece FS fun n ↦ FS <| n - 1) i) u)) i))
--     <| congrFun (congrArg DFunLike.coe <| id h.symm) i)).mp rfl




-- omit [IsRingFiltration FS fun n ↦ FS <| n - 1] [IsRingFiltration FT fun n ↦ FT <| n - 1] in
-- lemma Ggker_eq_Gfrange (Gexact : Function.Exact Gr[f] Gr[g]) (i : ℤ) :
--     Gr(i)[g].ker = Gr(i)[f].range := by
--   ext u
--   refine Iff.trans (Gf_zero_iff_of_in_ker g) ?_
--   rw[Function.Exact.addMonoidHom_ker_eq Gexact]
--   have (x : GradedPiece FR (fun n ↦ FR (n - 1)) i) : (of (GradedPiece FS fun n ↦ FS <| n - 1) i)
--       ((Gr[f] ((of (GradedPiece FR fun n ↦ FR <| n - 1) i) x)) i)
--       = Gr[f] ((of (GradedPiece FR fun n ↦ FR <| n - 1) i) x) := by
--     apply AssociatedGraded.ext_iff.mpr fun j ↦ ?_
--     by_cases ch : i = j
--     · rw[← ch, of_eq_same i ((Gr[f] ((of (GradedPiece FR fun n ↦ FR <| n - 1) i) x)) i)]
--     · rw[of_eq_of_ne i j ((Gr[f] ((of (GradedPiece FR fun n ↦ FR <| n - 1) i) x)) i) ch, G_to_Gf,
--         of_eq_of_ne i j x ch, map_zero]
--   exact ⟨fun ⟨x, hx⟩ ↦ ⟨x i, by rw[← G_to_Gf, hx, of_eq_same i u]⟩,
--     fun ⟨x, hx⟩ ↦ ⟨((of (GradedPiece FR fun n ↦ FR <| n - 1) i) x), by rw[← hx, Gof_eq_piece, this]⟩⟩


-- #check Nat.decreasingInduction
-- lemma Int.decreasingInduction' (m n : ℤ) {P : ℤ → Prop}
--     (h : (k : ℤ) → k ≤ n → m < k → P k → P (k - 1)) (mn : m ≤ n) (hP : P n) : P m := by
--   have (s : ℕ) (hs : s < n - m) : P (n - s) → P (n - s - 1) :=
--     h (n - s) (by linarith) (by linarith[hs])
--   obtain⟨r, hr⟩ : ∃ r : ℕ, r = n - m := CanLift.prf (n - m) (by linarith)
--   have : m = n - r := by simp only [hr, sub_sub_cancel]
--   rw[this]
--   have (t : ℕ) (hs : t ≤ n - m) : P (n - t) := by
--     induction' t with t ih
--     · simp only [Nat.cast_zero, sub_zero, hP]
--     · have : n - (t : ℤ) - 1 = n - ((t + 1 : ℕ) : ℤ) := Int.sub_sub n (↑t) 1
--       rw[← this]
--       apply h (n - t) (by linarith) (by linarith[hs])
--       apply ih (by linarith[hs])
--   apply this
--   simp only [hr, le_refl]


-- def P (y) := fun n ↦ y ∈ ⇑g.toRingHom '' (FS n)

-- lemma si (k)
-- (x : S) (hx : g.toRingHom x = y)
-- (s : ℤ) (hy1 : y ∈ FT p)
--  (xin : x ∈ FS k) (klt : p < k) (kle : k ≤ p + s) (h : P g y k) {Gexact : Function.Exact Gr[f] Gr[g]}:
--  P g y (k - 1) := by
--   have ch : s > 0 := by linarith
--   obtain⟨z₀, hz₀⟩ : ∃ z , Gr(k)[f] z = ⟦⟨x, xin⟩⟧ := by
--     show ⟦⟨x, xin⟩⟧ ∈ Gr(k)[f].range
--     rw[← Ggker_eq_Gfrange f g Gexact k]
--     refine Gf_zero g hx klt hy1
--   obtain⟨z, hz⟩ : ∃ z , Gr(k)[f] ⟦z⟧ = ⟦⟨x, xin⟩⟧ := by
--     obtain⟨z, eq⟩ := Quotient.exists_rep z₀
--     exact ⟨z, by rw[eq, hz₀]⟩
--   obtain⟨x', hx'⟩ : ∃ x' ∈ FS (k - 1), y = g.toRingHom x' := by
--     rw[← hx]
--     use x - f.toRingHom ↑z
--     constructor
--     · simp at hz
--       have : - f.toRingHom z + x ∈ FS (k - 1) := hz
--       rwa[neg_add_eq_sub (f.toRingHom ↑z) x] at this
--     ·
--       have : Gr[g].comp Gr[f] = Gr[g.comp f] := AssociatedGradedRingHom_comp g f
--       -- rw[Function.Exact.comp_eq_zero Gexact] at this
--       have : Gr[g.comp f] = 0 := by exact Eq.symm (DirectSum.addHom_ext fun i y ↦
--             congrFun this ((of (GradedPiece FR fun n ↦ FR (n - 1)) i) y))
--       have tt : Gr(k)[g.comp f] ⟦z⟧ = 0 := by
--         rw[(Geq0_iff_pieces0 (g ∘ f)).mp this k]
--         simp
--       have : (⟨(g.comp f).toRingHom z, (g.comp f).toFilteredHom.pieces_wise k z <| SetLike.coe_mem z⟩ : FT k) ∈
--       (((fun n ↦ FT (n - 1)) k) : AddSubgroup T).addSubgroupOf ((FT k) : AddSubgroup T) :=
--         (QuotientAddGroup.eq_zero_iff (⟨(g.comp f).toRingHom z,
--         (g.comp f).toFilteredHom.pieces_wise k z <| SetLike.coe_mem z⟩ : FT k)).mp tt
--       have : (g.comp f).toRingHom ↑z ∈ FT (k - 1) := by
--         exact this
--       -- have : (g ∘ f).toRingHom ↑z = 0 := by
--       --   apply?


      -- sorry


      -- have : g.toRingHom (f.toRingHom ↑z)= 0 := by
      --   show (g ∘ f).toRingHom z = 0


      --   -- simp only [Gf] at this

      --   -- have : ⟦(g ∘ f).toRingHom z⟧ = (0  := by
      --   --   sorry
      --     -- apply?
      --   #check (Gf (g ∘ f) k) ↑z
      --   #check (g ∘ f).toRingHom ↑z
      --   -- have : (Gf (g ∘ f) k) ↑z = (g ∘ f).toRingHom ↑z := by
      --   --   sorry
        -- simp only [Gf, GradedPiece.mk_eq] at this

        -- rw[] at this



        -- rw[← G_to_Gf]

        -- sorry
      -- rw[RingHom.map_sub g.toRingHom x (f.toRingHom z), this, sub_zero]




  -- sorry
  -- rcases Or.symm (LE.le.gt_or_eq sge0) with ch | ch
  -- · rw[← hx]
  --   rw[ch, add_zero] at xin
  --   exact Set.mem_image_of_mem (⇑g.toRingHom) xin
  -- ·

  --   have : ∃ u : FS p, y = g.toRingHom u := by
  --     -- by induction(hard)
  --     sorry
  --   sorry
  -- sorry



-- theorem strictness_under_exact_and_exhaustive' (Gexact : Function.Exact Gr[f] Gr[g])
-- (Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS <| n - 1)) :
--  ∀ {p : ℤ} {y : T}, y ∈ FT p → y ∈ Set.range (FilteredHom.toFun FS FT) → y ∈ FilteredHom.toFun FS FT '' ↑(FS p) := by
--   intro p y
--   constructor
--   · rintro ⟨x, xin, eq⟩
--     rw[← eq]

--     exact ⟨g.pieces_wise p x xin, by use x⟩
--   · rintro ⟨hy1, ⟨x, hx⟩⟩
--     obtain⟨s, sge0, xin⟩ : ∃s, s ≥ 0 ∧ x ∈ FS (p + s) := exists_nonneg_x_in_filtration Exhaustive
--     rcases Or.symm (LE.le.gt_or_eq sge0) with ch | ch
--     · rw[← hx]
--       rw[ch, add_zero] at xin
--       exact Set.mem_image_of_mem (⇑g.toRingHom) xin
--     · obtain⟨z₀, hz₀⟩ : ∃ z , Gr(p + s)[f] z = ⟦⟨x, xin⟩⟧ := by
--         show ⟦⟨x, xin⟩⟧ ∈ (Gr(p + s)[f]).range
--         rw[← Ggker_eq_Gfrange f g Gexact (p + s)]
--         exact Gf_zero g hx (by sorry) hy1
--       obtain⟨z, hz⟩ : ∃ z , Gr(p + s)[f] ⟦z⟧ = ⟦⟨x, xin⟩⟧ := by
--         obtain⟨z, eq⟩ := Quotient.exists_rep z₀
--         exact ⟨z, by rw[eq, hz₀]⟩
--       obtain⟨x', hx'⟩ : ∃ x' ∈ FS (p + s - 1), y = g.toRingHom x' := by
--         rw[← hx]
--         use x - f.toRingHom ↑z
--         constructor
--         · simp only [Gf, GradedPiece.mk_eq, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Quotient.lift_mk,
--             QuotientAddGroup.eq] at hz
--           have : - f.toRingHom z + x ∈ FS (p + s - 1) := hz
--           rwa[neg_add_eq_sub (f.toRingHom ↑z) x] at this
--         · have : g.toRingHom (f.toRingHom ↑z)= 0 := by
--             have : (Gr[g.comp f]) = 0 := sorry
--             sorry
--           rw[RingHom.map_sub g.toRingHom x (f.toRingHom z), this, sub_zero]
--       have : ∃ u : FS p, y = g.toRingHom u := by
--         -- by induction(hard)
--         sorry
--       sorry
    -- sorry

    -- have : P g y (p + s) := by
    --   use x
    --   simp only [SetLike.mem_coe, xin, hx, and_self]
    -- show P g y p
    -- apply Int.decreasingInduction' p (p + s)
    -- · apply si f g hx
    --   exact sge0
    --   exact xin
    --   exact hy1
    --   exact Gexact
    -- · linarith
    -- · exact this


-- theorem strictness_under_exact_and_exhaustive (Gexact : Function.Exact Gr[f] Gr[g])
-- (Exhaustive : IsExhaustiveFiltration FS (fun n ↦ FS <| n - 1)) : g.IsStrict :=
--   ⟨fun p y ↦ strictness_under_exact_and_exhaustive' f g Gexact Exhaustive p y,
--    fun p y ↦ strictness_under_exact_and_exhaustive' f g Gexact Exhaustive (p - 1) y⟩
