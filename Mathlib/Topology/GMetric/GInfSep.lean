import Mathlib.Topology.GMetric.Basic
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ENNReal.Basic

variable {α β:Type*}
namespace Metric
open Real

instance: FunLike (PseudoMetricSpace α) α (α → ℝ) where
  coe := fun x => x.dist
  coe_injective' := fun x y => by
    simp only
    intro h
    ext
    rw [h]

instance: FunLike (PseudoMetricSpace α) α (α → ℝ) where
  coe := fun x => x.dist
  coe_injective' := fun X Y => by
    cases X; cases Y; congr; simp; intro h; ext ;rw [h]

instance : GPseudoMetricClass (PseudoMetricSpace α) α ℝ where
  gdist_self := fun x => x.dist_self
  comm' := fun x => x.dist_comm
  triangle' := fun x => x.dist_triangle

instance: FunLike (MetricSpace α) α (α → ℝ) where
  coe := fun x => x.dist
  coe_injective' := fun X Y => by
    cases X; cases Y; congr; simp; intro h; ext; rw [h]

instance: GMetricClass (MetricSpace α) α ℝ where
  gdist_self := fun x => x.dist_self
  comm' := fun x => x.dist_comm
  triangle' := fun x => x.dist_triangle
  eq_of_dist_eq_zero := fun x => x.eq_of_dist_eq_zero

end Metric

namespace EMetricSpace
open ENNReal

instance: FunLike (PseudoEMetricSpace α) α (α → ℝ≥0∞) where
  coe := fun x => x.edist
  coe_injective' := fun X Y => by
    cases X; cases Y; congr; simp; intro h; ext; rw [h]

instance: FunLike (EMetricSpace α) α (α → ℝ≥0∞) where
  coe := fun x => x.edist
  coe_injective' := fun X Y => by
    cases X; cases Y; congr; simp; intro h; ext; rw [h]

instance: GPseudoMetricClass (PseudoEMetricSpace α) α ℝ≥0∞ where
  gdist_self := fun x => x.edist_self
  comm' := fun x => x.edist_comm
  triangle' := fun x => x.edist_triangle

instance: GMetricClass (EMetricSpace α) α ℝ≥0∞ where
  gdist_self := fun x => x.edist_self
  comm' := fun x => x.edist_comm
  triangle' := fun x => x.edist_triangle
  eq_of_dist_eq_zero := fun x => x.eq_of_edist_eq_zero

end EMetricSpace


namespace Set
open GMetric
section GinfSep

open Function

variable {γ:Type*} [CompleteLinearOrder γ] [AddCommMonoid γ] [CovariantClass γ γ (.+.) (.≤.)]

variable (gdist:α → α → γ) {x y :α} (s t:Set α) {d:γ}


/-- then infimum of the distance between separate points in some set-/
noncomputable def ginfsep : γ :=
  ⨅ (x ∈ s) (y ∈ s) (_:x ≠ y), gdist x y


section gdist
section compare


theorem le_ginfsep_iff :
    d ≤ ginfsep gdist s ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ gdist x y := by
  simp_rw [ginfsep, le_iInf_iff]

lemma ginfsep_nonneg_of_gdist_nonneg (gdist_nonneg:∀ x y, 0 ≤ gdist x y): 0 ≤ ginfsep gdist s := by
  rw [le_ginfsep_iff]; intros; apply gdist_nonneg

theorem ginfsep_pos : 0 < ginfsep gdist s ↔ ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ gdist x y := by
  constructor
  . intro h
    use ginfsep gdist s
    use h
    rw [← le_ginfsep_iff]
  intro ⟨c,⟨hcpos,hc⟩⟩
  suffices c ≤ ginfsep gdist s by exact gt_of_ge_of_gt this hcpos
  rw [le_ginfsep_iff]
  exact hc

theorem ginfsep_zero (gdist_nonneg:∀ x y, 0 ≤ gdist x y):
    ginfsep gdist s = 0 ↔ ∀ C > 0, ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ gdist x y < C := by
  constructor
  . intro h
    contrapose! h
    rw [← ginfsep_pos] at h
    exact ne_of_gt h
  . intro h
    contrapose! h
    rw [← ginfsep_pos]
    contrapose! h
    apply le_antisymm h $ ginfsep_nonneg_of_gdist_nonneg gdist s gdist_nonneg

theorem ginfsep_top :
    ginfsep gdist s = ⊤ ↔ ∀ x ∈ s, ∀ y ∈ s, x ≠ y → gdist x y = ⊤ := by
  simp_rw [ginfsep, iInf_eq_top]

theorem ginfsep_lt_top :
    ginfsep gdist s < ⊤ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ gdist x y < ⊤ := by
  simp_rw [ginfsep, iInf_lt_iff, exists_prop]

theorem ginfsep_ne_top :
    ginfsep gdist s ≠ ⊤ ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ gdist x y ≠ ⊤ := by
  simp_rw [← lt_top_iff_ne_top, ginfsep_lt_top]

theorem ginfsep_lt_iff :
    ginfsep gdist s < d ↔ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ gdist x y < d := by
  simp_rw [ginfsep, iInf_lt_iff, exists_prop]

theorem nontrivial_of_ginfsep_lt_top (hs : ginfsep gdist s < ⊤) : s.Nontrivial := by
  rcases (ginfsep_lt_top gdist s).1 hs with ⟨_, hx, _, hy, hxy, _⟩
  exact ⟨_, hx, _, hy, hxy⟩

theorem nontrivial_of_ginfsep_ne_top (hs : ginfsep gdist s ≠ ⊤) : s.Nontrivial :=
  nontrivial_of_ginfsep_lt_top gdist s (lt_top_iff_ne_top.mpr hs)

theorem Subsingleton.ginfsep (hs : s.Subsingleton) : s.ginfsep gdist = ⊤ := by
  rw [ginfsep_top]
  exact fun _ hx _ hy hxy => (hxy <| hs hx hy).elim

theorem le_ginfsep_image_iff {f : β → α} {s : Set β} : d ≤ ginfsep gdist (f '' s)
    ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≠ f y → d ≤ gdist (f x) (f y) := by
  simp_rw [le_ginfsep_iff, forall_mem_image]

theorem le_gdist_of_le_ginfsep {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hd : d ≤ s.ginfsep gdist) : d ≤ gdist x y :=
  (le_ginfsep_iff gdist s).1 hd x hx y hy hxy

theorem ginfsep_le_gdist_of_mem {x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y) :
    ginfsep gdist s ≤ gdist x y :=
  le_gdist_of_le_ginfsep gdist s hx hy hxy le_rfl

theorem ginfsep_le_of_mem_of_gdist_le {d x} (hx : x ∈ s) {y} (hy : y ∈ s) (hxy : x ≠ y)
    (hxy' : gdist x y ≤ d) : ginfsep gdist s ≤ d :=
  le_trans (ginfsep_le_gdist_of_mem gdist s hx hy hxy) hxy'

theorem le_ginfsep {d} (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → d ≤ gdist x y) : d ≤ ginfsep gdist s :=
  (le_ginfsep_iff gdist s).2 h

end compare


section sets
@[simp]
theorem ginfsep_empty : (∅ : Set α).ginfsep gdist = ⊤ :=
  subsingleton_empty.ginfsep gdist

@[simp]
theorem ginfsep_singleton : ({x} : Set α).ginfsep gdist = ⊤ :=
  subsingleton_singleton.ginfsep gdist

theorem ginfsep_iUnion_mem_option {ι : Type*} (o : Option ι) (s : ι → Set α) :
    (⋃ i ∈ o, s i).ginfsep gdist = ⨅ i ∈ o, (s i).ginfsep gdist := by cases o <;> simp

theorem ginfsep_anti (hst : s ⊆ t) : t.ginfsep gdist ≤ s.ginfsep gdist :=
  le_ginfsep gdist s fun _x hx _y hy => ginfsep_le_gdist_of_mem gdist t (hst hx) (hst hy)

theorem ginfsep_insert_le : (insert x s).ginfsep gdist ≤ ⨅ (y ∈ s) (_ : x ≠ y), gdist x y := by
  simp_rw [le_iInf_iff]
  refine' fun _ hy hxy => ginfsep_le_gdist_of_mem gdist (insert x s) (mem_insert _ _)
    (mem_insert_of_mem _ hy) hxy

theorem le_ginfsep_pair : gdist x y ⊓ gdist y x ≤ ({x, y} : Set α).ginfsep gdist := by
  simp_rw [le_ginfsep_iff, inf_le_iff, mem_insert_iff, mem_singleton_iff]
  rintro a (rfl | rfl) b (rfl | rfl) hab <;> (try simp only [le_refl, true_or, or_true]) <;>
    contradiction

theorem ginfsep_pair_le_left (hxy : x ≠ y) : ({x, y} : Set α).ginfsep gdist ≤ gdist x y :=
  ginfsep_le_gdist_of_mem gdist {x,y} (mem_insert _ _) (mem_insert_of_mem _ (mem_singleton _)) hxy

theorem ginfsep_pair_le_right (hxy : x ≠ y) : ({x, y} : Set α).ginfsep gdist ≤ gdist y x := by
  rw [pair_comm]; exact ginfsep_pair_le_left gdist hxy.symm

theorem ginfsep_pair_eq_inf
    (hxy : x ≠ y) : ({x, y} : Set α).ginfsep gdist = gdist x y ⊓ gdist y x :=
  le_antisymm (le_inf (ginfsep_pair_le_left gdist hxy) (ginfsep_pair_le_right gdist hxy))
  (le_ginfsep_pair gdist)

theorem ginfsep_eq_iInf : s.ginfsep gdist = ⨅ d : s.offDiag, (uncurry gdist) (d : α × α) := by
  refine' eq_of_forall_le_iff fun _ => _
  simp_rw [le_ginfsep_iff, le_iInf_iff, imp_forall_iff, SetCoe.forall, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

theorem ginfsep_of_fintype [DecidableEq α] [Fintype s] :
    s.ginfsep gdist = s.offDiag.toFinset.inf (uncurry gdist) := by
  refine' eq_of_forall_le_iff fun _ => _
  simp_rw [le_ginfsep_iff, imp_forall_iff, Finset.le_inf_iff, mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

theorem Finite.ginfsep
    (hs : s.Finite) : s.ginfsep gdist = hs.offDiag.toFinset.inf (uncurry gdist) := by
  refine' eq_of_forall_le_iff fun _ => _
  simp_rw [le_ginfsep_iff, imp_forall_iff, Finset.le_inf_iff, Finite.mem_toFinset, mem_offDiag,
    Prod.forall, uncurry_apply_pair, and_imp]

theorem Finset.coe_ginfsep [DecidableEq α] {s : Finset α} :
    (s : Set α).ginfsep gdist= s.offDiag.inf (uncurry gdist) := by
  simp_rw [ginfsep_of_fintype, ← Finset.coe_offDiag, Finset.toFinset_coe]

theorem Nontrivial.ginfsep_exists_of_finite [Finite s] (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.ginfsep gdist = gdist x y := by
  classical
    cases nonempty_fintype s
    simp_rw [ginfsep_of_fintype]
    rcases Finset.exists_mem_eq_inf s.offDiag.toFinset (by simpa) (uncurry gdist) with ⟨w, hxy, hed⟩
    simp_rw [mem_toFinset] at hxy
    refine' ⟨w.fst, hxy.1, w.snd, hxy.2.1, hxy.2.2, hed⟩

theorem Finite.ginfsep_exists_of_nontrivial (hsf : s.Finite) (hs : s.Nontrivial) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s.ginfsep gdist = gdist x y :=
  letI := hsf.fintype
  hs.ginfsep_exists_of_finite gdist

end sets
end gdist

section GPseudoMetric

variable {T:Type*} [FunLike T α (α → γ)] [GPseudoMetricClass T α γ]
  {gdist:T} {x y z : α} {s t : Set α}

theorem ginfsep_pair (hxy : x ≠ y) : ({x, y} : Set α).ginfsep gdist = gdist x y := by
  nth_rw 1 [← min_self (gdist x y)]
  convert ginfsep_pair_eq_inf gdist hxy using 2
  rw [comm']

theorem ginfsep_insert : ginfsep gdist (insert x s) =
    (⨅ (y ∈ s) (_ : x ≠ y), gdist x y) ⊓ s.ginfsep gdist := by
  refine' le_antisymm (le_min (ginfsep_insert_le gdist s) (ginfsep_anti gdist s (insert x s) (subset_insert _ _))) _
  simp_rw [le_ginfsep_iff, inf_le_iff, mem_insert_iff]
  rintro y (rfl | hy) z (rfl | hz) hyz
  · exact False.elim (hyz rfl)
  · exact Or.inl (iInf_le_of_le _ (iInf₂_le hz hyz))
  · rw [comm']
    exact Or.inl (iInf_le_of_le _ (iInf₂_le hy hyz.symm))
  · exact Or.inr (ginfsep_le_gdist_of_mem gdist s hy hz hyz)

theorem ginfsep_triple (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ginfsep gdist ({x, y, z} : Set α) = gdist x y ⊓ gdist x z ⊓ gdist y z := by
  simp_rw [ginfsep_insert, iInf_insert, iInf_singleton, ginfsep_singleton, inf_top_eq,
    ciInf_pos hxy, ciInf_pos hyz, ciInf_pos hxz]

variable (gdist_ne_top:∀ x y, gdist x y ≠ ⊤)

theorem subsingleton_of_ginfsep_eq_top (hs : s.ginfsep gdist = ⊤) : s.Subsingleton := by
  rw [ginfsep_top] at hs
  exact fun _ hx _ hy => of_not_not fun hxy => gdist_ne_top _ _ (hs _ hx _ hy hxy)

theorem ginfsep_eq_top_iff : s.ginfsep gdist = ⊤ ↔ s.Subsingleton :=
  ⟨subsingleton_of_ginfsep_eq_top gdist_ne_top,
  Subsingleton.ginfsep gdist s⟩

theorem Nontrivial.ginfsep_ne_top (hs : s.Nontrivial) : s.ginfsep gdist ≠ ⊤ := by
  contrapose! hs
  rw [not_nontrivial_iff]
  exact subsingleton_of_ginfsep_eq_top gdist_ne_top hs

theorem Nontrivial.ginfsep_lt_top (hs : s.Nontrivial) : s.ginfsep gdist < ⊤ := by
  rw [lt_top_iff_ne_top]
  exact hs.ginfsep_ne_top gdist_ne_top

theorem ginfsep_lt_top_iff : s.ginfsep gdist < ⊤ ↔ s.Nontrivial :=
  ⟨nontrivial_of_ginfsep_lt_top gdist s, Nontrivial.ginfsep_lt_top gdist_ne_top⟩

theorem ginfsep_ne_top_iff : s.ginfsep gdist ≠ ⊤ ↔ s.Nontrivial :=
  ⟨nontrivial_of_ginfsep_ne_top gdist s, Nontrivial.ginfsep_ne_top gdist_ne_top⟩
end GPseudoMetric


section GMetric


variable {T:Type*} [FunLike T α (α → γ)] [GMetricClass T α γ]
  {gdist:T} {x y z : α} {s t : Set α}

-- this isn't true when β = {⊤} = {0}
-- TODO: gdist_pos : [GMetricSpaceClass T α γ] (gdist : T) {x y : γ} : 0 < gdist x y ↔ x ≠ y
-- with assumption about γ having 0 ≠ ⊤
-- theorem ginfsep_pos_of_finite [Finite s] : 0 < s.ginfsep gdist := by
--   cases nonempty_fintype s
--   by_cases hs : s.Nontrivial
--   · rcases hs.ginfsep_exists_of_finite gdist with ⟨x, _hx, y, _hy, hxy, hxy'⟩
--     exact hxy'.symm ▸ gdist_pos.2 hxy
--   · rw [not_nontrivial_iff] at hs
--     exact (hs.ginfsep gdist).symm ▸ WithTop.zero_lt_top

-- theorem Finite.ginfsep_pos (hs : s.Finite) : 0 < s.ginfsep gdist :=
--   letI := hs.fintype
--   ginfsep_pos_of_finite

-- theorem relatively_discrete_of_finite [Finite s] :
--     ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ gdist x y := by
--   rw [← ginfsep_pos]
--   exact ginfsep_pos_of_finite


-- theorem Finite.relatively_discrete (hs : s.Finite) :
--     ∃ C > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → C ≤ edist x y :=
--   letI := hs.fintype
--   relatively_discrete_of_finite
end GMetric

end GinfSep
end Set
