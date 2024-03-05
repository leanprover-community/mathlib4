import Mathlib.Tactic
import Mathlib.Topology.Compactification.OnePoint
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Pointwise
import Mathlib.Topology.Separation
import Mathlib.Topology.MetricSpace.PseudoMetric

variable {X : Type _} [MetricSpace X]

structure isKatetov (f : X → ℝ) : Prop where
  le_dist : ∀ x y, |f x - f y| ≤ dist x y
  le_add : ∀ x y, dist x y ≤ f x + f y

theorem isKatetov_def {_ : MetricSpace X} {f : X → ℝ} :
  isKatetov f ↔ (∀ x y, |f x - f y| ≤ dist x y) ∧ (∀ x y, dist x y ≤ f x + f y) :=
  ⟨fun h ↦ ⟨h.le_dist, h.le_add⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

structure KatetovMap (X : Type*) [MetricSpace X] where
  protected toFun : X → ℝ
  protected isKatetovtoFun : isKatetov toFun

notation "E(" X ")" => KatetovMap X

section

class KatetovMapClass (F : Type*) (X : Type*) [MetricSpace X] [FunLike F X  ℝ] where
  map_katetov (f : F) : isKatetov f

end

export KatetovMapClass (map_katetov)

section KatetovMapClass

variable {F X : Type*} [MetricSpace X] [FunLike F X  ℝ]
variable [KatetovMapClass F X]

@[coe] def toKatetovMap (f : F) : E(X) := ⟨f, map_katetov f⟩

instance : CoeTC F E(X) := ⟨toKatetovMap⟩

end KatetovMapClass

namespace KatetovMap

variable {X : Type*} [MetricSpace X]

instance funLike : FunLike E(X) X ℝ where
  coe := KatetovMap.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance toKatetovMapClass : KatetovMapClass E(X) X where
  map_katetov := KatetovMap.isKatetovtoFun

@[simp]
theorem toFun_eq_coe {f : E(X)} : f.toFun = (f : X → ℝ) := rfl

instance : CanLift (X → ℝ) E(X) DFunLike.coe isKatetov := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

def Simps.apply (f : E(X)) : X → ℝ := f

initialize_simps_projections KatetovMap (toFun → apply)

#check ContinuousMapClass
@[simp]
protected theorem coe_coe {F : Type*} [FunLike F X ℝ] [KatetovMapClass F X] (f : F) :
  ⇑(f : E(X)) = f := rfl

@[ext]
theorem ext {f g : E(X)} (h : ∀ a, f a = g a) : f = g := DFunLike.ext _ _ h

protected def copy (f : E(X)) (f' : X → ℝ) (h : f' = f) : E(X) where
  toFun := f'
  isKatetovtoFun := h.symm ▸ f.isKatetovtoFun

@[simp]
theorem coe_copy (f : E(X)) (f' : X → ℝ) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : E(X)) (f' : X → ℝ) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable {f g : E(X)}

theorem katetov_set_coe (s : Set E(X)) (f : s) : isKatetov (f : X → ℝ) :=
  f.1.isKatetovtoFun

theorem coe_injective : @Function.Injective E(X) (X → ℝ) (↑) := fun f g h => by
  cases f; cases g; congr

@[simp]
theorem coe_mk (f : X → ℝ) (h : isKatetov f) : ⇑(⟨f, h⟩ : E(X)) = f :=
  rfl

end KatetovMap

lemma helper (x₀ : X) (f : E(X)) : ∀ x, |f x - dist x x₀| ≤ f x₀ := by
  refine fun x ↦ abs_le.mpr ⟨?_, ?_⟩
  · linarith [(map_katetov f).le_add x x₀]
  · linarith [le_of_abs_le <| (map_katetov f).le_dist x x₀]

theorem bounded_dist {f g : E(X)} : BddAbove {|f x - g x| | x : X} := by
  by_cases hn : Nonempty X
  · have x₀ := Classical.choice ‹Nonempty X›
    refine ⟨f x₀ + g x₀, fun _ ⟨x, hx⟩ ↦ ?_⟩; rw [← hx]
    have h : |f x - g x| ≤ |f x - dist x x₀| + |g x - dist x x₀|:= by
      rw [← abs_sub_comm (dist x x₀) (g x)]; apply abs_sub_le (f x) (dist x x₀) (g x)
    apply le_trans h <| add_le_add (helper x₀ f x) (helper x₀ g x)
  · refine ⟨0, fun _ ⟨x, _⟩ ↦ False.elim (hn ⟨x⟩)⟩

lemma sSup_eq_zero (s : Set ℝ) (hb : BddAbove s) (snonneg : ∀ x ∈ s, 0 ≤ x) (hsup : sSup s = 0)
  : ∀ x ∈ s, x = 0 := by
  refine (fun x xs ↦ le_antisymm (by rw [← hsup]; exact le_csSup hb xs) (snonneg x xs))

theorem katetov_nonneg (f : E(X)) (x : X) : 0 ≤ f x := by
  have : 0 ≤ f x + f x := by rw [← dist_self x]; exact (map_katetov f).le_add x x
  apply nonneg_add_self_iff.mp this

theorem empty_sSup_of_empty (h : IsEmpty X) (f g : E(X)) : ¬Set.Nonempty {|f x - g x| | x : X} := by
  by_contra hc
  obtain ⟨_, x, _⟩ := hc
  exact IsEmpty.false x

noncomputable instance: MetricSpace E(X) where
  dist f g := sSup {|f x - g x| | x : X}
  dist_self f := by
    by_cases h : Nonempty X
    · simp [dist]
    · simp [dist, sSup]
      have hf := empty_sSup_of_empty (not_nonempty_iff.mp h) f f
      simp only [sub_self, abs_zero] at hf
      simp_all only [false_and, dite_false, IsEmpty.forall_iff]
  dist_comm f g := by simp [dist, abs_sub_comm]
  dist_triangle f g h := by
    by_cases hc : Nonempty X
    · simp [dist]
      apply Real.sSup_le
      · rintro val ⟨x, rfl⟩
        rw [← csSup_add]
        · apply le_trans <| abs_sub_le (f x) (g x) (h x)
          apply le_csSup (by apply BddAbove.add <;> apply bounded_dist)
          refine Set.mem_add.mpr ⟨|f x - g x|, (by simp), (by simp)⟩
        · have x₀ := Classical.choice ‹Nonempty X›
          use |f x₀ - g x₀| ; simp
        · apply bounded_dist
        · have x₀ := Classical.choice ‹Nonempty X›
          use |g x₀ - h x₀| ; simp
        · apply bounded_dist
      · apply add_nonneg <;>
        { apply Real.sSup_nonneg; rintro val ⟨x, rfl⟩; apply abs_nonneg}
    · simp [dist, sSup]
      have hfh := empty_sSup_of_empty (not_nonempty_iff.mp hc) f h
      have hfg := empty_sSup_of_empty (not_nonempty_iff.mp hc) f g
      have hgh:= empty_sSup_of_empty (not_nonempty_iff.mp hc) g h
      simp_all only [false_and, dite_false]
      simp only [add_zero, le_refl]
  eq_of_dist_eq_zero := by
    intro f g h
    simp [dist] at h
    apply sSup_eq_zero at h
    · ext x; exact eq_of_sub_eq_zero <| abs_eq_zero.mp (h |f x - g x| ⟨x, rfl⟩)
    · apply bounded_dist
    · rintro _ ⟨x, rfl⟩; exact abs_nonneg _
  edist_dist x y:= by exact ENNReal.coe_nnreal_eq _

theorem dist_coe_le_dist (f g : E(X)) (x : X) : dist (f x) (g x) ≤ dist f g :=
  by refine le_csSup bounded_dist (by simp [dist])

theorem dist_le {C :ℝ} (C0 : (0 : ℝ) ≤ C) (f g : E(X)):
  dist f g ≤ C ↔ ∀ x : X, dist (f x) (g x) ≤ C := by
  refine ⟨fun h x => le_trans (dist_coe_le_dist _ _ x) h, fun H ↦ ?_⟩; simp [dist]
  apply Real.sSup_le (by simp [*] at *; assumption) (C0)

noncomputable instance : CompleteSpace E(X) :=
  Metric.complete_of_cauchySeq_tendsto fun (u : ℕ → E(X)) (hf : CauchySeq u) => by
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have u_bdd := fun x n m N hn hm => le_trans (dist_coe_le_dist _ _ x) (b_bound n m N hn hm)
    have ux_cau : ∀ x, CauchySeq fun n => u n x :=
      fun x => cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, u_bdd x, b_lim⟩
    choose f hf using fun x => cauchySeq_tendsto_of_complete (ux_cau x)
    have fF_bdd : ∀ x N, dist (u N x) (f x) ≤ b N :=
      fun x N => le_of_tendsto (tendsto_const_nhds.dist (hf x))
        (Filter.eventually_atTop.2 ⟨N, fun n hn => u_bdd x N n N (le_refl N) hn⟩)
    have kat_f : isKatetov f := by
      have h: ∀ x y,∀ ε > 0, |f x - f y| ≤ 2*ε + dist x y ∧ dist x y ≤ f x + f y + 2*ε:= by
        intro x y ε εpos
        rcases Metric.tendsto_atTop.mp (hf x) ε εpos with ⟨Nx, hNx⟩
        rcases Metric.tendsto_atTop.mp (hf y) ε εpos with ⟨Ny, hNy⟩
        simp [dist] at *
        set N := max Nx Ny
        specialize hNx N (le_max_left _ _)
        specialize hNy N (le_max_right _ _)
        constructor
        · calc
          _ = _ := by rw [← add_zero (f x), (show 0 = u N x - u N x + u N y - u N y by ring)]
          _ = |(f x - (u N) x) + ((u N) y - f y) + ((u N x) - (u N y))| := by ring_nf
          _ ≤ |(f x - (u N) x)| + |((u N) y - f y)| + |((u N x) - (u N y))| := by
              repeat apply (abs_add ..).trans; gcongr; try exact abs_add _ _
          _ ≤ 2*ε + dist x y := by
              rw [abs_sub_comm (f x)]
              linarith [(map_katetov (u N)).le_dist x y]
        · calc
          _ ≤ u N x + u N y := (map_katetov (u N)).le_add x y
          _ = _ := by rw [← add_zero (u N y), show 0 = f x - f x + f y - f y by ring]
          _ = f x + f y + (u N x - f x) + (u N y - f y) := by ring
          _ ≤ _ := by linarith [le_of_lt (lt_of_abs_lt hNx), le_of_lt (lt_of_abs_lt hNy)]
      constructor <;>
        { refine fun x y ↦ le_of_forall_pos_le_add (fun ε εpos ↦ ?_)
          linarith [h x y (ε/2) (half_pos εpos)]}
    · use ⟨f, kat_f⟩
      refine' tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) _ b_lim)
      refine (fun N ↦ (dist_le (b0 N) (u N) ⟨f, kat_f⟩).mpr (fun x => fF_bdd x N))

namespace KatetovKuratowskiEmbedding

def emptyMap [IsEmpty X] : E(X) := by
  refine ⟨fun x ↦ (IsEmpty.false x).elim, ?_⟩
  constructor <;> {intro x; exact (IsEmpty.false x).elim}

theorem exists_isometric_embedding (X : Type*) [MetricSpace X] :
  ∃ f : X → E(X), Isometry f := by
    by_cases h : Nonempty X
    · refine ⟨fun x : X ↦ ⟨fun y ↦ dist x y, ?_⟩, ?_⟩
      · constructor <;> (intro y z; rw [dist_comm x y])
        · rw [dist_comm x z]; exact abs_dist_sub_le y z x
        · exact dist_triangle y x z
      · refine Isometry.of_dist_eq (fun x y ↦ le_antisymm ?_ ?_)
        · refine Real.sSup_le ?_ dist_nonneg
          · simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
            refine fun z ↦ abs_dist_sub_le x y z
        · refine (Real.le_sSup_iff bounded_dist ?_).mpr  ?_
          · have x₀ := Classical.choice ‹Nonempty X›
            use |dist x x₀ - dist y x₀| ; simp
          · simp only [KatetovMap.coe_mk, Set.mem_setOf_eq, exists_exists_eq_and]
            refine fun ε εpos ↦ ⟨x, ?_⟩
            rw [dist_self, zero_sub, abs_neg, dist_comm, abs_of_nonneg (dist_nonneg)]
            exact add_lt_of_neg_right (dist y x) εpos
    · refine ⟨fun _ ↦ @emptyMap _ _ (not_nonempty_iff.mp h), ?_⟩
      intro x; exact ((not_nonempty_iff.mp h).false x).elim

end KatetovKuratowskiEmbedding

open KatetovKuratowskiEmbedding

noncomputable def katetovkuratowskiEmbedding (X : Type*) [MetricSpace X] : X ↪ E(X) := by
  choose f h using exists_isometric_embedding X; refine ⟨f, h.injective⟩

protected theorem katetovkuratowskiEmbedding.isometry (X : Type*) [MetricSpace X] :
  Isometry (katetovkuratowskiEmbedding X) :=
    Classical.choose_spec <| exists_isometric_embedding X
