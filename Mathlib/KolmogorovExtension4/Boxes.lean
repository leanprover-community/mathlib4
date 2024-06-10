import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.KolmogorovExtension4.Semiring

/-! # π-systems generating `MeasurableSpace.pi`

-/


open MeasureTheory Set

variable {ι : Type _} {α : ι → Type _}

section ProjectionMaps

section Measurable

variable [∀ i, MeasurableSpace (α i)]

theorem measurable_proj (I : Set ι) : Measurable fun (f : (i : ι) → α i) (i : I) ↦ f i := by
  rw [measurable_pi_iff]; exact fun i ↦ measurable_pi_apply _

theorem measurable_proj₂ (I J : Set ι) (hIJ : J ⊆ I) :
    Measurable fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ := by
  rw [measurable_pi_iff]; exact fun i ↦ measurable_pi_apply _

theorem measurable_proj₂' (I J : Finset ι) (hIJ : J ⊆ I) :
    Measurable fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ := by
  rw [measurable_pi_iff]; exact fun i ↦ measurable_pi_apply _

end Measurable

section Continuous

variable [∀ i, TopologicalSpace (α i)]

theorem continuous_proj (I : Set ι) : Continuous fun (f : (i : ι) → α i) (i : I) ↦ f i :=
  continuous_pi fun i : ↥I ↦ by apply continuous_apply

theorem continuous_proj₂ (I J : Set ι) (hIJ : J ⊆ I) :
    Continuous fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ :=
  continuous_pi fun i : ↥J ↦ by apply continuous_apply

theorem continuous_proj₂' (I J : Finset ι) (hIJ : J ⊆ I) :
    Continuous fun (f : (i : I) → α i) (i : J) ↦ f ⟨i, hIJ i.prop⟩ :=
  continuous_pi fun i : ↥J ↦ by apply continuous_apply

end Continuous

section isClosed_proj

open Filter

open scoped Topology Filter

variable {ι : Type _} {α : ι → Type _} [∀ i, TopologicalSpace (α i)] {s : Set (∀ i, α i)}

theorem continuous_cast {α β : Type _} [tα : TopologicalSpace α] [tβ : TopologicalSpace β]
    (h : α = β) (ht : HEq tα tβ) : Continuous fun x : α ↦ cast h x := by
  subst h
  convert continuous_id
  rw [← heq_iff_eq]
  exact ht.symm

def projCompl (α : ι → Type _) [∀ i, TopologicalSpace (α i)] (i : ι) (x : (i : ι) → α i) :
    (j : { k // k ≠ i }) → α j := fun j ↦ x j

lemma continuous_projCompl {i : ι} : Continuous (projCompl α i) :=
  continuous_pi fun _ ↦ continuous_apply _

def X (α : ι → Type _) [∀ i, TopologicalSpace (α i)] (i : ι) (s : Set ((j : ι) → α j)) :
    Set ((j : { k // k ≠ i }) → α j) := projCompl α i '' s

variable (i : ι) (x : ∀ i, α i)

lemma projCompl_mem (hx : x ∈ s) : projCompl α i x ∈ X α i s := by
  simp only [ne_eq, projCompl, X, mem_image]
  exact ⟨x, hx, rfl⟩

instance : TopologicalSpace (X α i s) := by rw [X]; infer_instance

lemma compactSpace_X (hs_compact : IsCompact s) : CompactSpace (X α i s) := by
  refine isCompact_iff_compactSpace.mp ?_
  refine IsCompact.image hs_compact ?_
  exact continuous_pi fun j ↦ continuous_apply _

def XY (α : ι → Type _) [∀ i, TopologicalSpace (α i)] (i : ι) (s : Set ((j : ι) → α j)) :
    Set ((j : ι) → α j) :=
  {x | projCompl α i x ∈ projCompl α i '' s}

lemma subset_xy : s ⊆ XY α i s := fun x hx ↦ ⟨x, hx, rfl⟩

lemma mem_xy_of_mem (hx : x ∈ s) : x ∈ XY α i s := subset_xy i hx

def fromXProd (α : ι → Type _) [∀ i, TopologicalSpace (α i)] (i : ι) (s : Set ((j : ι) → α j))
    [DecidableEq ι] :
    X α i s × α i → ∀ j, α j :=
  fun p j ↦
    if h : j = i then by refine cast ?_ p.2; rw [h] else (↑(p.1) : ∀ j : { k // k ≠ i }, α j) ⟨j, h⟩

lemma fromXProd_same (p : X α i s × α i) [DecidableEq ι] :
    fromXProd α i s p i = p.2 := by
  simp only [fromXProd, ne_eq, cast_eq, dite_true]

lemma projCompl_fromXProd (p : X α i s × α i) [DecidableEq ι] :
    projCompl α i (fromXProd α i s p) = p.1 := by
  ext1 j
  have : (j : ι) ≠ i := j.2
  simp only [fromXProd, projCompl]
  rw [dif_neg this]

lemma continuous_fromXProd [DecidableEq ι] : Continuous (fromXProd α i s) := by
  refine continuous_pi fun j ↦ ?_
  simp only [fromXProd]
  split_ifs with h
  · refine (continuous_cast _ ?_).comp continuous_snd
    rw [h]
  · exact (Continuous.comp (continuous_apply _) continuous_subtype_val).comp continuous_fst

lemma fromXProd_mem_XY (p : X α i s × α i) [DecidableEq ι] :
    fromXProd α i s p ∈ XY α i s := by
  simp only [XY, mem_image, mem_setOf_eq]
  obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
  exact ⟨y, hy_mem_s, hy_eq.trans (projCompl_fromXProd _ _).symm⟩

lemma fromXProd_projCompl (x : XY α i s) [DecidableEq ι] :
    fromXProd α i s ⟨⟨projCompl α i x, x.2⟩, (x : ∀ j, α j) i⟩ = (x : ∀ j, α j) := by
  ext1 j
  simp only [fromXProd, projCompl, ne_eq, dite_eq_right_iff]
  intro h
  rw [← heq_iff_eq]
  refine HEq.trans (cast_heq (_ : α i = α j) _) ?_
  rw [h]

def XYEquiv (α : ι → Type _) [∀ i, TopologicalSpace (α i)] (i : ι) (s : Set ((j : ι) → α j))
    [DecidableEq ι] :
    XY α i s ≃ₜ X α i s × α i :=
{ toFun := fun x ↦ ⟨⟨projCompl α i x, x.2⟩, (x : ∀ j, α j) i⟩
  invFun := fun p ↦ ⟨fromXProd α i s p, fromXProd_mem_XY _ p⟩
  left_inv := fun x ↦ by
    ext j
    simp only [ne_eq]
    rw [fromXProd_projCompl]
  right_inv := fun p ↦ by
    simp only [ne_eq]
    ext x
    · simp only
      rw [projCompl_fromXProd]
    · simp only
      exact fromXProd_same _ _
  continuous_toFun := by
    refine Continuous.prod_mk ?_ ?_
    · exact Continuous.subtype_mk (continuous_projCompl.comp continuous_subtype_val) _
    · exact (continuous_apply _).comp continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk (continuous_fromXProd _) _}

lemma snd_xyEquiv_preimage [DecidableEq ι] :
    Prod.snd '' (XYEquiv α i s '' ((fun (x : XY α i s) ↦ (x : ∀ j, α j)) ⁻¹' s))
      = (fun x : ∀ j, α j ↦ x i) '' s := by
  ext1 x
  simp only [ne_eq, XYEquiv, projCompl, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, mem_image,
    mem_preimage, Subtype.exists, exists_and_left, Prod.exists, Prod.mk.injEq, exists_and_right,
    exists_eq_right, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨y, _, z, hz_mem, _, hzx⟩
    exact ⟨z, hz_mem, hzx⟩
  · rintro ⟨z, hz_mem, hzx⟩
    exact ⟨projCompl α i z, projCompl_mem _ _ hz_mem, z, hz_mem, ⟨⟨mem_xy_of_mem _ _ hz_mem, rfl⟩, hzx⟩⟩

theorem isClosed_proj (hs_compact : IsCompact s) (hs_closed : IsClosed s) (i : ι) :
    IsClosed ((fun x : ∀ j, α j ↦ x i) '' s) := by
  let πi : (∀ j, α j) → α i := fun x : ∀ j, α j ↦ x i
  classical
  have h_image_eq : πi '' s
      = Prod.snd '' (XYEquiv α i s '' ((fun (x : XY α i s) ↦ (x : ∀ j, α j)) ⁻¹' s)) := by
    exact (snd_xyEquiv_preimage _).symm
  rw [h_image_eq]
  have : CompactSpace (X α i s) := compactSpace_X _ hs_compact
  refine isClosedMap_snd_of_compactSpace _ ?_
  rw [Homeomorph.isClosed_image]
  exact IsClosed.preimage continuous_subtype_val hs_closed

end isClosed_proj

end ProjectionMaps

section boxes

def box (t : (i : ι) → Set (α i)) (s : Finset ι) : Set ((i : ι) → α i) :=
  (s : Set ι).pi t

@[simp]
theorem mem_box (t : (i : ι) → Set (α i)) (s : Finset ι) (f : (i : ι) → α i) :
    f ∈ box t s ↔ ∀ i ∈ s, f i ∈ t i := by rw [box, mem_pi]; rfl

theorem box_congr {t₁ t₂ : (i : ι) → Set (α i)} (s : Finset ι) (h : ∀ i ∈ s, t₁ i = t₂ i) :
    box t₁ s = box t₂ s := by
  simp_rw [box]; rw [Set.pi_congr rfl]; exact h

theorem measurableSet_box [∀ i, MeasurableSpace (α i)] (t : (i : ι) → Set (α i)) (s : Finset ι)
    (h : ∀ i ∈ s, MeasurableSet (t i)) : MeasurableSet (box t s) :=
  MeasurableSet.pi (Finset.countable_toSet _) h

theorem box_inter (t₁ t₂ : (i : ι) → Set (α i)) (s₁ s₂ : Finset ι)
    (ht₁ : ∀ (i) (_ : i ∉ s₁), t₁ i = univ) (ht₂ : ∀ (i) (_ : i ∉ s₂), t₂ i = univ)
    [DecidableEq ι] :
    box (fun i ↦ t₁ i ∩ t₂ i) (s₁ ∪ s₂) = box t₁ s₁ ∩ box t₂ s₂ := by
  ext1 f
  rw [mem_inter_iff]
  simp_rw [mem_box]
  refine ⟨fun h ↦ ⟨fun i his₁ ↦ ?_, fun i his₂ ↦ ?_⟩, fun h i hi ↦ ?_⟩
  · exact inter_subset_left (h i (Finset.mem_union_left s₂ his₁))
  · exact inter_subset_right (h i (Finset.mem_union_right s₁ his₂))
  · rw [Finset.mem_union] at hi
    cases' hi with hi hi
    · by_cases hi2 : i ∈ s₂
      · exact ⟨h.1 i hi, h.2 i hi2⟩
      · refine ⟨h.1 i hi, ?_⟩
        rw [ht₂ i hi2]
        exact mem_univ _
    · by_cases hi1 : i ∈ s₁
      · exact ⟨h.1 i hi1, h.2 i hi⟩
      · refine ⟨?_, h.2 i hi⟩
        rw [ht₁ i hi1]
        exact mem_univ _

def boxes (C : (i : ι) → Set (Set (α i))) : Set (Set ((i : ι) → α i)) :=
  {S | ∃ s : Finset ι, ∃ t ∈ univ.pi C, S = box t s}

theorem boxes_eq_iUnion_image (C : ∀ i, Set (Set (α i))) :
    boxes C = ⋃ s : Finset ι, (fun t ↦ box t s) '' univ.pi C := by
  ext1 f
  rw [boxes, mem_iUnion]
  simp_rw [mem_image]
  simp only [mem_univ_pi, exists_prop, mem_setOf_eq]
  constructor <;> rintro ⟨s, t, ht, rfl⟩ <;> exact ⟨s, t, ht, rfl⟩

theorem isPiSystem_boxes {C : ∀ i, Set (Set (α i))} (hC : ∀ i, IsPiSystem (C i))
    (hC_univ : ∀ i, univ ∈ C i) : IsPiSystem (boxes C) := by
  rintro S₁ ⟨s₁, t₁, h₁, rfl⟩ S₂ ⟨s₂, t₂, h₂, rfl⟩ hst_nonempty
  classical
  let t₁' := s₁.piecewise t₁ fun i ↦ univ
  let t₂' := s₂.piecewise t₂ fun i ↦ univ
  have h1 : ∀ i ∈ s₁, t₁ i = t₁' i := fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h1' : ∀ (i) (_ : i ∉ s₁), t₁' i = univ := fun i hi ↦ Finset.piecewise_eq_of_not_mem _ _ _ hi
  have h2 : ∀ i ∈ s₂, t₂ i = t₂' i := fun i hi ↦ (Finset.piecewise_eq_of_mem _ _ _ hi).symm
  have h2' : ∀ (i) (_ : i ∉ s₂), t₂' i = univ := fun i hi ↦ Finset.piecewise_eq_of_not_mem _ _ _ hi
  rw [box_congr _ h1, box_congr _ h2]
  refine ⟨s₁ ∪ s₂, fun i ↦ t₁' i ∩ t₂' i, ?_, ?_⟩
  · rw [mem_pi]
    intro i _
    have : (t₁' i ∩ t₂' i).Nonempty := by
      obtain ⟨f, hf⟩ := hst_nonempty
      rw [box_congr _ h1, box_congr _ h2] at hf
      rw [mem_inter_iff, mem_box, mem_box] at hf
      refine ⟨f i, ⟨?_, ?_⟩⟩
      · by_cases hi₁ : i ∈ s₁
        · exact hf.1 i hi₁
        · rw [h1' i hi₁]
          exact mem_univ _
      · by_cases hi₂ : i ∈ s₂
        · exact hf.2 i hi₂
        · rw [h2' i hi₂]
          exact mem_univ _
    refine hC i _ ?_ _ ?_ this
    · by_cases hi₁ : i ∈ s₁
      · rw [← h1 i hi₁]
        exact h₁ i (mem_univ _)
      · rw [h1' i hi₁]
        exact hC_univ i
    · by_cases hi₂ : i ∈ s₂
      · rw [← h2 i hi₂]
        exact h₂ i (mem_univ _)
      · rw [h2' i hi₂]
        exact hC_univ i
  · rw [box_inter t₁' t₂' s₁ s₂ h1' h2']

variable (α)

theorem comap_eval_le_generateFrom_boxes_singleton [m : ∀ i, MeasurableSpace (α i)] (i : ι) :
    MeasurableSpace.comap (fun f : (i : ι) → α i ↦ f i) (m i) ≤
      MeasurableSpace.generateFrom
        ((fun t ↦ box t {i}) '' univ.pi fun i ↦ {s : Set (α i) | MeasurableSet s}) := by
  rw [MeasurableSpace.comap_eq_generateFrom]
  refine MeasurableSpace.generateFrom_mono fun S ↦ ?_
  simp only [mem_setOf_eq, mem_image, mem_univ_pi, forall_exists_index, and_imp]
  intro t ht h
  classical
  refine ⟨fun j ↦ if hji : j = i then by convert t else univ, fun j ↦ ?_, ?_⟩
  · by_cases hji : j = i
    · simp only [hji, eq_self_iff_true, eq_mpr_eq_cast, dif_pos]
      convert ht
      simp only [id_eq, cast_heq]
    · simp only [hji, not_false_iff, dif_neg, MeasurableSet.univ]
  · simp only [id_eq, eq_mpr_eq_cast, ← h]
    ext1 x
    simp only [mem_box, eq_mpr_eq_cast, Finset.mem_singleton, forall_eq, eq_self_iff_true, cast_eq,
      dite_eq_ite, if_true, mem_preimage]

variable {α}

theorem generateFrom_boxes [∀ i, MeasurableSpace (α i)] :
    MeasurableSpace.generateFrom (boxes fun i ↦ {s : Set (α i) | MeasurableSet s}) =
      @MeasurableSpace.pi ι α _ := by
  apply le_antisymm
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro S ⟨s, t, h, rfl⟩
    simp only [mem_univ_pi, mem_setOf_eq] at h
    exact measurableSet_box t s fun i _ ↦ h i
  · refine iSup_le fun i ↦ ?_
    refine (comap_eval_le_generateFrom_boxes_singleton α i).trans ?_
    refine MeasurableSpace.generateFrom_mono ?_
    rw [boxes_eq_iUnion_image]
    exact subset_iUnion
      (fun s ↦ (fun t : (i : ι) → Set (α i) ↦ box t s) '' univ.pi fun i ↦ setOf MeasurableSet)
      ({i} : Finset ι)

end boxes

section cylinder

def cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) : Set ((i : ι) → α i) :=
  (fun f : (i : ι) → α i ↦ fun i : s ↦ f i) ⁻¹' S

@[simp]
theorem mem_cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) (f : (i : ι) → α i) :
    f ∈ cylinder s S ↔ (fun i : s ↦ f i) ∈ S :=
  mem_preimage

theorem cylinder_empty (s : Finset ι) : cylinder s (∅ : Set (∀ i : s, α i)) = ∅ := by
  rw [cylinder, preimage_empty]

theorem cylinder_univ (s : Finset ι) : cylinder s (univ : Set (∀ i : s, α i)) = univ := by
  rw [cylinder, preimage_univ]

theorem cylinder_eq_empty_iff [h_nonempty : Nonempty ((i : ι) → α i)] (s : Finset ι)
    (S : Set (∀ i : s, α i)) : cylinder s S = ∅ ↔ S = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hS
    rw [← Ne, ← nonempty_iff_ne_empty] at hS
    let f := hS.some
    have hf : f ∈ S := hS.choose_spec
    classical
    let f' : (i : ι) → α i := fun i ↦ if hi : i ∈ s then f ⟨i, hi⟩ else h_nonempty.some i
    have hf' : f' ∈ cylinder s S := by
      rw [mem_cylinder]
      simp only [f', Finset.coe_mem, dif_pos]
      exact hf
    rw [h] at hf'
    exact not_mem_empty _ hf'
  · rw [h]; exact cylinder_empty _

theorem measurableSet_cylinder [∀ i, MeasurableSpace (α i)] (s : Finset ι)
    (S : Set (∀ i : s, α i)) (hS : MeasurableSet S) :
    MeasurableSet (cylinder s S) := by
  rw [cylinder]; exact measurableSet_preimage (measurable_proj _) hS

theorem inter_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (∀ i : s₁, α i)) (S₂ : Set (∀ i : s₂, α i))
    [DecidableEq ι] :
    cylinder s₁ S₁ ∩ cylinder s₂ S₂ =
      cylinder (s₁ ∪ s₂)
        ((fun f ↦ fun j : s₁ ↦ f ⟨j, Finset.mem_union_left s₂ j.prop⟩) ⁻¹' S₁ ∩
          (fun f ↦ fun j : s₂ ↦ f ⟨j, Finset.mem_union_right s₁ j.prop⟩) ⁻¹' S₂) := by
  ext1 f; simp only [mem_inter_iff, mem_cylinder, mem_setOf_eq]; rfl

theorem union_cylinder (s₁ s₂ : Finset ι) (S₁ : Set (∀ i : s₁, α i)) (S₂ : Set (∀ i : s₂, α i))
    [DecidableEq ι] :
    cylinder s₁ S₁ ∪ cylinder s₂ S₂ =
      cylinder (s₁ ∪ s₂)
        ((fun f ↦ fun j : s₁ ↦ f ⟨j, Finset.mem_union_left s₂ j.prop⟩) ⁻¹' S₁ ∪
          (fun f ↦ fun j : s₂ ↦ f ⟨j, Finset.mem_union_right s₁ j.prop⟩) ⁻¹' S₂) := by
  ext1 f; simp only [mem_union, mem_cylinder, mem_setOf_eq]; rfl

theorem compl_cylinder (s : Finset ι) (S : Set (∀ i : s, α i)) :
    (cylinder s S)ᶜ = cylinder s (Sᶜ) := by
  ext1 f; simp only [mem_compl_iff, mem_cylinder]

theorem diff_cylinder_same (s : Finset ι) (S T : Set (∀ i : s, α i)) :
    cylinder s S \ cylinder s T = cylinder s (S \ T) := by
  ext1 f; simp only [mem_diff, mem_cylinder]

theorem eq_of_cylinder_eq_of_subset [h_nonempty : Nonempty ((i : ι) → α i)] {I J : Finset ι}
    {S : Set (∀ i : I, α i)} {T : Set (∀ i : J, α i)} (h_eq : cylinder I S = cylinder J T)
    (hJI : J ⊆ I) :
    S = (fun f : ∀ i : I, α i ↦ fun j : J ↦ f ⟨j, hJI j.prop⟩) ⁻¹' T := by
  rw [Set.ext_iff] at h_eq
  simp only [mem_cylinder] at h_eq
  ext1 f
  simp only [mem_preimage]
  classical
  specialize h_eq fun i ↦ if hi : i ∈ I then f ⟨i, hi⟩ else h_nonempty.some i
  have h_mem : ∀ j : J, ↑j ∈ I := fun j ↦ hJI j.prop
  simp only [Finset.coe_mem, dite_true, h_mem] at h_eq
  exact h_eq

theorem cylinder_eq_cylinder_union [DecidableEq ι] (I : Finset ι) (S : Set (∀ i : I, α i))
    (J : Finset ι) :
    cylinder I S =
      cylinder (I ∪ J) ((fun f ↦ fun j : I ↦ f ⟨j, Finset.mem_union_left J j.prop⟩) ⁻¹' S) := by
  ext1 f; simp only [mem_cylinder, mem_preimage]

theorem disjoint_cylinder_iff [Nonempty ((i : ι) → α i)] {s t : Finset ι} {S : Set (∀ i : s, α i)}
    {T : Set (∀ i : t, α i)} [DecidableEq ι] :
    Disjoint (cylinder s S) (cylinder t T) ↔
      Disjoint
        ((fun f : ∀ i : (s ∪ t : Finset ι), α i
          ↦ fun j : s ↦ f ⟨j, Finset.mem_union_left t j.prop⟩) ⁻¹' S)
        ((fun f ↦ fun j : t ↦ f ⟨j, Finset.mem_union_right s j.prop⟩) ⁻¹' T) := by
  simp_rw [Set.disjoint_iff, subset_empty_iff, inter_cylinder, cylinder_eq_empty_iff]

theorem isClosed_cylinder [∀ i, TopologicalSpace (α i)] (I : Finset ι) (s : Set (∀ i : I, α i))
    (hs : IsClosed s) : IsClosed (cylinder I s) :=
  hs.preimage (continuous_proj _)

end cylinder

section cylinders

variable [∀ i, MeasurableSpace (α i)]

variable (α)

def cylinders : Set (Set ((i : ι) → α i)) :=
  ⋃ (s) (S) (_ : MeasurableSet S), {cylinder s S}

theorem empty_mem_cylinders : ∅ ∈ cylinders α := by
  simp_rw [cylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, MeasurableSet.empty, (cylinder_empty _).symm⟩

variable {α}

@[simp]
theorem mem_cylinders (t : Set ((i : ι) → α i)) :
    t ∈ cylinders α ↔ ∃ (s S : _) (_ : MeasurableSet S), t = cylinder s S := by
  simp_rw [cylinders, mem_iUnion, mem_singleton_iff]

noncomputable def cylinders.finset {t : Set ((i : ι) → α i)} (ht : t ∈ cylinders α) : Finset ι :=
  ((mem_cylinders t).mp ht).choose

def cylinders.set {t : Set ((i : ι) → α i)} (ht : t ∈ cylinders α) :
    Set (∀ i : cylinders.finset ht, α i) :=
  ((mem_cylinders t).mp ht).choose_spec.choose

theorem cylinders.measurableSet {t : Set ((i : ι) → α i)} (ht : t ∈ cylinders α) :
    MeasurableSet (cylinders.set ht) :=
  ((mem_cylinders t).mp ht).choose_spec.choose_spec.choose

theorem cylinders.eq_cylinder {t : Set ((i : ι) → α i)} (ht : t ∈ cylinders α) :
    t = cylinder (cylinders.finset ht) (cylinders.set ht) :=
  ((mem_cylinders t).mp ht).choose_spec.choose_spec.choose_spec

theorem cylinder_mem_cylinders (s : Finset ι) (S : Set (∀ i : s, α i)) (hS : MeasurableSet S) :
    cylinder s S ∈ cylinders α := by rw [mem_cylinders]; exact ⟨s, S, hS, rfl⟩

theorem inter_mem_cylinders {s t : Set (∀ i : ι, α i)} (hs : s ∈ cylinders α)
    (ht : t ∈ cylinders α) : s ∩ t ∈ cylinders α := by
  rw [mem_cylinders] at *
  obtain ⟨s₁, S₁, hS₁, rfl⟩ := hs
  obtain ⟨s₂, S₂, hS₂, rfl⟩ := ht
  classical
  refine ⟨s₁ ∪ s₂,
    (fun f ↦ (fun i ↦ f ⟨i, Finset.mem_union_left s₂ i.prop⟩ : ∀ i : s₁, α i)) ⁻¹' S₁ ∩
      {f | (fun i ↦ f ⟨i, Finset.mem_union_right s₁ i.prop⟩ : ∀ i : s₂, α i) ∈ S₂}, ?_, ?_⟩
  · refine MeasurableSet.inter ?_ ?_
    · exact (measurable_proj₂' (s₁ ∪ s₂) s₁ Finset.subset_union_left) hS₁
    · exact (measurable_proj₂' (s₁ ∪ s₂) s₂ Finset.subset_union_right) hS₂
  · exact inter_cylinder _ _ _ _

theorem compl_mem_cylinders {s : Set (∀ i : ι, α i)} (hs : s ∈ cylinders α) :
    sᶜ ∈ cylinders α := by
  rw [mem_cylinders] at hs ⊢
  obtain ⟨s, S, hS, rfl⟩ := hs
  refine ⟨s, Sᶜ, hS.compl, ?_⟩
  rw [compl_cylinder]

variable (α)

theorem univ_mem_cylinders : Set.univ ∈ cylinders α := by
  rw [← compl_empty]; exact compl_mem_cylinders (empty_mem_cylinders α)

variable {α}

theorem union_mem_cylinders {s t : Set (∀ i : ι, α i)} (hs : s ∈ cylinders α)
    (ht : t ∈ cylinders α) : s ∪ t ∈ cylinders α := by
  rw [union_eq_compl_compl_inter_compl]
  exact compl_mem_cylinders (inter_mem_cylinders (compl_mem_cylinders hs) (compl_mem_cylinders ht))

theorem diff_mem_cylinders {s t : Set (∀ i : ι, α i)} (hs : s ∈ cylinders α)
    (ht : t ∈ cylinders α) : s \ t ∈ cylinders α := by
  rw [diff_eq_compl_inter]; exact inter_mem_cylinders (compl_mem_cylinders ht) hs

theorem isPiSystem_cylinders : IsPiSystem (cylinders α) := fun _ hS _ hT _ ↦
  inter_mem_cylinders hS hT

theorem setField_cylinders : SetField (cylinders α) :=
  { empty_mem := empty_mem_cylinders α
    univ_mem := univ_mem_cylinders α
    union_mem := union_mem_cylinders
    diff_mem := diff_mem_cylinders }

theorem setRing_cylinders : MeasureTheory.SetRing (cylinders α) :=
  setField_cylinders.toSetRing

theorem setSemiringCylinders : MeasureTheory.SetSemiring (cylinders α) :=
  setField_cylinders.setSemiring

theorem iUnion_le_mem_cylinders {s : ℕ → Set (∀ i : ι, α i)} (hs : ∀ n, s n ∈ cylinders α)
    (n : ℕ) :
    (⋃ i ≤ n, s i) ∈ cylinders α :=
  setField_cylinders.iUnion_le_mem hs n

theorem iInter_le_mem_cylinders {s : ℕ → Set (∀ i : ι, α i)} (hs : ∀ n, s n ∈ cylinders α)
    (n : ℕ) :
    (⋂ i ≤ n, s i) ∈ cylinders α :=
  setField_cylinders.iInter_le_mem hs n

theorem generateFrom_cylinders :
    MeasurableSpace.generateFrom (cylinders α) = MeasurableSpace.pi := by
  apply le_antisymm
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro S hS
    obtain ⟨s, S, hSm, rfl⟩ := (mem_cylinders _).mp hS
    exact measurableSet_cylinder s S hSm
  · refine iSup_le fun i ↦ ?_
    refine (comap_eval_le_generateFrom_boxes_singleton α i).trans ?_
    refine MeasurableSpace.generateFrom_mono (fun x ↦ ?_)
    simp only [mem_image, mem_univ_pi, mem_setOf_eq, mem_cylinders, exists_prop,
      forall_exists_index, and_imp]
    rintro t ht rfl
    refine ⟨{i}, ?_, ?_, ?_⟩
    · exact {f | f ⟨i, Finset.mem_singleton_self i⟩ ∈ t i}
    · exact (measurable_pi_apply _) (ht i)
    · ext1 x
      simp only [mem_box, Finset.mem_singleton, forall_eq, mem_cylinder, mem_setOf_eq]

end cylinders

section closedCompactCylinders

variable [∀ i, TopologicalSpace (α i)]

variable (α)

def closedCompactCylinders : Set (Set ((i : ι) → α i)) :=
  ⋃ (s) (S) (_ : IsClosed S) (_ : IsCompact S), {cylinder s S}

theorem empty_mem_closedCompactCylinders : ∅ ∈ closedCompactCylinders α := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]
  exact ⟨∅, ∅, isClosed_empty, isCompact_empty, (cylinder_empty _).symm⟩

variable {α}

@[simp]
theorem mem_closedCompactCylinders (t : Set ((i : ι) → α i)) :
    t ∈ closedCompactCylinders α
      ↔ ∃ (s S : _) (_ : IsClosed S) (_ : IsCompact S), t = cylinder s S := by
  simp_rw [closedCompactCylinders, mem_iUnion, mem_singleton_iff]

noncomputable def closedCompactCylinders.finset {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    Finset ι :=
  ((mem_closedCompactCylinders t).mp ht).choose

def closedCompactCylinders.set {t : Set ((i : ι) → α i)} (ht : t ∈ closedCompactCylinders α) :
    Set (∀ i : closedCompactCylinders.finset ht, α i) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose

theorem closedCompactCylinders.isClosed {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    IsClosed (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.choose

theorem closedCompactCylinders.isCompact {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    IsCompact (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.choose_spec.choose

theorem closedCompactCylinders.eq_cylinder {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    t = cylinder (closedCompactCylinders.finset ht) (closedCompactCylinders.set ht) :=
  ((mem_closedCompactCylinders t).mp ht).choose_spec.choose_spec.choose_spec.choose_spec

theorem cylinder_mem_closedCompactCylinders (s : Finset ι) (S : Set (∀ i : s, α i))
    (hS_closed : IsClosed S) (hS_compact : IsCompact S) :
    cylinder s S ∈ closedCompactCylinders α := by
  rw [mem_closedCompactCylinders]
  exact ⟨s, S, hS_closed, hS_compact, rfl⟩

theorem mem_cylinder_of_mem_closedCompactCylinders [∀ i, MeasurableSpace (α i)]
    [∀ i, SecondCountableTopology (α i)] [∀ i, OpensMeasurableSpace (α i)]
    {t : Set ((i : ι) → α i)}
    (ht : t ∈ closedCompactCylinders α) :
    t ∈ cylinders α := by
  rw [mem_cylinders]
  refine ⟨closedCompactCylinders.finset ht, closedCompactCylinders.set ht, ?_, ?_⟩
  · exact (closedCompactCylinders.isClosed ht).measurableSet
  · exact closedCompactCylinders.eq_cylinder ht

end closedCompactCylinders
