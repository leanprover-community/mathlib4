import Mathlib.RingTheory.EGA48.InverseLimit

universe u

open AlgebraicGeometry CategoryTheory Limits

section

instance AlgebraicGeometry.Scheme.Cover.nonempty_of_nonempty {P : MorphismProperty Scheme}
    {X : Scheme.{u}}
    [Nonempty X] (𝒰 : X.Cover P) :
    Nonempty 𝒰.J :=
  Nonempty.map 𝒰.f ‹_›

end

variable {I : Type*} {S X : Scheme.{u}} [Category I]
  (D : I ⥤ Scheme.{u})
  (t : D ⟶ (Functor.const I).obj S)
  (f : X ⟶ S)
  (c : Cone D) (hc : IsLimit c)

lemma nonempty_of_nonempty [∀ i, Nonempty (D.obj i)]
    [∀ i, CompactSpace (D.obj i)] :
    Nonempty c.pt :=
  sorry

lemma exists_mem_of_isClosed_of_nonempty
    {j : I}
    (Z : ∀ (i : I) (hij : i ⟶ j), Set (D.obj i))
    (hZc : ∀ (i : I) (hij : i ⟶ j), IsClosed (Z i hij))
    (hZne : ∀ i hij, (Z i hij).Nonempty)
    (hstab : ∀ (i i' : I) (hi'i : i' ⟶ i) (hij : i ⟶ j) ,
      (D.map hi'i).base '' Z i' (hi'i ≫ hij) ⊆ Z i hij) :
    ∃ (s : c.pt), ∀ i hij, (c.π.app i).base s ∈ Z i hij :=
  sorry

lemma CommRingCat.exists_ge_ge_comp_eq_comp_of_finiteType [IsFiltered I]
    {A R : CommRingCat} (f : R ⟶ A) (hf : f.hom.FiniteType)
    (D : I ⥤ CommRingCat.{u})
    (t : (Functor.const I).obj R ⟶ D)
    (c : Cocone D) (hc : IsColimit c)
    {i : I} (a : A ⟶ D.obj i) (ha : t.app i = f ≫ a)
    {j : I} (b : A ⟶ D.obj j) (hb : t.app j = f ≫ b)
    (hab : a ≫ c.ι.app i = b ≫ c.ι.app j) :
    ∃ (k : I) (hik : i ⟶ k) (hjk : j ⟶ k),
      a ≫ D.map hik = b ≫ D.map hjk :=
  sorry

lemma Scheme.FiniteType.exists_ge_ge_comp_eq_comp_of_isAffine
    [IsAffine X] [∀ i, IsAffine (D.obj i)] [IsAffine c.pt]
    [∀ i, CompactSpace (D.obj i)]
    [LocallyOfFiniteType f]
    [IsCofiltered I]
    {i : I} (a : D.obj i ⟶ X) (ha : t.app i = a ≫ f)
    {j : I} (b : D.obj j ⟶ X) (hb : t.app j = b ≫ f)
    (hab : c.π.app i ≫ a = c.π.app j ≫ b) :
    ∃ (k : I) (hik : k ⟶ i) (hjk : k ⟶ j),
      D.map hik ≫ a = D.map hjk ≫ b := by
  sorry

section

variable [∀ i, CompactSpace (D.obj i)]
    [LocallyOfFiniteType f]
    [IsCofiltered I]

structure Aux where
  i : I
  a : D.obj i ⟶ X
  ha : t.app i = a ≫ f
  b : D.obj i ⟶ X
  hb : t.app i = b ≫ f
  hab : c.π.app i ≫ a = c.π.app i ≫ b
  𝒰S : S.OpenCover
  𝒰X (i : (Scheme.Cover.pullbackCover 𝒰S f).J) : ((𝒰S.pullbackCover f).obj i).OpenCover

namespace Aux

noncomputable section

variable {D t f c}
variable (A : Aux D t f c)

lemma exists_index : ∃ (i' : I) (hii' : i' ⟶ A.i),
    ((D.map hii' ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb)).base ⁻¹'
      ((Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X : Set <|
        ↑(pullback f f))ᶜ)) = ∅ := by
  let W := Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X
  by_contra! h
  let Z (i' : I) (hii' : i' ⟶ A.i) :=
    (D.map hii' ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb)).base ⁻¹'
      W.carrierᶜ
  obtain ⟨s, hs⟩ := exists_mem_of_isClosed_of_nonempty D c Z
    (fun _ _ ↦ (W.isOpen.isClosed_compl).preimage <| Scheme.Hom.continuous _) h
    (by
      intro i i' hii' hij
      simp [Z]
      simp_rw [← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.comp_base, ← Category.assoc,
        ← D.map_comp]
      rfl)
  have := hs A.i (𝟙 A.i)
  simp [Z] at this
  apply this
  apply Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange
  rw [← Scheme.comp_base_apply]
  use (c.π.app A.i ≫ A.a).base s
  rw [← Scheme.comp_base_apply]
  congr 4
  apply pullback.hom_ext <;> simp [hab]

def i' : I := A.exists_index.choose

def hii' : A.i' ⟶ A.i := A.exists_index.choose_spec.choose

def g := (D.map A.hii' ≫ pullback.lift A.a A.b (A.ha.symm.trans A.hb))

lemma range_g_subset :
    Set.range A.g.base ⊆ Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X := by
  have heq := A.exists_index.choose_spec.choose_spec
  simp at heq
  simp [Aux.hii', g]
  exact heq

noncomputable def 𝒰D : Scheme.OpenCover.{u} (D.obj A.i') :=
    .mkOfCovers (Σ i : A.𝒰S.J, (A.𝒰X i).J) _
      (fun i ↦ ((Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X).pullbackCover A.g).map ⟨i.1, i.2, i.2⟩)
      (by
        intro x
        have := A.range_g_subset ⟨x, rfl⟩
        simp only [Scheme.Cover.pullbackCover_obj, Scheme.Pullback.openCoverOfBase_J,
          Scheme.Pullback.openCoverOfBase_obj, Scheme.Pullback.openCoverOfLeftRight_J,
          Scheme.Cover.pullbackCover_map, Sigma.exists]
        simp_rw [← Set.mem_range]
        simp_rw [Scheme.Pullback.range_fst]
        simpa [Scheme.Pullback.diagonalCoverDiagonalRange] using this)

attribute [-simp] cast_eq eq_mpr_eq_cast

def D' (j : A.𝒰D.J) : Over A.i' ⥤ Scheme where
  obj o := (A.𝒰D.pullbackCover (D.map o.hom)).obj j
  map ou := pullback.map _ _ _ _ (D.map ou.left)
    (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← D.map_comp, Over.w ou]) rfl
  map_id _ := by
    apply pullback.hom_ext <;> simp
  map_comp _ _ := by
    apply pullback.hom_ext <;> simp

set_option maxHeartbeats 0
def c' (j : A.𝒰D.J) : Cone (A.D' j) :=
  { pt := pullback (c.π.app A.i ≫ A.a) ((A.𝒰X j.1).map j.2 ≫ (A.𝒰S.pullbackCover f).map j.1)
    π :=
      { app ou := by
          dsimp [D', 𝒰D]
          refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
          refine pullback.map
            _ _ _ _
            (c.π.app ou.left)
            (pullback.diagonal _)
            (pullback.diagonal f) ?_ ?_ 
          · apply pullback.hom_ext <;> simp [g]; exact A.hab
          · apply pullback.hom_ext <;>
              simp [g, Scheme.Pullback.diagonalCover_map]
        naturality o u ou := by
          apply pullback.hom_ext <;>
            simp [g, A.hab, D', Scheme.Cover.pullbackCover,
              Scheme.Pullback.diagonalCover, Scheme.Cover.pullbackHom, 𝒰D]
          apply pullback.hom_ext <;>
            simp [g, A.hab, D', 𝒰D]
        } }

def hc' (j : A.𝒰D.J) : IsLimit (A.c' j) := sorry

lemma exists_eq (j : A.𝒰D.J) : ∃ (k : I) (hki' : k ⟶ A.i'),
    (A.𝒰D.pullbackCover (D.map hki')).map j ≫ D.map (hki' ≫ A.hii') ≫ A.a =
      (A.𝒰D.pullbackCover (D.map hki')).map j ≫ D.map (hki' ≫ A.hii') ≫ A.b :=
  sorry

end

set_option maxHeartbeats 0
lemma Scheme.FiniteType.exists_ge_ge_comp_eq_comp
    [∀ i, CompactSpace (D.obj i)]
    [LocallyOfFiniteType f]
    [IsCofiltered I]
    {i : I} (a : D.obj i ⟶ X) (ha : t.app i = a ≫ f)
    {j : I} (b : D.obj j ⟶ X) (hb : t.app j = b ≫ f)
    (hab : c.π.app i ≫ a = c.π.app j ≫ b) :
    ∃ (k : I) (hik : k ⟶ i) (hjk : k ⟶ j),
      D.map hik ≫ a = D.map hjk ≫ b := by
  classical
  wlog h : i = j
  · let o := IsCofiltered.min i j
    have := this D t f c (D.map (IsCofiltered.minToLeft i j) ≫ a)
      (by simp [← ha])
      (D.map (IsCofiltered.minToRight i j) ≫ b)
      (by simp [← hb]) (by simpa)
      rfl
    obtain ⟨k, hik, hjk, heq⟩ := this
    use k, hik ≫ IsCofiltered.minToLeft i j, hjk ≫ IsCofiltered.minToRight i j
    simpa using heq
  subst h
  let A : Aux D t f c :=
    { i := i
      a := a
      ha := ha
      b := b
      hb := hb
      hab := hab
      𝒰S := S.affineCover
      𝒰X i := Scheme.affineCover _ }
  let 𝒰 := Scheme.Pullback.diagonalCover f A.𝒰S A.𝒰X
  let W := Scheme.Pullback.diagonalCoverDiagonalRange f A.𝒰S A.𝒰X
  have := A.exists_eq
  choose k hki' heq using this
  let 𝒰Df := A.𝒰D.finiteSubcover
  cases' isEmpty_or_nonempty (D.obj A.i') with h h
  · use A.i', A.hii', A.hii'
    apply isInitialOfIsEmpty.hom_ext
  let O : Finset I := {A.i'} ∪ Finset.univ.image (fun i : 𝒰Df.J ↦ k <| A.𝒰D.f i.1)
  let o := Nonempty.some (inferInstanceAs <| Nonempty 𝒰Df.J)
  have ho : k (A.𝒰D.f o.1) ∈ O := by
    simp [O]
  obtain ⟨l, hl1, hl2⟩ := IsCofiltered.inf_exists O
    (Finset.univ.image (fun i : 𝒰Df.J ↦
      ⟨k <| A.𝒰D.f i.1, A.i', by simp [O], by simp [O], hki' <| A.𝒰D.f i.1⟩))
  have (w v : 𝒰Df.J) :
      hl1 (by simp [O]) ≫ hki' (A.𝒰D.f w.1) = hl1 (by simp [O]) ≫ hki' (A.𝒰D.f v.1) := by
    trans hl1 (show A.i' ∈ O by simp [O])
    apply hl2
    apply Finset.mem_image_of_mem
    simp
    symm
    apply hl2
    apply Finset.mem_image_of_mem
    simp
  simp [-Finset.mem_union, Finset.forall_mem_union, O] at hl2
  refine ⟨l, ?_, ?_, ?_⟩
  · exact hl1 ho ≫ hki' _ ≫ A.hii'
  · exact hl1 ho ≫ hki' _ ≫ A.hii'
  · apply (𝒰Df.pullbackCover (D.map <| hl1 ho ≫ hki' _)).hom_ext
    intro u
    let F : pullback (D.map (hl1 ho ≫ hki' (A.𝒰D.f o.1))) (𝒰Df.map u) ⟶
        pullback (D.map (hki' <| A.𝒰D.f u.1)) (A.𝒰D.map <| A.𝒰D.f u.1) :=
      pullback.map _ _ _ _ (D.map <| hl1 (by simp [O]))
        (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← D.map_comp, this]) rfl
    have hF : F ≫ pullback.fst (D.map (hki' _)) (A.𝒰D.map _) =
        pullback.fst _ _ ≫ D.map (hl1 (by simp [O])) := by
      simp [F]
    simp [Scheme.Cover.pullbackCover_map] at heq ⊢
    simp_rw [← D.map_comp_assoc, reassoc_of% this o u, D.map_comp_assoc]
    rw [← reassoc_of% hF, ← reassoc_of% hF]
    rw [heq]

end Aux

end
