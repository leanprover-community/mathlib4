/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Inseparable
import Mathlib.Topology.SubsetProperties

/-!
# Alexandrov-discrete topological spaces

This file defines Alexandrov-discrete spaces, aka finitely generated spaces.

A space is Alexandrov-discrete if the (arbitrary) intersection of open sets is open.

## TODO

Rest of the API

## Tags

Alexandroff, discrete, finitely generated, fg space
-/

open Set TopologicalSpace

/-- A topological space is **Alexandrov-discrete** or **finitely generated** if the intersection of
a family of open sets is open. -/
class AlexandrovDiscrete (α : Type*) [TopologicalSpace α] : Prop where
  /-- The intersection of a family of open sets is an open set. Use `isOpen_sInter` in the root
  namespace instead. -/
  protected isOpen_sInter : ∀ s : Set (Set α), (∀ t ∈ s, IsOpen t) → IsOpen (⋂₀ s)

variable {ι : Sort*} {α : Type*} [TopologicalSpace α] [AlexandrovDiscrete α] {S : Set (Set α)}
  {f : ι → Set α}

lemma isOpen_sInter : (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S) := AlexandrovDiscrete.isOpen_sInter _

lemma isOpen_iInter (hf : ∀ i, IsOpen (f i)) : IsOpen (⋂ i, f i) :=
isOpen_sInter $ forall_range_iff.2 hf

lemma isClosed_sUnion (hS : ∀ s ∈ S, IsClosed s) : IsClosed (⋃₀ S) := by
  simp only [←isOpen_compl_iff, compl_sUnion] at hS ⊢; exact isOpen_sInter $ ball_image_iff.2 hS

lemma isClosed_iUnion (hf : ∀ i, IsClosed (f i)) : IsClosed (⋃ i, f i) :=
isClosed_sUnion $ forall_range_iff.2 hf

lemma isClopen_sUnion (hS : ∀ s ∈ S, IsClopen s) : IsClopen (⋃₀ S) :=
⟨isOpen_sUnion λ s hs ↦ (hS s hs).1, isClosed_sUnion λ s hs ↦ (hS s hs).2⟩

lemma isClopen_iUnion (hf : ∀ i, IsClopen (f i)) : IsClopen (⋃ i, f i) :=
⟨isOpen_iUnion λ i ↦ (hf i).1, isClosed_iUnion λ i ↦ (hf i).2⟩
