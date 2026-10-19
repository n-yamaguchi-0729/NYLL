/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.HenselianLocalGeometricSection
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Prescribed geometric lifts from a strictly local spectrum

An étale morphism admits a unique lift of a map from a strictly local
spectrum once a field-valued point over its closed point has been fixed.
The construction applies the actual section theorem to the fiber product.
The pointing field can be any extension of the residue field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace AlgebraicGeometry.Etale

universe u

/-- A prescribed field point over the closed point of a strictly local
spectrum lifts uniquely along an arbitrary étale morphism. -/
theorem existsUnique_lift_of_closedFieldPoint
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f]
    (b : Spec (.of R) ⟶ Y) {Ω : Type u} [Field Ω]
    (j : Spec (.of Ω) ⟶ Spec (.of R))
    (hj : j default = IsLocalRing.closedPoint R)
    (s : Spec (.of Ω) ⟶ X) (hs : s ≫ f = j ≫ b) :
    ∃! l : Spec (.of R) ⟶ X, l ≫ f = b ∧ j ≫ l = s := by
  let p : Spec (.of Ω) ⟶ pullback f b := pullback.lift s j hs
  obtain ⟨σ, hσ, hUnique⟩ := existsUnique_section_of_closedFieldPoint R
    (pullback.snd f b) j hj p (pullback.lift_snd _ _ _)
  have hbase : (σ ≫ pullback.fst f b) ≫ f = b := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ.1, Category.id_comp]
  have hpoint : j ≫ (σ ≫ pullback.fst f b) = s := by
    rw [← Category.assoc, hσ.2]
    exact pullback.lift_fst _ _ _
  refine ⟨σ ≫ pullback.fst f b, ⟨hbase, hpoint⟩, ?_⟩
  intro l hl
  let a : Spec (.of R) ⟶ pullback f b := pullback.lift l (𝟙 _)
    (by rw [hl.1, Category.id_comp])
  have ha : a ≫ pullback.snd f b = 𝟙 _ := pullback.lift_snd _ _ _
  have hpa : j ≫ a = p := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
      exact hl.2
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
  have heq : a = σ := hUnique a ⟨ha, hpa⟩
  calc
    l = a ≫ pullback.fst f b := (pullback.lift_fst _ _ _).symm
    _ = σ ≫ pullback.fst f b := congrArg (fun q => q ≫ pullback.fst f b) heq

end AlgebraicGeometry.Etale
