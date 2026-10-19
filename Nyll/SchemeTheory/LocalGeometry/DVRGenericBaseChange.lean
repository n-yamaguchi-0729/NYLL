/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.FieldExtensions.DVRFractionFieldAway
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The generic open after a DVR base extension

Let `C` be a DVR over `B`, and let its actual fraction field `L` also
extend a coefficient ring `K` over `B`. Inverting a nonzero nonunit of
`C` gives `L`. Pullback pasting therefore identifies the generic open
of `X ×[Spec B] Spec C` with the coefficient extension to `L` of
`X ×[Spec B] Spec K`.

Both the original scheme coordinate and the fraction field coordinate
are retained. This permits a cover descended to a finite coefficient
field to be used on the actual generic open of a normalized DVR base.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SchemeTheory

universe u

/-- The generic open after extending the base to a DVR is the actual
coefficient extension of the original generic fibre. The comparison
preserves both projections, using the given compatible algebra maps. -/
theorem exists_dvrGenericBaseChangeIso
    (B C K L : Type u) [CommRing B] [CommRing C] [CommRing K] [Field L]
    [IsDomain C] [IsDiscreteValuationRing C]
    [Algebra B C] [Algebra B K] [Algebra C L] [Algebra K L] [Algebra B L]
    [IsScalarTower B C L] [IsScalarTower B K L] [IsFractionRing C L]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of B))
    (π : C) (hπ0 : π ≠ 0) (hπ : ¬ IsUnit π) :
    let β := Spec.map (CommRingCat.ofHom (algebraMap B C))
    let η := Spec.map (CommRingCat.ofHom (algebraMap B K))
    let ψ := Spec.map (CommRingCat.ofHom (algebraMap K L))
    let μ := Spec.map (CommRingCat.ofHom (algebraMap C L))
    let ε := Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away π)))
    ∃ δ : Spec (.of (Localization.Away π)) ≅ Spec (.of L),
      δ.hom ≫ μ = ε ∧
      ∃ e : pullback (pullback.snd f β) ε ≅ pullback ψ (pullback.snd f η),
        e.hom ≫ pullback.snd ψ (pullback.snd f η) ≫ pullback.fst f η =
          pullback.fst (pullback.snd f β) ε ≫ pullback.fst f β ∧
        e.hom ≫ pullback.fst ψ (pullback.snd f η) =
          pullback.snd (pullback.snd f β) ε ≫ δ.hom := by
  intro β η ψ μ ε
  have : IsLocalization.Away π L :=
    isLocalizationAway_fractionField_of_isDiscreteValuationRing C L π hπ0 hπ
  let eRing : L ≃ₐ[C] Localization.Away π :=
    IsLocalization.algEquiv (Submonoid.powers π) L (Localization.Away π)
  let δ : Spec (.of (Localization.Away π)) ≅ Spec (.of L) :=
    Scheme.Spec.mapIso eRing.toRingEquiv.toCommRingCatIso.op
  have hδ : δ.hom ≫ μ = ε := by
    change Spec.map (CommRingCat.ofHom eRing.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C L)) = ε
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact eRing.toAlgHom.comp_algebraMap
  have hcomp : μ ≫ β = ψ ≫ η := by
    change Spec.map (CommRingCat.ofHom (algebraMap C L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B C)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B K))
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsScalarTower.algebraMap_eq B C L).symm.trans
      (IsScalarTower.algebraMap_eq B K L)
  have : IsIso δ.hom := δ.isIso_hom
  let a : pullback (pullback.snd f β) ε ⟶ pullback (pullback.snd f β) μ :=
    pullback.map (pullback.snd f β) ε (pullback.snd f β) μ
      (𝟙 (pullback f β)) δ.hom (𝟙 (Spec (.of C)))
      (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id]; exact hδ.symm)
  have : IsIso a := inferInstance
  have haFst : a ≫ pullback.fst (pullback.snd f β) μ =
      pullback.fst (pullback.snd f β) ε := by
    simp only [a, pullback.lift_fst, Category.comp_id]
  have haSnd : a ≫ pullback.snd (pullback.snd f β) μ =
      pullback.snd (pullback.snd f β) ε ≫ δ.hom := by
    exact pullback.lift_snd _ _ _
  let e : pullback (pullback.snd f β) ε ≅ pullback ψ (pullback.snd f η) :=
    asIso a ≪≫ pullbackLeftPullbackSndIso f β μ ≪≫
      pullback.congrHom rfl hcomp ≪≫ (pullbackLeftPullbackSndIso f η ψ).symm ≪≫
        pullbackSymmetry (pullback.snd f η) ψ
  refine ⟨δ, hδ, e, ?_, ?_⟩
  · calc
      _ = a ≫ pullback.fst (pullback.snd f β) μ ≫ pullback.fst f β := by
        simp only [e, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
          pullbackSymmetry_hom_comp_snd_assoc, pullbackLeftPullbackSndIso_inv_fst,
          pullback.congrHom_hom, pullback.lift_fst, Category.comp_id,
          pullbackLeftPullbackSndIso_hom_fst]
      _ = _ := by rw [← Category.assoc, haFst]
  · simp only [e, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
      pullbackSymmetry_hom_comp_fst, pullbackLeftPullbackSndIso_inv_snd_snd,
      pullback.congrHom_hom, pullback.lift_snd, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_snd, haSnd]

end SchemeTheory
