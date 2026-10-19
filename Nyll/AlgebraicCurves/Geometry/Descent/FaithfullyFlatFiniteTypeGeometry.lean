/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Descent.FaithfullyFlatProperties
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothSeparatedQuasiCompactGeometricallyConnected

/-!
# Finite-type geometry under faithfully flat scalar extension

The existing fpqc descent results apply without a separability assumption and
without requiring the descended scheme to be proper. This is the form needed
for positive-modulus generalized Jacobians.
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicCurves.Geometry.Curves.Proofs
open
  smooth_isSeparated_quasiCompact_geometricallyConnected_of_finiteEtale_baseChange.AlgebraicGeometry
open FiniteEtaleBaseChangeDescent'

namespace AlgebraicGeometry

/-- Smoothness, separation, quasi-compactness and geometric connectedness descend
along an arbitrary faithfully flat extension of affine bases. -/
theorem smooth_isSeparated_quasiCompact_geometricallyConnected_of_faithfullyFlat_baseChange
    (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {X' : Scheme.{u}} (x' : X' ⟶ Spec (CommRingCat.of R'))
    (hsm : Smooth x') (hsep : IsSeparated x') (hqc : QuasiCompact x')
    (hgc : GeometricallyConnected x')
    (e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≅ X')
    (he : e.hom ≫ x' = pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) :
    Smooth f ∧ IsSeparated f ∧ QuasiCompact f ∧ GeometricallyConnected f := by
  have hff : (CommRingCat.ofHom (algebraMap R R')).hom.FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  obtain ⟨hfl, hsu⟩ := (flat_and_surjective_SpecMap_iff _).mpr hff
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := ⟨⟨hsu, hfl⟩, inferInstance⟩
  have hres (P : MorphismProperty Scheme.{u}) (hbc : P.IsStableUnderBaseChange) :
      P.RespectsIso := by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro g h j
    exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk j.inv.w))
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    hres @Smooth smooth_isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
    hres @GeometricallyConnected (GeometricallyConnected.eq_geometrically ▸ inferInstance)
  have : MorphismProperty.RespectsIso (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    hres @QuasiCompact quasiCompact_isStableUnderBaseChange
  have hsm' : Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
    rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso @Smooth e.hom x').mpr hsm
  have hsep' : IsSeparated (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
    rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso @IsSeparated e.hom x').mpr hsep
  have hqc' : QuasiCompact (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
    rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso @QuasiCompact e.hom x').mpr hqc
  have hgc' : GeometricallyConnected
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R R')))) := by
    rw [← he]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected e.hom x').mpr hgc
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R R'))) := hsu
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact.{u}
    exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hσ hsm'
  · have := FiniteEtaleBaseChangeDescent'.isSeparated_descendsAlong.{u}
    exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @IsSeparated)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hσ hsep'
  · exact FiniteEtaleBaseChangeDescent'.quasiCompact_of_pullback_snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))
  · exact FiniteEtaleBaseChangeDescent'.geometricallyConnected_of_pullback_snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R R')))

end AlgebraicGeometry
