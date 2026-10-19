/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.FiniteFamilyModel
import Nyll.EtaleFundamentalGroups.FiniteEtale.FiniteField.GaloisModel
import Nyll.EtaleFundamentalGroups.GaloisCovers.IsomorphismTransport
import Nyll.SchemeTheory.LocalGeometry.DVRGenericBaseChange
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.RingTheory.Henselian.FiniteSeparableNormalizationDVR
import Nyll.SchemeTheory.RingTheory.Henselian.HenselianIntegralDomainLocal
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# A Galois model on the generic open of a finite DVR normalization

A Galois cover of the geometric generic fibre first descends to a finite
separable coefficient field, together with all its deck transformations.
The integral closure of the original strictly Henselian DVR in this
field is an actual finite strictly Henselian DVR. Its generic open is
identified with the finite coefficient fibre by pullback pasting.

Transporting the descended cover through this comparison gives a
Galois cover of the actual generic open of the normalized base. Its
automorphism-group order equals that of the original cover, and its
pullback along the displayed coefficient inclusion recovers that cover.
Thus this reduction preserves the prime-to-characteristic condition.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

open EtaleFundamentalGroups

universe u

/-- A geometric Galois cover has a model, with the same automorphism
order, on the actual generic open of a finite strictly Henselian DVR
normalization. Its comparison to the finite coefficient fibre retains
the maps to the original scheme and the new DVR. -/
theorem exists_strictHenselianDVR_galois_model
    (B K Ω : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [HenselianLocalRing B] [IsSepClosed (IsLocalRing.ResidueField B)]
    [Field K] [Field Ω] [Algebra B K] [IsFractionRing B K]
    [Algebra K Ω] [Algebra B Ω] [IsScalarTower B K Ω] [Algebra.IsSeparable K Ω]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (f : X ⟶ Spec (.of B)) :
    let η := Spec.map (CommRingCat.ofHom (algebraMap B K))
    let XK : Scheme.{u} := Limits.pullback f η
    let fK : XK ⟶ Spec (.of K) := Limits.pullback.snd f η
    let φΩ := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
    let XΩ : Scheme.{u} := Limits.pullback φΩ fK
    ∀ [ConnectedSpace XΩ] (Z : FiniteEtale XΩ) [IsGalois Z],
    ∃ H : IntermediateField K Ω, FiniteDimensional K H ∧
      let C := integralClosure B H
      let : IsLocalRing C := SchemeTheory.isLocalRing_of_integral_domain_henselian B C
      Module.Finite B C ∧ IsFractionRing C H ∧ IsDiscreteValuationRing C ∧
        HenselianLocalRing C ∧ IsSepClosed (IsLocalRing.ResidueField C) ∧
        IsLocalHom (algebraMap B C) ∧
        ∃ π : C, Irreducible π ∧
          let β := Spec.map (CommRingCat.ofHom (algebraMap B C))
          let ε := Spec.map (CommRingCat.ofHom (R := C) (S := Localization.Away π)
            (algebraMap C (Localization.Away π)))
          let μ := Spec.map (CommRingCat.ofHom (algebraMap C H))
          let U : Scheme.{u} := Limits.pullback (Limits.pullback.snd f β) ε
          let φH := Spec.map (CommRingCat.ofHom (algebraMap K H))
          let XH : Scheme.{u} := Limits.pullback φH fK
          let cH : XΩ ⟶ XH := Limits.pullback.map φΩ fK φH fK
            (Spec.map (CommRingCat.ofHom H.val.toRingHom)) (𝟙 XK) (𝟙 _)
            (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
            (by rw [Category.comp_id, Category.id_comp])
          ∃ e : U ≅ XH,
            e.hom ≫ Limits.pullback.snd φH fK ≫ Limits.pullback.fst f η =
              Limits.pullback.fst (Limits.pullback.snd f β) ε ≫ Limits.pullback.fst f β ∧
            e.hom ≫ Limits.pullback.fst φH fK ≫ μ =
              Limits.pullback.snd (Limits.pullback.snd f β) ε ≫ ε ∧
            ∃ hU : ConnectedSpace U,
              let : ConnectedSpace U := hU
              ∃ Y : FiniteEtale U, IsGalois Y ∧ Nat.card (Aut Y) = Nat.card (Aut Z) ∧
                Nonempty ((pullback (cH ≫ e.inv)).obj Y ≅ Z) := by
  intro η XK fK φΩ XΩ hXΩ Z hZ
  have : IsAffineHom (Limits.pullback.fst f η) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f η).flip (inferInstance : IsAffineHom η)
  have : CompactSpace XK := inferInstanceAs (CompactSpace ↥(Limits.pullback f η))
  have : QuasiSeparatedSpace XK :=
    quasiSeparatedSpace_of_quasiSeparated (Limits.pullback.fst f η)
  obtain ⟨H, hH, hXH, N, hN, hNCard, ⟨eN⟩⟩ :=
    exists_finiteIntermediateField_galois_scheme_model K Ω XK fK Z
  have : FiniteDimensional K H := hH
  let C := integralClosure B H
  let : IsLocalRing C := SchemeTheory.isLocalRing_of_integral_domain_henselian B C
  have hNormalization := SchemeTheory.finiteSeparableNormalization_strictHenselianDVR B K H
  have hFraction : IsFractionRing C H := hNormalization.2.1
  have hDVR : IsDiscreteValuationRing C := hNormalization.2.2.1
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible C
  let β := Spec.map (CommRingCat.ofHom (algebraMap B C))
  let ε : Spec (.of (Localization.Away π)) ⟶ Spec (.of C) :=
    Spec.map (CommRingCat.ofHom (R := C) (S := Localization.Away π)
      (algebraMap C (Localization.Away π)))
  let μ := Spec.map (CommRingCat.ofHom (algebraMap C H))
  let U : Scheme.{u} := Limits.pullback (Limits.pullback.snd f β) ε
  let φH := Spec.map (CommRingCat.ofHom (algebraMap K H))
  let XH : Scheme.{u} := Limits.pullback φH fK
  let cH : XΩ ⟶ XH := Limits.pullback.map φΩ fK φH fK
    (Spec.map (CommRingCat.ofHom H.val.toRingHom)) (𝟙 XK) (𝟙 _)
    (by rw [Category.comp_id, ← Spec.map_comp]; rfl)
    (by rw [Category.comp_id, Category.id_comp])
  have : ConnectedSpace XH := hXH
  have : IsGalois N := hN
  obtain ⟨δ, hδ, e, heX, heH⟩ := SchemeTheory.exists_dvrGenericBaseChangeIso
    B C K H X f π hπ.ne_zero hπ.not_isUnit
  have heC : e.hom ≫ Limits.pullback.fst φH fK ≫ μ =
      Limits.pullback.snd (Limits.pullback.snd f β) ε ≫ ε := by
    rw [← Category.assoc, heH, Category.assoc, hδ]
  have hU : ConnectedSpace U := e.hom.homeomorph.connectedSpace_iff.mpr hXH
  let Y : FiniteEtale U := (pullback e.hom).obj N
  have hY : IsGalois Y ∧ Nat.card (Aut Y) = Nat.card (Aut N) :=
    isGalois_pullback_and_card_aut_of_isIso e.hom N
  have hRecovery : Nonempty ((pullback (cH ≫ e.inv)).obj Y ≅ Z) := by
    refine ⟨finiteEtalePullbackCompObjIso (cH ≫ e.inv) e.hom cH ?_ N ≪≫ eN⟩
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  exact ⟨H, hH, hNormalization.1, hFraction, hDVR, hNormalization.2.2.2.1,
    hNormalization.2.2.2.2.1, hNormalization.2.2.2.2.2, π, hπ, e, heX, heC,
    hU, Y, hY.1, hY.2.trans hNCard, hRecovery⟩

end AlgebraicGeometry.FiniteEtale
