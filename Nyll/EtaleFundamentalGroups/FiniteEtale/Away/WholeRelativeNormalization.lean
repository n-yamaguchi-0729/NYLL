/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.ChosenFractionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.WholeNormalizationRestriction
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.SchemeTheory.Normalization.Affine
import Nyll.SchemeTheory.Normalization.AffineFiniteEtale
import Nyll.SchemeTheory.Normalization.IntegralClosure.Nested
import Nyll.SchemeTheory.Normalization.Localization.IntegralClosureAwayEquiv
import Nyll.SchemeTheory.Normalization.Localization.IntegralClosureAwayPullback
import Nyll.SchemeTheory.Normalization.SourceIso
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The relative normalization of the original base-changed away cover

After a normal affine base change `D / R`, take the actual pullback of
the original finite étale cover of `R[1/f]`, and compose its structure
map with the away open immersion into `Spec D`. The relative
normalization of this actual composite is canonically isomorphic over
`Spec D` to `Spec (integralClosure D (F ⊗[K] Y.functionField))`.

The comparison first recovers the original pullback over `D[1/f]`, then
applies the normalization universal property to the actual source
isomorphism. Taking the `D`-integral closure inside the intermediate
`D[1/f]`-integral closure is shown to keep the same ambient elements.

Thus the whole normalization used by the local ramification and purity
calculation is the relative normalization of the original cover. This
is the model comparison used to transfer local results to the global
relative normalization, whose affine pieces are already glued.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

private theorem exists_normalizationIso_of_affineSourceModel
    (R E C : Type u) [CommRing R] [CommRing E] [CommRing C]
    [Algebra R E] [Algebra R C] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of R)) [QuasiCompact g] [QuasiSeparated g]
    (eModel : Spec (.of E) ≅ X)
    (hModel : eModel.hom ≫ g = affineStructureMap R E)
    (eRing : integralClosure R E ≃ₐ[R] C) :
    ∃ e : g.normalization ≅ Spec (.of C),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) = g.fromNormalization := by
  let eSource : (affineStructureMap R E).normalization ≅ g.normalization :=
    Scheme.Hom.normalizationSourceIso (affineStructureMap R E) g eModel hModel
  let eNested : Spec (.of (integralClosure R E)) ≅ Spec (.of C) :=
    Scheme.Spec.mapIso eRing.symm.toRingEquiv.toCommRingCatIso.op
  have hNested : eNested.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R E))) := by
    change Spec.map (CommRingCat.ofHom eRing.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R C)) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact eRing.symm.commutes r
  let e : g.normalization ≅ Spec (.of C) :=
    eSource.symm ≪≫ specNormalizationIso R E ≪≫ eNested
  refine ⟨e, ?_⟩
  change (eSource.inv ≫ (specNormalizationIso R E).hom ≫ eNested.hom) ≫ _ = _
  rw [Category.assoc, Category.assoc, hNested,
    specNormalizationIso_hom_fromNormalization]
  rw [← Scheme.Hom.normalizationSourceIso_hom_fromNormalization
    (affineStructureMap R E) g eModel hModel]
  exact Iso.inv_hom_id_assoc eSource g.fromNormalization

/-- The whole generic tensor normalization is the relative normalization
of the actual original away cover after the specified normal base change. -/
theorem exists_wholeRelativeNormalizationIso
    {R D K F : Type u}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [CommRing D] [IsDomain D] [IsIntegrallyClosed D] [Algebra R D]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field F] [Algebra R F] [Algebra D F] [Algebra K F]
    [IsScalarTower R D F] [IsScalarTower R K F] [IsFractionRing D F]
    (f : R) (hf : f ≠ 0)
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) [IsConnected Y] :
    let S := Localization.Away f
    let : IsDomain S := IsLocalization.Away.isDomain S hf
    let : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    let : IsIntegral Y.left := isIntegral_left_of_isConnected_finiteEtale Y
    let : Algebra K Y.left.functionField :=
      finiteEtaleAwayChosenFractionFieldAlgebra (K := K) f hf Y
    let G := F ⊗[K] Y.left.functionField
    let C := integralClosure D G
    let S' := Localization.Away (algebraMap R D f)
    let : Algebra S S' := (Localization.awayMap (algebraMap R D) f).toAlgebra
    let y : Y.left ⟶ Spec (.of S) := Y.hom
    let b := Spec.map (CommRingCat.ofHom (algebraMap S S'))
    let j := Spec.map (CommRingCat.ofHom (algebraMap D S'))
    let g := pullback.snd y b ≫ j
    let : IsFinite y := Y.prop.toIsFinite
    let : QuasiCompact g := inferInstance
    let : QuasiSeparated g := inferInstance
    ∃ e : g.normalization ≅ Spec (.of C),
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap D C)) = g.fromNormalization := by
  intro S hDomainS hNormalS hIntegralY aKL G C S' aSS' y b j g hFiniteY hQcG hQsG
  have hRF : Function.Injective (algebraMap R F) := by
    rw [IsScalarTower.algebraMap_eq R K F]
    exact (algebraMap K F).injective.comp (IsFractionRing.injective R K)
  have hRD : Function.Injective (algebraMap R D) := by
    intro x y hxy
    apply hRF
    rw [IsScalarTower.algebraMap_apply R D F,
      IsScalarTower.algebraMap_apply R D F, hxy]
  let d := algebraMap R D f
  have hd : d ≠ 0 := by simpa only [map_zero] using hRD.ne hf
  let : Algebra S' F := localizationAwayToExtensionAlgebra (K := F) (L := F) d hd
  have : IsScalarTower D S' F :=
    localizationAwayToExtension_isScalarTower (K := F) (L := F) d hd
  have : IsScalarTower D S' G :=
    TensorProduct.isScalarTower_left (R := K) (R'₂ := D) (R' := S')
  let E := integralClosure S' G
  have hAway := SchemeTheory.isPullback_spec_integralClosure_away D G d
  obtain ⟨eRecovery, hRecovery⟩ :=
    exists_wholeNormalizationAwayRestrictionIso (R := R) (D := D) (K := K) (F := F) f hf Y
  let eModel : Spec (.of E) ≅ pullback y b := hAway.isoPullback ≪≫ eRecovery
  have hModel : eModel.hom ≫ g = affineStructureMap D E := by
    change (hAway.isoPullback.hom ≫ eRecovery.hom) ≫ (pullback.snd y b ≫ j) = _
    rw [Category.assoc, ← Category.assoc eRecovery.hom, hRecovery,
      ← Category.assoc, hAway.isoPullback_hom_snd, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro d'
    exact (IsScalarTower.algebraMap_apply D S' E d').symm
  let eRing : integralClosure D E ≃ₐ[D] C :=
    SchemeTheory.integralClosureInIntegralClosureAlgEquiv D S' G
  exact exists_normalizationIso_of_affineSourceModel D E C g eModel hModel eRing

end EtaleFundamentalGroups
