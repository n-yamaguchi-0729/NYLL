/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.ChosenFractionField
import Nyll.EtaleFundamentalGroups.FiniteEtale.Away.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.BaseChange.AffineNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.FunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.FiniteEtale.Integral
import Nyll.SchemeTheory.Normalization.Localization.IntegralClosureAwayEquiv
import Nyll.SchemeTheory.Normalization.Localization.IntegralClosureAwayPullback
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Recovering the original away cover from the whole normalization

Let `Y` be an actual connected finite étale cover of `Spec (R[1/f])`.
For a normal domain `D / R`, with compatible fraction fields `F / K`,
normalize `D` in the entire tensor `F ⊗[K] Y.functionField`.
Its restriction to `D[1/f]` is the actual base change of the original
cover `Y`, by an isomorphism over `D[1/f]`.

The action of the chosen fraction field on the cover's function field
is constructed from the original cover. All localization actions are
compared using their values on `R`; no generic-fibre or normalization
comparison is assumed. This is the recovery step for a normalized root
extension, independently of the separate proof that it is étale along
the special fibre.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open scoped TensorProduct

namespace EtaleFundamentalGroups

universe u

/-- The whole normalized generic base change restricts to the actual
base change of the original away cover, over the actual away base. -/
theorem exists_wholeNormalizationAwayRestrictionIso
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
    ∃ e : pullback (Spec.map (CommRingCat.ofHom (algebraMap D C)))
          (Spec.map (CommRingCat.ofHom (algebraMap D S'))) ≅
        pullback (Y.hom : Y.left ⟶ Spec (.of S))
          (Spec.map (CommRingCat.ofHom (algebraMap S S'))),
      e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  intro S hDomainS hNormalS hIntegralY aKL G C S' aSS'
  let L := Y.left.functionField
  let : Algebra R L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
  have : IsScalarTower R K L :=
    (finiteEtaleAwayChosenFractionField_finite_separable (K := K) f hf Y).1
  let : Algebra S L := finiteEtaleSpecFunctionFieldAlgebra (.of S) Y
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra S K := localizationAwayToExtensionAlgebra (K := K) (L := K) f hf
  have : IsScalarTower R S K :=
    localizationAwayToExtension_isScalarTower (K := K) (L := K) f hf
  have : IsFractionRing S K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) S K
  have hSL : algebraMap S L = (algebraMap K L).comp (algebraMap S K) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro r
    change algebraMap S L (algebraMap R S r) =
      algebraMap K L (algebraMap S K (algebraMap R S r))
    rw [← IsScalarTower.algebraMap_apply R S L,
      ← IsScalarTower.algebraMap_apply R S K, ← IsScalarTower.algebraMap_apply R K L]
  have : IsScalarTower S K L := IsScalarTower.of_algebraMap_eq' hSL
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
  have : IsDomain S' := IsLocalization.Away.isDomain S' hd
  have : IsIntegrallyClosed S' :=
    isIntegrallyClosed_of_isLocalization S' (Submonoid.powers d)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hd))
  let : Algebra S' F := localizationAwayToExtensionAlgebra (K := F) (L := F) d hd
  have : IsScalarTower D S' F :=
    localizationAwayToExtension_isScalarTower (K := F) (L := F) d hd
  have : IsFractionRing S' F :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers d) S' F
  let : Algebra S F := ((algebraMap K F).comp (algebraMap S K)).toAlgebra
  have : IsScalarTower S K F := IsScalarTower.of_algebraMap_eq' rfl
  have hSF : (algebraMap S' F).comp (algebraMap S S') = algebraMap S F := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro r
    change algebraMap S' F
      ((Localization.awayMap (algebraMap R D) f) (algebraMap R S r)) =
        algebraMap K F (algebraMap S K (algebraMap R S r))
    calc
      _ = algebraMap S' F (algebraMap D S' (algebraMap R D r)) :=
        congrArg (algebraMap S' F) (IsLocalization.map_eq _ r)
      _ = algebraMap D F (algebraMap R D r) :=
        (IsScalarTower.algebraMap_apply D S' F _).symm
      _ = algebraMap R F r := (IsScalarTower.algebraMap_apply R D F r).symm
      _ = algebraMap K F (algebraMap R K r) := IsScalarTower.algebraMap_apply R K F r
      _ = _ := congrArg (algebraMap K F) (IsScalarTower.algebraMap_apply R S K r)
  have : IsScalarTower S S' F := IsScalarTower.of_algebraMap_eq' hSF.symm
  have : IsScalarTower D S' G :=
    TensorProduct.isScalarTower_left (R := K) (R'₂ := D) (R' := S')
  have hRestriction := SchemeTheory.isPullback_spec_integralClosure_away D G d
  obtain ⟨eCover, hCover⟩ :=
    exists_finiteEtaleAffineBaseChangeNormalizationIso (.of S) Y K S' F
  refine ⟨hRestriction.isoPullback.symm ≪≫ eCover, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hCover]
  exact hRestriction.isoPullback_inv_snd

end EtaleFundamentalGroups
