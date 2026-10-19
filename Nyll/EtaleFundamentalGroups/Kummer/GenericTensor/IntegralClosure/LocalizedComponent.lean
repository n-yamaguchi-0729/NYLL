/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.ComponentExtraction
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.EtaleFundamentalGroups.Normalization.Localization.IntegralClosureAtPrimeEquiv
import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Finiteness

/-!
# From a local product normalization to a global component localization

A finite étale normalization over `R_q` in an entire generic tensor product
gives finite étaleness for the localization of the normalization of `R` in
each of its literal field components. The coefficient maps agree by the
universal property of the actual prime localization. This comparison is
proved here, rather than required as additional scalar data.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uK uF uL

/-- Local étaleness for the whole generic product gives the exact
localized component normalization used by purity over the original base. -/
theorem localization_integralClosure_genericTensorFieldComponent_etale_of_product
    (R : Type uR) (K : Type uK) (F : Type uF) (L : Type uL)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Field K] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra K F] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (q : Ideal R) [q.IsPrime]
    [Algebra (Localization.AtPrime q) F]
    [IsScalarTower R (Localization.AtPrime q) F]
    [IsFractionRing (Localization.AtPrime q) F] :
    let W := Localization.AtPrime q
    let G := F ⊗[K] L
    let : Algebra W G := genericTensorProductLeftScalarAlgebra
    Algebra.Etale W (integralClosure W G) →
      ∀ (m : Ideal G) [m.IsMaximal],
        let M := GenericTensorFieldComponent m
        let : Algebra R M := genericTensorFieldComponentLeftScalarAlgebra m
        let : IsScalarTower R F M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
        Algebra.Etale W (Localization
          (Algebra.algebraMapSubmonoid (integralClosure R M) q.primeCompl)) := by
  intro W G aWG hWhole m hm M aRM hRFM
  have : IsIntegrallyClosed W :=
    isIntegrallyClosed_of_isLocalization W q.primeCompl q.primeCompl_le_nonZeroDivisors
  let aWM : Algebra W M := genericTensorFieldComponentLeftScalarAlgebra m
  have hComponent : Algebra.Etale W (integralClosure W M) :=
    integralClosure_genericTensorFieldComponent_etale_of_product W K F L hWhole m
  let aCanonical : Algebra W M :=
    localizationAtPrimeToExtensionAlgebra (K := F) (L := M) q
  have hCanonicalMap (r : R) :
      aCanonical.algebraMap (algebraMap R W r) = algebraMap R M r := by
    let : Algebra W M := aCanonical
    let : SMul W M := aCanonical.toSMul
    have : IsScalarTower R W M :=
      localizationAtPrimeToExtension_isScalarTower (K := F) (L := M) q
    exact (IsScalarTower.algebraMap_apply R W M r).symm
  have hNativeMap (r : R) :
      aWM.algebraMap (algebraMap R W r) = algebraMap R M r := by
    change algebraMap F M (algebraMap W F (algebraMap R W r)) =
      algebraMap F M (algebraMap R F r)
    rw [← IsScalarTower.algebraMap_apply R W F]
  have hAlgebra : aWM = aCanonical := by
    apply Algebra.algebra_ext
    intro w
    apply DFunLike.congr_fun (f := aWM.algebraMap) (g := aCanonical.algebraMap) ?_ w
    apply IsLocalization.ringHom_ext q.primeCompl
    ext r
    exact (hNativeMap r).trans (hCanonicalMap r).symm
  have hCanonicalEtale :
      let : Algebra W M := aCanonical
      Algebra.Etale W (integralClosure W M) := by
    exact hAlgebra ▸ hComponent
  exact localization_integralClosure_etale_of_local_integralClosure_etale
    (K := F) (L := M) q hCanonicalEtale

end EtaleFundamentalGroups
