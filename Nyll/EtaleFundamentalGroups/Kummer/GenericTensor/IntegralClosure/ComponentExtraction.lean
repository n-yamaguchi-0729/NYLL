/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic
import Nyll.EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product
import Nyll.SchemeTheory.Normalization.IntegralClosure.FiniteProduct
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Extracting a normalized generic tensor component

The actual Artinian product decomposition of a separable generic tensor
product identifies the normalization with the product of its component
normalizations. Formal étaleness then passes to each literal component.
Finiteness of integral closure over a normal Noetherian domain supplies
finite presentation, so each component normalization is étale.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uR uK uF uL

/-- Étaleness of the normalization in the whole generic tensor product
implies étaleness of the normalization in any one of its actual maximal
quotient fields. All factor comparisons and finiteness are constructed. -/
theorem integralClosure_genericTensorFieldComponent_etale_of_product
    (R : Type uR) (K : Type uK) (F : Type uF) (L : Type uL)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    [Field K] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra K F] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    let G := F ⊗[K] L
    let : Algebra R G := genericTensorProductLeftScalarAlgebra
    Algebra.Etale R (integralClosure R G) →
      ∀ (m : Ideal G) [m.IsMaximal],
        let : Algebra R (GenericTensorFieldComponent m) :=
          genericTensorFieldComponentLeftScalarAlgebra m
        Algebra.Etale R (integralClosure R (GenericTensorFieldComponent m)) := by
  intro G aRG hWhole m hm aRM
  have : Algebra.Etale K L :=
    { formallyEtale := Algebra.FormallyEtale.of_isSeparable K L
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance }
  have : Module.Finite F G := Module.Finite.base_change K F L
  have : Algebra.Etale F G := inferInstance
  have : IsArtinianRing G := isArtinian_of_tower F inferInstance
  have : IsReduced G := Algebra.FormallyUnramified.isReduced_of_field F G
  let e := SchemeTheory.integralClosureFactorsEquiv R G
  have : Algebra.FormallyEtale R (integralClosure R G) := hWhole.formallyEtale
  have hPi : Algebra.FormallyEtale R
      (∀ q : MaximalSpectrum G, integralClosure R (G ⧸ q.asIdeal)) :=
    Algebra.FormallyEtale.of_equiv e
  let M := GenericTensorFieldComponent m
  have hFormally : Algebra.FormallyEtale R (integralClosure R M) :=
    (Algebra.FormallyEtale.pi_iff
      (fun q : MaximalSpectrum G ↦ integralClosure R (G ⧸ q.asIdeal))).mp hPi ⟨m, hm⟩
  have : IsScalarTower R F M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite R (integralClosure R M) :=
    IsIntegralClosure.finite R F M (integralClosure R M)
  have : Module.FinitePresentation R (integralClosure R M) :=
    Module.finitePresentation_of_finite R (integralClosure R M)
  exact ⟨hFormally, Algebra.FinitePresentation.of_finitePresentation R (integralClosure R M)⟩

end EtaleFundamentalGroups
