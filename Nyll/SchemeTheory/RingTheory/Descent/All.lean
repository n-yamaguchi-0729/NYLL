/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Descent.AlgebraizedRingEtaleNeighborhood
public import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleDatum
public import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatOnOpenImage
public import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatAlgebraEqualizer
public import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatGradedAlgebraEqualizer
public import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleEqualizer
public import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleHomDescent
public import Nyll.SchemeTheory.RingTheory.Descent.ModuleBaseChangeHomExt
public import Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayAlgebraGluing
public import Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayPairGluing
public import Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayTensorDetection
public import Nyll.SchemeTheory.RingTheory.Descent.FiniteSubalgebraLocalization
public import Nyll.SchemeTheory.RingTheory.Descent.FiniteEtaleNeighborhood
public import Nyll.SchemeTheory.RingTheory.Descent.BoundaryNormalIntegralClosure
public import Nyll.SchemeTheory.RingTheory.Descent.IntegralClosureLocalizationAway
public import Nyll.SchemeTheory.RingTheory.Descent.FiniteNormalizationModel
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleLocalNormality

public import Nyll.SchemeTheory.RingTheory.Descent.EtaleFiniteFactor
public import Nyll.SchemeTheory.RingTheory.Descent.EtalePrimeLocalization
public import Nyll.SchemeTheory.RingTheory.Descent.FiniteNormalizationNeighborhood
public import Nyll.SchemeTheory.RingTheory.Descent.FiniteNormalizationSpreading

public import Nyll.SchemeTheory.RingTheory.Descent.FiniteType
public import Nyll.SchemeTheory.RingTheory.Descent.FinitePresentation
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
public import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatNormality
public import Nyll.SchemeTheory.RingTheory.Descent.SmoothAtPrimeNormality

public import Nyll.SchemeTheory.RingTheory.Descent.InvertibleModule


/- Canonical aggregate for SchemeTheory.RingTheory.Descent. -/
public import Nyll.SchemeTheory.RingTheory.Descent.TensorComparison
public import Nyll.SchemeTheory.RingTheory.Descent.GradedSubalgebra
public import Nyll.SchemeTheory.RingTheory.Descent.GradedBaseChange
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleSource
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleOpenImage
public import Nyll.SchemeTheory.RingTheory.Descent.PrincipalLocalizationModel
public import Nyll.SchemeTheory.RingTheory.Descent.LocalizationNormalIntegralClosure
public import Nyll.SchemeTheory.RingTheory.Descent.FiniteUnramifiedNeighborhood
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleLocalDomainOfIntegralNormalExtension
public import Nyll.SchemeTheory.RingTheory.Descent.EtaleLocalIrreducibilityOfIntegralNormalExtension

/-!
# Faithfully flat descent and gluing of algebras

This aggregate exposes module and algebra equalizers, homomorphism descent, prime-away
gluing, finite etale neighborhoods, and descent of finite type and finite presentation.
-/
