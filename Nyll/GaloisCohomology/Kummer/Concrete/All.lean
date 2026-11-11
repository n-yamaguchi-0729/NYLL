/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.QuadraticSquareClasses
public import Nyll.GaloisCohomology.Kummer.Concrete.NormalRestrictionKernel
public import Nyll.GaloisCohomology.Kummer.Concrete.NormalRestrictionResidualAction
public import Nyll.GaloisCohomology.Kummer.Concrete.NormalRestrictionKernelFinite
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteResidualAbelianizationAction
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteCharacterAction
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteContinuousCharacterAction
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteH1Action
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerEvaluation
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerH1
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerNaturality
public import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.Correspondence
public import Nyll.GaloisCohomology.Kummer.Concrete.CyclicExtension
public import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.All
public import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicField
public import Nyll.GaloisCohomology.Kummer.Concrete.ExtensionRoundTrip
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteCharacterEquiv
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteGaloisDual
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteGeneration
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerNormalizedGenerator
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerRootRestriction
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteKummerStageCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteSupport
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupAbsoluteAction
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupConjugation
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
public import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation
public import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureTransport
public import Nyll.GaloisCohomology.Kummer.Concrete.GaloisCohomology
public import Nyll.GaloisCohomology.Kummer.Concrete.InfiniteCharacterEquiv
public import Nyll.GaloisCohomology.Kummer.Concrete.InfiniteContinuity
public import Nyll.GaloisCohomology.Kummer.Concrete.InfiniteGeneration
public import Nyll.GaloisCohomology.Kummer.Concrete.InfiniteInverse
public import Nyll.GaloisCohomology.Kummer.Concrete.KummerCorrespondenceFormula
public import Nyll.GaloisCohomology.Kummer.Concrete.LastPrimePowerRoot
public import Nyll.GaloisCohomology.Kummer.Concrete.LocalMaximalKummerExtension
public import Nyll.GaloisCohomology.Kummer.Concrete.LocalUnitKummerUnramified
public import Nyll.GaloisCohomology.Kummer.Concrete.MaximalKummerSubgroup
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimeCyclicEigenunit
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimePowerRootObstruction
public import Nyll.GaloisCohomology.Kummer.Concrete.RadicalExtension
public import Nyll.GaloisCohomology.Kummer.Concrete.RadicalQuotient
public import Nyll.GaloisCohomology.Kummer.Concrete.RestrictedFinite
public import Nyll.GaloisCohomology.Kummer.Concrete.RootCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.SUnitPreparation.All
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearClosureTransport
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugation
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearConjugationTopology
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtensionNorm

public import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicInvariantCharacter
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupCharacterDescent

public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteRootPowerAction
public import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureCharacterConjugation
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteH1TrivialCharacter
public import Nyll.GaloisCohomology.Kummer.Concrete.SemilinearRestriction
public import Nyll.GaloisCohomology.Kummer.Concrete.InvariantKummerPowerWitness
public import Nyll.GaloisCohomology.Kummer.Concrete.DescendedCharacterAction


public import Nyll.GaloisCohomology.Kummer.Concrete.MovingRootOfUnity

public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerCharacterAction
public import Nyll.GaloisCohomology.Kummer.Concrete.RootOfUnityPowerAction
public import Nyll.GaloisCohomology.Kummer.Concrete.RootKummerInvariantCharacter
public import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicInvariantKummerTrace


public import Nyll.GaloisCohomology.Kummer.Concrete.SeparableKummerH1
public import Nyll.GaloisCohomology.Kummer.Concrete.SeparableClosureConjugation
public import Nyll.GaloisCohomology.Kummer.Concrete.SeparableAbsoluteKummer
public import Nyll.GaloisCohomology.Kummer.Concrete.SeparableAbsoluteKummerNaturality
public import Nyll.GaloisCohomology.Kummer.Concrete.FieldMapNaturality
public import Nyll.GaloisCohomology.Kummer.Concrete.PowerClassCharacterApproximation
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimeToCyclotomicTower
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimaryRootsDivisibility
public import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousHilbert90
public import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousRootCocycleLifting

public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteRestrictionConjugation

public import Nyll.GaloisCohomology.Kummer.Concrete.NormalRestrictionCharacterExtension
public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteCharacterAverage
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicCocycleLifting
public import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicOpenCocycleLifting

public import Nyll.GaloisCohomology.Kummer.Concrete.ProlongationCharacterApproximation
public import Nyll.GaloisCohomology.Kummer.Concrete.InvariantCompletionCharacter
public import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicCompletionApproximation
public import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicInfiniteImage
public import Nyll.GaloisCohomology.Kummer.Concrete.MixedCharacteristicCharacters
public import Nyll.GaloisCohomology.Kummer.Concrete.CompletionAbelianModPower

public import Nyll.GaloisCohomology.Kummer.Concrete.PrimaryRootsFiniteness

public import Nyll.GaloisCohomology.Kummer.Concrete.SeparableGaloisClosureConjugation
public import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupSeparableAbsoluteAction
public import Nyll.GaloisCohomology.Kummer.Concrete.ContinuousKummerScalar

public import Nyll.GaloisCohomology.Kummer.Concrete.RadicalPowerSaturation

public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtensionFieldRange

/-!
# Concrete Kummer extensions and characters

Collects concrete Kummer extensions, character correspondences, root actions,
restriction kernels, finite approximations, and S-unit preparations.
-/
