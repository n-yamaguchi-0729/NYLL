/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Normalization.Branch.All
public import Nyll.EtaleFundamentalGroups.Normalization.EtaleDominantQuotient
public import Nyll.EtaleFundamentalGroups.Normalization.FiniteEtaleGenericFiber
public import Nyll.EtaleFundamentalGroups.Normalization.IntegralClosure.All
public import Nyll.EtaleFundamentalGroups.Normalization.Localization.All
public import Nyll.EtaleFundamentalGroups.Normalization.Primes.All
public import Nyll.EtaleFundamentalGroups.Normalization.Products.All
public import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedNormalBase
public import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedNormalization
public import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedFiberDegree
public import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedSubfield
public import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedGeometricInertia

public import Nyll.EtaleFundamentalGroups.Normalization.GenericNormalizationChartAction

public import Nyll.EtaleFundamentalGroups.Normalization.AffineInertiaCriterion
public import Nyll.EtaleFundamentalGroups.Normalization.FiniteFractionFieldModel
public import Nyll.EtaleFundamentalGroups.Normalization.FiniteNormalModelNeighborhood
public import Nyll.EtaleFundamentalGroups.Normalization.FiniteNormalizationLocalCriterion
public import Nyll.EtaleFundamentalGroups.Normalization.LocalUnramifiedCriterion

public import Nyll.EtaleFundamentalGroups.Normalization.GlobalLocalUnramifiedCriterion

public import Nyll.EtaleFundamentalGroups.Normalization.FieldSourceNormalization
public import Nyll.EtaleFundamentalGroups.Normalization.AffineUnramifiedSubfield

public import Nyll.EtaleFundamentalGroups.Normalization.NormalLocalFiberDegree
public import Nyll.EtaleFundamentalGroups.Normalization.FiberDegreeCriterion
public import Nyll.EtaleFundamentalGroups.Normalization.GlobalFiberDegreeCriterion
public import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedCriteria
public import Nyll.EtaleFundamentalGroups.Normalization.FiniteNormalFieldSource

public import Nyll.EtaleFundamentalGroups.Normalization.FiniteNormalFieldSourceGeneric
public import Nyll.EtaleFundamentalGroups.Normalization.OpenNormalizationFiniteModel

public import Nyll.EtaleFundamentalGroups.Normalization.ConstantHilbertClassField
public import Nyll.EtaleFundamentalGroups.Normalization.HilbertClassField
public import Nyll.EtaleFundamentalGroups.Normalization.UnramifiedCurveField

/-!
# Normalization infrastructure

Integral closures, normalization primes, localization comparisons, and product factors.
-/

/-! Canonical aggregate for EtaleFundamentalGroups.Normalization. -/
