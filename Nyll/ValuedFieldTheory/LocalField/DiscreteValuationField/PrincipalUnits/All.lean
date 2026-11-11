/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismEquiv
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.PrimePowerRoots
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueQuotient
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.ResidueRoots
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerDecomposition
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.TeichmullerLift

public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.PositiveCharacteristicQuotient

/-!
# Principal units of discrete valuation fields

This aggregate exposes the principal-unit filtration, residue quotients and roots,
Teichmuller lifts and decomposition, and automorphism transport.
-/
