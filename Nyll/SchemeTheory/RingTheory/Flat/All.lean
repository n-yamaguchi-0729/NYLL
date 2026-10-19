/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Flat.LocalAdicBasis
import Nyll.SchemeTheory.RingTheory.Flat.NilpotentFlatBasis
import Nyll.SchemeTheory.RingTheory.Flat.AlgebraQuasiFiniteFlat
import Nyll.SchemeTheory.RingTheory.Flat.FibralCriterion
import Nyll.SchemeTheory.RingTheory.Flat.FiniteSubalgebra
import Nyll.SchemeTheory.RingTheory.Flat.FiniteSubalgebraLocalization
import Nyll.SchemeTheory.RingTheory.Flat.GenericFlatness
import Nyll.SchemeTheory.RingTheory.Flat.IntegrallyClosedIsDomainIsIntegrallyClosed
import Nyll.SchemeTheory.RingTheory.Flat.Kernel
import Nyll.SchemeTheory.RingTheory.Flat.LocalCriterion
import Nyll.SchemeTheory.RingTheory.Flat.LocalRingMemRangeAlgebraMap
import Nyll.SchemeTheory.RingTheory.Flat.LocalRingReducedQuotientMap
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatBijectiveKerBaseChangeHomHomologyBaseChangeLinearEquiv
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatFinitePresentation
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatFlatKerBijectiveKerBaseChangeHom
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatIsLocalHom
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatIsUnitKerBaseChangeLeRange
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatIsUnitProjectiveKerBaseChange
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatKerBaseChangeEqBotKerLeRange
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatKerBaseChangeLeRange
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatKerLeRangeIsMaximalKerBaseChangeQuotientLeRange
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatMaximalIdealRTensorInjective
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatProjectiveKerBaseChange
import Nyll.SchemeTheory.RingTheory.Flat.ModuleFlatProjectiveKerBijectiveKerBaseChangeHom
import Nyll.SchemeTheory.RingTheory.Flat.OpenLocus
import Nyll.SchemeTheory.RingTheory.Flat.Product
import Nyll.SchemeTheory.RingTheory.Flat.RingHomQuasiFiniteCodescendsAlongFaithfullyFlat
import Nyll.SchemeTheory.RingTheory.Flat.TensorExactness
import Nyll.SchemeTheory.RingTheory.Flat.TensorInjectivity
import Nyll.SchemeTheory.RingTheory.Flat.TorLocalCriterion
