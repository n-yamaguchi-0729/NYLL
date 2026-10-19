/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Nyll.JacobianVarieties.WeilPairing.CharZeroNondegeneracy
import Nyll.JacobianVarieties.WeilPairing.Datum
import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingPairCorrespondenceEqPairCorrespondence
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingPairEqPair
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingPairPullbackEqPairPushforwardAlongHom
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingInseparableProjection
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingPairSemilinearSmul
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingPerfect
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingToHomInjectiveDivisible
import Nyll.JacobianVarieties.WeilPairing.DivisorialPairingToHomInjectiveDivisibleCoprime
import Nyll.JacobianVarieties.WeilPairing.HasPrincipalDivisorsFiniteDimensional
import Nyll.JacobianVarieties.WeilPairing.WeilDatumAddLeftPairing
import Nyll.JacobianVarieties.WeilPairing.WeilDatumPairingEqPrincipalSub
import Nyll.JacobianVarieties.WeilPairing.WeilPairingInseparableProjection
import Nyll.JacobianVarieties.WeilPairing.WeilDatumPairingEqPairingPullbackPushforwardAlongSeparableAlong
import Nyll.JacobianVarieties.WeilPairing.WeilDatumPairingNeZero
import Nyll.JacobianVarieties.WeilPairing.WeilDatumSymmPairing
import Nyll.JacobianVarieties.WeilPairing.DivisionDifference
import Nyll.JacobianVarieties.WeilPairing.ConstantExtension

import Nyll.JacobianVarieties.WeilPairing.TransportedDivisorialPairing
