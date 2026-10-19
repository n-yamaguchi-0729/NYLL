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

import Nyll.JacobianVarieties.Pic0.PullbackAlong
import Nyll.JacobianVarieties.Pic0.PushforwardAlong
import Nyll.JacobianVarieties.Pic0.BaseChange
import Nyll.AlgebraicCurves.Divisors.ClassGroup.Pic0Congr
import Nyll.JacobianVarieties.Pic0.GenusFFEqPic0AddEquivAlgebraMapEqComp
import Nyll.JacobianVarieties.Pic0.AddOrderOfMkDvdPrincipal
import Nyll.JacobianVarieties.Pic0.ConormCorrespondenceEqCorrespondenceConorm
import Nyll.JacobianVarieties.Pic0.ConormSmulEqSmulConorm
import Nyll.JacobianVarieties.Pic0.CorrespondenceCorrespondenceComm
import Nyll.JacobianVarieties.Pic0.EquivAddEquivMkEqSmulRingEquiv
import Nyll.JacobianVarieties.Pic0.EquivPointsAddPoincareIsoOfPointPicardRepresentabilityCurveModel
import Nyll.JacobianVarieties.Pic0.PicardZeroPointClassification
import Nyll.JacobianVarieties.Pic0.InjectiveAddMonoidHomTorsionApplyEqInvSmulD
import Nyll.JacobianVarieties.Pic0.InjectiveAddMonoidHomTorsionDlog
import Nyll.JacobianVarieties.Pic0.InjectiveConormConstantExtension
import Nyll.JacobianVarieties.Pic0.JacobianPackAlgClosed
import Nyll.JacobianVarieties.Pic0.MkEqDvdOrdMemTorsion
import Nyll.JacobianVarieties.Pic0.MkEqNotMemSupport
import Nyll.JacobianVarieties.Pic0.NsmulEqJacobianPack
import Nyll.JacobianVarieties.Pic0.OrdEqMulPowNeNeZero
import Nyll.JacobianVarieties.Pic0.OrdEqMulNsmulMkEqZero
import Nyll.JacobianVarieties.Pic0.RelativeGroupLawEquivCurveModel
import Nyll.JacobianVarieties.Pic0.SchemeHomOverPushforwardAlong
import Nyll.JacobianVarieties.Pic0.ZsmulEqFiniteDimensionalRatFunc
import Nyll.JacobianVarieties.Pic0.PrincipalRingEquiv
import Nyll.JacobianVarieties.Pic0.MemClosureMkSingleSubSingle
import Nyll.JacobianVarieties.Pic0.MemClosureMkSingleSubSingleNotMem
import Nyll.JacobianVarieties.Pic0.MkEqZeroIffPow
import Nyll.JacobianVarieties.Pic0.NatCardTorsionEqConstantExtension
import Nyll.JacobianVarieties.Pic0.DivisorialWeilPairingData
import Nyll.JacobianVarieties.Pic0.DivisorialWeilPairingDataAlgClosed
import Nyll.JacobianVarieties.Pic0.NsmulMkEqZeroPrincipal
import Nyll.JacobianVarieties.Pic0.PushforwardAlongHomSmul
import Nyll.JacobianVarieties.Pic0.PushforwardHomPullbackHom
import Nyll.JacobianVarieties.Pic0.RangeEqSetOfCartierFixedIsRegularDiff
import Nyll.JacobianVarieties.Pic0.RoofPackageSurjective
import Nyll.JacobianVarieties.Pic0.TorsionApplyEqTraceAlongPullback
import Nyll.JacobianVarieties.Pic0.TorsionBijectiveInjective
import Nyll.JacobianVarieties.Pic0.TorsionAddMonoidHomEvalEqPairing
import Nyll.JacobianVarieties.Pic0.TorsionOrdEqMul
import Nyll.JacobianVarieties.Pic0.TorsionMoveIsRational
import Nyll.JacobianVarieties.Pic0.ZsmulMkEqZeroPrincipal
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
