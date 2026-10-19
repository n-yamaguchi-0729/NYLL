/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.EffectiveDivisorRigidification
import Nyll.JacobianVarieties.Generalized.RigidifiedDivisorLinearEquivalence
import Nyll.AlgebraicCurves.Models.Sections.SectionRatioCongruence
import Nyll.AlgebraicCurves.Models.Sections.RationalSectionDivisor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Sections.SectionVanishingClosedSubscheme
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealZeroSchemeIdealInvModuleSection

/-! # A trivial rigidified divisor class is modulus-principal -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Scheme.Modules
open AlgebraicGeometry.GeneralizedJacobian
open AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

omit [IsAlgClosed K] in
/-- Equality of the actual normalized inverse-ideal classes produces a
rational function congruent to one along the full original modulus. -/
theorem modulusPrincipal_of_rigidifiedIdealClass_eq
    (J P : M.C.IdealSheafData) (hJ : J.IsInvertible) (hP : P.IsInvertible)
    (haJ : ∀ z : I.subscheme, I.subschemeι z ∉ J.support)
    (haP : ∀ z : I.subscheme, I.subschemeι z ∉ P.support)
    (he : classOf (ofInvertibleIdeal I.subschemeι J hJ haJ) =
      classOf (ofInvertibleIdeal I.subschemeι P hP haP)) :
    (M.cartierModulus J hJ).toDivisor - (M.cartierModulus P hP).toDivisor ∈
      (M.cartierModulus I hI).principal := by
  obtain ⟨s, hzero, hrestriction⟩ :=
    (classOf_ofInvertibleIdeal_eq_iff I.subschemeι J P hJ hP haJ haP).mp he
  have hzeroP : zeroSchemeIdeal P.invModuleSection = P := hP.zeroSchemeIdeal_invModuleSection
  have hs : s ≠ 0 := ne_zero_of_zeroSchemeIdeal_isInvertible s (hzero.symm ▸ hJ)
  have ht : P.invModuleSection ≠ 0 :=
    ne_zero_of_zeroSchemeIdeal_isInvertible P.invModuleSection (hzeroP.symm ▸ hP)
  have has : ∀ z : I.subscheme, I.subschemeι z ∉ (zeroSchemeIdeal s).support := by
    simpa only [hzero] using haJ
  have hat : ∀ z : I.subscheme,
      I.subschemeι z ∉ (zeroSchemeIdeal P.invModuleSection).support := by
    simpa only [hzeroP] using haP
  obtain ⟨f, hf, hratio⟩ := M.exists_congruentOne_rationalSectionRatio I hI
    hP.isInvertible_invModule s P.invModuleSection hs ht hrestriction has hat
  refine ⟨f, hf, fun w => ?_⟩
  have hdiv := M.rationalSectionRatio_divisor hP.isInvertible_invModule s
    P.invModuleSection hs ht f hratio w
  simpa only [hzero, hzeroP] using hdiv

/-- The actual divisor-to-rigidified-class map has no kernel elements beyond
the full modulus-principal subgroup. -/
theorem rigidifiedDivisorAwayHom_ker_le_principal
    (E : (M.cartierModulus I hI).divAway)
    (hE : M.rigidifiedDivisorAwayHom I hI E = 0) :
    (E : Divisor K F) ∈ (M.cartierModulus I hI).principal := by
  classical
  let A : Modulus K F := E.1.mapRange Int.toNat rfl
  let B : Modulus K F := E.1.mapRange (fun n : ℤ => (-n).toNat) rfl
  have hdecomp : E.1 = A.toDivisor - B.toDivisor := by
    ext w
    simp only [Finsupp.sub_apply, Modulus.toDivisor_apply, A, B, Finsupp.mapRange_apply]
    omega
  have ha : ∀ w, A w ≠ 0 → M.cartierModulus I hI w = 0 := by
    intro w hw
    by_contra hmod
    have hew := E.2 w hmod
    apply hw
    change Int.toNat (E.1 w) = 0
    rw [hew, Int.toNat_zero]
  have hb : ∀ w, B w ≠ 0 → M.cartierModulus I hI w = 0 := by
    intro w hw
    by_contra hmod
    have hew := E.2 w hmod
    apply hw
    change Int.toNat (-(E.1 w)) = 0
    rw [hew, neg_zero, Int.toNat_zero]
  have hclasses : classOf (ofInvertibleIdeal I.subschemeι (M.pointIdealProduct A)
      (M.pointIdealProduct_isInvertible A) (M.pointIdealProduct_avoids_modulus I hI A ha)) =
      classOf (ofInvertibleIdeal I.subschemeι (M.pointIdealProduct B)
        (M.pointIdealProduct_isInvertible B) (M.pointIdealProduct_avoids_modulus I hI B hb)) := by
    have hm : M.rigidifiedDivisorHom I hI A.toDivisor =
        M.rigidifiedDivisorHom I hI B.toDivisor := by
      apply sub_eq_zero.mp
      rw [← map_sub, ← hdecomp]
      exact hE
    rw [M.rigidifiedDivisorHom_effective I hI A ha,
      M.rigidifiedDivisorHom_effective I hI B hb] at hm
    exact congrArg Additive.toMul hm
  have hp := M.modulusPrincipal_of_rigidifiedIdealClass_eq I hI
    (M.pointIdealProduct A) (M.pointIdealProduct B)
    (M.pointIdealProduct_isInvertible A) (M.pointIdealProduct_isInvertible B)
    (M.pointIdealProduct_avoids_modulus I hI A ha)
    (M.pointIdealProduct_avoids_modulus I hI B hb) hclasses
  simpa only [M.cartierModulus_pointIdealProduct A, M.cartierModulus_pointIdealProduct B,
    ← hdecomp] using hp

end AlgebraicCurve.CurveModel
