/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedDivisorKernelForward
import Nyll.AlgebraicCurves.Models.Sections.PrescribedRationalSection
import Nyll.AlgebraicCurves.Models.Sections.SectionRatioRestriction

/-! # A modulus-principal divisor has trivial actual rigidified class -/

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

/-- A full-modulus principal difference gives an actual isomorphism of the
canonically rigidified inverse ideals. The prescribed function is lifted using
its proved Cartier pole bound and normalized on the entire closed modulus. -/
theorem rigidifiedIdealClass_eq_of_modulusPrincipal
    (J P : M.C.IdealSheafData) (hJ : J.IsInvertible) (hP : P.IsInvertible)
    (haJ : ∀ z : I.subscheme, I.subschemeι z ∉ J.support)
    (haP : ∀ z : I.subscheme, I.subschemeι z ∉ P.support)
    (hprincipal : (M.cartierModulus J hJ).toDivisor -
      (M.cartierModulus P hP).toDivisor ∈ (M.cartierModulus I hI).principal) :
    classOf (ofInvertibleIdeal I.subschemeι J hJ haJ) =
      classOf (ofInvertibleIdeal I.subschemeι P hP haP) := by
  obtain ⟨f, hf, horder⟩ := hprincipal
  have hpole : ∀ w : Place K F, 0 ≤ w.ord f + (M.cartierModulus P hP w : ℤ) := by
    intro w
    have hw := horder w
    change (M.cartierModulus J hJ w : ℤ) - (M.cartierModulus P hP w : ℤ) = w.ord f at hw
    omega
  obtain ⟨s, hs, hratio⟩ := M.exists_section_of_cartier_pole_bound P hP f hf.ne_zero hpole
  have hzeroP : zeroSchemeIdeal P.invModuleSection = P := hP.zeroSchemeIdeal_invModuleSection
  have ht : P.invModuleSection ≠ 0 :=
    ne_zero_of_zeroSchemeIdeal_isInvertible P.invModuleSection (hzeroP.symm ▸ hP)
  let Q := zeroSchemeIdeal s
  have hQ : Q.IsInvertible := hP.isInvertible_invModule.isInvertible_zeroSchemeIdeal_of_ne_zero s hs
  have hmod : M.cartierModulus Q hQ = M.cartierModulus J hJ := by
    ext w
    have hdiv := M.rationalSectionRatio_divisor hP.isInvertible_invModule s
      P.invModuleSection hs ht f hratio w
    simp only [hzeroP] at hdiv
    change (M.cartierModulus Q hQ w : ℤ) - (M.cartierModulus P hP w : ℤ) = w.ord f at hdiv
    have hw := horder w
    change (M.cartierModulus J hJ w : ℤ) - (M.cartierModulus P hP w : ℤ) = w.ord f at hw
    omega
  have hQJ : Q = J := by
    calc
      Q = M.pointIdealProduct (M.cartierModulus Q hQ) := M.eq_pointIdealProduct_cartierModulus Q hQ
      _ = M.pointIdealProduct (M.cartierModulus J hJ) := congrArg M.pointIdealProduct hmod
      _ = J := (M.eq_pointIdealProduct_cartierModulus J hJ).symm
  have hsI : ∀ z : I.subscheme, I.subschemeι z ∉ (zeroSchemeIdeal s).support := by
    simpa only [show zeroSchemeIdeal s = J from hQJ] using haJ
  have htI : ∀ z : I.subscheme,
      I.subschemeι z ∉ (zeroSchemeIdeal P.invModuleSection).support := by
    simpa only [hzeroP] using haP
  exact (classOf_ofInvertibleIdeal_eq_iff I.subschemeι J P hJ hP haJ haP).mpr
    ⟨s, hQJ, M.pullbackSection_eq_of_congruentOne_ratio I hI hP.isInvertible_invModule
      s P.invModuleSection f hf hratio hsI htI⟩

/-- Every principal divisor with the prescribed full congruence is killed by
the actual divisor-to-rigidified-class homomorphism. -/
theorem principal_le_rigidifiedDivisorAwayHom_ker
    (E : (M.cartierModulus I hI).divAway)
    (hE : (E : Divisor K F) ∈ (M.cartierModulus I hI).principal) :
    M.rigidifiedDivisorAwayHom I hI E = 0 := by
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
  have hclasses := M.rigidifiedIdealClass_eq_of_modulusPrincipal I hI
    (M.pointIdealProduct A) (M.pointIdealProduct B)
    (M.pointIdealProduct_isInvertible A) (M.pointIdealProduct_isInvertible B)
    (M.pointIdealProduct_avoids_modulus I hI A ha)
    (M.pointIdealProduct_avoids_modulus I hI B hb)
    (by simpa only [M.cartierModulus_pointIdealProduct A,
      M.cartierModulus_pointIdealProduct B, ← hdecomp] using hE)
  change M.rigidifiedDivisorHom I hI E.1 = 0
  rw [hdecomp, map_sub, M.rigidifiedDivisorHom_effective I hI A ha,
    M.rigidifiedDivisorHom_effective I hI B hb, hclasses, sub_self]

/-- The kernel is exactly the principal subgroup with full modulus congruence. -/
theorem rigidifiedDivisorAwayHom_eq_zero_iff
    (E : (M.cartierModulus I hI).divAway) :
    M.rigidifiedDivisorAwayHom I hI E = 0 ↔
      (E : Divisor K F) ∈ (M.cartierModulus I hI).principal :=
  ⟨M.rigidifiedDivisorAwayHom_ker_le_principal I hI E,
    M.principal_le_rigidifiedDivisorAwayHom_ker I hI E⟩

end AlgebraicCurve.CurveModel
