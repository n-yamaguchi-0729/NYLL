/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusOpenComplement
import Nyll.JacobianVarieties.Generalized.DivisorScalarExtension
import Nyll.JacobianVarieties.Generalized.ModulusComplementBaseChange
import Nyll.JacobianVarieties.Generalized.VectorGroupRegularMapModulus
import Nyll.AlgebraicCurves.Geometry.Sheaves.Pullback.PullbackFoldrTwistIso
import Nyll.AlgebraicCurves.Models.Construction.OfSmoothProperCurve

/-! # One ground-field power dominates a geometric boundary modulus

The original relative Cartier boundary divisor is retained over the ground
field. A finite maximum of the geometric modulus coefficients determines
one positive exponent. Its actual ground Cartier power dominates the full
geometric modulus, including multiplicities introduced by imperfect base
change, and leaves the original complement unchanged.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GeneralizedJacobian

/-- The actual scalar-extended relative divisor has the inverse-image
ideal on the original base-changed curve, with all multiplicities. -/
theorem modulusCurveIdeal_scalarExtension
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) {d : ℕ}
    (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
    (L : Type u) [Field L] [Algebra K L] :
    modulusCurveIdeal (D.changeBaseOfIdentity (specMap K L)) =
      (modulusCurveIdeal D).comap (pullback.fst c (specMap K L)) := by
  change (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))).ker = _
  rw [divisorScalarExtensionModulusIso_square, Scheme.Hom.ker_comp_of_isIso]
  have hp := isPullback_modulusBaseChange c (modulusCurveMap D) (specMap K L)
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← hp.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

/-- The actual extended complement is the inverse image of the original
open complement, without replacing the scalar-extended divisor. -/
theorem modulusComplement_scalarExtension
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) {d : ℕ}
    (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
    (L : Type u) [Field L] [Algebra K L] :
    modulusComplement (modulusCurveMap (D.changeBaseOfIdentity (specMap K L))) =
      pullback.fst c (specMap K L) ⁻¹ᵁ modulusComplement (modulusCurveMap D) := by
  change (modulusCurveIdeal (D.changeBaseOfIdentity (specMap K L))).support.compl = _
  rw [modulusCurveIdeal_scalarExtension, Scheme.IdealSheafData.support_comap]
  rfl

private theorem cartierModulus_power_of_ideal_eq
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (M : CurveModel K F) (I J : M.C.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (n : ℕ) (hJI : J = I ^ n) :
    M.cartierModulus J hJ = n • M.cartierModulus I hI := by
  subst J
  ext w
  let x := M.placeEquiv.symm w
  change M.cartierMultiplicity (I ^ n) hJ x = n * M.cartierMultiplicity I hI x
  apply M.stalk_maximalIdeal_pow_injective x
  change IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^
      M.cartierMultiplicity (I ^ n) hJ x =
    IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) ^
      (n * M.cartierMultiplicity I hI x)
  rw [← M.stalkIdeal_eq_maximalIdeal_pow (I ^ n) hJ x,
    Scheme.IdealSheafData.stalkIdeal_pow, M.stalkIdeal_eq_maximalIdeal_pow I hI x,
    ← pow_mul, Nat.mul_comm]

open AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_pullback_foldr_twist_iso in
/-- A fixed relative Cartier divisor has a positive ground-field power
dominating any finitely supported geometric modulus on its boundary.
The support condition is stated using the actual geometric Cartier
multiplicities; in the application it follows from exact boundary support. -/
theorem exists_groundModulus_power_dominating
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) [IsProper c] [SmoothOfRelativeDimension 1 c]
    [GeometricallyIntegral c] {d : ℕ}
    (D : RelEffCartierDiv c d (𝟙 (Spec (.of K))))
    (L : Type u) [Field L] [Algebra K L] :
    let cL := baseChange K c L
    let DL := D.changeBaseOfIdentity (specMap K L)
    let _ : Algebra L (pullback c (specMap K L)).functionField :=
      (baseToFunctionField cL).toAlgebra
    let ML := CurveModel.ofSmoothProperCurve cL
    ∀ E : Modulus L (pullback c (specMap K L)).functionField,
      (∀ w, ML.cartierModulus (modulusCurveIdeal DL)
          (modulusCurveIdeal_isInvertible DL) w = 0 → E w = 0) →
    ∃ (N : ℕ) (_ : 0 < N) (e : ℕ)
      (P : RelEffCartierDiv c e (𝟙 (Spec (.of K)))),
      modulusCurveIdeal P = (modulusCurveIdeal D) ^ N ∧
      modulusComplement (modulusCurveMap P) = modulusComplement (modulusCurveMap D) ∧
      E ≤ ML.cartierModulus (modulusCurveIdeal (P.changeBaseOfIdentity (specMap K L)))
        (modulusCurveIdeal_isInvertible (P.changeBaseOfIdentity (specMap K L))) := by
  intro cL DL algL ML E hE
  classical
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  let _ : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
  let M := CurveModel.ofSmoothProperCurve c
  let A := ML.cartierModulus (modulusCurveIdeal DL) (modulusCurveIdeal_isInvertible DL)
  let N := E.support.sup (fun w => E w) + 1
  have hN : 0 < N := Nat.zero_lt_succ _
  have hEA : E ≤ N • A := by
    intro w
    change E w ≤ N * A w
    by_cases hw : E w = 0
    · rw [hw]
      exact Nat.zero_le _
    have hAw : 0 < A w := Nat.pos_of_ne_zero (fun h => hw (hE w h))
    have hEN : E w ≤ N :=
      (Finset.le_sup (Finsupp.mem_support_iff.mpr hw)).trans (Nat.le_succ _)
    exact hEN.trans ((Nat.mul_one N).symm.le.trans (Nat.mul_le_mul_left N hAw))
  let I := modulusCurveIdeal D
  have hI : I.IsInvertible := modulusCurveIdeal_isInvertible D
  have hex : ∃ (e : ℕ) (P : RelEffCartierDiv c e (𝟙 (Spec (.of K)))),
      modulusCurveIdeal P = I ^ N :=
    M.exists_relativeDivisor_ideal (I ^ N) (hI.pow N)
  obtain ⟨e, P, hP⟩ := hex
  have hcomp : modulusComplement (modulusCurveMap P) =
      modulusComplement (modulusCurveMap D) := by
    change (modulusCurveIdeal P).support.compl = I.support.compl
    rw [hP, Scheme.IdealSheafData.support_pow I N (Nat.ne_of_gt hN)]
  have hPL : modulusCurveIdeal (P.changeBaseOfIdentity (specMap K L)) =
      (modulusCurveIdeal DL) ^ N := by
    calc
      _ = (modulusCurveIdeal P).comap (pullback.fst c (specMap K L)) :=
        modulusCurveIdeal_scalarExtension c P L
      _ = (I ^ N).comap (pullback.fst c (specMap K L)) :=
        congrArg (fun J : C.IdealSheafData => J.comap (pullback.fst c (specMap K L))) hP
      _ = (I.comap (pullback.fst c (specMap K L))) ^ N :=
        AlgebraicGeometry.Scheme.IdealSheafData.comap_pow
          (pullback.fst c (specMap K L)) I N
      _ = (modulusCurveIdeal DL) ^ N :=
        congrArg (fun J : (pullback c (specMap K L)).IdealSheafData => J ^ N)
          (modulusCurveIdeal_scalarExtension c D L).symm
  refine ⟨N, hN, e, P, hP, hcomp, ?_⟩
  have hmodulus : ML.cartierModulus
      (modulusCurveIdeal (P.changeBaseOfIdentity (specMap K L)))
      (modulusCurveIdeal_isInvertible (P.changeBaseOfIdentity (specMap K L))) = N • A :=
    cartierModulus_power_of_ideal_eq ML (modulusCurveIdeal DL)
      (modulusCurveIdeal (P.changeBaseOfIdentity (specMap K L)))
      (modulusCurveIdeal_isInvertible DL)
      (modulusCurveIdeal_isInvertible (P.changeBaseOfIdentity (specMap K L))) N hPL
  exact hEA.trans_eq hmodulus.symm

end AlgebraicGeometry.GeneralizedJacobian
