/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedEulerDegree
import Nyll.JacobianVarieties.Generalized.DivisorRigidification
import Nyll.AlgebraicCurves.Models.Points.IsRationalPointPlace
import Nyll.AlgebraicCurves.Places.Evaluation.Evaluation
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomFiniteFinrankSubschemeIotaKerPow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPow

/-! # The actual divisor-to-bundle map preserves degree -/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
open scoped BigOperators

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)
  (𝒱 : M.C.TwoAffineOpenCover)

include M in
/-- Every actual place of this algebraically closed model has residue degree one. -/
theorem place_deg_eq_one (w : Place K F) : w.deg = 1 := by
  have h := Place.deg_eq_one_of_isRational
    (M.isRational_pointEquivPlace (M.pointEquivPlace.symm w))
  simpa only [M.pointEquivPlace.apply_symm_apply] using h

/-- The canonically rigidified inverse ideal of an actual point has Euler degree one. -/
theorem eulerDegree_rigidifiedPointBundle (w : Place K F)
    (hw : M.cartierModulus I hI w = 0) :
    eulerDegree M.toBase 𝒱 I.subschemeι
      (Additive.ofMul (classOf (M.rigidifiedPointBundle I hI w hw))) = 1 := by
  let ε := pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1 (M.placeEquiv.symm w).2
  have hε : ε ≫ M.toBase = 𝟙 _ :=
    pointOfClosedPoint_comp M.toBase (M.placeEquiv.symm w).1 (M.placeEquiv.symm w).2
  have hp := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε
  have hd := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id ε hε 1
  have hχ := (hp.pow 1).eulerChar_sectionsOf_tensor_invModule_eq
    M.toBase hd.1 hd.2.1 (𝟙_ M.C.Modules) (Scheme.Modules.isInvertible_unit M.C) 𝒱
  change moduleEulerCharacteristic M.toBase 𝒱 (𝟙_ M.C.Modules ⊗ (ε.ker ^ 1).invModule) =
    moduleEulerCharacteristic M.toBase 𝒱 (𝟙_ M.C.Modules) + (1 : ℕ) at hχ
  rw [pow_one] at hχ
  rw [moduleEulerCharacteristic_iso M.toBase 𝒱 (λ_ ε.ker.invModule)] at hχ
  rw [eulerDegree_classOf]
  change moduleEulerCharacteristic M.toBase 𝒱 ε.ker.invModule -
    moduleEulerCharacteristic M.toBase 𝒱 (𝟙_ M.C.Modules) = 1
  omega

/-- The actual class of every divisor avoiding the full modulus has exactly
its usual function-field degree. -/
theorem eulerDegree_rigidifiedDivisorAwayHom
    (E : (M.cartierModulus I hI).divAway) :
    eulerDegree M.toBase 𝒱 I.subschemeι (M.rigidifiedDivisorAwayHom I hI E) =
      Divisor.degree (E : Divisor K F) := by
  classical
  change eulerDegree M.toBase 𝒱 I.subschemeι (M.rigidifiedDivisorHom I hI E.1) = _
  rw [rigidifiedDivisorHom, Finsupp.liftAddHom_apply, Divisor.degree,
    Finsupp.liftAddHom_apply]
  change eulerDegree M.toBase 𝒱 I.subschemeι
    (∑ w ∈ E.1.support, E.1 w • Additive.ofMul (M.rigidifiedPointClass I hI w)) =
      ∑ w ∈ E.1.support, E.1 w * (w.deg : ℤ)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  have hwa : M.cartierModulus I hI w = 0 := by
    by_contra hmod
    exact (Finsupp.mem_support_iff.mp hw) (E.2 w hmod)
  rw [map_zsmul, rigidifiedPointClass, dite_eq_left hwa,
    M.eulerDegree_rigidifiedPointBundle I hI 𝒱 w hwa, M.place_deg_eq_one w]
  simp only [zsmul_eq_mul, Int.natCast_one, mul_one, Int.cast_id]

end AlgebraicCurve.CurveModel
