/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Models.Divisors.CartierModulus
import Nyll.AlgebraicCurves.Models.Divisors.PointIdealSupport
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
import Nyll.JacobianVarieties.Generalized.DivisorClasses
import Nyll.JacobianVarieties.Generalized.RigidifiedDivisorTensor
import Nyll.JacobianVarieties.Generalized.RigidifiedCommutativity
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Actual rigidified bundles of divisors away from a Cartier modulus

Each place outside the modulus gives the inverse ideal of its actual rational
point with its canonical section normalized on the entire modulus. Integer
linear extension constructs the divisor-to-rigidified-class homomorphism.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GeneralizedJacobian

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

/-- The actual point of an allowed place is disjoint from the original modulus. -/
theorem pointIdeal_avoids_modulus (w : Place K F) (hw : M.cartierModulus I hI w = 0) :
    ∀ z : I.subscheme, I.subschemeι.base z ∉
      (pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1
        (M.placeEquiv.symm w).2).ker.support := by
  intro z hz
  have hz' : I.subschemeι z = (M.placeEquiv.symm w).1 := by
    have hs := M.pointOfClosedPoint_ker_support (M.placeEquiv.symm w)
    change I.subschemeι z ∈
      ((pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1
        (M.placeEquiv.symm w).2).ker.support : Set M.C) at hz
    rw [hs] at hz
    exact hz
  have hzI : I.subschemeι z ∈ I.support := by
    change I.subschemeι z ∈ (I.support : Set M.C)
    rw [← I.range_subschemeι]
    exact ⟨z, rfl⟩
  exact (M.cartierModulus_eq_zero_iff I hI w).mp hw (hz' ▸ hzI)

/-- `O(w)` with its canonical full-modulus rigidification, for an allowed place. -/
def rigidifiedPointBundle (w : Place K F) (hw : M.cartierModulus I hI w = 0) :
    RigidifiedLineBundle I.subschemeι :=
  RigidifiedLineBundle.ofInvertibleIdeal I.subschemeι
    (pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1 (M.placeEquiv.symm w).2).ker
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id _
      (pointOfClosedPoint_comp M.toBase (M.placeEquiv.symm w).1 (M.placeEquiv.symm w).2))
    (M.pointIdeal_avoids_modulus I hI w hw)

/-- The point class, extended by the identity at forbidden places for finite summation. -/
def rigidifiedPointClass (w : Place K F) : RigidifiedLineBundle.Classes I.subschemeι :=
  if hw : M.cartierModulus I hI w = 0 then
    RigidifiedLineBundle.classOf (M.rigidifiedPointBundle I hI w hw)
  else 1

/-- Integer divisors give actual tensor-product classes of canonical point bundles. -/
def rigidifiedDivisorHom :
    Divisor K F →+ Additive (RigidifiedLineBundle.Classes I.subschemeι) :=
  Finsupp.liftAddHom (fun w =>
    { toFun := fun n : ℤ => n • Additive.ofMul (M.rigidifiedPointClass I hI w)
      map_zero' := zero_zsmul _
      map_add' := fun m n => add_zsmul _ m n })

/-- The concrete homomorphism on the actual subgroup of divisors away from the modulus. -/
def rigidifiedDivisorAwayHom :
    (M.cartierModulus I hI).divAway →+
      Additive (RigidifiedLineBundle.Classes I.subschemeι) :=
  (M.rigidifiedDivisorHom I hI).comp (M.cartierModulus I hI).divAway.subtype

/-- A single allowed point maps to its actual canonically rigidified inverse ideal. -/
theorem rigidifiedDivisorHom_single (w : Place K F) (hw : M.cartierModulus I hI w = 0) :
    M.rigidifiedDivisorHom I hI (Finsupp.single w 1) =
      Additive.ofMul (RigidifiedLineBundle.classOf (M.rigidifiedPointBundle I hI w hw)) := by
  rw [rigidifiedDivisorHom, Finsupp.liftAddHom_apply_single]
  change (1 : ℤ) • Additive.ofMul (M.rigidifiedPointClass I hI w) = _
  rw [one_zsmul, rigidifiedPointClass, dite_eq_left hw]

/-- A difference of allowed points maps to the quotient of their full-modulus classes. -/
theorem rigidifiedDivisorHom_point_difference
    (w v₀ : Place K F) (hw : M.cartierModulus I hI w = 0)
    (h₀ : M.cartierModulus I hI v₀ = 0) :
    M.rigidifiedDivisorHom I hI (Finsupp.single w 1 - Finsupp.single v₀ 1) =
      Additive.ofMul
        (RigidifiedLineBundle.classOf (M.rigidifiedPointBundle I hI w hw) /
          RigidifiedLineBundle.classOf (M.rigidifiedPointBundle I hI v₀ h₀)) := by
  rw [map_sub, M.rigidifiedDivisorHom_single I hI w hw,
    M.rigidifiedDivisorHom_single I hI v₀ h₀]
  rfl

end AlgebraicCurve.CurveModel
