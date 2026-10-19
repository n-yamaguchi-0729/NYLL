/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.DivisorRigidification
import Nyll.JacobianVarieties.Generalized.RigidifiedDivisorProducts
import Nyll.AlgebraicCurves.Models.Divisors.CartierIdealEquiv

/-!
# Effective divisor compatibility of the actual rigidified divisor map

The map on function-field divisors sends the full multiplicity divisor of an
actual effective Cartier ideal to its canonically rigidified inverse ideal.
The proof uses equality of the original ideal with the product of its point
ideals, retaining every multiplicity and the chosen section normalization.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GeneralizedJacobian
open AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
open scoped BigOperators

namespace AlgebraicCurve.CurveModel

attribute [local instance] CurveModel.isIntegral CurveModel.isProper CurveModel.smooth

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F]
  (M : CurveModel K F) (I : M.C.IdealSheafData) (hI : I.IsInvertible)

private theorem pointPower_isInvertible (E : Modulus K F) (w : Place K F) :
    ((pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1
      (M.placeEquiv.symm w).2).ker ^ E w).IsInvertible :=
  (Scheme.Hom.isInvertible_ker_of_comp_eq_id _
    (pointOfClosedPoint_comp M.toBase (M.placeEquiv.symm w).1
      (M.placeEquiv.symm w).2)).pow (E w)

private theorem pointPower_avoids (E : Modulus K F)
    (hE : ∀ w, E w ≠ 0 → M.cartierModulus I hI w = 0) (w : Place K F) :
    ∀ z : I.subscheme, I.subschemeι.base z ∉
      ((pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1
        (M.placeEquiv.symm w).2).ker ^ E w).support := by
  by_cases hw : E w = 0
  · intro z
    rw [hw, pow_zero, Scheme.IdealSheafData.one_eq_top,
      Scheme.IdealSheafData.support_top]
    exact fun h => h
  · exact avoids_pow I.subschemeι _ (M.pointIdeal_avoids_modulus I hI w (hE w hw)) (E w)

/-- An effective divisor away from the modulus has an actual disjoint point product. -/
theorem pointIdealProduct_avoids_modulus (E : Modulus K F)
    (hE : ∀ w, E w ≠ 0 → M.cartierModulus I hI w = 0) :
    ∀ z : I.subscheme, I.subschemeι.base z ∉ (M.pointIdealProduct E).support :=
  avoids_finset_prod I.subschemeι E.support _ (pointPower_avoids M I hI E hE)

/-- Effective function-field divisors map to the actual canonically rigidified
point product, not merely to its underlying ordinary Picard class. -/
theorem rigidifiedDivisorHom_effective (E : Modulus K F)
    (hE : ∀ w, E w ≠ 0 → M.cartierModulus I hI w = 0) :
    M.rigidifiedDivisorHom I hI E.toDivisor =
      Additive.ofMul (classOf (ofInvertibleIdeal I.subschemeι (M.pointIdealProduct E)
        (M.pointIdealProduct_isInvertible E)
        (M.pointIdealProduct_avoids_modulus I hI E hE))) := by
  classical
  rw [rigidifiedDivisorHom, Finsupp.liftAddHom_apply, Modulus.toDivisor,
    Finsupp.sum_mapRange_index (fun _ => zero_zsmul _)]
  change (∑ w ∈ E.support, (E w : ℤ) • Additive.ofMul (M.rigidifiedPointClass I hI w)) =
    Additive.ofMul (classOf (ofInvertibleIdeal I.subschemeι
      (∏ w ∈ E.support, (pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1
        (M.placeEquiv.symm w).2).ker ^ E w)
      (isInvertible_finset_prod E.support _ (pointPower_isInvertible M E))
      (avoids_finset_prod I.subschemeι E.support _ (pointPower_avoids M I hI E hE))))
  rw [classOf_ofInvertibleIdeal_finset_prod I.subschemeι E.support _
    (pointPower_isInvertible M E) (pointPower_avoids M I hI E hE), ofMul_prod]
  apply Finset.sum_congr rfl
  intro w hw
  have hwa := hE w (Finsupp.mem_support_iff.mp hw)
  have hpow := classOf_ofInvertibleIdeal_pow I.subschemeι
    (pointOfClosedPoint M.toBase (M.placeEquiv.symm w).1 (M.placeEquiv.symm w).2).ker
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id _
      (pointOfClosedPoint_comp M.toBase (M.placeEquiv.symm w).1 (M.placeEquiv.symm w).2))
    (M.pointIdeal_avoids_modulus I hI w hwa) (E w)
  rw [hpow, ofMul_pow, natCast_zsmul]
  congr 1
  rw [rigidifiedPointClass, dite_eq_left hwa]
  rfl

/-- The full divisor of a Cartier ideal away from the modulus maps to that
ideal's specified rigidified inverse module. -/
theorem rigidifiedDivisorHom_cartierModulus (J : M.C.IdealSheafData) (hJ : J.IsInvertible)
    (ha : ∀ z : I.subscheme, I.subschemeι.base z ∉ J.support) :
    M.rigidifiedDivisorHom I hI (M.cartierModulus J hJ).toDivisor =
      Additive.ofMul (classOf (ofInvertibleIdeal I.subschemeι J hJ ha)) := by
  have hE : ∀ w, M.cartierModulus J hJ w ≠ 0 → M.cartierModulus I hI w = 0 := by
    intro w hw
    apply (M.cartierModulus_eq_zero_iff I hI w).mpr
    intro hxI
    have hxrange : (M.placeEquiv.symm w).1 ∈ Set.range I.subschemeι := by
      rw [I.range_subschemeι]
      exact hxI
    obtain ⟨z, hz⟩ := hxrange
    apply hw
    apply (M.cartierModulus_eq_zero_iff J hJ w).mpr
    rw [← hz]
    exact ha z
  have h := M.rigidifiedDivisorHom_effective I hI (M.cartierModulus J hJ) hE
  simpa only [← M.eq_pointIdealProduct_cartierModulus J hJ] using h

omit [IsAlgClosed K] in
/-- The full multiplicity divisor of a disjoint Cartier ideal belongs to the
actual function-field subgroup of divisors away from the modulus. -/
theorem cartierModulus_toDivisor_mem_divAway
    (J : M.C.IdealSheafData) (hJ : J.IsInvertible)
    (ha : ∀ z : I.subscheme, I.subschemeι.base z ∉ J.support) :
    (M.cartierModulus J hJ).toDivisor ∈ (M.cartierModulus I hI).divAway := by
  intro w hw
  have hxI : (M.placeEquiv.symm w).1 ∈ I.support := by
    by_contra hx
    exact hw ((M.cartierModulus_eq_zero_iff I hI w).mpr hx)
  have hxrange : (M.placeEquiv.symm w).1 ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hxI
  obtain ⟨z, hz⟩ := hxrange
  have hxJ : (M.placeEquiv.symm w).1 ∉ J.support := hz ▸ ha z
  rw [Modulus.toDivisor_apply,
    (M.cartierModulus_eq_zero_iff J hJ w).mpr hxJ, Int.natCast_zero]

end AlgebraicCurve.CurveModel
