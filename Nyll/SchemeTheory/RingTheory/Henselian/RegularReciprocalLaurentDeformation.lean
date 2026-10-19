/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.RegularBlockFormalDeformation

/-! # The generic field deformation of the actual regular-block base map

The reciprocal deformation of K[[s]] extends to K((s)) because its image
in L[[T]] has nonzero constant coefficient on every nonzero denominator.
It therefore agrees with the integral deformation on every power series,
not merely on its parameter. Its reciprocal parameter is translated by T.
This is the actual generic base change used for the regular-block trace.
-/

noncomputable section

open scoped nonZeroDivisors

namespace LaurentSeries

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private def nativePowerSeriesInclusion : PowerSeries K →ₐ[K] LaurentSeries K where
  toRingHom := HahnSeries.ofPowerSeries ℤ K
  commutes' _ := rfl

/-- The native coefficient map from the integral base to a common Laurent
extension field. -/
def regularBlockCoefficients (i : LaurentSeries K →ₐ[K] L) : PowerSeries K →ₐ[K] L :=
  i.comp nativePowerSeriesInclusion

private def regularReciprocalPowerSeriesMap (i : LaurentSeries K →ₐ[K] L) :
    PowerSeries K →ₐ[K] PowerSeries L :=
  (PowerSeries.mapAlgHom (regularBlockCoefficients i)).comp
    PowerSeries.reciprocalParameterDeformation

private theorem constantCoeff_regularReciprocalPowerSeriesMap
    (i : LaurentSeries K →ₐ[K] L) (f : PowerSeries K) :
    PowerSeries.constantCoeff (regularReciprocalPowerSeriesMap i f) =
      i (HahnSeries.ofPowerSeries ℤ K f) := by
  change PowerSeries.constantCoeff
    (PowerSeries.map (regularBlockCoefficients i).toRingHom
      (PowerSeries.reciprocalParameterDeformation f)) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_reciprocalParameterDeformation]
  rfl

private theorem regularReciprocalPowerSeriesMap_isUnit
    (i : LaurentSeries K →ₐ[K] L) (f : PowerSeries K) (hf : f ≠ 0) :
    IsUnit (regularReciprocalPowerSeriesMap i f) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [constantCoeff_regularReciprocalPowerSeriesMap]
  apply isUnit_iff_ne_zero.mpr
  intro h
  exact hf (HahnSeries.ofPowerSeries_injective
    ((i.injective (h.trans (map_zero i).symm)).trans (map_zero _).symm))

/-- Localizing the actual integral reciprocal deformation constructs its
actual generic-field deformation in every common coefficient field. -/
def regularReciprocalDeformation (i : LaurentSeries K →ₐ[K] L) :
    LaurentSeries K →ₐ[K] PowerSeries L := by
  have htower := IsScalarTower.of_algebraMap_eq
    (R := K) (S := PowerSeries K) (A := LaurentSeries K) (fun _ => rfl)
  exact IsLocalization.liftAlgHom (S := LaurentSeries K) (M := (PowerSeries K)⁰)
    (f := regularReciprocalPowerSeriesMap i)
    (fun f => regularReciprocalPowerSeriesMap_isUnit i (f : PowerSeries K)
      (mem_nonZeroDivisors_iff_ne_zero.mp f.property))

/-- Agreement with the entire original integral deformation. -/
theorem regularReciprocalDeformation_coe
    (i : LaurentSeries K →ₐ[K] L) (f : PowerSeries K) :
    regularReciprocalDeformation i (HahnSeries.ofPowerSeries ℤ K f) =
      PowerSeries.map (regularBlockCoefficients i).toRingHom
        (PowerSeries.reciprocalParameterDeformation f) := by
  exact IsLocalization.lift_eq (S := LaurentSeries K)
    (fun g : (PowerSeries K)⁰ => regularReciprocalPowerSeriesMap_isUnit i (g : PowerSeries K)
      (mem_nonZeroDivisors_iff_ne_zero.mp g.property)) f

/-- The actual generic deformation has the specified residue embedding. -/
theorem constantCoeff_comp_regularReciprocalDeformation
    (i : LaurentSeries K →ₐ[K] L) :
    PowerSeries.constantCoeff.comp (regularReciprocalDeformation i).toRingHom = i.toRingHom := by
  apply IsLocalization.ringHom_ext (M := (PowerSeries K)⁰)
  apply RingHom.ext
  intro f
  change PowerSeries.constantCoeff
    (regularReciprocalDeformation i (HahnSeries.ofPowerSeries ℤ K f)) = _
  rw [regularReciprocalDeformation_coe]
  exact constantCoeff_regularReciprocalPowerSeriesMap i f

/-- The integral parameter satisfies the exact reciprocal deformation
identity after extension to the common coefficient field. -/
theorem regularReciprocalDeformation_parameter
    (i : LaurentSeries K →ₐ[K] L) :
    let r : LaurentSeries K := HahnSeries.single 1 1
    regularReciprocalDeformation i r * (1 + PowerSeries.C (i r) * PowerSeries.X) =
      PowerSeries.C (i r) := by
  intro r
  have hden : PowerSeries.constantCoeff
      (1 + PowerSeries.C (PowerSeries.X : PowerSeries K) * PowerSeries.X) = 1 := by
    rw [map_add, map_one, map_mul, PowerSeries.constantCoeff_C,
      PowerSeries.constantCoeff_X, mul_zero, add_zero]
  have h : PowerSeries.reciprocalParameterDeformation (PowerSeries.X : PowerSeries K) *
      (1 + PowerSeries.C (PowerSeries.X : PowerSeries K) * PowerSeries.X) =
        PowerSeries.C (PowerSeries.X : PowerSeries K) := by
    rw [PowerSeries.reciprocalParameterDeformation_X, mul_assoc,
      PowerSeries.invOfUnit_mul _ 1 hden, mul_one]
  have hm := congrArg (PowerSeries.map (regularBlockCoefficients i).toRingHom) h
  rw [map_mul, map_add, map_one, map_mul, PowerSeries.map_C, PowerSeries.map_X] at hm
  dsimp only [r]
  rw [← (PowerSeries.coe_X (R := K)), regularReciprocalDeformation_coe]
  exact hm

/-- Thus the reciprocal base coordinate is actually translated by the
new formal parameter, in every characteristic. -/
theorem regularReciprocalDeformation_reciprocal_parameter
    (i : LaurentSeries K →ₐ[K] L) :
    let r : LaurentSeries K := HahnSeries.single 1 1
    regularReciprocalDeformation i r⁻¹ = PowerSeries.C (i r⁻¹) + PowerSeries.X := by
  intro r
  let ρ := regularReciprocalDeformation i
  have hr : r ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  have hi : PowerSeries.C (i r) * PowerSeries.C (i r⁻¹) = (1 : PowerSeries L) := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hr, map_one, map_one]
  have hfactor : (1 + PowerSeries.C (i r) * PowerSeries.X) * PowerSeries.C (i r⁻¹) =
      PowerSeries.C (i r⁻¹) + PowerSeries.X := by
    calc
      _ = PowerSeries.C (i r⁻¹) +
          (PowerSeries.C (i r) * PowerSeries.C (i r⁻¹)) * PowerSeries.X := by ring
      _ = _ := by rw [hi, one_mul]
  have hright := congrArg (fun A : PowerSeries L => A * PowerSeries.C (i r⁻¹))
    (regularReciprocalDeformation_parameter i)
  rw [mul_assoc, hfactor, hi] at hright
  have hleft : ρ r * ρ r⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hr, map_one]
  have hρr : ρ r ≠ 0 := by
    intro h
    exact hr (ρ.injective (h.trans (map_zero ρ).symm))
  exact mul_left_cancel₀ hρr (hleft.trans hright.symm)

end LaurentSeries
