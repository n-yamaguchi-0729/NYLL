/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Modulus.TameReciprocalModulusReduction
import Nyll.AlgebraicCurves.Places.Orders.TameLaurentDeformation
import Nyll.SchemeTheory.RingTheory.Henselian.SeparatingFormalTranslationComparison

/-! # The normalized tame deformation is the actual reciprocal formal lift

The tame parameter equation gives translation of the reciprocal parameter
by an algebraic cancellation identity. After restricting the constructed
Laurent deformation to the source field, finite-separable uniqueness
identifies it with every actual formal lift having that reciprocal shift
and the prescribed residue embedding. Its coefficient bounds are retained.
-/

noncomputable section

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- The tame parameter equation forces the full reciprocal shift. This is
an identity for any actual algebra homomorphism satisfying the equation;
no continuity or compatibility of formal lifts is assumed. -/
theorem reciprocal_shift_of_tame_parameter_equation
    (Ψ : LaurentSeries K →ₐ[K] PowerSeries (LaurentSeries K)) (e : ℕ)
    (hΨ : Ψ (HahnSeries.single (1 : ℤ) (1 : K)) ^ e *
      (1 + PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) * PowerSeries.X) =
        PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e)) :
    Ψ ((HahnSeries.single (e : ℤ) (1 : K))⁻¹) =
      PowerSeries.C ((HahnSeries.single (e : ℤ) (1 : K))⁻¹) + PowerSeries.X := by
  let s : LaurentSeries K := (HahnSeries.single (1 : ℤ) (1 : K)) ^ e
  have hs : s ≠ 0 := pow_ne_zero e (HahnSeries.single_ne_zero one_ne_zero)
  have hparam : Ψ s * (1 + PowerSeries.C s * PowerSeries.X) = PowerSeries.C s := by
    change Ψ ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) * _ = _
    rw [map_pow]
    exact hΨ
  have hC : PowerSeries.C s * PowerSeries.C s⁻¹ = (1 : PowerSeries (LaurentSeries K)) := by
    rw [← map_mul, mul_inv_cancel₀ hs, map_one]
  have hfactor : (1 + PowerSeries.C s * PowerSeries.X) * PowerSeries.C s⁻¹ =
      PowerSeries.C s⁻¹ + PowerSeries.X := by
    calc
      _ = PowerSeries.C s⁻¹ + (PowerSeries.C s * PowerSeries.C s⁻¹) * PowerSeries.X := by
        ring
      _ = _ := by rw [hC, one_mul]
  have hright := congrArg (fun A : PowerSeries (LaurentSeries K) =>
    A * PowerSeries.C s⁻¹) hparam
  rw [mul_assoc, hfactor, hC] at hright
  have hleft : Ψ s * Ψ s⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hs, map_one]
  have hΨs : Ψ s ≠ 0 := by
    intro h
    exact hs (Ψ.injective (h.trans (map_zero Ψ).symm))
  have hshift := mul_left_cancel₀ hΨs (hleft.trans hright.symm)
  have hsmon : HahnSeries.single (e : ℤ) (1 : K) = s := RatFunc.single_one_eq_pow e
  calc
    _ = Ψ s⁻¹ := congrArg (fun a : LaurentSeries K => Ψ a⁻¹) hsmon
    _ = PowerSeries.C s⁻¹ + PowerSeries.X := hshift
    _ = _ := congrArg
      (fun a : LaurentSeries K => PowerSeries.C a⁻¹ + PowerSeries.X) hsmon.symm

end LaurentSeries

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The constructed tame local deformation is the unique formal lift of
the normalized source embedding translating `1 / (g - 1)`. Its sharp
coefficient bounds therefore apply to any actual lift with that shift. -/
theorem exists_unique_normalized_tame_reciprocal_lift
    [PerfectField K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (v : Place K F) (g : Fˣ) (e : ℕ) (hepos : 0 < e) (he : (e : K) ≠ 0)
    (hg : v.ord ((g : F) - 1) = (e : ℤ))
    (i : F →ₐ[K] LaurentSeries K)
    (hi : i ((g : F) - 1) = HahnSeries.single (e : ℤ) (1 : K)) :
    ∃ ρ : F →ₐ[K] PowerSeries (LaurentSeries K),
      PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom ∧
      ρ (((g : F) - 1)⁻¹) =
        PowerSeries.C (i (((g : F) - 1)⁻¹)) + PowerSeries.X ∧
      (∀ f : F, ∀ n : ℕ, 0 < n →
        PowerSeries.coeff n (ρ f - PowerSeries.C (i f)) ≠ 0 →
          (e : ℤ) * n + (i f).order ≤
            (PowerSeries.coeff n (ρ f - PowerSeries.C (i f))).order) ∧
      ∀ θ : F →ₐ[K] PowerSeries (LaurentSeries K),
        PowerSeries.constantCoeff.comp θ.toRingHom = i.toRingHom →
        θ (((g : F) - 1)⁻¹) =
          PowerSeries.C (i (((g : F) - 1)⁻¹)) + PowerSeries.X → θ = ρ := by
  obtain ⟨hz, hfinite, hseparable⟩ := v.tame_reciprocal_parameter g e hepos he hg
  have : FiniteDimensional (IntermediateField.adjoin K {((g : F) - 1)⁻¹}) F := hfinite
  have : Algebra.IsSeparable (IntermediateField.adjoin K {((g : F) - 1)⁻¹}) F := hseparable
  obtain ⟨Ψ, hΨ0, hΨparameter, hΨorder⟩ :=
    LaurentSeries.exists_tameFormalDeformation (K := K) e he
  let ρ : F →ₐ[K] PowerSeries (LaurentSeries K) := Ψ.comp i
  have hρ0 : PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom := by
    apply RingHom.ext
    intro f
    exact RingHom.congr_fun hΨ0 (i f)
  have hρz : ρ (((g : F) - 1)⁻¹) =
      PowerSeries.C (i (((g : F) - 1)⁻¹)) + PowerSeries.X := by
    change Ψ (i (((g : F) - 1)⁻¹)) = _
    have hiz : i (((g : F) - 1)⁻¹) = (HahnSeries.single (e : ℤ) (1 : K))⁻¹ := by
      rw [map_inv₀, hi]
    calc
      _ = Ψ ((HahnSeries.single (e : ℤ) (1 : K))⁻¹) := congrArg Ψ hiz
      _ = PowerSeries.C ((HahnSeries.single (e : ℤ) (1 : K))⁻¹) + PowerSeries.X :=
        LaurentSeries.reciprocal_shift_of_tame_parameter_equation Ψ e hΨparameter
      _ = _ := congrArg (fun a => PowerSeries.C a + PowerSeries.X) hiz.symm
  refine ⟨ρ, hρ0, hρz, ?_, ?_⟩
  · exact fun f n hn hc => hΨorder (i f) n hn hc
  · intro θ hθ0 hθz
    exact PowerSeries.formalLift_ext_of_separating_parameter
      (((g : F) - 1)⁻¹) hz i θ ρ (hθz.trans hρz.symm) hθ0 hρ0

end AlgebraicCurve.Place
