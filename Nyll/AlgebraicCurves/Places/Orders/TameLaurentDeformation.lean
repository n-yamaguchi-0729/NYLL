/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.LaurentFormalTranslationOrder
import Nyll.AlgebraicCurves.Places.Orders.TameParameterOrder
import Nyll.AlgebraicCurves.Places.Orders.TameSeriesCompositionOrder
import Nyll.AlgebraicCurves.Places.ValuationRings.OrdEqNegLogValuationSubringEq

/-! # Actual tame deformation of the completed local field

The Hensel-constructed tame displacement is substituted into the actual
Laurent translation. Its coefficient growth is `e*n + order(f)` for every
Laurent function, including one with a pole. Restriction along an actual
field embedding retains the given residue embedding and the same bound.
-/

noncomputable section

open scoped WithZero

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- The parameter place of the Laurent field, constructed from the
height-one prime `(X)` in its power-series valuation ring. -/
def orderPlace : AlgebraicCurve.Place K (LaurentSeries K) := by
  have htower := IsScalarTower.of_algebraMap_eq
    (R := K) (S := PowerSeries K) (A := LaurentSeries K) (fun _ => rfl)
  exact AlgebraicCurve.Place.ofHeightOneSpectrum (PowerSeries.idealX K)

/-- The normalized order of the actual parameter place equals Laurent
order, including the shared convention that zero has order zero. -/
theorem orderPlace_ord (f : LaurentSeries K) : (orderPlace (K := K)).ord f = f.order := by
  by_cases hf : f = 0
  · subst f
    rw [AlgebraicCurve.Place.ord_zero, HahnSeries.order_zero]
  have hv : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) f ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hf
  rw [(orderPlace (K := K)).ord_eq_neg_log_of_valuationSubring_eq
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) rfl
    (LaurentSeries.valuation_single_zpow K 1) hf]
  have hle : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) f ≤
      WithZero.exp (-f.order) :=
    (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).mpr
      (fun _ hj => HahnSeries.coeff_eq_zero_of_lt_order hj)
  have hlog := (WithZero.log_le_iff_le_exp hv).mpr hle
  have hvanish :=
    (LaurentSeries.valuation_le_iff_coeff_lt_log_eq_zero K hv).mp le_rfl
  have hle' : -WithZero.log ((Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) f) ≤
      f.order := by
    by_contra h
    have hlt : f.order < -WithZero.log
        ((Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) f) := lt_of_not_ge h
    exact hf (HahnSeries.coeff_order_eq_zero.mp (hvanish f.order hlt))
  omega

/-- The actual local deformation sends the normalized tame parameter to
its Hensel branch, has identity residue, and satisfies the sharp affine
coefficient bound for every Laurent function. -/
theorem exists_tameFormalDeformation (e : ℕ) (he : (e : K) ≠ 0) :
    ∃ ρ : LaurentSeries K →ₐ[K] PowerSeries (LaurentSeries K),
      PowerSeries.constantCoeff.comp ρ.toRingHom = RingHom.id (LaurentSeries K) ∧
      ρ (HahnSeries.single (1 : ℤ) (1 : K)) ^ e *
        (1 + PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) * PowerSeries.X) =
          PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) ∧
      ∀ f : LaurentSeries K, ∀ n : ℕ, 0 < n →
        PowerSeries.coeff n (ρ f - PowerSeries.C f) ≠ 0 →
          (e : ℤ) * n + f.order ≤ (PowerSeries.coeff n (ρ f - PowerSeries.C f)).order := by
  let v := orderPlace (K := K)
  let r : LaurentSeries K := HahnSeries.single 1 1
  have hr : v.ord r = 1 := by
    rw [orderPlace_ord, HahnSeries.order_single one_ne_zero]
  obtain ⟨B, _hB0, _hBe, hS⟩ := v.exists_tameParameterChange_exact_orders e he r hr
  let S := PowerSeries.C r * PowerSeries.rescale (r ^ e)
    (PowerSeries.map (algebraMap K (LaurentSeries K)) B)
  have hS0 : PowerSeries.constantCoeff S = r := hS.1
  let δ := S - PowerSeries.C r
  have hδ0 : PowerSeries.constantCoeff δ = 0 := by
    change PowerSeries.constantCoeff (S - PowerSeries.C r) = 0
    rw [map_sub, hS0, PowerSeries.constantCoeff_C, sub_self]
  let A : PowerSeries (LaurentSeries K) →ₐ[LaurentSeries K]
      PowerSeries (LaurentSeries K) :=
    PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hδ0)
  let ρ : LaurentSeries K →ₐ[K] PowerSeries (LaurentSeries K) :=
    (A.restrictScalars K).comp formalTranslation
  have hρ0 (f : LaurentSeries K) : PowerSeries.constantCoeff (ρ f) = f := by
    change PowerSeries.constantCoeff
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hδ0)
        (formalTranslation f)) = f
    rw [PowerSeries.coe_substAlgHom]
    change MvPowerSeries.constantCoeff (PowerSeries.subst δ (formalTranslation f)) = f
    rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hδ0]
    exact constantCoeff_formalTranslation f
  have hρr : ρ r = S := by
    change A (formalTranslation r) = S
    rw [formalTranslation_parameter, map_add]
    have hC : A (PowerSeries.C r) = PowerSeries.C r := A.commutes r
    have hX : A PowerSeries.X = δ :=
      PowerSeries.substAlgHom_X (PowerSeries.HasSubst.of_constantCoeff_zero' hδ0)
    rw [hC, hX]
    change PowerSeries.C r + (S - PowerSeries.C r) = S
    abel
  refine ⟨ρ, RingHom.ext hρ0, ?_, ?_⟩
  · change ρ r ^ e * (1 + PowerSeries.C (r ^ e) * PowerSeries.X) = _
    rw [hρr]
    exact hS.2.1
  · intro f n hn hc
    have hcoeff : PowerSeries.coeff n (ρ f - PowerSeries.C f) =
        PowerSeries.coeff n (PowerSeries.subst δ (formalTranslation f)) := by
      rw [map_sub, PowerSeries.coeff_C_of_ne_zero (Nat.ne_of_gt hn), sub_zero]
      change PowerSeries.coeff n
        (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hδ0)
          (formalTranslation f)) = _
      rw [PowerSeries.coe_substAlgHom]
    rw [hcoeff] at hc ⊢
    have h := v.powerSeries_subst_coeff_ord_affine
      (formalTranslation f) δ f.order 1 e 1 le_rfl hδ0
      (fun m hm => by
        rw [orderPlace_ord]
        simpa only [one_mul] using order_coeff_formalTranslation_ge f m hm)
      (fun m hm hne => by
        rw [hS.2.2 m hm hne]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, le_refl]) n hc
    rw [orderPlace_ord] at h
    simpa only [add_sub_cancel_right, add_comm] using h

/-- Restricting the constructed tame deformation along an actual field
embedding preserves that residue embedding and controls the displacement of
every embedded function, including a fixed global separating parameter. -/
theorem exists_tameFormalDeformation_comp
    {F : Type*} [Field F] [Algebra K F]
    (i : F →ₐ[K] LaurentSeries K) (e : ℕ) (he : (e : K) ≠ 0) :
    ∃ ρ : F →ₐ[K] PowerSeries (LaurentSeries K),
      PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom ∧
      ∀ f : F, ∀ n : ℕ, 0 < n →
        PowerSeries.coeff n (ρ f - PowerSeries.C (i f)) ≠ 0 →
          (e : ℤ) * n + (i f).order ≤
            (PowerSeries.coeff n (ρ f - PowerSeries.C (i f))).order := by
  obtain ⟨ρ, hρ0, _hparameter, horder⟩ := exists_tameFormalDeformation (K := K) e he
  refine ⟨ρ.comp i, ?_, fun f n hn hc => horder (i f) n hn hc⟩
  apply RingHom.ext
  intro f
  exact RingHom.congr_fun hρ0 (i f)

end LaurentSeries
