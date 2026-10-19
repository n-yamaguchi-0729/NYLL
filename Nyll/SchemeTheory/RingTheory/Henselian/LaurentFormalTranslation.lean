/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.LaurentSeries

/-! # Actual formal translation on the Laurent field

Bivariate substitution constructs translation on the power-series ring.
After including the coefficient ring in its Laurent field, every nonzero
denominator has invertible constant coefficient. Localization therefore
extends translation to the entire Laurent field, with residue the identity.
The construction uses all coefficients and is valid in positive characteristic.
-/

noncomputable section

open scoped nonZeroDivisors

namespace PowerSeries

variable {K : Type*} [Field K]

private def oneVariableEquiv : MvPowerSeries (Fin 1) K ≃ₐ[K] PowerSeries K :=
  MvPowerSeries.renameEquiv K (Equiv.ofUnique (Fin 1) Unit)

private theorem coeff_oneVariableEquiv (f : MvPowerSeries (Fin 1) K) (n : ℕ) :
    coeff n (oneVariableEquiv f) = MvPowerSeries.coeff (Finsupp.single 0 n) f := by
  let e : Fin 1 ≃ Unit := Equiv.ofUnique (Fin 1) Unit
  have hs : Finsupp.embDomain e.toEmbedding (Finsupp.single 0 n) =
      Finsupp.single () n := by
    rw [Finsupp.embDomain_single]
  change MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.rename e f) = _
  rw [← hs]
  exact MvPowerSeries.coeff_embDomain_rename e.toEmbedding f (Finsupp.single 0 n)

private theorem oneVariableEquiv_X :
    oneVariableEquiv (MvPowerSeries.X (0 : Fin 1)) = (X : PowerSeries K) := by
  change MvPowerSeries.rename (Equiv.ofUnique (Fin 1) Unit)
    (MvPowerSeries.X (0 : Fin 1)) = X
  rw [MvPowerSeries.rename_X]
  rfl

private theorem hasSubst_twoVariables : HasSubst
    (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
  HasSubst.of_constantCoeff_zero (by
    rw [map_add, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_X, add_zero])

/-- Formal translation of a power series, constructed by bivariate
substitution and regrouping the two formal variables. -/
def formalTranslation : PowerSeries K →ₐ[K] PowerSeries (PowerSeries K) :=
  (mapAlgHom oneVariableEquiv.toAlgHom).comp
    ((MvPowerSeries.finSuccEquiv K 1).toAlgHom.comp
      (substAlgHom hasSubst_twoVariables))

/-- Every translated coefficient is the actual Hasse coefficient, with the
binomial factor interpreted in the coefficient field. -/
theorem coeff_coeff_formalTranslation (f : PowerSeries K) (n m : ℕ) :
    coeff m (coeff n (formalTranslation f)) =
      ((n + m).choose n : K) * coeff (n + m) f := by
  change coeff m (coeff n (mapAlgHom oneVariableEquiv.toAlgHom
    (MvPowerSeries.finSuccEquiv K 1 (substAlgHom hasSubst_twoVariables f)))) = _
  rw [mapAlgHom_apply, coeff_map]
  change coeff m (oneVariableEquiv
    (coeff n (MvPowerSeries.finSuccEquiv K 1 (substAlgHom hasSubst_twoVariables f)))) = _
  rw [coeff_oneVariableEquiv, MvPowerSeries.coeff_coeff_finSuccEquiv, coe_substAlgHom]
  change MvPowerSeries.coeff ((Finsupp.single (0 : Fin 1) m).cons n)
    (subst (MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X 1) f) = _
  have hindex : ((Finsupp.single (0 : Fin 1) m).cons n) (1 : Fin 2) = m := by
    change ((Finsupp.single (0 : Fin 1) m).cons n) (0 : Fin 1).succ = m
    rw [Finsupp.cons_succ, Finsupp.single_eq_same]
  simpa only [Finsupp.cons_zero, hindex] using
    coeff_subst_X_zero_add_X_one f ((Finsupp.single (0 : Fin 1) m).cons n)

/-- Taking the new formal parameter to zero recovers the original series. -/
theorem constantCoeff_formalTranslation (f : PowerSeries K) :
    constantCoeff (formalTranslation f) = f := by
  ext m
  simpa only [coeff_zero_eq_constantCoeff, Nat.zero_add, Nat.choose_zero_right,
    Nat.cast_one, one_mul] using coeff_coeff_formalTranslation f 0 m

/-- The original parameter is translated by the new formal parameter. -/
theorem formalTranslation_X :
    formalTranslation (X : PowerSeries K) = C X + X := by
  change mapAlgHom oneVariableEquiv.toAlgHom
    (MvPowerSeries.finSuccEquiv K 1 (substAlgHom hasSubst_twoVariables X)) = _
  rw [substAlgHom_X, map_add, MvPowerSeries.finSuccEquiv_X_zero]
  have hsucc : MvPowerSeries.finSuccEquiv K 1 (MvPowerSeries.X (1 : Fin 2)) =
      C (MvPowerSeries.X (0 : Fin 1)) :=
    MvPowerSeries.finSuccEquiv_X_succ (R := K) (0 : Fin 1)
  rw [hsucc]
  rw [mapAlgHom_apply, map_add, map_X, map_C]
  change X + C (oneVariableEquiv (MvPowerSeries.X (0 : Fin 1))) = _
  rw [oneVariableEquiv_X, add_comm]

end PowerSeries

namespace LaurentSeries

variable {K : Type*} [Field K]

private def coefficientInclusion : PowerSeries K →ₐ[K] LaurentSeries K where
  toRingHom := HahnSeries.ofPowerSeries ℤ K
  commutes' _ := rfl

/-- The power-series translation with its coefficients included in the
Laurent field. -/
def powerSeriesTranslation :
    PowerSeries K →ₐ[K] PowerSeries (LaurentSeries K) :=
  (PowerSeries.mapAlgHom (coefficientInclusion (K := K))).comp
    PowerSeries.formalTranslation

theorem constantCoeff_powerSeriesTranslation (f : PowerSeries K) :
    PowerSeries.constantCoeff (powerSeriesTranslation f) = (f : LaurentSeries K) := by
  change PowerSeries.constantCoeff (PowerSeries.mapAlgHom
    (coefficientInclusion (K := K)) (PowerSeries.formalTranslation f)) = _
  rw [PowerSeries.mapAlgHom_apply, ← PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    PowerSeries.constantCoeff_formalTranslation]
  rfl

private theorem powerSeriesTranslation_isUnit
    (f : PowerSeries K) (hf : f ≠ 0) : IsUnit (powerSeriesTranslation f) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [constantCoeff_powerSeriesTranslation]
  apply isUnit_iff_ne_zero.mpr
  intro h
  apply hf
  exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)

/-- Translation on the entire Laurent field, obtained by localizing the
actual power-series translation into a power-series ring. -/
def formalTranslation : LaurentSeries K →ₐ[K] PowerSeries (LaurentSeries K) := by
  have htower := IsScalarTower.of_algebraMap_eq
    (R := K) (S := PowerSeries K) (A := LaurentSeries K) (fun _ => rfl)
  exact IsLocalization.liftAlgHom (S := LaurentSeries K) (M := (PowerSeries K)⁰)
    (f := powerSeriesTranslation)
    (fun f => powerSeriesTranslation_isUnit (f : PowerSeries K)
      (mem_nonZeroDivisors_iff_ne_zero.mp f.property))

/-- Laurent translation agrees with the original bivariate construction on
every power series. -/
theorem formalTranslation_coe (f : PowerSeries K) :
    formalTranslation (f : LaurentSeries K) = powerSeriesTranslation f := by
  exact IsLocalization.lift_eq (S := LaurentSeries K)
    (fun g : (PowerSeries K)⁰ => powerSeriesTranslation_isUnit (g : PowerSeries K)
      (mem_nonZeroDivisors_iff_ne_zero.mp g.property)) f

/-- Translation on the entire Laurent field has residue the identity. -/
theorem constantCoeff_comp_formalTranslation :
    (PowerSeries.constantCoeff (R := LaurentSeries K)).comp formalTranslation.toRingHom =
      RingHom.id (LaurentSeries K) := by
  apply IsLocalization.ringHom_ext (M := (PowerSeries K)⁰)
  apply RingHom.ext
  intro f
  change PowerSeries.constantCoeff (formalTranslation (f : LaurentSeries K)) =
    (f : LaurentSeries K)
  rw [formalTranslation_coe, constantCoeff_powerSeriesTranslation]

theorem constantCoeff_formalTranslation (f : LaurentSeries K) :
    PowerSeries.constantCoeff (formalTranslation f) = f :=
  RingHom.congr_fun constantCoeff_comp_formalTranslation f

/-- The actual Laurent parameter is sent to its sum with the new parameter. -/
theorem formalTranslation_parameter :
    formalTranslation (HahnSeries.single (1 : ℤ) (1 : K)) =
      PowerSeries.C (HahnSeries.single (1 : ℤ) (1 : K)) + PowerSeries.X := by
  rw [← (PowerSeries.coe_X (R := K)), formalTranslation_coe]
  change PowerSeries.mapAlgHom (coefficientInclusion (K := K))
    (PowerSeries.formalTranslation PowerSeries.X) = _
  rw [PowerSeries.formalTranslation_X, PowerSeries.mapAlgHom_apply, map_add,
    PowerSeries.map_C, PowerSeries.map_X]
  rfl

/-- A translated power-series coefficient has a constructed integral
power-series preimage, before any order estimates are used. -/
theorem coeff_formalTranslation_coe (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (formalTranslation (f : LaurentSeries K)) =
      ((PowerSeries.coeff n (PowerSeries.formalTranslation f) : PowerSeries K) :
        LaurentSeries K) := by
  rw [formalTranslation_coe]
  change PowerSeries.coeff n (PowerSeries.mapAlgHom (coefficientInclusion (K := K))
    (PowerSeries.formalTranslation f)) = _
  rw [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map]
  rfl

end LaurentSeries
