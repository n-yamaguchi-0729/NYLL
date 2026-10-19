/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Actual evaluation on the generic formal diagonal

The tensor evaluation `a ⊗ b ↦ σ(a) C(b)` has constant coefficient equal
to multiplication. Denominators outside the diagonal prime therefore map
to units, constructing an actual map from its local ring into power series.
-/

noncomputable section

open scoped TensorProduct

namespace PowerSeries

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The prime of the generic diagonal is the kernel of multiplication. -/
def diagonalPrime : PrimeSpectrum (F ⊗[K] F) :=
  ⟨RingHom.ker (Algebra.TensorProduct.lmul' K (S := F)).toRingHom,
    RingHom.ker_isPrime _⟩

/-- The actual tensor evaluation keeps the first point moving and the
second point constant. -/
def diagonalTensorMap (σ : F →ₐ[K] PowerSeries F) :
    (F ⊗[K] F) →ₐ[K] PowerSeries F :=
  Algebra.TensorProduct.productMap σ (IsScalarTower.toAlgHom K F (PowerSeries F))

/-- Reduction of the formal diagonal evaluation is multiplication. -/
theorem constantCoeff_diagonalTensorMap
    (σ : F →ₐ[K] PowerSeries F)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    (r : F ⊗[K] F) :
    PowerSeries.constantCoeff (diagonalTensorMap σ r) =
      Algebra.TensorProduct.lmul' K r := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    change PowerSeries.constantCoeff (σ a * PowerSeries.C b) = a * b
    rw [map_mul, PowerSeries.constantCoeff_C]
    exact congrArg (fun z : F => z * b) (RingHom.congr_fun hσ0 a)
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- Every denominator outside the diagonal prime becomes an actual unit. -/
theorem isUnit_diagonalTensorMap
    (σ : F →ₐ[K] PowerSeries F)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    (s : (diagonalPrime (K := K) (F := F)).asIdeal.primeCompl) :
    IsUnit (diagonalTensorMap σ s) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [constantCoeff_diagonalTensorMap σ hσ0]
  apply isUnit_iff_ne_zero.mpr
  intro hs
  exact s.property (RingHom.mem_ker.mpr hs)

/-- Actual evaluation of functions regular at the generic diagonal. -/
def diagonalEvaluation
    (σ : F →ₐ[K] PowerSeries F)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F) :
    Localization.AtPrime (diagonalPrime (K := K) (F := F)).asIdeal →+*
      PowerSeries F :=
  IsLocalization.lift (g := (diagonalTensorMap σ).toRingHom)
    (isUnit_diagonalTensorMap σ hσ0)

/-- The local-ring evaluation extends the original tensor evaluation. -/
theorem diagonalEvaluation_algebraMap
    (σ : F →ₐ[K] PowerSeries F)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    (r : F ⊗[K] F) :
    diagonalEvaluation σ hσ0
        (algebraMap (F ⊗[K] F)
          (Localization.AtPrime (diagonalPrime (K := K) (F := F)).asIdeal) r) =
      diagonalTensorMap σ r :=
  IsLocalization.lift_eq (isUnit_diagonalTensorMap σ hσ0) r

end PowerSeries
