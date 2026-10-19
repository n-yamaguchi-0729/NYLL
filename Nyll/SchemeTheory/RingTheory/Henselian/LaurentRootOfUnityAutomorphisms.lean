/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.TameLaurentNormalization
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Data.Fintype.EquivFin

/-! # Root-of-unity automorphisms of the Laurent field

Unit rescaling is first constructed on the power-series ring and then extended
through its actual fraction field. Roots of unity fix every series in the
corresponding power of the parameter, and all fractions of those series.
-/

noncomputable section

namespace PowerSeries

variable {K : Type*} [Field K]

private def unitRescaleAlgHom (a : K) : PowerSeries K →ₐ[K] PowerSeries K where
  __ := rescale a
  commutes' b := by
    change rescale a (C b) = C b
    ext n
    by_cases hn : n = 0
    · subst n
      simp only [coeff_rescale, coeff_C, ↓reduceIte, pow_zero, one_mul]
    · simp only [coeff_rescale, coeff_C, hn, ↓reduceIte, mul_zero]

/-- Multiplication of the parameter by a unit is an algebra automorphism. -/
def rescaleUnitEquiv (ζ : Kˣ) : PowerSeries K ≃ₐ[K] PowerSeries K where
  __ := unitRescaleAlgHom (ζ : K)
  invFun := rescale ((ζ⁻¹ : Kˣ) : K)
  left_inv A := by
    change rescale ((ζ⁻¹ : Kˣ) : K) (rescale (ζ : K) A) = A
    rw [rescale_rescale]
    simp only [Units.mul_inv, rescale_one, RingHom.id_apply]
  right_inv A := by
    change rescale (ζ : K) (rescale ((ζ⁻¹ : Kˣ) : K) A) = A
    rw [rescale_rescale]
    simp only [Units.inv_mul, rescale_one, RingHom.id_apply]

/-- Unit rescaling preserves the order of every power series. -/
theorem rescaleUnitEquiv_order (ζ : Kˣ) (A : PowerSeries K) :
    (rescaleUnitEquiv ζ A).order = A.order := by
  change (rescale (ζ : K) A).order = A.order
  refine le_antisymm ?_ ?_
  · apply le_order A
    intro n hn
    have h := coeff_of_lt_order (φ := rescale (ζ : K) A) n hn
    rw [coeff_rescale] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero n ζ.ne_zero)
  · apply le_order
    intro n hn
    rw [coeff_rescale, coeff_of_lt_order n hn, mul_zero]

/-- An `e`-th root of unity fixes every actual series in the `e`-th power
of the parameter, not only the parameter monomial. -/
theorem rescaleUnitEquiv_expand (ζ : Kˣ) (e : ℕ) (he : e ≠ 0)
    (hζ : (ζ : K) ^ e = 1) (A : PowerSeries K) :
    rescaleUnitEquiv ζ (expand e he A) = expand e he A := by
  change rescale (ζ : K) (expand e he A) = expand e he A
  ext n
  rw [coeff_rescale]
  by_cases hn : e ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [pow_mul, hζ, one_pow, one_mul]
  · rw [coeff_expand_of_not_dvd e he A hn, mul_zero]

end PowerSeries

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- The actual Laurent-field automorphism induced by unit rescaling. -/
def rescaleUnitEquiv (ζ : Kˣ) : LaurentSeries K ≃ₐ[K] LaurentSeries K :=
  (exists_orderPreservingExtension (PowerSeries.rescaleUnitEquiv ζ)
    (PowerSeries.rescaleUnitEquiv_order ζ)).choose

/-- This Laurent automorphism extends the specified power-series rescaling. -/
theorem rescaleUnitEquiv_coe (ζ : Kˣ) (A : PowerSeries K) :
    rescaleUnitEquiv ζ (A : LaurentSeries K) =
      (PowerSeries.rescale (ζ : K) A : LaurentSeries K) :=
  (exists_orderPreservingExtension (PowerSeries.rescaleUnitEquiv ζ)
    (PowerSeries.rescaleUnitEquiv_order ζ)).choose_spec.1 A

/-- Unit rescaling preserves all Laurent orders, including negative orders. -/
theorem rescaleUnitEquiv_order (ζ : Kˣ) (A : LaurentSeries K) :
    (rescaleUnitEquiv ζ A).order = A.order :=
  (exists_orderPreservingExtension (PowerSeries.rescaleUnitEquiv ζ)
    (PowerSeries.rescaleUnitEquiv_order ζ)).choose_spec.2 A

/-- The parameter is sent to its prescribed unit multiple. -/
theorem rescaleUnitEquiv_parameter (ζ : Kˣ) :
    rescaleUnitEquiv ζ (HahnSeries.single (1 : ℤ) (1 : K)) =
      HahnSeries.C (ζ : K) * HahnSeries.single (1 : ℤ) (1 : K) := by
  rw [← PowerSeries.coe_X, rescaleUnitEquiv_coe, PowerSeries.rescale_X,
    PowerSeries.coe_mul, PowerSeries.coe_C, PowerSeries.coe_X]

/-- Every root of unity gives an automorphism fixing the parameter power. -/
theorem rescaleUnitEquiv_parameter_pow (ζ : Kˣ) (e : ℕ)
    (hζ : (ζ : K) ^ e = 1) :
    rescaleUnitEquiv ζ (HahnSeries.single (1 : ℤ) (1 : K) ^ e) =
      HahnSeries.single (1 : ℤ) (1 : K) ^ e := by
  rw [map_pow, rescaleUnitEquiv_parameter, mul_pow, ← map_pow, hζ, map_one, one_mul]

/-- The whole expanded power-series base is fixed. -/
theorem rescaleUnitEquiv_expand (ζ : Kˣ) (e : ℕ) (he : e ≠ 0)
    (hζ : (ζ : K) ^ e = 1) (A : PowerSeries K) :
    rescaleUnitEquiv ζ (PowerSeries.expand e he A : LaurentSeries K) =
      (PowerSeries.expand e he A : LaurentSeries K) := by
  rw [rescaleUnitEquiv_coe]
  exact congrArg (fun f : PowerSeries K => (f : LaurentSeries K))
    (PowerSeries.rescaleUnitEquiv_expand ζ e he hζ A)

/-- Fractions of expanded power series are fixed as well. This identifies
an actual fixed Laurent base, rather than just a fixed rational parameter. -/
theorem rescaleUnitEquiv_expanded_div (ζ : Kˣ) (e : ℕ) (he : e ≠ 0)
    (hζ : (ζ : K) ^ e = 1) (A B : PowerSeries K) :
    rescaleUnitEquiv ζ
        ((PowerSeries.expand e he A : LaurentSeries K) /
          (PowerSeries.expand e he B : LaurentSeries K)) =
      (PowerSeries.expand e he A : LaurentSeries K) /
        (PowerSeries.expand e he B : LaurentSeries K) := by
  rw [map_div₀, rescaleUnitEquiv_expand ζ e he hζ A,
    rescaleUnitEquiv_expand ζ e he hζ B]

/-- Distinct unit multipliers give distinct Laurent embeddings. -/
theorem rescaleUnitEquiv_toAlgHom_injective :
    Function.Injective (fun ζ : Kˣ => (rescaleUnitEquiv ζ).toAlgHom) := by
  intro ζ η h
  have hx := congrArg
    (fun f : LaurentSeries K →ₐ[K] LaurentSeries K =>
      f (PowerSeries.X : PowerSeries K)) h
  change rescaleUnitEquiv ζ (PowerSeries.X : PowerSeries K) =
    rescaleUnitEquiv η (PowerSeries.X : PowerSeries K) at hx
  rw [rescaleUnitEquiv_coe, rescaleUnitEquiv_coe] at hx
  have hseries := HahnSeries.ofPowerSeries_injective hx
  have hc := congrArg (PowerSeries.coeff 1) hseries
  apply Units.ext
  simpa only [PowerSeries.coeff_rescale, PowerSeries.coeff_X, ↓reduceIte,
    pow_one, mul_one] using hc

/-- Over an algebraically closed coefficient field, a tame exponent supplies
exactly that many distinct order-preserving embeddings fixing its parameter
power. No algebraic closedness of the Laurent field is asserted or used. -/
theorem exists_tame_parameter_embeddings [IsAlgClosed K]
    (e : ℕ) (he : (e : K) ≠ 0) :
    ∃ ι : Fin e → LaurentSeries K →ₐ[K] LaurentSeries K,
      Function.Injective ι ∧
      (∀ j A, (ι j A).order = A.order) ∧
      ∀ j, ι j (HahnSeries.single (1 : ℤ) (1 : K) ^ e) =
        HahnSeries.single (1 : ℤ) (1 : K) ^ e := by
  let : NeZero (e : K) := ⟨he⟩
  let : NeZero e := .of_neZero_natCast K
  let := Fintype.ofFinite (rootsOfUnity e K)
  have hcard : Fintype.card (rootsOfUnity e K) = e := by
    rw [← Nat.card_eq_fintype_card]
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K e
  let labels : Fin e ≃ rootsOfUnity e K := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun j => (rescaleUnitEquiv (labels j).val).toAlgHom, ?_, ?_, ?_⟩
  · intro i j hij
    apply labels.injective
    apply Subtype.ext
    exact rescaleUnitEquiv_toAlgHom_injective hij
  · intro j A
    exact rescaleUnitEquiv_order (labels j).val A
  · intro j
    exact rescaleUnitEquiv_parameter_pow (labels j).val e
      ((mem_rootsOfUnity' e (labels j).val).mp (labels j).property)

end LaurentSeries
