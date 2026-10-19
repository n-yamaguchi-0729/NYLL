/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Evaluation.PlaceValueRestrictAlong
import Nyll.AlgebraicCurves.Places.Rational.InfinityArithmetic
import Nyll.AlgebraicCurves.Places.Rational.RatFuncOrdXSubC

/-! # Exact reciprocal contact and the original infinity valuation

An exact positive contact order for `g - 1` identifies the restricted place
of the actual reciprocal coordinate with infinity, computes its ramification
index, and determines the order of every rational function under that same
field map. This retains the map used by the original finite curve morphism.
-/

noncomputable section

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open Classical in
/-- Exact contact computes both the original place over infinity and its
ramification index; consequently it computes orders of all base functions. -/
theorem reciprocal_contact_infinity
    (φ : RatFunc K →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral)
    (v : Place K F) (g : Fˣ) (e : ℕ) (he : 0 < e)
    (hg : v.ord ((g : F) - 1) = (e : ℤ))
    (hz : φ RatFunc.X = ((g : F) - 1)⁻¹) :
    v.restrictAlong φ hφ = RationalFunctionField.placeInfty K ∧
      ramificationIndexAlong φ v = e ∧
      ∀ f : RatFunc K,
        v.ord (φ f) = (e : ℤ) * (RationalFunctionField.placeInfty K).ord f := by
  classical
  have hpole : v.ord (φ RatFunc.X) = -(e : ℤ) := by
    rw [hz, ord_inv, hg]
  have hnegative : (v.restrictAlong φ hφ).ord RatFunc.X < 0 :=
    (ord_restrictAlong_neg_iff φ hφ v RatFunc.X).mpr (by rw [hpole]; omega)
  have hv : v.restrictAlong φ hφ = RationalFunctionField.placeInfty K := by
    by_contra h
    exact (not_le_of_gt hnegative)
      (RationalFunctionField.ord_X_nonneg_of_ne_placeInfty K h)
  have hram : ramificationIndexAlong φ v = e := by
    have h := ord_restrictAlong φ hφ v RatFunc.X
    rw [hpole, hv, RationalFunctionField.ord_placeInfty_X, mul_neg_one] at h
    omega
  refine ⟨hv, hram, ?_⟩
  intro f
  rw [ord_restrictAlong φ hφ, hv, hram]

/-- A rational coordinate which vanishes at a place is its uniformizer,
including when the rational curve uses its native model function field. -/
theorem ord_rational_coordinate_of_pos
    {B : Type*} [Field B] [Algebra K B]
    (p : RatFunc K ≃ₐ[K] B) (v : Place K B)
    (hpos : 0 < v.ord (p RatFunc.X)) : v.ord (p RatFunc.X) = 1 := by
  classical
  let v₀ := congrRingEquiv p.symm.toRingEquiv p.symm.commutes v
  have hv : v₀.ord RatFunc.X = v.ord (p RatFunc.X) := by
    have h := ord_congrRingEquiv p.symm.toRingEquiv p.symm.commutes v (p RatFunc.X)
    change v₀.ord (p.symm (p RatFunc.X)) = _ at h
    rw [p.symm_apply_apply] at h
    exact h
  have hord := RationalFunctionField.ord_X_sub_C K 0 v₀
  simp only [Polynomial.C_0, sub_zero, RatFunc.algebraMap_X, Finsupp.add_apply] at hord
  by_cases hzero : v₀ = RationalFunctionField.placeOfPoint K 0
  · have hzeroord : v₀.ord RatFunc.X = 1 := by
      rw [hord, hzero, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (RationalFunctionField.placeOfPoint_ne_placeInfty K 0),
        add_zero]
    exact hv.symm.trans hzeroord
  · have hn : v₀.ord RatFunc.X ≤ 0 := by
      rw [hord, Finsupp.single_eq_of_ne hzero, zero_add]
      by_cases hinf : v₀ = RationalFunctionField.placeInfty K
      · rw [hinf, Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_eq_of_ne hinf]
    exact False.elim ((not_le_of_gt hpos) (hv ▸ hn))

/-- Exact contact over a rational native base computes the actual completed
base uniformizer and the native ramification index, without changing fields. -/
theorem rational_contact_ramification
    {B : Type*} [Field B] [Algebra K B] [Algebra B F] [IsScalarTower K B F]
    [Algebra.IsIntegral B F]
    (p : RatFunc K ≃ₐ[K] B) (w : Place K F) (e : ℕ) (he : 0 < e)
    (hcontact : w.ord (algebraMap B F (p RatFunc.X)) = (e : ℤ)) :
    (w.restrict B).ord (p RatFunc.X) = 1 ∧ w.ramificationIndex B = e := by
  have h := w.ord_restrict (p RatFunc.X)
  rw [hcontact] at h
  have hpositive : 0 < (w.restrict B).ord (p RatFunc.X) := by
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (Int.natCast_nonneg (w.ramificationIndex B)) (le_of_not_gt hn)
    rw [← h] at hnonpos
    omega
  have hu := ord_rational_coordinate_of_pos p (w.restrict B) hpositive
  refine ⟨hu, ?_⟩
  rw [hu, mul_one] at h
  omega

end AlgebraicCurve.Place
