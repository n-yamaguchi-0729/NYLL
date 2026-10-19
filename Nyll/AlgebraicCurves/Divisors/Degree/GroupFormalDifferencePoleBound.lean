/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Degree.FormalDiagonalPoleBound
import Nyll.AlgebraicCurves.Places.Orders.PowerSeriesRescaleIntegral
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveFormalTranslation
import Nyll.SchemeTheory.GroupSchemes.GroupDiagonalCoordinates

/-! # Uniform poles for actual group-valued formal differences

A curve function field supplies a separating parameter and its actual formal
translation. The difference of two generic group points factors through the
chosen identity chart at the generic diagonal. The resulting local coordinate
functions have one effective divisor bounding every coefficient of any finite
family. The chart factorization and coefficient bounds are constructed, not
hypotheses on the given group point.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj CategoryTheory.Obj BigOperators

namespace AlgebraicCurve

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]

/-- A finite family of actual identity-chart coordinates of a group-valued
formal difference has a common coefficient-pole bound. The curve parameter,
formal translation, chart factorization, and divisor are all constructed. -/
theorem exists_groupFormalDifference_family_divisor_bound
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G).left ⊆ V)
    {Index : Type*} [Finite Index] (a : Index → Γ(G.left, V)) :
    ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K {t}) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K {t}) F ∧
      ∃ (σ : F →ₐ[K] PowerSeries F)
        (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F),
        σ t = PowerSeries.C t + PowerSeries.X ∧
        ∃ D : Modulus K F, ∀ (i : Index) (v : Place K F) (n : ℕ),
          -((D v * (n + 1) : ℕ) : ℤ) ≤
            v.ord (PowerSeries.coeff n
              (PowerSeries.diagonalEvaluation σ hσ0
                (GroupDiagonal.diagonalCoordinates x V hV hunit (a i)))) := by
  classical
  let : Fintype Index := Fintype.ofFinite Index
  obtain ⟨t, ht, hfinite, hseparable, σ, hσ, _⟩ :=
    IsCurveOver.exists_separating_formalTranslation (K := K) (F := F)
  have : FiniteDimensional (IntermediateField.adjoin K {t}) F := hfinite
  have : Algebra.IsSeparable (IntermediateField.adjoin K {t}) F := hseparable
  choose E hE using fun i => exists_formalDiagonalEvaluation_divisor_bound
    (K := K) t ht σ hσ.1 hσ.2
      (GroupDiagonal.diagonalCoordinates x V hV hunit (a i))
  refine ⟨t, ht, hfinite, hseparable, σ, hσ.2, hσ.1, ∑ i, E i, ?_⟩
  intro i v n
  have hle : E i v ≤ (∑ j, E j) v := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (E j v)) (Finset.mem_univ i)
  exact (neg_le_neg (Int.ofNat_le.mpr (Nat.mul_le_mul_right (n + 1) hle))).trans
    (hE i v n)

/-- After the explicit local parameter scaling, the centered coordinates of
the actual group difference are series over the valuation ring. One divisor
works for every coefficient, every place, and the entire finite coordinate family. -/
theorem exists_groupFormalDifference_integral_coordinates
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G).left ⊆ V)
    {Index : Type*} [Finite Index] (a : Index → Γ(G.left, V)) :
    ∃ (t : F) (σ : F →ₐ[K] PowerSeries F)
      (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
      (D : Modulus K F),
      Transcendental K t ∧ σ t = PowerSeries.C t + PowerSeries.X ∧
      ∀ (v : Place K F) (π : F), v.ord π = 1 → ∀ i : Index,
        let S := PowerSeries.diagonalEvaluation σ hσ0
          (GroupDiagonal.diagonalCoordinates x V hV hunit (a i))
        ∃ B : PowerSeries v.toValuationSubring,
          B.map v.toValuationSubring.subtype =
            PowerSeries.rescale (π ^ (2 * D v))
              (S - PowerSeries.C (PowerSeries.constantCoeff S)) := by
  obtain ⟨t, ht, _, _, σ, hσ0, hσt, D, hD⟩ :=
    exists_groupFormalDifference_family_divisor_bound G x V hV hunit a
  refine ⟨t, σ, hσ0, D, ht, hσt, ?_⟩
  intro v π hπ i S
  apply v.exists_uniformizer_rescale_powerSeries_valuationSubring
    (S - PowerSeries.C (PowerSeries.constantCoeff S)) (D v) π hπ
  · rw [map_sub, PowerSeries.constantCoeff_C, sub_self]
  · intro n
    by_cases hn : n = 0
    · subst n
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub,
        PowerSeries.constantCoeff_C, sub_self, v.ord_zero]
      omega
    · rw [map_sub, PowerSeries.coeff_C_of_ne_zero hn, sub_zero]
      exact hD i v n

end AlgebraicCurve
