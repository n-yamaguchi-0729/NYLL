/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Projective.AffineLineFormalCancellation
import Nyll.AlgebraicCurves.Places.Orders.IntegralGroupPowerSeriesOrders

/-! # Constancy from an integral formal difference at infinity

An actual integral group-valued difference, reducing to the unit after a
possibly ramified extension of the infinity valuation, forces constancy of
the original affine-line morphism. The proof extracts its actual polynomial
coordinates in every degree, so it remains valid in positive characteristic.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicCurve
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.AffineLineGroupFormalDifference

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  {G : Over (Spec (.of K))} [GrpObj G] [IsSeparated G.hom]

open Classical in
/-- A formal difference with an actual integral lift and unit reduction at
infinity detects constancy, also after ramification. The coordinate bounds
are derived from that point, rather than supplied as an additional input. -/
theorem constant_of_integral_difference
    (τ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (v : Place K F) (i : RatFunc K →ₐ[K] F) (e : ℕ)
    (hi : ∀ f : RatFunc K,
      v.ord (i f) = (e : ℤ) * (RationalFunctionField.placeInfty K).ord f)
    (p : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries v.toValuationSubring)))) ⟶ G)
    (hred : Spec.map (CommRingCat.ofHom (PowerSeries.map
        (IsLocalRing.residue v.toValuationSubring))) ≫ p.left =
      (1 : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (PowerSeries v.ResidueField)))) ⟶ G).left)
    (hgeneric : Spec.map (CommRingCat.ofHom (PowerSeries.map
        v.toValuationSubring.subtype)) ≫ p.left =
      Spec.map (CommRingCat.ofHom (PowerSeries.map
        (i.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K))))) ≫ difference τ) :
    τ.left = Spec.map (CommRingCat.ofHom (Polynomial.C (R := K))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫ τ.left := by
  let j := i.toRingHom.comp (algebraMap (Polynomial K) (RatFunc K))
  let φ : Γ(G.left, V) →+* PowerSeries F :=
    (PowerSeries.map j).comp (coordinates τ V hV hunit)
  have hφ : Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec =
      Spec.map (CommRingCat.ofHom (PowerSeries.map v.toValuationSubring.subtype)) ≫ p.left := by
    rw [hgeneric]
    change Spec.map (CommRingCat.ofHom ((PowerSeries.map j).comp
      (coordinates τ V hV hunit))) ≫ hV.fromSpec = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, coordinates_spec]
  apply constant_of_coordinates_positive_infinity_order τ V hV hunit
  intro a n hn hne
  have hpos := v.coordinates_positive_of_integral_group_point p hred V hV hunit φ hφ a n
  dsimp only at hpos
  have hc : PowerSeries.coeff n
      (φ a - PowerSeries.C (algebraMap K F (identityCoordinates V hV hunit a))) =
      i (algebraMap (Polynomial K) (RatFunc K)
        (PowerSeries.coeff n (coordinates τ V hV hunit a))) := by
    rw [map_sub, PowerSeries.coeff_C_of_ne_zero (Nat.ne_of_gt hn), sub_zero]
    exact PowerSeries.coeff_map j n (coordinates τ V hV hunit a)
  rw [hc] at hpos
  rcases hpos with hz | hp
  · exact False.elim (hne ((map_eq_zero_iff _
      (RatFunc.algebraMap_injective K)).mp
        ((map_eq_zero_iff i i.injective).mp hz)))
  · rw [hi] at hp
    by_contra h
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg e) (le_of_not_gt h)
    exact (not_le_of_gt hp) hnonpos

end AlgebraicGeometry.AffineLineGroupFormalDifference
