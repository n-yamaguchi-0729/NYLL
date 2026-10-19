/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Orders.GroupPowerSeriesPositiveOrders
import Nyll.SchemeTheory.GroupSchemes.IntegralGroupPowerSeriesCoordinates

/-! # Positive coordinate orders of integral group points reducing to the unit

The integral point itself, rather than assumed coordinate estimates, supplies
positive orders for every centered affine coordinate in every degree.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.Place

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- A series lifted to the actual valuation ring with scalar residue has
zero or positive centered coefficients, including its degree-zero coefficient. -/
theorem positive_orders_of_powerSeries_lift
    (v : Place K F) (f : PowerSeries F) (c : K)
    (B : PowerSeries v.toValuationSubring)
    (hB : PowerSeries.map v.toValuationSubring.subtype B = f)
    (hred : PowerSeries.map (IsLocalRing.residue v.toValuationSubring) B =
      PowerSeries.C (algebraMap K v.ResidueField c)) (n : ℕ) :
    PowerSeries.coeff n (f - PowerSeries.C (algebraMap K F c)) = 0 ∨
      0 < v.ord (PowerSeries.coeff n (f - PowerSeries.C (algebraMap K F c))) := by
  let b := PowerSeries.coeff n (B - PowerSeries.C (algebraMap K v.toValuationSubring c))
  have hb : (b : F) = PowerSeries.coeff n
      (f - PowerSeries.C (algebraMap K F c)) := by
    change v.toValuationSubring.subtype (PowerSeries.coeff n
      (B - PowerSeries.C (algebraMap K v.toValuationSubring c))) = _
    have hc : v.toValuationSubring.subtype (algebraMap K v.toValuationSubring c) =
        algebraMap K F c := v.coe_algebraMap c
    rw [← PowerSeries.coeff_map, map_sub, PowerSeries.map_C, hc, hB]
  have hker : b ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.ker_residue]
    change IsLocalRing.residue v.toValuationSubring b = 0
    change IsLocalRing.residue v.toValuationSubring
      (PowerSeries.coeff n (B - PowerSeries.C (algebraMap K v.toValuationSubring c))) = 0
    rw [← PowerSeries.coeff_map, map_sub, PowerSeries.map_C, hred]
    have hc : IsLocalRing.residue v.toValuationSubring
        (algebraMap K v.toValuationSubring c) = algebraMap K v.ResidueField c := by
      rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    rw [hc, sub_self, map_zero]
  have h := (v.mk_mem_maximalIdeal_iff_eq_zero_or_ord_pos b.property).mp hker
  rwa [hb] at h

/-- Every affine identity coordinate of an actual integral group point
reducing to the unit has positive centered orders. No coordinate integrality
or chart factorization is assumed. -/
theorem coordinates_positive_of_integral_group_point
    (v : Place K F) {G : Over (Spec (.of K))} [GrpObj G]
    (p : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries v.toValuationSubring)))) ⟶ G)
    (hred : Spec.map (CommRingCat.ofHom (PowerSeries.map
        (IsLocalRing.residue v.toValuationSubring))) ≫ p.left =
      (1 : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (PowerSeries v.ResidueField)))) ⟶ G).left)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (φ : Γ(G.left, V) →+* PowerSeries F)
    (hφ : Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec =
      Spec.map (CommRingCat.ofHom (PowerSeries.map v.toValuationSubring.subtype)) ≫ p.left)
    (a : Γ(G.left, V)) (n : ℕ) :
    let c := AffineLineGroupFormalDifference.identityCoordinates V hV hunit a
    PowerSeries.coeff n (φ a - PowerSeries.C (algebraMap K F c)) = 0 ∨
      0 < v.ord (PowerSeries.coeff n (φ a - PowerSeries.C (algebraMap K F c))) := by
  intro c
  let j : v.toValuationSubring →ₐ[K] F :=
    IsScalarTower.toAlgHom K v.toValuationSubring F
  let ρ : v.toValuationSubring →ₐ[K] v.ResidueField :=
    IsScalarTower.toAlgHom K v.toValuationSubring v.ResidueField
  have : IsLocalHom ρ.toRingHom := by
    change IsLocalHom (algebraMap v.toValuationSubring v.ResidueField)
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    infer_instance
  obtain ⟨ψ, hψ, hψred⟩ := IntegralGroupPowerSeries.exists_coordinate_lift_of_integral_point
    j ρ p hred V hV hunit φ hφ
  apply v.positive_orders_of_powerSeries_lift (φ a) c (ψ a)
    (RingHom.congr_fun hψ a) _ n
  have h := RingHom.congr_fun hψred a
  change PowerSeries.map (IsLocalRing.residue v.toValuationSubring) (ψ a) =
    algebraMap K (PowerSeries v.ResidueField) c at h
  simpa only [PowerSeries.algebraMap_apply] using h

end AlgebraicCurve.Place
