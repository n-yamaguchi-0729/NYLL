/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Basic
import Nyll.SchemeTheory.GroupSchemes.IntegralGroupPowerSeries

/-! # Integral group-valued series from positive place orders

Zero or strictly positive orders of every centered generator coefficient
construct series over the actual valuation ring. The centered coefficients
lie in its maximal ideal, so coefficientwise residue is the unit augmentation.
The generic affine-coordinate construction then gives an actual integral
group-valued point reducing to the unit; no integral lift is assumed.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve.Place

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- Positive orders construct the actual valuation-ring series, including
its scalar constant part, and put every centered coefficient in the maximal ideal. -/
theorem exists_powerSeries_valuationSubring_reducing_to_scalar
    (v : Place K F) (f : PowerSeries F) (c : K)
    (hpos : ∀ n : ℕ,
      PowerSeries.coeff n (f - PowerSeries.C (algebraMap K F c)) = 0 ∨
        0 < v.ord (PowerSeries.coeff n
          (f - PowerSeries.C (algebraMap K F c)))) :
    ∃ B : PowerSeries v.toValuationSubring,
      PowerSeries.map v.toValuationSubring.subtype B = f ∧
      ∀ n : ℕ, PowerSeries.coeff n
        (B - PowerSeries.C (algebraMap K v.toValuationSubring c)) ∈
          IsLocalRing.maximalIdeal v.toValuationSubring := by
  have hmem (n : ℕ) : PowerSeries.coeff n
      (f - PowerSeries.C (algebraMap K F c)) ∈ v.toValuationSubring := by
    rcases hpos n with hz | hpositive
    · rw [hz]
      exact zero_mem _
    · exact v.mem_toValuationSubring_of_ord_nonneg hpositive.le
  let B₀ : PowerSeries v.toValuationSubring := PowerSeries.mk fun n =>
    ⟨PowerSeries.coeff n (f - PowerSeries.C (algebraMap K F c)), hmem n⟩
  have hB₀ : PowerSeries.map v.toValuationSubring.subtype B₀ =
      f - PowerSeries.C (algebraMap K F c) := by
    apply PowerSeries.ext
    intro n
    simp only [B₀, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    rfl
  refine ⟨B₀ + PowerSeries.C (algebraMap K v.toValuationSubring c), ?_, ?_⟩
  · have hc : v.toValuationSubring.subtype (algebraMap K v.toValuationSubring c) =
        algebraMap K F c := v.coe_algebraMap c
    rw [map_add, hB₀, PowerSeries.map_C, hc, sub_add_cancel]
  · intro n
    rw [add_sub_cancel_right]
    simp only [B₀, PowerSeries.coeff_mk]
    exact (v.mk_mem_maximalIdeal_iff_eq_zero_or_ord_pos (hmem n)).mpr (hpos n)

/-- Strictly positive centered coefficient orders on finitely many affine
generators construct an actual group point over the valuation-ring series.
Its generic point is the given chart point, and its entire residue series is
the group unit. All coefficient degrees, including degree zero, are covered. -/
theorem exists_integral_group_point_of_positive_orders
    (v : Place K F) {A : Type u} [CommRing A] [Algebra K A]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G]
    (i : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A))) ⟶ G)
    (φ : A →ₐ[K] PowerSeries F) (ε : A →ₐ[K] K)
    (hε : Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ i.left =
      (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K))) ⟶ G).left)
    (S : Finset A) (hS : Algebra.adjoin K (S : Set A) = ⊤)
    (hpos : ∀ a ∈ S, ∀ n : ℕ,
      PowerSeries.coeff n (φ a - PowerSeries.C (algebraMap K F (ε a))) = 0 ∨
        0 < v.ord (PowerSeries.coeff n
          (φ a - PowerSeries.C (algebraMap K F (ε a))))) :
    ∃ p : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (PowerSeries v.toValuationSubring)))) ⟶ G,
      Spec.map (CommRingCat.ofHom (PowerSeries.map v.toValuationSubring.subtype)) ≫
          p.left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i.left ∧
      Spec.map (CommRingCat.ofHom (PowerSeries.map
        (IsLocalRing.residue v.toValuationSubring))) ≫ p.left =
          (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
            (PowerSeries (IsLocalRing.ResidueField v.toValuationSubring))))) ⟶ G).left := by
  let inclusion : v.toValuationSubring →ₐ[K] F :=
    IsScalarTower.toAlgHom K v.toValuationSubring F
  let reduction : v.toValuationSubring →ₐ[K]
      IsLocalRing.ResidueField v.toValuationSubring :=
    IsScalarTower.toAlgHom K v.toValuationSubring
      (IsLocalRing.ResidueField v.toValuationSubring)
  have hinclusion : Function.Injective inclusion := Subtype.val_injective
  obtain ⟨p, hp, hpred⟩ :=
    IntegralGroupPowerSeries.exists_integral_point_reducing_to_unit
      inclusion hinclusion reduction i φ ε
      (by apply Over.OverMorphism.ext; exact hε) S hS (by
        intro a ha
        obtain ⟨B, hB, hBred⟩ :=
          v.exists_powerSeries_valuationSubring_reducing_to_scalar
            (φ a) (ε a) (hpos a ha)
        refine ⟨B, hB, ?_⟩
        intro n
        change PowerSeries.coeff n
          (B - PowerSeries.C (algebraMap K v.toValuationSubring (ε a))) ∈
            RingHom.ker (IsLocalRing.residue v.toValuationSubring)
        rw [IsLocalRing.ker_residue]
        exact hBred n)
  refine ⟨p, ?_, ?_⟩
  · exact congrArg (fun f : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries F)))) ⟶ G => f.left) hp
  · exact congrArg (fun f : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries (IsLocalRing.ResidueField v.toValuationSubring))))) ⟶ G =>
        f.left) hpred

end AlgebraicCurve.Place
