/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Degree.GroupFormalDifferenceTameOrder
import Nyll.AlgebraicCurves.Places.Orders.GroupPowerSeriesPositiveOrders
import Nyll.SchemeTheory.GroupSchemes.GroupDiagonalCoordinateAlgebra

/-! # Actual integral points for sufficiently ramified tame group differences

The original group's local finite-type structure supplies finite generators
of an affine identity chart. Their actual global pole bounds give positive
centered Laurent orders after a sufficiently ramified tame deformation.
The chart algebra and unit augmentation then construct an actual point over
the power-series ring of the Laurent valuation ring. Its generic point is
the original moving-versus-constant group difference, and its entire residue
series is the unit. Integrality and finite generation are constructed here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

/-- One global bound supplies actual integral group points for all tame
local deformations above its threshold. Their generic point is the actual
group difference and their residue is the actual unit. The finite chart
generators and all coordinate-algebra compatibility are supplied internally. -/
theorem exists_groupFormalDifference_uniform_tame_integral
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (G : Over (Spec (.of K))) [GrpObj G] [LocallyOfFiniteType G.hom]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    ∃ t : F, Transcendental K t ∧ ∃ D : Modulus K F,
      ∀ (v : Place K F) (i : F →ₐ[K] LaurentSeries K),
        (∀ f : F, (i f).order = v.ord f) → ∀ e : ℕ, (e : K) ≠ 0 →
        let c : ℤ := max 1 (2 * (D v : ℤ))
        let b : ℤ := min (v.ord t) c
        c - b < (e : ℤ) →
        ∃ Ψ : LaurentSeries K →ₐ[K] PowerSeries (LaurentSeries K),
          PowerSeries.constantCoeff.comp Ψ.toRingHom = RingHom.id (LaurentSeries K) ∧
          Ψ (HahnSeries.single (1 : ℤ) (1 : K)) ^ e *
            (1 + PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) * PowerSeries.X) =
              PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) ∧
          ∃ p : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
              (PowerSeries (LaurentSeries.orderPlace (K := K)).toValuationSubring)))) ⟶ G,
            Spec.map (CommRingCat.ofHom (PowerSeries.map
                (LaurentSeries.orderPlace (K := K)).toValuationSubring.subtype)) ≫ p.left =
              Spec.map (CommRingCat.ofHom
                (PowerSeries.diagonalTensorMapAlong i (Ψ.comp i)).toRingHom) ≫
                  GroupDiagonal.diagonalDifference x ∧
            Spec.map (CommRingCat.ofHom (PowerSeries.map
                (IsLocalRing.residue
                  (LaurentSeries.orderPlace (K := K)).toValuationSubring))) ≫ p.left =
              (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
                (PowerSeries (IsLocalRing.ResidueField
                  (LaurentSeries.orderPlace (K := K)).toValuationSubring))))) ⟶ G).left := by
  let := GroupDiagonal.coordinateAlgebra V hV
  have hfinite : Algebra.FiniteType K Γ(G.left, V) :=
    GroupDiagonal.coordinateAlgebra_finiteType V hV
  obtain ⟨S, hS⟩ := hfinite.out
  obtain ⟨t, ht, _hfinite, _hseparable, _σ, _hσ0, _hσt, D, hlocal⟩ :=
    exists_groupFormalDifference_uniform_tame_order G x V hV hunit
      (fun a : S => (a : Γ(G.left, V)))
  refine ⟨t, ht, D, ?_⟩
  intro v i hi e he c b hlarge
  obtain ⟨Ψ, hΨ0, hparameter, hρ0, hpositive⟩ := hlocal v i hi e he hlarge
  let w := LaurentSeries.orderPlace (K := K)
  let ε : Γ(G.left, V) →ₐ[K] K :=
    GroupDiagonal.identityCoordinatesAlgHom V hV hunit
  let φ : Γ(G.left, V) →ₐ[K] PowerSeries (LaurentSeries K) :=
    GroupDiagonal.formalCoordinatesAlongAlgHom x V hV hunit i (Ψ.comp i) hρ0
  have hpos : ∀ a ∈ S, ∀ n : ℕ,
      PowerSeries.coeff n (φ a - PowerSeries.C (algebraMap K (LaurentSeries K) (ε a))) = 0 ∨
        0 < w.ord (PowerSeries.coeff n
          (φ a - PowerSeries.C (algebraMap K (LaurentSeries K) (ε a)))) := by
    intro a ha n
    have hc : PowerSeries.constantCoeff (φ a) =
        algebraMap K (LaurentSeries K) (ε a) :=
      GroupDiagonal.constantCoeff_formalCoordinatesAlong x V hV hunit i (Ψ.comp i) hρ0 a
    have hcenter : φ a - PowerSeries.C (algebraMap K (LaurentSeries K) (ε a)) =
        φ a - PowerSeries.C (PowerSeries.constantCoeff (φ a)) :=
      congrArg (fun z : LaurentSeries K => φ a - PowerSeries.C z) hc.symm
    rw [hcenter, LaurentSeries.orderPlace_ord]
    by_cases hz : PowerSeries.coeff n
        (φ a - PowerSeries.C (PowerSeries.constantCoeff (φ a))) = 0
    · exact Or.inl hz
    · right
      have hn : 0 < n := by
        by_contra hn
        have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
        subst n
        apply hz
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub,
          PowerSeries.constantCoeff_C, sub_self]
      exact (hpositive ⟨a, ha⟩ n hn hz).2
  obtain ⟨p, hp, hpred⟩ := w.exists_integral_group_point_of_positive_orders G
    (GroupDiagonal.coordinateInclusion V hV) φ ε
    (GroupDiagonal.identityCoordinatesAlgHom_spec V hV hunit) S hS hpos
  refine ⟨Ψ, hΨ0, hparameter, p, ?_, hpred⟩
  exact hp.trans
    (GroupDiagonal.formalCoordinatesAlong_spec x V hV hunit i (Ψ.comp i) hρ0)

end AlgebraicCurve
