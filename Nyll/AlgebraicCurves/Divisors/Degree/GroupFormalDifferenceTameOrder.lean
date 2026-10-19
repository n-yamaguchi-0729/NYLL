/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Degree.GroupFormalDifferencePoleBound
import Nyll.AlgebraicCurves.Places.Orders.TameLaurentDeformation
import Nyll.SchemeTheory.GroupSchemes.GroupDiagonalFormalSubstitution

/-! # Positive local order of actual tame group differences

One global separating translation and effective divisor are constructed
for a finite family of actual group-chart coordinates. At any place with
an actual order-preserving Laurent embedding, the Hensel-constructed tame
deformation has positive order on every nonzero centered coordinate
coefficient once its ramification exceeds an explicit bound. The original
Laurent-parameter equation is retained for subsequent trace comparison.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve

variable {K F : Type u} [Field K] [Field F] [Algebra K F]

private theorem centered_diagonal_tame_order
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F)
    (hσt : σ t = PowerSeries.C t + PowerSeries.X)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    (v : Place K F) (i : F →ₐ[K] LaurentSeries K)
    (hi : ∀ f : F, (i f).order = v.ord f)
    (ρ : F →ₐ[K] PowerSeries (LaurentSeries K))
    (hρ0 : PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom)
    (e d : ℕ)
    (hρ : ∀ n, 0 < n →
      PowerSeries.coeff n (ρ t - PowerSeries.C (i t)) ≠ 0 →
        (e : ℤ) * n + v.ord t ≤
          (PowerSeries.coeff n (ρ t - PowerSeries.C (i t))).order)
    (z : Localization.AtPrime
      (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal)
    (hz : ∀ n, -((d * (n + 1) : ℕ) : ℤ) ≤
      v.ord (PowerSeries.coeff n (PowerSeries.diagonalEvaluation σ hσ0 z))) :
    let c : ℤ := max 1 (2 * (d : ℤ))
    let b : ℤ := min (v.ord t) c
    let Q := PowerSeries.diagonalEvaluationAlong i ρ hρ0 z
    ∀ n, PowerSeries.coeff n (Q - PowerSeries.C (PowerSeries.constantCoeff Q)) ≠ 0 →
      ((e : ℤ) + b - c) * n ≤
        (PowerSeries.coeff n (Q - PowerSeries.C (PowerSeries.constantCoeff Q))).order := by
  intro c b Q
  let S := PowerSeries.diagonalEvaluation σ hσ0 z
  let A := PowerSeries.map i.toRingHom (S - PowerSeries.C (PowerSeries.constantCoeff S))
  let B := ρ t - PowerSeries.C (i t)
  let w := LaurentSeries.orderPlace (K := K)
  have hB0 : PowerSeries.constantCoeff B = 0 := by
    have ht0 : PowerSeries.constantCoeff (ρ t) = i t := RingHom.congr_fun hρ0 t
    change PowerSeries.constantCoeff (ρ t - PowerSeries.C (i t)) = 0
    rw [map_sub, PowerSeries.constantCoeff_C, ht0, sub_self]
  have hA : ∀ m, PowerSeries.coeff m A ≠ 0 →
      0 - c * m ≤ w.ord (PowerSeries.coeff m A) := by
    intro m hm
    have hm0 : m ≠ 0 := by
      intro h
      subst m
      apply hm
      change PowerSeries.coeff 0 (PowerSeries.map i.toRingHom
        (S - PowerSeries.C (PowerSeries.constantCoeff S))) = 0
      rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        map_sub, PowerSeries.constantCoeff_C, sub_self, map_zero]
    have hm1 : (1 : ℤ) ≤ (m : ℤ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
    change 0 - c * m ≤ w.ord
      (PowerSeries.coeff m (PowerSeries.map i.toRingHom
        (S - PowerSeries.C (PowerSeries.constantCoeff S))))
    rw [PowerSeries.coeff_map, map_sub, PowerSeries.coeff_C_of_ne_zero hm0, sub_zero,
      LaurentSeries.orderPlace_ord]
    change 0 - c * m ≤ (i (PowerSeries.coeff m S)).order
    rw [hi]
    have hc : 2 * (d : ℤ) ≤ c := le_max_right _ _
    have hcm := mul_le_mul_of_nonneg_right hc (Int.natCast_nonneg m)
    have hdm := mul_le_mul_of_nonneg_left hm1 (Int.natCast_nonneg d)
    calc
      0 - c * (m : ℤ) ≤ -((d * (m + 1) : ℕ) : ℤ) := by
        push_cast
        nlinarith
      _ ≤ v.ord (PowerSeries.coeff m S) := hz m
  have hB : ∀ n, 0 < n → PowerSeries.coeff n B ≠ 0 →
      (e : ℤ) * n + b ≤ w.ord (PowerSeries.coeff n B) := by
    intro n hn hne
    rw [LaurentSeries.orderPlace_ord]
    exact (add_le_add_right (min_le_left (v.ord t) c) _).trans (hρ n hn hne)
  have hQ : Q - PowerSeries.C (PowerSeries.constantCoeff Q) =
      PowerSeries.subst B A :=
    PowerSeries.diagonalEvaluationAlong_centered_substitution
      t ht σ hσt hσ0 i ρ hρ0 z
  intro n hne
  rw [hQ] at hne ⊢
  have h := w.powerSeries_subst_coeff_ord_affine A B 0 c e b
    (min_le_right _ _) hB0 hA hB n hne
  rw [LaurentSeries.orderPlace_ord] at h
  simpa only [zero_add] using h

/-- From an actual global coordinate bound, construct the whole tame
Laurent deformation and positive orders for the given finite coordinate
family. The field-parameter equation is retained, rather than replaced by
an embedding-only existence result. -/
theorem exists_groupFormalDifference_tame_deformation_of_bound
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F)
    (hσt : σ t = PowerSeries.C t + PowerSeries.X)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    (G : Over (Spec (.of K))) [GrpObj G]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    {Index : Type*} (a : Index → Γ(G.left, V)) (D : Modulus K F)
    (hD : ∀ j v n, -((D v * (n + 1) : ℕ) : ℤ) ≤
      v.ord (PowerSeries.coeff n (PowerSeries.diagonalEvaluation σ hσ0
        (GroupDiagonal.diagonalCoordinates x V hV hunit (a j)))))
    (v : Place K F) (i : F →ₐ[K] LaurentSeries K)
    (hi : ∀ f : F, (i f).order = v.ord f) (e : ℕ) (he : (e : K) ≠ 0) :
    let c : ℤ := max 1 (2 * (D v : ℤ))
    let b : ℤ := min (v.ord t) c
    c - b < (e : ℤ) →
    ∃ Ψ : LaurentSeries K →ₐ[K] PowerSeries (LaurentSeries K),
      PowerSeries.constantCoeff.comp Ψ.toRingHom = RingHom.id (LaurentSeries K) ∧
      Ψ (HahnSeries.single (1 : ℤ) (1 : K)) ^ e *
        (1 + PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) * PowerSeries.X) =
          PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) ∧
      ∃ hρ0 : PowerSeries.constantCoeff.comp (Ψ.comp i).toRingHom = i.toRingHom,
        ∀ (j : Index) (n : ℕ), 0 < n →
          let Q := GroupDiagonal.formalCoordinatesAlong x V hV hunit i (Ψ.comp i) hρ0 (a j)
          PowerSeries.coeff n (Q - PowerSeries.C (PowerSeries.constantCoeff Q)) ≠ 0 →
            ((e : ℤ) + b - c) * n ≤
                (PowerSeries.coeff n (Q - PowerSeries.C (PowerSeries.constantCoeff Q))).order ∧
              0 < (PowerSeries.coeff n
                (Q - PowerSeries.C (PowerSeries.constantCoeff Q))).order := by
  intro c b hlarge
  obtain ⟨Ψ, hΨ0, hparameter, horder⟩ :=
    LaurentSeries.exists_tameFormalDeformation (K := K) e he
  have hρ0 : PowerSeries.constantCoeff.comp (Ψ.comp i).toRingHom = i.toRingHom := by
    apply RingHom.ext
    intro f
    exact RingHom.congr_fun hΨ0 (i f)
  refine ⟨Ψ, hΨ0, hparameter, hρ0, ?_⟩
  intro j n hn Q hne
  have hρ : ∀ m, 0 < m →
      PowerSeries.coeff m ((Ψ.comp i) t - PowerSeries.C (i t)) ≠ 0 →
        (e : ℤ) * m + v.ord t ≤
          (PowerSeries.coeff m ((Ψ.comp i) t - PowerSeries.C (i t))).order := by
    intro m hm hne
    have h := horder (i t) m hm hne
    rwa [hi] at h
  have hbound := centered_diagonal_tame_order t ht σ hσt hσ0 v i hi
    (Ψ.comp i) hρ0 e (D v) hρ
    (GroupDiagonal.diagonalCoordinates x V hV hunit (a j)) (hD j v) n hne
  refine ⟨hbound, ?_⟩
  have hslope : 0 < (e : ℤ) + b - c := by omega
  have hnInt : 0 < (n : ℤ) := by exact_mod_cast hn
  exact (mul_pos hslope hnInt).trans_le hbound

/-- A fixed finite family of actual group coordinates has one constructed
global divisor and separating translation which work at every place and
for every supplied order-preserving Laurent embedding. Above the explicit
threshold all centered tame-deformation coefficients have positive order. -/
theorem exists_groupFormalDifference_uniform_tame_order
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (G : Over (Spec (.of K))) [GrpObj G]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    {Index : Type*} [Finite Index] (a : Index → Γ(G.left, V)) :
    ∃ t : F, Transcendental K t ∧
      FiniteDimensional (IntermediateField.adjoin K {t}) F ∧
      Algebra.IsSeparable (IntermediateField.adjoin K {t}) F ∧
      ∃ (σ : F →ₐ[K] PowerSeries F)
        (_hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F),
        σ t = PowerSeries.C t + PowerSeries.X ∧
        ∃ D : Modulus K F, ∀ (v : Place K F) (i : F →ₐ[K] LaurentSeries K),
          (∀ f : F, (i f).order = v.ord f) → ∀ e : ℕ, (e : K) ≠ 0 →
          let c : ℤ := max 1 (2 * (D v : ℤ))
          let b : ℤ := min (v.ord t) c
          c - b < (e : ℤ) →
          ∃ Ψ : LaurentSeries K →ₐ[K] PowerSeries (LaurentSeries K),
            PowerSeries.constantCoeff.comp Ψ.toRingHom = RingHom.id (LaurentSeries K) ∧
            Ψ (HahnSeries.single (1 : ℤ) (1 : K)) ^ e *
              (1 + PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) * PowerSeries.X) =
                PowerSeries.C ((HahnSeries.single (1 : ℤ) (1 : K)) ^ e) ∧
            ∃ hρ0 : PowerSeries.constantCoeff.comp (Ψ.comp i).toRingHom = i.toRingHom,
              ∀ (j : Index) (n : ℕ), 0 < n →
                let Q := GroupDiagonal.formalCoordinatesAlong
                  x V hV hunit i (Ψ.comp i) hρ0 (a j)
                PowerSeries.coeff n (Q - PowerSeries.C (PowerSeries.constantCoeff Q)) ≠ 0 →
                  ((e : ℤ) + b - c) * n ≤
                    (PowerSeries.coeff n
                      (Q - PowerSeries.C (PowerSeries.constantCoeff Q))).order ∧
                  0 < (PowerSeries.coeff n
                    (Q - PowerSeries.C (PowerSeries.constantCoeff Q))).order := by
  obtain ⟨t, ht, hfinite, hseparable, σ, hσ0, hσt, D, hD⟩ :=
    exists_groupFormalDifference_family_divisor_bound G x V hV hunit a
  have : FiniteDimensional (IntermediateField.adjoin K {t}) F := hfinite
  have : Algebra.IsSeparable (IntermediateField.adjoin K {t}) F := hseparable
  refine ⟨t, ht, hfinite, hseparable, σ, hσ0, hσt, D, ?_⟩
  intro v i hi e he
  exact exists_groupFormalDifference_tame_deformation_of_bound
    t ht σ hσt hσ0 G x V hV hunit a D hD v i hi e he

end AlgebraicCurve
