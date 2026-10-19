/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Degree.GroupFormalDifferenceTameIntegral
import Nyll.AlgebraicCurves.Places.Orders.TameReciprocalFormalLift
import Nyll.SchemeTheory.GroupSchemes.IntegralGroupPowerSeries

/-! # Integral differences for the actual reciprocal boundary lifts

The normalized tame parameter equation identifies the constructed integral
group difference with the unique formal lift translating `1 / (g - 1)`.
Consequently actual formal factors with the prescribed residue and reciprocal
shift have integral differences reducing to the unit. A finite list of these
factors, with repetitions retained, has the same property by the group law.
The finite-flat interior block is not included in this tame assertion.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicCurve

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]

/-- The actual unique reciprocal lift has an integral group difference.
The pole divisor, lift, comparison, and integral point are all constructed;
only the exact normalized contact and its explicit size are input data. -/
theorem exists_groupFormalDifference_reciprocal_integral
    (G : Over (Spec (.of K))) [GrpObj G] [LocallyOfFiniteType G.hom]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    ∃ t : F, Transcendental K t ∧ ∃ D : Modulus K F,
      ∀ (v : Place K F) (i : F →ₐ[K] LaurentSeries K),
        (∀ f : F, (i f).order = v.ord f) →
        ∀ (g : Fˣ) (e : ℕ), 0 < e → (e : K) ≠ 0 →
        v.ord ((g : F) - 1) = (e : ℤ) →
        i ((g : F) - 1) = HahnSeries.single (e : ℤ) (1 : K) →
        let c : ℤ := max 1 (2 * (D v : ℤ))
        let b : ℤ := min (v.ord t) c
        c - b < (e : ℤ) →
        ∃ ρ : F →ₐ[K] PowerSeries (LaurentSeries K),
          PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom ∧
          ρ (((g : F) - 1)⁻¹) =
            PowerSeries.C (i (((g : F) - 1)⁻¹)) + PowerSeries.X ∧
          (∀ θ : F →ₐ[K] PowerSeries (LaurentSeries K),
            PowerSeries.constantCoeff.comp θ.toRingHom = i.toRingHom →
            θ (((g : F) - 1)⁻¹) =
              PowerSeries.C (i (((g : F) - 1)⁻¹)) + PowerSeries.X → θ = ρ) ∧
          ∃ p : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
              (PowerSeries (LaurentSeries.orderPlace (K := K)).toValuationSubring)))) ⟶ G,
            Spec.map (CommRingCat.ofHom (PowerSeries.map
                (LaurentSeries.orderPlace (K := K)).toValuationSubring.subtype)) ≫ p.left =
              Spec.map (CommRingCat.ofHom
                (PowerSeries.diagonalTensorMapAlong i ρ).toRingHom) ≫
                  GroupDiagonal.diagonalDifference x ∧
            Spec.map (CommRingCat.ofHom (PowerSeries.map
                (IsLocalRing.residue
                  (LaurentSeries.orderPlace (K := K)).toValuationSubring))) ≫ p.left =
              (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
                (PowerSeries (IsLocalRing.ResidueField
                  (LaurentSeries.orderPlace (K := K)).toValuationSubring))))) ⟶ G).left := by
  obtain ⟨t, ht, D, hlocal⟩ :=
    exists_groupFormalDifference_uniform_tame_integral G x V hV hunit
  refine ⟨t, ht, D, ?_⟩
  intro v i hi g e hepos he hg hnormal c b hlarge
  obtain ⟨ρ, hρ0, hρz, _hρorder, hρunique⟩ :=
    v.exists_unique_normalized_tame_reciprocal_lift g e hepos he hg i hnormal
  obtain ⟨Ψ, hΨ0, hparameter, p, hp, hpred⟩ := hlocal v i hi e he hlarge
  have hcomp0 : PowerSeries.constantCoeff.comp (Ψ.comp i).toRingHom = i.toRingHom := by
    apply RingHom.ext
    intro f
    exact RingHom.congr_fun hΨ0 (i f)
  have hiz : i (((g : F) - 1)⁻¹) =
      (HahnSeries.single (e : ℤ) (1 : K))⁻¹ := by
    rw [map_inv₀, hnormal]
  have hcompz : (Ψ.comp i) (((g : F) - 1)⁻¹) =
      PowerSeries.C (i (((g : F) - 1)⁻¹)) + PowerSeries.X := by
    change Ψ (i (((g : F) - 1)⁻¹)) = _
    rw [hiz]
    exact LaurentSeries.reciprocal_shift_of_tame_parameter_equation Ψ e hparameter
  have hcomp : Ψ.comp i = ρ := hρunique (Ψ.comp i) hcomp0 hcompz
  refine ⟨ρ, hρ0, hρz, hρunique, p, ?_, hpred⟩
  rw [hcomp] at hp
  exact hp

/-- The actual reciprocal formal factors at any finite list of normalized
boundary embeddings have integral group differences, whose product reduces
to the unit. Repeated embeddings remain repeated factors in the product. -/
theorem exists_groupFormalDifference_reciprocal_list_integral
    (G : Over (Spec (.of K))) [GrpObj G] [LocallyOfFiniteType G.hom]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    ∃ t : F, Transcendental K t ∧ ∃ D : Modulus K F,
      ∀ (I : Type u) (l : List I) (v : I → Place K F)
        (i : I → F →ₐ[K] LaurentSeries K),
        (∀ a f, (i a f).order = (v a).ord f) →
        ∀ (g : Fˣ) (e : ℕ), 0 < e → (e : K) ≠ 0 →
        (∀ a, (v a).ord ((g : F) - 1) = (e : ℤ)) →
        (∀ a, i a ((g : F) - 1) = HahnSeries.single (e : ℤ) (1 : K)) →
        (∀ a, let c : ℤ := max 1 (2 * (D (v a) : ℤ))
          c - min ((v a).ord t) c < (e : ℤ)) →
        ∀ θ : I → F →ₐ[K] PowerSeries (LaurentSeries K),
        (∀ a, PowerSeries.constantCoeff.comp (θ a).toRingHom = (i a).toRingHom) →
        (∀ a, θ a (((g : F) - 1)⁻¹) =
          PowerSeries.C (i a (((g : F) - 1)⁻¹)) + PowerSeries.X) →
        ∃ p : I → (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
            (PowerSeries (LaurentSeries.orderPlace (K := K)).toValuationSubring)))) ⟶ G),
          (∀ a, Spec.map (CommRingCat.ofHom (PowerSeries.map
              (LaurentSeries.orderPlace (K := K)).toValuationSubring.subtype)) ≫ (p a).left =
            Spec.map (CommRingCat.ofHom
              (PowerSeries.diagonalTensorMapAlong (i a) (θ a)).toRingHom) ≫
                GroupDiagonal.diagonalDifference x) ∧
          Spec.map (CommRingCat.ofHom (PowerSeries.map
              (IsLocalRing.residue
                (LaurentSeries.orderPlace (K := K)).toValuationSubring))) ≫
                  (l.map p).prod.left =
            (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
              (PowerSeries (IsLocalRing.ResidueField
                (LaurentSeries.orderPlace (K := K)).toValuationSubring))))) ⟶ G).left := by
  classical
  obtain ⟨t, ht, D, hlocal⟩ :=
    exists_groupFormalDifference_reciprocal_integral G x V hV hunit
  refine ⟨t, ht, D, ?_⟩
  intro I l v i hi g e hepos he hg hnormal hlarge θ hθ0 hθz
  have hex (a : I) : ∃ p : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
        (PowerSeries (LaurentSeries.orderPlace (K := K)).toValuationSubring)))) ⟶ G,
      Spec.map (CommRingCat.ofHom (PowerSeries.map
          (LaurentSeries.orderPlace (K := K)).toValuationSubring.subtype)) ≫ p.left =
        Spec.map (CommRingCat.ofHom
          (PowerSeries.diagonalTensorMapAlong (i a) (θ a)).toRingHom) ≫
            GroupDiagonal.diagonalDifference x ∧
      Spec.map (CommRingCat.ofHom (PowerSeries.map
          (IsLocalRing.residue
            (LaurentSeries.orderPlace (K := K)).toValuationSubring))) ≫ p.left =
        (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K
          (PowerSeries (IsLocalRing.ResidueField
            (LaurentSeries.orderPlace (K := K)).toValuationSubring))))) ⟶ G).left := by
    obtain ⟨ρ, _hρ0, _hρz, hρunique, p, hp, hpred⟩ :=
      hlocal (v a) (i a) (hi a) g e hepos he (hg a) (hnormal a) (hlarge a)
    have hθ : θ a = ρ := hρunique (θ a) (hθ0 a) (hθz a)
    rw [hθ]
    exact ⟨p, hp, hpred⟩
  choose p hp hpred using hex
  refine ⟨p, hp, ?_⟩
  let O := (LaurentSeries.orderPlace (K := K)).toValuationSubring
  let reduction : O →ₐ[K] IsLocalRing.ResidueField O :=
    IsScalarTower.toAlgHom K O (IsLocalRing.ResidueField O)
  have hprod := IntegralGroupPowerSeries.reduction_list_prod_eq_one reduction (l.map p) (by
    intro y hy
    obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hy
    apply Over.OverMorphism.ext
    exact hpred a)
  exact congrArg
    (fun f : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries (IsLocalRing.ResidueField O))))) ⟶ G => f.left) hprod

end AlgebraicCurve
