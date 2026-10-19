/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.SeparatingFormalTranslationComparison
import Nyll.SchemeTheory.GroupSchemes.GroupDiagonalCoordinates

/-! # Change of formal translation for actual group diagonal coordinates

A formal deformation with residue an embedding evaluates the same local
ring of the generic diagonal: denominators have nonzero residue and hence
are units. Localization uniqueness lifts the separating-parameter comparison
from field elements to every element of this local ring. In particular it
substitutes the actual affine-chart coordinates of the group difference.
The resulting coordinate homomorphism represents the pulled-back original
group difference, by the already constructed diagonal-chart factorization.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace PowerSeries

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L]

/-- Tensor evaluation with a specified residue embedding. Its two points
are the actual moving lift and the constant embedded point. -/
def diagonalTensorMapAlong (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L) :
    (F ⊗[K] F) →ₐ[K] PowerSeries L :=
  Algebra.TensorProduct.productMap ρ
    ((IsScalarTower.toAlgHom K L (PowerSeries L)).comp i)

/-- Reduction of the tensor evaluation is embedded multiplication. -/
theorem constantCoeff_diagonalTensorMapAlong
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : constantCoeff.comp ρ.toRingHom = i.toRingHom)
    (r : F ⊗[K] F) :
    constantCoeff (diagonalTensorMapAlong i ρ r) =
      i (Algebra.TensorProduct.lmul' K r) := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    change constantCoeff (ρ a * C (i b)) = i (a * b)
    have ha : constantCoeff (ρ a) = i a := RingHom.congr_fun hρ0 a
    rw [map_mul, constantCoeff_C, ha, map_mul]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]

private theorem isUnit_diagonalTensorMapAlong
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : constantCoeff.comp ρ.toRingHom = i.toRingHom)
    (s : (diagonalPrime (K := K) (F := F)).asIdeal.primeCompl) :
    IsUnit (diagonalTensorMapAlong i ρ s) := by
  apply isUnit_iff_constantCoeff.mpr
  rw [constantCoeff_diagonalTensorMapAlong i ρ hρ0]
  apply isUnit_iff_ne_zero.mpr
  intro hs
  apply s.property
  apply RingHom.mem_ker.mpr
  exact i.injective (hs.trans (map_zero i).symm)

/-- Actual evaluation on the original generic diagonal after changing the
residue field. The localization lift is constructed from unit denominators. -/
def diagonalEvaluationAlong
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : constantCoeff.comp ρ.toRingHom = i.toRingHom) :
    Localization.AtPrime (diagonalPrime (K := K) (F := F)).asIdeal →+*
      PowerSeries L :=
  IsLocalization.lift (g := (diagonalTensorMapAlong i ρ).toRingHom)
    (isUnit_diagonalTensorMapAlong i ρ hρ0)

/-- The constructed local evaluation extends the actual tensor evaluation. -/
theorem diagonalEvaluationAlong_algebraMap
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : constantCoeff.comp ρ.toRingHom = i.toRingHom)
    (r : F ⊗[K] F) :
    diagonalEvaluationAlong i ρ hρ0
        (algebraMap (F ⊗[K] F)
          (Localization.AtPrime (diagonalPrime (K := K) (F := F)).asIdeal) r) =
      diagonalTensorMapAlong i ρ r :=
  IsLocalization.lift_eq (isUnit_diagonalTensorMapAlong i ρ hρ0) r

/-- The separating-parameter comparison extends to every actual function
regular at the generic diagonal, by uniqueness of the localization lift. -/
theorem diagonalEvaluationAlong_substitution
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F) (hσt : σ t = C t + X)
    (hσ0 : constantCoeff.comp σ.toRingHom = RingHom.id F)
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : constantCoeff.comp ρ.toRingHom = i.toRingHom)
    (z : Localization.AtPrime (diagonalPrime (K := K) (F := F)).asIdeal) :
    diagonalEvaluationAlong i ρ hρ0 z =
      subst (ρ t - C (i t)) (map i.toRingHom (diagonalEvaluation σ hσ0 z)) := by
  let δ : PowerSeries L := ρ t - C (i t)
  have hδ : constantCoeff δ = 0 := by
    have ht0 : constantCoeff (ρ t) = i t := RingHom.congr_fun hρ0 t
    change constantCoeff (ρ t - C (i t)) = 0
    rw [map_sub, constantCoeff_C, ht0, sub_self]
  let S : PowerSeries L →ₐ[L] PowerSeries L :=
    substAlgHom (HasSubst.of_constantCoeff_zero' hδ)
  have hS (f : F) : S (map i.toRingHom (σ f)) = ρ f := by
    change substAlgHom (HasSubst.of_constantCoeff_zero' hδ)
      (map i.toRingHom (σ f)) = _
    rw [coe_substAlgHom]
    exact formalTranslation_substitution t ht σ hσt hσ0 i ρ hρ0 f
  have h : diagonalEvaluationAlong i ρ hρ0 =
      S.toRingHom.comp ((map i.toRingHom).comp (diagonalEvaluation σ hσ0)) := by
    apply IsLocalization.ringHom_ext
      (M := (diagonalPrime (K := K) (F := F)).asIdeal.primeCompl)
    apply RingHom.ext
    intro r
    change diagonalEvaluationAlong i ρ hρ0 (algebraMap _ _ r) =
      S (map i.toRingHom (diagonalEvaluation σ hσ0 (algebraMap _ _ r)))
    rw [diagonalEvaluationAlong_algebraMap, diagonalEvaluation_algebraMap]
    induction r using TensorProduct.inductionOn with
    | tmul a b =>
      change ρ a * C (i b) = S (map i.toRingHom (σ a * C b))
      rw [map_mul, map_C, map_mul, hS]
      have hC : S (C (i b)) = C (i b) := S.commutes (i b)
      change ρ a * C (i b) = ρ a * S (C (i b))
      rw [hC]
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  have hz := RingHom.congr_fun h z
  change diagonalEvaluationAlong i ρ hρ0 z =
    substAlgHom (HasSubst.of_constantCoeff_zero' hδ)
      (map i.toRingHom (diagonalEvaluation σ hσ0 z)) at hz
  rw [coe_substAlgHom] at hz
  exact hz

/-- Centering at the actual constant coefficient commutes with the same
change of formal translation, ready for zero-constant substitution estimates. -/
theorem diagonalEvaluationAlong_centered_substitution
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F) (hσt : σ t = C t + X)
    (hσ0 : constantCoeff.comp σ.toRingHom = RingHom.id F)
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : constantCoeff.comp ρ.toRingHom = i.toRingHom)
    (z : Localization.AtPrime (diagonalPrime (K := K) (F := F)).asIdeal) :
    diagonalEvaluationAlong i ρ hρ0 z - C (constantCoeff (diagonalEvaluationAlong i ρ hρ0 z)) =
      subst (ρ t - C (i t))
        (map i.toRingHom (diagonalEvaluation σ hσ0 z -
          C (constantCoeff (diagonalEvaluation σ hσ0 z)))) := by
  have hδ : constantCoeff (ρ t - C (i t)) = 0 := by
    have ht0 : constantCoeff (ρ t) = i t := RingHom.congr_fun hρ0 t
    rw [map_sub, constantCoeff_C, ht0, sub_self]
  have hc : constantCoeff (diagonalEvaluationAlong i ρ hρ0 z) =
      i (constantCoeff (diagonalEvaluation σ hσ0 z)) := by
    rw [diagonalEvaluationAlong_substitution t ht σ hσt hσ0 i ρ hρ0]
    change MvPowerSeries.constantCoeff (subst (ρ t - C (i t))
      (map i.toRingHom (diagonalEvaluation σ hσ0 z))) = _
    rw [constantCoeff_subst_of_constantCoeff_zero hδ]
    rfl
  rw [hc, diagonalEvaluationAlong_substitution t ht σ hσt hσ0 i ρ hρ0,
    map_sub, map_C, subst_sub (HasSubst.of_constantCoeff_zero' hδ), subst_C]
  rfl

end PowerSeries

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupDiagonal

variable {K F L : Type u} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L]
  {G : Over (Spec (.of K))} [GrpObj G]

/-- Coordinates of the actual formal group difference with any specified
residue embedding and formal lift. -/
def formalCoordinatesAlong
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom) :
    Γ(G.left, V) →+* PowerSeries L :=
  (PowerSeries.diagonalEvaluationAlong i ρ hρ0).comp (diagonalCoordinates x V hV hunit)

/-- The constructed coordinate homomorphism represents the original group
difference pulled back by the actual moving and constant tensor points. -/
theorem formalCoordinatesAlong_spec
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom) :
    Spec.map (CommRingCat.ofHom (formalCoordinatesAlong x V hV hunit i ρ hρ0)) ≫
        hV.fromSpec =
      Spec.map (CommRingCat.ofHom (PowerSeries.diagonalTensorMapAlong i ρ).toRingHom) ≫
        diagonalDifference x := by
  have hmap :
      (PowerSeries.diagonalEvaluationAlong i ρ hρ0).comp
          (algebraMap (F ⊗[K] F)
            (Localization.AtPrime (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal)) =
        (PowerSeries.diagonalTensorMapAlong i ρ).toRingHom := by
    apply RingHom.ext
    exact PowerSeries.diagonalEvaluationAlong_algebraMap i ρ hρ0
  change Spec.map (CommRingCat.ofHom
    ((PowerSeries.diagonalEvaluationAlong i ρ hρ0).comp
      (diagonalCoordinates x V hV hunit))) ≫ hV.fromSpec = _
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, diagonalCoordinates_spec]
  change Spec.map (CommRingCat.ofHom (PowerSeries.diagonalEvaluationAlong i ρ hρ0)) ≫
    (Spec.map (CommRingCat.ofHom (algebraMap (F ⊗[K] F)
      (Localization.AtPrime (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal))) ≫
        diagonalDifference x) = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hmap]

/-- Changing the formal field translation substitutes the actual affine
coordinates; coordinate compatibility is a consequence, not a hypothesis. -/
theorem formalCoordinatesAlong_substitution
    (t : F) (ht : Transcendental K t)
    [FiniteDimensional (IntermediateField.adjoin K {t}) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K {t}) F]
    (σ : F →ₐ[K] PowerSeries F)
    (hσt : σ t = PowerSeries.C t + PowerSeries.X)
    (hσ0 : PowerSeries.constantCoeff.comp σ.toRingHom = RingHom.id F)
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom)
    (a : Γ(G.left, V)) :
    formalCoordinatesAlong x V hV hunit i ρ hρ0 a =
      PowerSeries.subst (ρ t - PowerSeries.C (i t))
        (PowerSeries.map i.toRingHom
          (PowerSeries.diagonalEvaluation σ hσ0 (diagonalCoordinates x V hV hunit a))) :=
  PowerSeries.diagonalEvaluationAlong_substitution t ht σ hσt hσ0 i ρ hρ0 _

end AlgebraicGeometry.GroupDiagonal
