/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.RegularBlockFormalDeformation
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Integral coefficient extension of an actual regular-block point

A local coefficient map K[[s]] → R transports the actual reciprocal
formal difference into G(R[[T]]). Its whole residue is the group unit,
and its generic coefficient extension is computed without replacing the
original group point or reconstructing a trace.
-/

noncomputable section

universe u

namespace PowerSeries

/-- Every actual local K-algebra map from K[[s]] has constant-coefficient
residue. This converts localness of the constructed completion map into the
coefficientwise residue identity needed for an integral group point. -/
theorem residue_comp_localAlgHom {K R : Type*} [Field K] [CommRing R]
    [IsLocalRing R] [Algebra K R] (j : PowerSeries K →ₐ[K] R)
    [IsLocalHom j.toRingHom] :
    (IsLocalRing.residue R).comp j.toRingHom =
      (algebraMap K (IsLocalRing.ResidueField R)).comp constantCoeff := by
  apply RingHom.ext
  intro f
  have hf : f - C (constantCoeff f) ∈ IsLocalRing.maximalIdeal (PowerSeries K) := by
    rw [← ker_coeff_eq_max_ideal, RingHom.mem_ker, map_sub, constantCoeff_C, sub_self]
  have hjf : j (f - C (constantCoeff f)) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal] at hf ⊢
    exact fun h => hf ((isUnit_map_iff j.toRingHom _).mp h)
  have hzero := (IsLocalRing.residue_eq_zero_iff _).mpr hjf
  rw [map_sub, map_sub, sub_eq_zero] at hzero
  change IsLocalRing.residue R (j f) = algebraMap K (IsLocalRing.ResidueField R)
    (constantCoeff f)
  rw [hzero]
  change IsLocalRing.residue R (j (algebraMap K (PowerSeries K) (constantCoeff f))) = _
  rw [j.commutes, IsScalarTower.algebraMap_apply K R (IsLocalRing.ResidueField R)]
  rfl

end PowerSeries

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.RegularBlockFormalDeformation

private def coefficientMap {K A B : Type u} [Field K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (j : A →ₐ[K] B) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries B)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries A)))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (PowerSeries.map j.toRingHom))) (by
    change Spec.map (CommRingCat.ofHom (PowerSeries.map j.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries A))) =
        Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries B)))
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (PowerSeries.mapAlgHom j).comp_algebraMap))

private theorem coefficientMap_comp
    {K A B C : Type u} [Field K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (j : A →ₐ[K] B) (k : B →ₐ[K] C) :
    coefficientMap (k.comp j) = coefficientMap k ≫ coefficientMap j := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (PowerSeries.map (k.comp j).toRingHom)) =
    Spec.map (CommRingCat.ofHom (PowerSeries.map k.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (PowerSeries.map j.toRingHom))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro f
  apply PowerSeries.ext
  intro n
  rfl

/-- The actual regular-block difference after an integral coefficient map. -/
def integralCoefficientDifference
    {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    {G : Over (Spec (.of K))} [GrpObj G]
    (j : PowerSeries K →ₐ[K] R)
    (x : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries K)))) ⟶ G) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (PowerSeries R)))) ⟶ G :=
  coefficientMap j ≫ difference x

/-- Localness of the constructed coefficient map proves that the entire
integral regular-block difference reduces to one over the residue series. -/
theorem integralCoefficientDifference_residue
    {K R : Type u} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
    {G : Over (Spec (.of K))} [GrpObj G]
    (j : PowerSeries K →ₐ[K] R) [IsLocalHom j.toRingHom]
    (x : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries K)))) ⟶ G) :
    Spec.map (CommRingCat.ofHom (PowerSeries.map (IsLocalRing.residue R))) ≫
        (integralCoefficientDifference j x).left =
      (1 : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (PowerSeries (IsLocalRing.ResidueField R))))) ⟶ G).left := by
  let ρ : R →ₐ[K] IsLocalRing.ResidueField R :=
    IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)
  let cc : PowerSeries K →ₐ[K] K :=
    { toRingHom := PowerSeries.constantCoeff
      commutes' := fun a => PowerSeries.constantCoeff_C a }
  let κ : K →ₐ[K] IsLocalRing.ResidueField R := Algebra.ofId K _
  have hmaps : ρ.comp j = κ.comp cc := by
    apply AlgHom.ext
    exact RingHom.congr_fun (PowerSeries.residue_comp_localAlgHom j)
  have hred : coefficientMap cc ≫ difference x =
      (1 : Over.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (PowerSeries K)))) ⟶ G) := by
    apply Over.OverMorphism.ext
    exact difference_residue x
  have h : coefficientMap ρ ≫ integralCoefficientDifference j x = 1 := by
    change coefficientMap ρ ≫ (coefficientMap j ≫ difference x) = _
    rw [← Category.assoc, ← coefficientMap_comp, hmaps,
      coefficientMap_comp, Category.assoc, hred, MonObj.comp_one]
  exact congrArg (fun f : Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap K (PowerSeries (IsLocalRing.ResidueField R))))) ⟶ G => f.left) h

/-- Generic coefficient extension of the actual integral point is exactly
the original regular difference with the composite coefficient map. -/
theorem integralCoefficientDifference_generic
    {K R L : Type u} [Field K] [CommRing R] [CommRing L]
    [Algebra K R] [Algebra K L]
    {G : Over (Spec (.of K))} [GrpObj G]
    (j : PowerSeries K →ₐ[K] R) (k : R →ₐ[K] L)
    (x : Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (PowerSeries K)))) ⟶ G) :
    Spec.map (CommRingCat.ofHom (PowerSeries.map k.toRingHom)) ≫
        (integralCoefficientDifference j x).left =
      (integralCoefficientDifference (k.comp j) x).left := by
  have h : coefficientMap k ≫ integralCoefficientDifference j x =
      integralCoefficientDifference (k.comp j) x := by
    change coefficientMap k ≫ (coefficientMap j ≫ difference x) = _
    rw [← Category.assoc, ← coefficientMap_comp]
    rfl
  exact congrArg (fun f : Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap K (PowerSeries L)))) ⟶ G => f.left) h

end AlgebraicGeometry.RegularBlockFormalDeformation
