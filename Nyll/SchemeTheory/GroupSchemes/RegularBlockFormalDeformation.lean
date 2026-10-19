/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.LaurentFormalTranslation
import Nyll.SchemeTheory.GroupSchemes.AffineLineGroupFormalDifference

/-! # Integral reciprocal deformation of a regular group-valued block

Formal translation followed by substitution of `-s²T/(1+sT)` constructs
the actual homomorphism `K[[s]] → K[[s]][[T]]` sending `s` to `s/(1+sT)`.
Its constant coefficient is the identity, and coefficientwise reduction
modulo `s` is constant inclusion after reduction. Therefore the difference
of any actual integral group-valued point and its deformation is an
integral group-valued point whose reduction is the identity. No splitting
of the original finite-flat block or restriction on its ramification is used.
-/

noncomputable section

universe u

namespace PowerSeries

variable {K : Type u} [Field K]

private def reciprocalDenominator : PowerSeries (PowerSeries K) :=
  1 + C (X : PowerSeries K) * X

private theorem reciprocalDenominator_constantCoeff :
    constantCoeff (reciprocalDenominator (K := K)) = 1 := by
  simp [reciprocalDenominator]

private def reciprocalDisplacement : PowerSeries (PowerSeries K) :=
  -(C (X : PowerSeries K)) ^ 2 * X *
    invOfUnit (reciprocalDenominator (K := K)) 1

private theorem reciprocalDisplacement_constantCoeff :
    constantCoeff (reciprocalDisplacement (K := K)) = 0 := by
  simp [reciprocalDisplacement]

private theorem reciprocalDisplacement_hasSubst :
    HasSubst (reciprocalDisplacement (K := K)) :=
  HasSubst.of_constantCoeff_zero reciprocalDisplacement_constantCoeff

private theorem reciprocalDisplacement_residue :
    map (constantCoeff (R := K)) (reciprocalDisplacement (K := K)) = 0 := by
  simp [reciprocalDisplacement]

private def reciprocalSubstitution :
    PowerSeries (PowerSeries K) →+* PowerSeries (PowerSeries K) where
  toFun f := subst (reciprocalDisplacement (K := K)) f
  map_one' := by
    have h := subst_C (a := reciprocalDisplacement (K := K)) (1 : PowerSeries K)
    simpa only [map_one] using h
  map_mul' f g := subst_mul (reciprocalDisplacement_hasSubst (K := K)) f g
  map_zero' := by
    have h := subst_C (a := reciprocalDisplacement (K := K)) (0 : PowerSeries K)
    simpa only [map_zero] using h
  map_add' f g := subst_add (reciprocalDisplacement_hasSubst (K := K)) f g

/-- The integral deformation sending the coefficient parameter `s` to
`s/(1+sT)`, constructed by substitution in the actual formal translation. -/
def reciprocalParameterDeformation :
    PowerSeries K →ₐ[K] PowerSeries (PowerSeries K) where
  toRingHom := reciprocalSubstitution.comp formalTranslation.toRingHom
  commutes' a := by
    change reciprocalSubstitution (formalTranslation (algebraMap K (PowerSeries K) a)) = _
    rw [formalTranslation.commutes]
    rw [PowerSeries.algebraMap_apply]
    change subst (reciprocalDisplacement (K := K)) (C (algebraMap K (PowerSeries K) a)) = _
    rw [subst_C]
    rfl

private theorem reciprocalParameterDeformation_apply (f : PowerSeries K) :
    reciprocalParameterDeformation f =
      subst (reciprocalDisplacement (K := K)) (formalTranslation f) := rfl

/-- The new formal parameter vanishing recovers the original series. -/
theorem constantCoeff_reciprocalParameterDeformation (f : PowerSeries K) :
    constantCoeff (reciprocalParameterDeformation f) = f := by
  rw [reciprocalParameterDeformation_apply]
  change MvPowerSeries.constantCoeff (subst (reciprocalDisplacement (K := K))
    (formalTranslation f)) = f
  rw [constantCoeff_subst_of_constantCoeff_zero
    (reciprocalDisplacement_constantCoeff (K := K))]
  exact constantCoeff_formalTranslation f

/-- The image of `s` is the actual quotient by the unit `1+sT`. -/
theorem reciprocalParameterDeformation_X :
    reciprocalParameterDeformation (X : PowerSeries K) =
      C (X : PowerSeries K) *
        invOfUnit (1 + C (X : PowerSeries K) * X) 1 := by
  rw [reciprocalParameterDeformation_apply, formalTranslation_X,
    subst_add reciprocalDisplacement_hasSubst, subst_C,
    subst_X reciprocalDisplacement_hasSubst]
  let a : PowerSeries (PowerSeries K) := C (X : PowerSeries K)
  let d := reciprocalDenominator (K := K)
  let v := invOfUnit d 1
  have hd : d * v = 1 :=
    mul_invOfUnit d 1 reciprocalDenominator_constantCoeff
  have hv : v * d = 1 :=
    invOfUnit_mul d 1 reciprocalDenominator_constantCoeff
  change a + (-a ^ 2 * X * v) = a * v
  have hprod : (a + (-a ^ 2 * X * v)) * d = a := by
    calc
      (a + (-a ^ 2 * X * v)) * d =
          a * d - a ^ 2 * X * (v * d) := by ring
      _ = a * d - a ^ 2 * X := by rw [hv, mul_one]
      _ = a := by
        change a * (1 + a * X) - a ^ 2 * X = a
        ring
  calc
    a + (-a ^ 2 * X * v) = (a + (-a ^ 2 * X * v)) * (d * v) := by
      rw [hd, mul_one]
    _ = ((a + (-a ^ 2 * X * v)) * d) * v := by ring
    _ = a * v := by rw [hprod]

/-- Coefficientwise reduction modulo `s` makes the actual deformation
constant in `T`. This is a statement about all coefficients. -/
theorem reciprocalParameterDeformation_residue (f : PowerSeries K) :
    map (constantCoeff (R := K)) (reciprocalParameterDeformation f) =
      C (constantCoeff f) := by
  rw [reciprocalParameterDeformation_apply]
  change MvPowerSeries.map (constantCoeff (R := K))
    (subst (reciprocalDisplacement (K := K)) (formalTranslation f)) = _
  rw [map_subst reciprocalDisplacement_hasSubst]
  change subst (map (constantCoeff (R := K)) (reciprocalDisplacement (K := K)))
    (map (constantCoeff (R := K)) (formalTranslation f)) = _
  rw [reciprocalDisplacement_residue, subst_zero_eq_C_constantCoeff]
  change C (constantCoeff (map (constantCoeff (R := K)) (formalTranslation f))) = _
  congr 1
  change constantCoeff (constantCoeff (formalTranslation f)) = constantCoeff f
  rw [constantCoeff_formalTranslation]

/-- The residue identity as an equality of the constructed ring homomorphisms. -/
theorem map_constantCoeff_comp_reciprocalParameterDeformation :
    (map (constantCoeff (R := K))).comp reciprocalParameterDeformation.toRingHom =
      (C (R := K)).comp constantCoeff := by
  apply RingHom.ext
  intro f
  exact reciprocalParameterDeformation_residue f

end PowerSeries

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.RegularBlockFormalDeformation

variable {K : Type u} [Field K]

private abbrev scalarSpec (A : Type u) [CommRing A] [Algebra K A] :
    Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))

private def scalarSpecMap {A B : Type u} [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] (f : A →ₐ[K] B) :
    scalarSpec (K := K) B ⟶ scalarSpec (K := K) A :=
  Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K B))
    rw [← Spec.map_comp]
    apply congrArg (fun h : CommRingCat.of K ⟶ CommRingCat.of B => Spec.map h)
    exact CommRingCat.hom_ext f.comp_algebraMap)

private theorem scalarSpecMap_comp {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    scalarSpecMap (g.comp f) = scalarSpecMap g ≫ scalarSpecMap f := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (g.comp f).toRingHom) =
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp]
  rfl

private def constantInclusion : PowerSeries K →ₐ[K] PowerSeries (PowerSeries K) where
  toRingHom := PowerSeries.C
  commutes' a := (PowerSeries.algebraMap_apply (r := a)).symm

private def coefficientResidue : PowerSeries K →ₐ[K] K where
  toRingHom := PowerSeries.constantCoeff
  commutes' a := PowerSeries.constantCoeff_C a

private def residue : PowerSeries (PowerSeries K) →ₐ[K] PowerSeries K :=
  PowerSeries.mapAlgHom coefficientResidue

private theorem residue_deformation :
    (residue (K := K)).comp PowerSeries.reciprocalParameterDeformation =
      residue.comp constantInclusion := by
  apply AlgHom.ext
  intro f
  change PowerSeries.map (PowerSeries.constantCoeff (R := K))
      (PowerSeries.reciprocalParameterDeformation f) =
    PowerSeries.map (PowerSeries.constantCoeff (R := K)) (PowerSeries.C f)
  rw [PowerSeries.reciprocalParameterDeformation_residue, PowerSeries.map_C]

variable {G : Over (Spec (.of K))} [GrpObj G]

/-- The actual integral formal difference of any `G(K[[s]])` point under
`s ↦ s/(1+sT)`. It is defined over `K[[s]][[T]]`, without passing to a
splitting field or choosing individual points of a finite-flat block. -/
def difference (x : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (PowerSeries K)))) ⟶ G) :
    Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (PowerSeries (PowerSeries K))))) ⟶ G :=
  (scalarSpecMap PowerSeries.reciprocalParameterDeformation ≫ x) *
    (scalarSpecMap constantInclusion ≫ x)⁻¹

/-- Reduction modulo the coefficient parameter sends the entire actual
group-valued difference to the unit over `K[[T]]`. -/
theorem difference_residue (x : Over.mk (Spec.map
      (CommRingCat.ofHom (algebraMap K (PowerSeries K)))) ⟶ G) :
    Spec.map (CommRingCat.ofHom
      (PowerSeries.map (PowerSeries.constantCoeff (R := K)))) ≫
        (difference x).left =
      (1 : Over.mk (Spec.map
        (CommRingCat.ofHom (algebraMap K (PowerSeries K)))) ⟶ G).left := by
  have h : scalarSpecMap residue ≫ difference x =
      (1 : scalarSpec (K := K) (PowerSeries K) ⟶ G) := by
    change scalarSpecMap residue ≫
      ((scalarSpecMap PowerSeries.reciprocalParameterDeformation ≫ x) *
        (scalarSpecMap constantInclusion ≫ x)⁻¹) = _
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
      ← scalarSpecMap_comp, ← scalarSpecMap_comp, residue_deformation, mul_inv_cancel]
  exact congrArg (fun a : scalarSpec (K := K) (PowerSeries K) ⟶ G => a.left) h

end AlgebraicGeometry.RegularBlockFormalDeformation
