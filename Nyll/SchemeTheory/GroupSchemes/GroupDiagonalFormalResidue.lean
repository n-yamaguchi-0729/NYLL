/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.GroupDiagonalFormalSubstitution
import Nyll.SchemeTheory.GroupSchemes.AffineLineGroupFormalDifference

/-! # The actual unit residue of formal diagonal coordinates

The constant coefficient is evaluation at the original group unit, followed
by the given coefficient-field inclusion. Thus centering the actual formal
coordinates is the same as subtracting the scalar unit coordinates.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupDiagonal

variable {K F L : Type u} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L]
  {G : Over (Spec (.of K))} [GrpObj G]

private theorem one_left {S T : Scheme.{u}} (H : Over S) [GrpObj H]
    (t : T ⟶ S) :
    (1 : Over.mk t ⟶ H).left = t ≫ (1 : Over.mk (𝟙 S) ⟶ H).left := by
  have h : (Over.homMk t (by simp) : Over.mk t ⟶ Over.mk (𝟙 S)) ≫
      (1 : Over.mk (𝟙 S) ⟶ H) = 1 := MonObj.comp_one _
  exact (congrArg (fun a : Over.mk t ⟶ H => a.left) h).symm

/-- Reduction in the deformation parameter is the actual unit-coordinate
map, with scalars in the prescribed residue field. -/
theorem constantCoeff_comp_formalCoordinatesAlong
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom) :
    PowerSeries.constantCoeff.comp (formalCoordinatesAlong x V hV hunit i ρ hρ0) =
      (algebraMap K L).comp
        (AffineLineGroupFormalDifference.identityCoordinates V hV hunit) := by
  have htensor : PowerSeries.constantCoeff.comp
      (PowerSeries.diagonalTensorMapAlong i ρ).toRingHom =
        i.toRingHom.comp (Algebra.TensorProduct.lmul' K (S := F)).toRingHom := by
    apply RingHom.ext
    exact PowerSeries.constantCoeff_diagonalTensorMapAlong i ρ hρ0
  have h : CommRingCat.ofHom
      (PowerSeries.constantCoeff.comp (formalCoordinatesAlong x V hV hunit i ρ hρ0)) =
      CommRingCat.ofHom ((algebraMap K L).comp
        (AffineLineGroupFormalDifference.identityCoordinates V hV hunit)) := by
    apply Spec.map_injective
    apply (cancel_mono hV.fromSpec).mp
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      formalCoordinatesAlong_spec, AffineLineGroupFormalDifference.identityCoordinates_spec]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, htensor,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      diagonalDifference_diagonal, one_left, ← Category.assoc, ← Spec.map_comp]
    apply congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of L =>
      Spec.map f ≫ (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left)
    exact CommRingCat.hom_ext i.comp_algebraMap
  exact congrArg (fun f : CommRingCat.of Γ(G.left, V) ⟶ CommRingCat.of L => f.hom) h

/-- Every coordinate series has its scalar unit value as constant term. -/
theorem constantCoeff_formalCoordinatesAlong
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom)
    (a : Γ(G.left, V)) :
    PowerSeries.constantCoeff (formalCoordinatesAlong x V hV hunit i ρ hρ0 a) =
      algebraMap K L (AffineLineGroupFormalDifference.identityCoordinates V hV hunit a) :=
  RingHom.congr_fun (constantCoeff_comp_formalCoordinatesAlong x V hV hunit i ρ hρ0) a

end AlgebraicGeometry.GroupDiagonal
