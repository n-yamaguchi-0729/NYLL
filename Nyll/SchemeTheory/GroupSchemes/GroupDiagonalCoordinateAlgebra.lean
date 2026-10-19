/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.GroupDiagonalFormalResidue
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The actual algebra of an affine group identity chart

The structural scheme morphism defines the scalar action on the chart's
sections. The chart inclusion, unit augmentation, and formal diagonal
coordinates are then morphisms over that same base. Local finite type of
the original group supplies finite algebra generators of this actual chart.
No alternative group or independently chosen scalar action is used.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace AlgebraicGeometry.GroupDiagonal

variable {K : Type u} [Field K] {G : Over (Spec (.of K))}

/-- The scalar action supplied by the actual chart structural morphism. -/
@[reducible] def coordinateAlgebra (V : G.left.Opens) (hV : IsAffineOpen V) :
    Algebra K Γ(G.left, V) :=
  (Spec.preimage (hV.fromSpec ≫ G.hom)).hom.toAlgebra

/-- The original affine-chart inclusion with its actual base structure. -/
def coordinateInclusion (V : G.left.Opens) (hV : IsAffineOpen V) :
    let := coordinateAlgebra V hV
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K Γ(G.left, V)))) ⟶ G := by
  let := coordinateAlgebra V hV
  exact Over.homMk hV.fromSpec (Spec.map_preimage (hV.fromSpec ≫ G.hom)).symm

/-- A locally finite-type group has finitely many algebra generators on
this affine chart, with the scalar action induced by its actual structure map. -/
theorem coordinateAlgebra_finiteType [LocallyOfFiniteType G.hom]
    (V : G.left.Opens) (hV : IsAffineOpen V) :
    let := coordinateAlgebra V hV
    Algebra.FiniteType K Γ(G.left, V) := by
  let := coordinateAlgebra V hV
  apply RingHom.finiteType_algebraMap.mp
  change (Spec.preimage (hV.fromSpec ≫ G.hom)).hom.FiniteType
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
  rw [Spec.map_preimage]
  infer_instance

private theorem coordinateMap_comp_algebraMap
    (V : G.left.Opens) (hV : IsAffineOpen V)
    {B : Type u} [CommRing B] [Algebra K B]
    (φ : Γ(G.left, V) →+* B)
    (hφ : (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ≫ G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K B))) :
    let := coordinateAlgebra V hV
    φ.comp (algebraMap K Γ(G.left, V)) = algebraMap K B := by
  let := coordinateAlgebra V hV
  have h : CommRingCat.ofHom (φ.comp (algebraMap K Γ(G.left, V))) =
      CommRingCat.ofHom (algebraMap K B) := by
    apply Spec.map_injective
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    change Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (Spec.preimage (hV.fromSpec ≫ G.hom)) = _
    rw [Spec.map_preimage, ← Category.assoc]
    exact hφ
  exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of B => f.hom) h

variable [GrpObj G]

/-- Unit evaluation is a homomorphism of the actual chart algebra over K. -/
def identityCoordinatesAlgHom (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    let := coordinateAlgebra V hV
    Γ(G.left, V) →ₐ[K] K := by
  let := coordinateAlgebra V hV
  refine { toRingHom := AffineLineGroupFormalDifference.identityCoordinates V hV hunit
           commutes' := ?_ }
  intro a
  apply RingHom.congr_fun (coordinateMap_comp_algebraMap V hV
    (AffineLineGroupFormalDifference.identityCoordinates V hV hunit) ?_) a
  rw [AffineLineGroupFormalDifference.identityCoordinates_spec]
  exact (Over.w (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G)).trans (Spec.map_id _).symm

private theorem one_left {S T : Scheme.{u}} (H : Over S) [GrpObj H] (t : T ⟶ S) :
    (1 : Over.mk t ⟶ H).left = t ≫ (1 : Over.mk (𝟙 S) ⟶ H).left := by
  have h := MonObj.comp_one (M := H) (Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 S))
  exact (congrArg (fun a : Over.mk t ⟶ H => a.left) h).symm

/-- The augmentation and chart inclusion give the original group unit,
with the scalar-spectrum source used by the integral-point construction. -/
theorem identityCoordinatesAlgHom_spec (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    let := coordinateAlgebra V hV
    Spec.map (CommRingCat.ofHom (identityCoordinatesAlgHom V hV hunit).toRingHom) ≫
      (coordinateInclusion V hV).left =
        (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K K))) ⟶ G).left := by
  let := coordinateAlgebra V hV
  change Spec.map (CommRingCat.ofHom
    (AffineLineGroupFormalDifference.identityCoordinates V hV hunit)) ≫ hV.fromSpec = _
  calc
    _ = (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left :=
      AffineLineGroupFormalDifference.identityCoordinates_spec V hV hunit
    _ = Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫
        (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left := by
      change _ = Spec.map (𝟙 (CommRingCat.of K)) ≫ _
      rw [Spec.map_id, Category.id_comp]
    _ = _ := (one_left G (Spec.map (CommRingCat.ofHom (algebraMap K K)))).symm

/-- The tensor difference is a morphism over the original base field. -/
theorem diagonalDifference_comp_structure
    {F : Type u} [Field F] [Algebra K F]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G) :
    diagonalDifference x ≫ G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K (F ⊗[K] F))) := by
  unfold diagonalDifference
  exact Over.w _

/-- The actual formal coordinates preserve the native chart scalar action. -/
def formalCoordinatesAlongAlgHom
    {F L : Type u} [Field F] [Field L] [Algebra K F] [Algebra K L]
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V)
    (i : F →ₐ[K] L) (ρ : F →ₐ[K] PowerSeries L)
    (hρ0 : PowerSeries.constantCoeff.comp ρ.toRingHom = i.toRingHom) :
    let := coordinateAlgebra V hV
    Γ(G.left, V) →ₐ[K] PowerSeries L := by
  let := coordinateAlgebra V hV
  refine { toRingHom := formalCoordinatesAlong x V hV hunit i ρ hρ0
           commutes' := ?_ }
  intro a
  apply RingHom.congr_fun (coordinateMap_comp_algebraMap V hV
    (formalCoordinatesAlong x V hV hunit i ρ hρ0) ?_) a
  rw [formalCoordinatesAlong_spec, Category.assoc, diagonalDifference_comp_structure,
    ← Spec.map_comp]
  apply congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of (PowerSeries L) => Spec.map f)
  exact CommRingCat.hom_ext (PowerSeries.diagonalTensorMapAlong i ρ).comp_algebraMap

end AlgebraicGeometry.GroupDiagonal
