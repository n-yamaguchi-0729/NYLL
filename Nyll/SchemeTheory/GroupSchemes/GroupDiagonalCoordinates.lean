/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.FormalDiagonalEvaluation
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Actual group coordinates at the generic diagonal

The quotient of the two pullbacks of an actual group-valued point is the
identity on the diagonal. Its restriction to the local ring of the diagonal
therefore factors through every open identity neighbourhood. For an affine
neighbourhood this constructs its coordinate ring map into that local ring.
No formal parameter or bound on coefficients is part of this construction.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace AlgebraicGeometry.GroupDiagonal

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

private theorem scalarSpecMap_id (A : Type u) [CommRing A] [Algebra K A] :
    scalarSpecMap (AlgHom.id K A) = 𝟙 (scalarSpec (K := K) A) := by
  apply Over.OverMorphism.ext
  change Spec.map (𝟙 (CommRingCat.of A)) = 𝟙 _
  exact Spec.map_id _

variable {F : Type u} [Field F] [Algebra K F]
variable {G : Over (Spec (.of K))} [GrpObj G]

/-- The actual quotient of the two pullbacks of a group-valued point. -/
def diagonalDifference
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G) :
    Spec (.of (F ⊗[K] F)) ⟶ G.left :=
  ((scalarSpecMap (Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] F) ≫ x) *
    (scalarSpecMap (Algebra.TensorProduct.includeRight : F →ₐ[K] F ⊗[K] F) ≫ x)⁻¹).left

/-- On the diagonal the two actual pullbacks cancel. -/
theorem diagonalDifference_diagonal
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' K (S := F)).toRingHom) ≫
      diagonalDifference x =
        (1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G).left := by
  have h : scalarSpecMap (Algebra.TensorProduct.lmul' K (S := F)) ≫
      ((scalarSpecMap (Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] F) ≫ x) *
        (scalarSpecMap (Algebra.TensorProduct.includeRight : F →ₐ[K] F ⊗[K] F) ≫ x)⁻¹) =
      (1 : scalarSpec (K := K) F ⟶ G) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
      ← scalarSpecMap_comp, ← scalarSpecMap_comp,
      Algebra.TensorProduct.lmul'_comp_includeLeft,
      Algebra.TensorProduct.lmul'_comp_includeRight,
      scalarSpecMap_id, Category.id_comp, mul_inv_cancel]
  exact congrArg (fun a : scalarSpec (K := K) F ⟶ G => a.left) h

/-- The actual group difference restricted to the local ring of the diagonal. -/
def localDiagonalDifference
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G) :
    Spec (.of (Localization.AtPrime
      (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal)) ⟶ G.left :=
  Spec.map (CommRingCat.ofHom (algebraMap (F ⊗[K] F)
    (Localization.AtPrime (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal))) ≫
      diagonalDifference x

private theorem localization_closedPoint :
    Spec.map (CommRingCat.ofHom (algebraMap (F ⊗[K] F)
      (Localization.AtPrime (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal)))
      (IsLocalRing.closedPoint _) = PowerSeries.diagonalPrime (K := K) (F := F) := by
  apply PrimeSpectrum.ext
  exact Localization.AtPrime.under_maximalIdeal

private theorem diagonal_closedPoint :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' K (S := F)).toRingHom)
      (IsLocalRing.closedPoint F) = PowerSeries.diagonalPrime (K := K) (F := F) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (Algebra.TensorProduct.lmul' K (S := F)).toRingHom
    (IsLocalRing.maximalIdeal F) =
      RingHom.ker (Algebra.TensorProduct.lmul' K (S := F)).toRingHom
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

private theorem one_left {S T : Scheme.{u}} (H : Over S) [GrpObj H]
    (t : T ⟶ S) :
    (1 : Over.mk t ⟶ H).left = t ≫ (1 : Over.mk (𝟙 S) ⟶ H).left := by
  have h := MonObj.comp_one (M := H)
    (Over.homMk t : Over.mk t ⟶ Over.mk (𝟙 S))
  exact (congrArg (fun a : Over.mk t ⟶ H => a.left) h).symm

/-- Every open identity neighbourhood contains the full local group difference. -/
theorem localDiagonalDifference_preimage
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    localDiagonalDifference x ⁻¹ᵁ V = ⊤ := by
  apply Scheme.preimage_eq_top_of_closedPoint_mem
  change (diagonalDifference x)
    (Spec.map (CommRingCat.ofHom (algebraMap (F ⊗[K] F)
      (Localization.AtPrime (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal)))
        (IsLocalRing.closedPoint _)) ∈ V
  rw [localization_closedPoint]
  let z : Spec (CommRingCat.of F) := IsLocalRing.closedPoint F
  have hd := congrArg (fun f : Spec (CommRingCat.of F) ⟶ G.left => f z)
    (diagonalDifference_diagonal x)
  have hu := congrArg (fun f : Spec (CommRingCat.of F) ⟶ G.left => f z)
    (one_left G (Spec.map (CommRingCat.ofHom (algebraMap K F))))
  have hp := congrArg (fun y => diagonalDifference x y)
    (diagonal_closedPoint (K := K) (F := F))
  exact (hp ▸ hd.symm ▸ hu.symm ▸ hunit ⟨_, rfl⟩)

/-- The actual local group difference, factored through an open identity neighbourhood. -/
def localDiagonalLift
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    Spec (.of (Localization.AtPrime
      (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal)) ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (localDiagonalDifference x) (by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ localDiagonalDifference x ⁻¹ᵁ V := by
      rw [localDiagonalDifference_preimage x V hunit]
      trivial
    exact ⟨⟨localDiagonalDifference x z, hz⟩, rfl⟩)

/-- The constructed open-neighbourhood factor recovers the original difference. -/
theorem localDiagonalLift_fac
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    localDiagonalLift x V hunit ≫ V.ι = localDiagonalDifference x :=
  IsOpenImmersion.lift_fac _ _ _

/-- Actual affine coordinate functions of the difference, as elements of the
local ring at the generic diagonal. -/
def diagonalCoordinates
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    Γ(G.left, V) →+*
      Localization.AtPrime (PowerSeries.diagonalPrime (K := K) (F := F)).asIdeal :=
  (Spec.preimage (localDiagonalLift x V hunit ≫ hV.isoSpec.hom)).hom

/-- The coordinate homomorphism represents the actual localized group difference. -/
theorem diagonalCoordinates_spec
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G)
    (V : G.left.Opens) (hV : IsAffineOpen V)
    (hunit : Set.range (1 : Over.mk (𝟙 (Spec (.of K))) ⟶ G).left ⊆ V) :
    Spec.map (CommRingCat.ofHom (diagonalCoordinates x V hV hunit)) ≫ hV.fromSpec =
      localDiagonalDifference x := by
  change Spec.map (Spec.preimage (localDiagonalLift x V hunit ≫ hV.isoSpec.hom)) ≫
    hV.fromSpec = _
  rw [Spec.map_preimage, Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec]
  exact localDiagonalLift_fac x V hunit

end AlgebraicGeometry.GroupDiagonal
