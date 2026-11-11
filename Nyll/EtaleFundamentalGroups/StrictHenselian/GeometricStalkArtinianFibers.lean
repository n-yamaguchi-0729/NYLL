/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkGeometricFibers
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNoetherian
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.Artinian.Ring

/-!
# Reduced Artinian fibers of the actual Noetherian henselization

Geometric fibers are reduced by the existing actual strict-local
comparison. Descent through the algebraic closure gives reducedness for
arbitrary field-valued base changes; the existing integrality supplier
already gives their zero-dimensionality.

For the residue field of an original prime, Noetherianity follows from
the existing Noetherian stalk theorem and essentially finite type base
change in the other tensor factor. Hence the actual fiber is a reduced
Artinian ring. No finite degree of a henselization residue extension is
assumed.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

/-- Every field fiber of the actual geometric stalk is reduced and
zero-dimensional, with the original structure algebra retained. -/
theorem geometricStalk_tensor_reduced_and_zeroDim
    {R Ω K : Type u} [CommRing R] [Field Ω] [Field K]
    [Algebra R K] (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    IsReduced (K ⊗[R] H) ∧ Ring.KrullDimLE 0 (K ⊗[R] H) := by
  intro H actualStructureAlgebra
  let B := K ⊗[R] H
  let L := AlgebraicClosure K
  let C := B ⊗[K] L
  let e : C ≃ₐ[K] L ⊗[R] H :=
    (Algebra.TensorProduct.comm K B L).trans
      (Algebra.TensorProduct.cancelBaseChange R K K L H)
  have : IsReduced (L ⊗[R] H) :=
    geometricStalk_tensor_isReduced_of_isAlgClosed (K := L) φ
  have : IsReduced C := isReduced_of_injective e e.injective
  have hinj : Function.Injective (algebraMap B C) :=
    Algebra.TensorProduct.includeLeft_injective (R := K) (S := K) (A := B) (B := L)
      (RingHom.injective (algebraMap K L))
  exact ⟨isReduced_of_injective (algebraMap B C) hinj,
    geometricStalk_tensor_krullDimLE_zero (K := K) φ⟩

/-- The native residue-field fiber of the actual geometric stalk over a
Noetherian local base is a reduced Artinian ring. -/
theorem geometricStalk_residueFiber_reduced_and_artinian
    {R Ω : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field Ω] (φ : R →+* Ω) [IsLocalHom φ] (p : Ideal R) [p.IsPrime] :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    IsReduced (p.ResidueField ⊗[R] H) ∧ IsArtinianRing (p.ResidueField ⊗[R] H) := by
  intro H actualStructureAlgebra
  have : IsNoetherianRing H := geometricStalk_isNoetherianRing φ
  have : IsNoetherianRing (H ⊗[R] p.ResidueField) :=
    Algebra.EssFiniteType.isNoetherianRing H (H ⊗[R] p.ResidueField)
  have : IsNoetherianRing (p.ResidueField ⊗[R] H) :=
    isNoetherianRing_of_ringEquiv (H ⊗[R] p.ResidueField)
      (Algebra.TensorProduct.comm R H p.ResidueField).toRingEquiv
  obtain ⟨hred, hdim⟩ := geometricStalk_tensor_reduced_and_zeroDim
    (K := p.ResidueField) φ
  have : Ring.KrullDimLE 0 (p.ResidueField ⊗[R] H) := hdim
  exact ⟨hred, IsNoetherianRing.isArtinianRing_of_krullDimLE_zero⟩

end EtaleFundamentalGroups.StrictHenselian
