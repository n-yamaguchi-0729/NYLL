/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkTensorLocal
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkGenericIntegral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Actual geometric fibers of the pointed étale stalk

The existing local comparison after a strictly henselian base change
identifies each local ring of a geometric fiber with its algebraically
closed coefficient field, proving reducedness. The already proved
integrality of every field fiber supplies zero-dimensionality.
These statements concern every original base prime, not only the
closed-point residue field of the henselization.

This supplies geometric reducedness of the actual henselization map.
It does not assert regularity or an approximation property of its
completion map.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

private theorem fieldResidue_isAlgClosed
    (K : Type u) [Field K] [IsAlgClosed K] :
    IsAlgClosed (IsLocalRing.ResidueField K) :=
  IsAlgClosed.of_ringEquiv K (IsLocalRing.ResidueField K)
    (RingEquiv.ofBijective (IsLocalRing.residue K)
      ⟨RingHom.injective _, IsLocalRing.residue_surjective⟩)

/-- Every localization of an actual geometric fiber is its original
algebraically closed coefficient field, hence the geometric fiber is reduced. -/
theorem geometricStalk_tensor_isReduced_of_isAlgClosed
    {R Ω K : Type u} [CommRing R] [Field Ω] [Field K]
    [Algebra R K] [IsAlgClosed K] (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    IsReduced (K ⊗[R] H) := by
  intro H actualStructureAlgebra
  have : IsAlgClosed (IsLocalRing.ResidueField K) := fieldResidue_isAlgClosed K
  apply isReduced_ofLocalizationMaximal (K ⊗[R] H)
  intro q hq
  have : q.IsPrime := hq.isPrime
  have : q.LiesOver (IsLocalRing.maximalIdeal K) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  let e : K ≃+* Localization.AtPrime q :=
    RingEquiv.ofBijective (algebraMap K (Localization.AtPrime q))
      (geometricStalk_tensor_localizationAtPrime_bijective φ q)
  exact isReduced_of_injective e.symm e.symm.injective

/-- The existing integrality theorem makes every prime in any actual
field fiber maximal; algebraic closedness of the field is unnecessary. -/
theorem geometricStalk_tensor_krullDimLE_zero
    {R Ω K : Type u} [CommRing R] [Field Ω] [Field K]
    [Algebra R K] (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    Ring.KrullDimLE 0 (K ⊗[R] H) := by
  intro H actualStructureAlgebra
  have : Algebra.IsIntegral K (K ⊗[R] H) := geometricStalk_tensor_isIntegral φ K
  apply Ring.KrullDimLE.mk₀
  intro q hq
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under q
    (Ideal.isMaximal_of_isPrime (q.under K))

/-- The original structure map to the actual geometric stalk has reduced
geometric fibers at every original base prime. -/
theorem geometricStalkStructureMap_isGeometricallyReduced
    {R Ω : Type u} [CommRing R] [Field Ω] (φ : R →+* Ω) :
    let H := geometricStalk (Spec.map (CommRingCat.ofHom φ))
    let : Algebra R H := (geometricStalkStructureMap φ).toAlgebra
    Algebra.IsGeometricallyReduced R H := by
  intro H actualStructureAlgebra
  constructor
  intro p hp
  exact geometricStalk_tensor_isReduced_of_isAlgClosed
    (K := AlgebraicClosure p.ResidueField) φ

end EtaleFundamentalGroups.StrictHenselian
