/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestriction
import Nyll.SchemeTheory.RingTheory.Localization.ArtinianUnitLifting
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Surjectivity of the actual finite-algebra unit restriction -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct

namespace SchemeTheory.Affine.UnitNormPolynomial

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (bA : Basis ι R A) (bB : Basis κ R B) (f : A →ₐ[R] B)
  (hf : Function.Surjective f)

omit [DecidableEq ι] [Fintype ι] in
include bA hf in
/-- Restriction lifts units after every field-valued scalar extension; finite
algebras may be nonreduced and the quotient kernel need not be nilpotent. -/
theorem tensorUnitsRestriction_surjective [Finite ι] {L : Type u} [Field L] [Algebra R L] :
    Function.Surjective (Units.map
      (Algebra.TensorProduct.map (AlgHom.id R L) f).toRingHom.toMonoidHom) := by
  have : Module.Finite R A := Module.Finite.of_basis bA
  have : IsArtinianRing (L ⊗[R] A) := isArtinian_of_tower L inferInstance
  exact SchemeTheory.artinian_unitsMap_surjective _
    (Algebra.TensorProduct.map_surjective (AlgHom.id R L) f Function.surjective_id hf)

include hf in
/-- Every residue-field point of the target norm open lifts to the source norm
open, proving scheme-theoretic surjectivity of the actual restriction morphism. -/
theorem surjective_restrictionMap : Surjective (restrictionMap bA bB f) := by
  constructor
  intro y
  let L := (unitOpen bB).residueField y
  obtain ⟨q, hq⟩ := Spec.map_surjective ((unitOpen bB).fromSpecResidueField y)
  let : Algebra R L := (q.hom.comp (algebraMap R (CoordinateRing bB))).toAlgebra
  let qB : CoordinateRing bB →ₐ[R] L :=
    { q.hom with commutes' := fun _ => rfl }
  obtain ⟨a, ha⟩ := tensorUnitsRestriction_surjective bA f hf (homEquivUnits bB qB)
  let qA : CoordinateRing bA →ₐ[R] L := (homEquivUnits bA).symm a
  have hqA : qA.comp (restrictionRingHom bA bB f) = qB := by
    apply (homEquivUnits bB).injective
    rw [restrictionRingHom_homEquiv]
    exact ((congrArg
      (Units.map (Algebra.TensorProduct.map (AlgHom.id R L) f).toRingHom.toMonoidHom)
      ((homEquivUnits bA).apply_symm_apply a))).trans ha
  have hmap : Spec.map (CommRingCat.ofHom qA.toRingHom) ≫ restrictionMap bA bB f =
      (unitOpen bB).fromSpecResidueField y := by
    rw [restrictionMap, ← Spec.map_comp, ← hq]
    congr 1
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom hqA
  let z : Spec ((unitOpen bB).residueField y) := IsLocalRing.closedPoint L
  refine ⟨Spec.map (CommRingCat.ofHom qA.toRingHom) z, ?_⟩
  exact (congrArg (fun k : Spec ((unitOpen bB).residueField y) ⟶ unitOpen bB => k z)
    hmap).trans (Scheme.fromSpecResidueField_apply y z)

end SchemeTheory.Affine.UnitNormPolynomial
