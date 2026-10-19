/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# The actual standard cover of a projective-space base change

The inverse of the canonical projective-space base-change isomorphism
takes a standard coordinate open to the preimage of the original
coordinate open under the first projection. The two ordered affine
covers therefore agree, with their original ordered index type.

This identifies the cover used by the native Serre comparison with
the first-projection cover used by the existing Rees coefficient maps.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "Y" => pullback (π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A)))
local notation "p" => pullback.fst (π R n) (Spec.map (CommRingCat.ofHom (algebraMap R A)))

private theorem firstProjection_isAffineHom : IsAffineHom p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{u})
    (self := isAffineHom_isStableUnderBaseChange)
    (IsPullback.of_hasPullback (π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))).flip
    (isAffineHom_of_isAffine (Spec.map (CommRingCat.ofHom (algebraMap R A))))

attribute [local instance] firstProjection_isAffineHom

/-- The actual inverse base-change isomorphism and first projection
give the same preimage of each corresponding coordinate chart. -/
theorem baseChangeIso_inv_preimage_basicOpen_X (i : Fin (n + 1)) :
    (isPullback_map R A n).isoPullback.inv ⁻¹ᵁ Proj.basicOpen 𝒜A (MvPolynomial.X i) =
      p ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i) := by
  let e : Proj 𝒜A ≅ Y := (isPullback_map R A n).isoPullback
  calc
    e.inv ⁻¹ᵁ Proj.basicOpen 𝒜A (MvPolynomial.X i) =
        e.inv ⁻¹ᵁ (map R A n ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i)) :=
      congrArg (fun U : (Proj 𝒜A).Opens => e.inv ⁻¹ᵁ U)
        (map_preimage_basicOpen_X R A n i).symm
    _ = (e.inv ≫ map R A n) ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i) :=
      (Scheme.Hom.comp_preimage e.inv (map R A n) _).symm
    _ = p ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i) :=
      congrArg (fun h : Y ⟶ Proj 𝒜R => h ⁻¹ᵁ Proj.basicOpen 𝒜R (MvPolynomial.X i))
        (isPullback_map R A n).isoPullback_inv_fst

/-- The coordinate cover transported through the scheme isomorphism
is precisely the cover obtained from the original first projection. -/
theorem stdCoverPullback_baseChangeIso_inv :
    stdCoverPullback (isPullback_map R A n).isoPullback.inv = stdCoverPullback p := by
  dsimp only [stdCoverPullback]
  congr 1
  funext i
  exact baseChangeIso_inv_preimage_basicOpen_X R A n i.down

end AlgebraicGeometry.ProjSpace
