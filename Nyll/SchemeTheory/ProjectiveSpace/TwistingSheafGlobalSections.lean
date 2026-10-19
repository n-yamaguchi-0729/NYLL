/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafBaseScalars
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafHomogeneousRatios
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialSections
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialDescent
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Homogeneous polynomials and actual global twisting-sheaf modules

The homogeneous-polynomial section comparison respects the original
base action induced by the projective structure morphism. Together
with actual coordinate denominator removal, this gives an `R`-linear
equivalence with the original global section module used by the native
sheaf-to-Čech construction.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The original structural scalar acts on the glued polynomial section
by scaling its homogeneous numerator. -/
theorem polynomialTwistingSection_smul (d : ℕ) (r : R) (p : 𝒜 d) :
    polynomialTwistingSection R n d (r • p) =
      ((π R n).constToPresheaf.app (op ⊤)).hom r • polynomialTwistingSection R n d p := by
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    ((twistingSheaf R n).tensorPow d) (twistingCover R n) ⊤
    (fun _ => le_top) (iSup_twistingCover R n).ge).1
  intro i
  have hcoef : (Proj 𝒜).presheaf.map
        (homOfLE (le_top : standardOpen R n i.down ≤ ⊤)).op
        (((π R n).constToPresheaf.app (op ⊤)).hom r) =
      ((π R n).constToPresheaf.app (op (standardOpen R n i.down))).hom r :=
    (congrArg (fun f : CommRingCat.of R ⟶ Γ(Proj 𝒜, standardOpen R n i.down) => f r)
      ((π R n).constToPresheaf.naturality
        (homOfLE (le_top : standardOpen R n i.down ≤ ⊤)).op)).symm
  rw [((twistingSheaf R n).tensorPow d).map_smul, hcoef,
    polynomialTwistingSection_restrict, polynomialTwistingSection_restrict]
  change homogeneousRatioSection R n d (r • p) i.down •
      ((twistingSheaf R n).tensorPow d).presheaf.map
        (homOfLE (le_top : standardOpen R n i.down ≤ ⊤)).op
        (tensorPowSection (twistingCoordinateSection R n i.down) d) =
    ((π R n).constToPresheaf.app (op (standardOpen R n i.down))).hom r •
      (homogeneousRatioSection R n d p i.down •
        ((twistingSheaf R n).tensorPow d).presheaf.map
          (homOfLE (le_top : standardOpen R n i.down ≤ ⊤)).op
          (tensorPowSection (twistingCoordinateSection R n i.down) d))
  rw [homogeneousRatioSection_smul, mul_smul]

/-- The native polynomial-section map, linear for the original base action. -/
def polynomialTwistingSectionLinearMap (d : ℕ) :
    𝒜 d →ₗ[R] sectionModuleOverBase (π R n) ((twistingSheaf R n).tensorPow d) ⊤ where
  toFun p := polynomialTwistingSection R n d p
  map_add' p q := polynomialTwistingSection_add R n d p q
  map_smul' r p := polynomialTwistingSection_smul R n d r p

/-- The actual homogeneous degree-`d` piece is the global section module
of `O(d)`, with its original structural `R`-module action. -/
def polynomialTwistingSectionLinearEquiv (d : ℕ) :
    𝒜 d ≃ₗ[R] sectionModuleOverBase (π R n) ((twistingSheaf R n).tensorPow d) ⊤ :=
  LinearEquiv.ofBijective (polynomialTwistingSectionLinearMap R n d)
    ⟨polynomialTwistingSection_injective R n d, polynomialTwistingSection_surjective R n d⟩

/-- The linear equivalence evaluates to the original glued polynomial section. -/
theorem polynomialTwistingSectionLinearEquiv_apply (d : ℕ) (p : 𝒜 d) :
    polynomialTwistingSectionLinearEquiv R n d p = polynomialTwistingSection R n d p := rfl

/-- Polynomial recovery returns the original global section. -/
theorem polynomialTwistingSectionLinearEquiv_symm_apply (d : ℕ)
    (z : sectionModuleOverBase (π R n) ((twistingSheaf R n).tensorPow d) ⊤) :
    polynomialTwistingSection R n d ((polynomialTwistingSectionLinearEquiv R n d).symm z) = z :=
  (polynomialTwistingSectionLinearEquiv R n d).apply_symm_apply z

end AlgebraicGeometry.ProjSpace
