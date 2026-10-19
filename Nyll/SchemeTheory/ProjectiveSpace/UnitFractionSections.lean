/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteUnitClosedImmersionProj
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafHomogeneousRatios
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Actual structure-sheaf sections as free homogeneous fractions

For the identity immersion of projective space, the homogeneous kernel
in the existing closed-immersion fraction model is zero. A polynomial
which vanishes on one coordinate chart is already zero, since that
coordinate is a non-zero-divisor over every coefficient ring.

The original map from free homogeneous fractions to regular functions
is therefore bijective on every nonempty coordinate intersection. Its
linear equivalence retains the original structural scalar action and
commutes with the actual restriction maps.
-/

noncomputable section

universe u

open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry.ProjSpace

open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
open ProjSpaceCech

-- The closed-immersion model disables these original fraction instances
-- after its implementation. Only their original owners are used here.
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem fractionMap_injective
    {R : Type u} [CommRing R] {n : ℕ} {D E : GradedModule R n}
    (φ : GradedModule.Hom D E) (hφ : Function.Injective φ.toLinearMap)
    (I : Finset (Fin (n + 1))) : Function.Injective (φ.secMap I) := by
  rintro ⟨x⟩ ⟨y⟩ hxy
  obtain ⟨c, hc, h⟩ := (GradedModule.sec_mk_eq E I).mp hxy
  apply (GradedModule.sec_mk_eq D I).mpr
  refine ⟨c, hc, hφ ?_⟩
  exact (φ.map_monMul (c + y.denExp) x.num).trans
    (h.trans (φ.map_monMul (c + x.denExp) y.num).symm)

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

private theorem testAt_id_eq (d : ℕ) (p : 𝒜 d) (i : Fin (n + 1)) :
    ClosedImmCech.testAt (𝟙 (Proj 𝒜)) d i p = homogeneousRatioSection R n d p i := by
  rw [ClosedImmCech.testAt, Scheme.Hom.id_app]
  rfl

/-- The actual homogeneous kernel defining the identity closed immersion
is zero, over an arbitrary coefficient ring. -/
theorem identityImmersion_homogeneousKernel_eq_bot :
    ClosedImmCech.J (𝟙 (Proj 𝒜)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  unfold ClosedImmCech.J
  apply iSup_le
  intro d
  rintro _ ⟨p, hp, rfl⟩
  have hchart := hp (0 : Fin (n + 1))
  rw [testAt_id_eq] at hchart
  have hzero : p = 0 := homogeneousRatioSection_injective R n d 0
    (hchart.trans (homogeneousRatioSection_zero R n d 0).symm)
  exact (Submodule.mem_bot R).mpr (congrArg Subtype.val hzero)

/-- The original free-fraction map is injective on every nonempty
coordinate intersection; its closed-immersion kernel has just been
proved to vanish. -/
theorem unitFreeFractionMap_injective
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Function.Injective (ClosedImmCech.freeSec (𝟙 (Proj 𝒜)) I hI) := by
  have hq : Function.Injective (ClosedImmCech.mkQHom (𝟙 (Proj 𝒜))).toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    exact (Submodule.ker_mkQ (ClosedImmCech.J (𝟙 (Proj 𝒜)))).trans
      (identityImmersion_homogeneousKernel_eq_bot R n)
  have hmap := fractionMap_injective (ClosedImmCech.mkQHom (𝟙 (Proj 𝒜))) hq I
  let f : GradedModule.sec (GradedModule.free R n) I →ₗ[R]
      (OModulePresheaf.unit ((𝟙 (Proj 𝒜)) ≫ π R n)).obj
        ((𝟙 (Proj 𝒜)) ⁻¹ᵁ Proj.basicOpen 𝒜
          (∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R))) :=
    ClosedImmCech.freeSec (𝟙 (Proj 𝒜)) I hI
  have hf : LinearMap.ker f = ⊥ := le_antisymm
    ((ClosedImmCech.freeSec_ker_le (𝟙 (Proj 𝒜)) I hI).trans
      (LinearMap.ker_eq_bot.mpr hmap).le) bot_le
  exact (LinearMap.ker_eq_bot (f := f)).mp hf

/-- The actual linear equivalence between free homogeneous fractions
and regular functions on a nonempty coordinate intersection. -/
def unitFreeFractionEquiv (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    GradedModule.sec (GradedModule.free R n) I ≃ₗ[R]
      (OModulePresheaf.unit ((𝟙 (Proj 𝒜)) ≫ π R n)).obj
        ((𝟙 (Proj 𝒜)) ⁻¹ᵁ Proj.basicOpen 𝒜
          (∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R))) :=
  LinearEquiv.ofBijective (ClosedImmCech.freeSec (𝟙 (Proj 𝒜)) I hI)
    ⟨unitFreeFractionMap_injective R n I hI,
      ClosedImmCech.freeSec_surjective (𝟙 (Proj 𝒜)) I hI⟩

theorem unitFreeFractionEquiv_apply
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty)
    (z : GradedModule.sec (GradedModule.free R n) I) :
    unitFreeFractionEquiv R n I hI z = ClosedImmCech.freeSec (𝟙 (Proj 𝒜)) I hI z := rfl

/-- Enlarging the set of inverted coordinates agrees with the original
structure-sheaf restriction, on each actual homogeneous fraction. -/
theorem unitFreeFractionEquiv_restrict
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) (hI : I.Nonempty)
    (z : GradedModule.sec (GradedModule.free R n) I) :
    unitFreeFractionEquiv R n J (hI.mono hIJ) (GradedModule.secIncl _ hIJ z) =
      (OModulePresheaf.unit ((𝟙 (Proj 𝒜)) ≫ π R n)).res
        (by
          rw [← ClosedImmCech.finsetInf_basicOpen (𝟙 (Proj 𝒜)),
            ← ClosedImmCech.finsetInf_basicOpen (𝟙 (Proj 𝒜))]
          exact biInf_mono hIJ)
        (unitFreeFractionEquiv R n I hI z) := by
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  exact ClosedImmCech.secAux_face (𝟙 (Proj 𝒜)) hIJ hI x

end AlgebraicGeometry.ProjSpace
