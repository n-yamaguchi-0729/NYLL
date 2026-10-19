/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.UnitFractionSections
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteUnitClosedImmersionProj
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Ring

/-!
# Pointwise evaluation of actual homogeneous fractions

The original closed-immersion construction pads separate coordinate
denominators to one power of their product. The polynomial identity
proved here removes that padding in the localization at each actual
projective point. Consequently the established linear equivalence to
regular functions evaluates to the original numerator divided by the
original coordinate monomial.
-/

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization
open scoped BigOperators

namespace AlgebraicGeometry.ProjSpace

open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
open ProjSpaceCech

attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The actual intersection of the specified projective coordinate charts. -/
abbrev coordinateIntersection (I : Finset (Fin (n + 1))) : (Proj 𝒜).Opens :=
  Proj.basicOpen 𝒜 (∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R))

theorem coordinateIntersection_le_standardOpen
    {I : Finset (Fin (n + 1))} {i : Fin (n + 1)} (hi : i ∈ I) :
    coordinateIntersection R n I ≤ standardOpen R n i := by
  change (𝟙 (Proj 𝒜)) ⁻¹ᵁ coordinateIntersection R n I ≤ standardOpen R n i
  rw [← ClosedImmCech.finsetInf_basicOpen (𝟙 (Proj 𝒜))]
  exact iInf_le_of_le i (iInf_le _ hi)

/-- A coordinate monomial supported on inverted coordinates belongs to
the original denominator submonoid. -/
theorem coordinateMonomial_mem_of_supported
    (S : Submonoid (MvPolynomial (Fin (n + 1)) R))
    (I : Finset (Fin (n + 1))) (a : Fin (n + 1) → ℕ)
    (ha : ∀ j ∉ I, a j = 0) (hI : ∀ j ∈ I, MvPolynomial.X j ∈ S) :
    (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^ a j) ∈ S := by
  apply prod_mem
  intro j _
  by_cases hj : j ∈ I
  · exact pow_mem (hI j hj) (a j)
  · rw [ha j hj, pow_zero]
    exact one_mem S

private theorem padding_mul_denominator
    (I : Finset (Fin (n + 1))) (a : Fin (n + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0) :
    (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^ ClosedImmCech.pad I a j) *
        (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^ a j) =
      (∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) ^ (∑ j, a j) := by
  have h : (∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) ^
      (∑ j, a j) * 1 =
      (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^
        (if j ∈ I then ∑ k, a k else 0)) * 1 :=
    (ClosedImmCech.prodXpow_eq_monMul (A := R) I (∑ j, a j)
      (1 : MvPolynomial (Fin (n + 1)) R)).trans
      (GradedModule.free_monMul_apply _ (1 : MvPolynomial (Fin (n + 1)) R))
  simp only [mul_one] at h
  calc
    _ = ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^
        (ClosedImmCech.pad I a j + a j) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun j _ => (pow_add _ _ _).symm)
    _ = ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^
        (if j ∈ I then ∑ k, a k else 0) :=
      Finset.prod_congr rfl (fun j _ =>
        congrArg (fun e : ℕ => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^ e)
          (ClosedImmCech.pad_add_supp I a ha j))
    _ = _ := h.symm

private theorem padded_fraction_eq
    (S : Submonoid (MvPolynomial (Fin (n + 1)) R))
    (I : Finset (Fin (n + 1))) (a : Fin (n + 1) → ℕ)
    (ha : ∀ j ∉ I, a j = 0) (hI : ∀ j ∈ I, MvPolynomial.X j ∈ S)
    (hprod : (∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) ∈ S)
    (p : MvPolynomial (Fin (n + 1)) R) :
    Localization.mk (S := S)
        (GradedModule.monMul (GradedModule.free R n) (ClosedImmCech.pad I a) p)
        ⟨(∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) ^ (∑ j, a j),
          pow_mem hprod _⟩ =
      Localization.mk (S := S) p
        ⟨∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^ a j,
          coordinateMonomial_mem_of_supported R n S I a ha hI⟩ := by
  calc
    _ = Localization.mk (S := S)
        ((∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^
          ClosedImmCech.pad I a j) * p)
        ⟨(∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) ^ (∑ j, a j),
          pow_mem hprod _⟩ :=
      congrArg (fun m : MvPolynomial (Fin (n + 1)) R => Localization.mk (S := S) m
        ⟨(∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) ^ (∑ j, a j),
          pow_mem hprod _⟩) (GradedModule.free_monMul_apply (ClosedImmCech.pad I a) p)
    _ = _ := by
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [Submonoid.coe_one, one_mul]
      calc
        _ = ((∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^
            ClosedImmCech.pad I a j) *
            (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^ a j)) * p := by ring
        _ = _ := congrArg (fun b : MvPolynomial (Fin (n + 1)) R => b * p)
          (padding_mul_denominator R n I a ha)

/-- At every actual projective point, the established function-section
equivalence has exactly the original numerator and coordinate denominator. -/
theorem unitFreeFractionEquiv_apply_mk_val
    (I : Finset (Fin (n + 1))) (hI : I.Nonempty)
    (y : GradedModule.Frac (GradedModule.free R n) I)
    (x : coordinateIntersection R n I) :
    let P : ProjectiveSpectrum 𝒜 := x.val
    let : P.asHomogeneousIdeal.toIdeal.IsPrime := P.isPrime
    ((unitFreeFractionEquiv R n I hI (GradedModule.sec.mk _ I y)).val x).val =
      Localization.mk (S := P.asHomogeneousIdeal.toIdeal.primeCompl) y.num
        ⟨∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^ y.denExp j,
          coordinateMonomial_mem_of_supported R n _ I y.denExp y.hden
            (fun j hj => coordinateIntersection_le_standardOpen R n (i := j) hj x.property)⟩ := by
  intro P hP
  have hprod : (∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) ∈
      P.asHomogeneousIdeal.toIdeal.primeCompl := x.property
  change Localization.mk (S := P.asHomogeneousIdeal.toIdeal.primeCompl)
      (GradedModule.monMul (GradedModule.free R n) (ClosedImmCech.pad I y.denExp) y.num)
      ⟨(∏ j ∈ I, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R)) ^
        (∑ j, y.denExp j), pow_mem hprod _⟩ = _
  exact padded_fraction_eq R n _ I y.denExp y.hden
    (fun j hj => coordinateIntersection_le_standardOpen R n (i := j) hj x.property) hprod y.num

end AlgebraicGeometry.ProjSpace
