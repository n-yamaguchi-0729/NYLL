/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.UnitFractionEvaluation
import Nyll.SchemeTheory.ProjectiveSpace.UnitFractionSections
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Cech.ModulePresheafCechFiniteUnitClosedImmersionProj
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechGradedModule
import Nyll.SchemeTheory.Cohomology.Cech.ProjSpaceCechShiftedFractions
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
import Mathlib.GroupTheory.MonoidLocalization.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Defs
import Mathlib.Tactic.Ring

/-!
# Actual chart coefficients of shifted homogeneous fractions

Dividing by a chosen coordinate to the twist degree identifies shifted
homogeneous fractions with actual regular functions. This equivalence
commutes with restriction. Changing the coordinate gives precisely the
powered transition function of the native twisting sheaf; the identity
is checked in the ordinary localization at every projective point.
-/

noncomputable section

universe u

open CategoryTheory HomogeneousLocalization
open scoped BigOperators

namespace AlgebraicGeometry.ProjSpace

open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
open ProjSpaceCech Scheme.Modules.GlueOfCocycle

attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Actual regular chart coefficients of shifted homogeneous fractions,
using exactly the scalar action from the original structure morphism. -/
def twistingFractionCoefficientEquiv (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I) :
    GradedModule.sec (GradedModule.FD R n d) I ≃ₗ[R]
      (OModulePresheaf.unit ((𝟙 (Proj 𝒜)) ≫ π R n)).obj
        (coordinateIntersection R n I) :=
  (GradedModule.coordinateShiftEquiv (GradedModule.free R n) d i hi).trans
    (unitFreeFractionEquiv R n I ⟨i, hi⟩)

theorem twistingFractionCoefficientEquiv_apply (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n d) I) :
    twistingFractionCoefficientEquiv R n d i hi z =
      unitFreeFractionEquiv R n I ⟨i, hi⟩
        (GradedModule.coordinateShiftEquiv (GradedModule.free R n) d i hi z) := rfl

/-- Choosing the same coordinate before and after further localization
gives the original structure-sheaf restriction on actual coefficients. -/
theorem twistingFractionCoefficientEquiv_restrict (d : ℕ)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (i : Fin (n + 1)) (hi : i ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n d) I) :
    twistingFractionCoefficientEquiv R n d i (hIJ hi)
        (GradedModule.secIncl _ hIJ z) =
      (OModulePresheaf.unit ((𝟙 (Proj 𝒜)) ≫ π R n)).res
        (by
          change (𝟙 (Proj 𝒜)) ⁻¹ᵁ coordinateIntersection R n J ≤
            (𝟙 (Proj 𝒜)) ⁻¹ᵁ coordinateIntersection R n I
          rw [← ClosedImmCech.finsetInf_basicOpen (𝟙 (Proj 𝒜)),
            ← ClosedImmCech.finsetInf_basicOpen (𝟙 (Proj 𝒜))]
          exact biInf_mono hIJ)
        (twistingFractionCoefficientEquiv R n d i hi z) := by
  rw [twistingFractionCoefficientEquiv_apply, twistingFractionCoefficientEquiv_apply,
    GradedModule.coordinateShiftEquiv_restrict]
  exact unitFreeFractionEquiv_restrict R n hIJ ⟨i, hi⟩
    (GradedModule.coordinateShiftEquiv (GradedModule.free R n) d i hi z)

private theorem coordinateMonomial_add_single
    (a : Fin (n + 1) → ℕ) (i : Fin (n + 1)) (d : ℕ) :
    (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^
        (a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) i d) j) =
      (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^ a j) *
        (MvPolynomial.X i) ^ d := by
  have hs : (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) R) ^
      Pi.single (M := fun _ : Fin (n + 1) => ℕ) i d j) = (MvPolynomial.X i) ^ d := by
    rw [Finset.prod_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      rw [Pi.single_eq_of_ne (M := fun _ : Fin (n + 1) => ℕ) hji d, pow_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, hs]

private theorem coordinate_fraction_eq
    (S : Submonoid (MvPolynomial (Fin (n + 1)) R))
    (a : Fin (n + 1) → ℕ) (p : MvPolynomial (Fin (n + 1)) R)
    (d : ℕ) (i j : Fin (n + 1))
    (hi : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∈ S)
    (hdi : (∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^
      (a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) i d) k) ∈ S)
    (hdj : (∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^
      (a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) j d) k) ∈ S) :
    Localization.mk (S := S) p
        ⟨∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^
          (a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) i d) k, hdi⟩ =
      (Localization.mk (S := S) (MvPolynomial.X j)
        ⟨(MvPolynomial.X i) ^ 1, pow_mem hi 1⟩) ^ d *
        Localization.mk (S := S) p
          ⟨∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^
            (a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) j d) k, hdj⟩ := by
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, SubmonoidClass.coe_pow,
    pow_one, one_mul, coordinateMonomial_add_single]
  ring

/-- Changing the coordinate produces the actual transition function
of `O(d)` on the original coordinate intersection. -/
theorem twistingFractionCoefficientEquiv_transition (d : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) (hj : j ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n d) I) :
    (show Γ(Proj 𝒜, coordinateIntersection R n I) from
      twistingFractionCoefficientEquiv R n d i hi z) =
      rO (coordinateIntersection_le_standardOpen R n hi)
          (coordinateRatioSection R n i j) ^ d *
        (show Γ(Proj 𝒜, coordinateIntersection R n I) from
          twistingFractionCoefficientEquiv R n d j hj z) := by
  obtain ⟨q, rfl⟩ := Quotient.exists_rep z
  let qi : GradedModule.Frac (GradedModule.free R n) I :=
    GradedModule.coordinateDenominatorFrac (GradedModule.free R n) d i hi q
  let qj : GradedModule.Frac (GradedModule.free R n) I :=
    GradedModule.coordinateDenominatorFrac (GradedModule.free R n) d j hj q
  let ci : Γ(Proj 𝒜, coordinateIntersection R n I) :=
    twistingFractionCoefficientEquiv R n d i hi (GradedModule.sec.mk _ I q)
  let cj : Γ(Proj 𝒜, coordinateIntersection R n I) :=
    twistingFractionCoefficientEquiv R n d j hj (GradedModule.sec.mk _ I q)
  let ui : Γ(Proj 𝒜, coordinateIntersection R n I) :=
    unitFreeFractionEquiv R n I ⟨i, hi⟩ (GradedModule.sec.mk _ I qi)
  let uj : Γ(Proj 𝒜, coordinateIntersection R n I) :=
    unitFreeFractionEquiv R n I ⟨j, hj⟩ (GradedModule.sec.mk _ I qj)
  have hci : ci = ui := congrArg (unitFreeFractionEquiv R n I ⟨i, hi⟩)
    (GradedModule.coordinateShiftEquiv_apply_mk (GradedModule.free R n) d i hi q)
  have hcj : cj = uj := congrArg (unitFreeFractionEquiv R n I ⟨j, hj⟩)
    (GradedModule.coordinateShiftEquiv_apply_mk (GradedModule.free R n) d j hj q)
  change ci = rO (coordinateIntersection_le_standardOpen R n hi)
    (coordinateRatioSection R n i j) ^ d * cj
  rw [hci, hcj]
  apply Subtype.ext
  funext x
  let P : ProjectiveSpectrum 𝒜 := x.val
  have : P.asHomogeneousIdeal.toIdeal.IsPrime := P.isPrime
  have hxi : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∈
      P.asHomogeneousIdeal.toIdeal.primeCompl :=
    coordinateIntersection_le_standardOpen R n hi x.property
  let vi : HomogeneousLocalization 𝒜 P.asHomogeneousIdeal.toIdeal.primeCompl := ui.val x
  let vj : HomogeneousLocalization 𝒜 P.asHomogeneousIdeal.toIdeal.primeCompl := uj.val x
  let vr : HomogeneousLocalization 𝒜 P.asHomogeneousIdeal.toIdeal.primeCompl :=
    (rO (coordinateIntersection_le_standardOpen R n hi)
      (coordinateRatioSection R n i j)).val x
  let p : MvPolynomial (Fin (n + 1)) R := q.num
  let deni : P.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^ qi.denExp k,
      coordinateMonomial_mem_of_supported R n _ I qi.denExp qi.hden
        (fun k hk => coordinateIntersection_le_standardOpen R n (i := k) hk x.property)⟩
  let denj : P.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^ qj.denExp k,
      coordinateMonomial_mem_of_supported R n _ I qj.denExp qj.hden
        (fun k hk => coordinateIntersection_le_standardOpen R n (i := k) hk x.property)⟩
  have hvi : vi.val = Localization.mk (S := P.asHomogeneousIdeal.toIdeal.primeCompl)
      p deni := unitFreeFractionEquiv_apply_mk_val R n I ⟨i, hi⟩ qi x
  have hvj : vj.val = Localization.mk (S := P.asHomogeneousIdeal.toIdeal.primeCompl)
      p denj := unitFreeFractionEquiv_apply_mk_val R n I ⟨j, hj⟩ qj x
  have hratio : vr.val =
      Localization.mk (S := P.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.X j)
        ⟨(MvPolynomial.X i) ^ 1, pow_mem hxi 1⟩ := rfl
  apply HomogeneousLocalization.val_injective
  change vi.val = (vr ^ d * vj).val
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, hvi, hvj, hratio]
  exact coordinate_fraction_eq R n P.asHomogeneousIdeal.toIdeal.primeCompl
    q.denExp p d i j hxi deni.property denj.property

end AlgebraicGeometry.ProjSpace
