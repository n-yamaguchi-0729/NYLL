/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafCocycle
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafChartRestriction
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafHomogeneousNumerators
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafHomogeneousRatios
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPolynomialSections
import Nyll.SchemeTheory.Modules.Descent.GlueOfCocycle
import Nyll.SchemeTheory.Modules.Frames.Frames
import Nyll.SchemeTheory.Modules.Sections.SectionsGluing
import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.RingTheory.Polynomial.HomogeneousCoordinateDivision
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Choose

/-!
# Recovering a homogeneous polynomial from an actual twisting-sheaf section

Coordinate frames express an actual global `O(d)` section as compatible
regular functions on standard charts. A common numerator degree turns
their compatibility into polynomial cross multiplication. Coordinate
division removes the excess denominator and yields a degree-`d`
homogeneous polynomial. Thus the native polynomial-section map is
bijective over every coefficient ring, including in projective dimension zero.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev res {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    Γ(M, U) →+ Γ(M, V) := (M.presheaf.map (homOfLE h).op).hom

private theorem res_res {X : Scheme.{u}} (M : X.Modules) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(M, U)) :
    res M hWV (res M hVU s) = res M (hWV.trans hVU) s := by
  change (M.presheaf.map (homOfLE hVU).op ≫
    M.presheaf.map (homOfLE hWV).op).hom s = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

private theorem res_smul {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (r : Γ(X, U)) (s : Γ(M, U)) :
    res M h (r • s) = rO h r • res M h s := M.map_smul (homOfLE h) r s

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Actual compatibility on an overlap gives a polynomial cross-multiplication
equation for numerators of the same degree. -/
theorem homogeneous_cross_mul_of_overlap {d N : ℕ} (hdN : d ≤ N)
    (p q : 𝒜 N) (i j : Fin (n + 1))
    (h : rO (inf_le_left : standardOpen R n i ⊓ standardOpen R n j ≤ standardOpen R n i)
        (homogeneousRatioSection R n N p i) =
      rO (inf_le_left : standardOpen R n i ⊓ standardOpen R n j ≤ standardOpen R n i)
          (coordinateRatioSection R n i j) ^ d *
        rO inf_le_right (homogeneousRatioSection R n N q j)) :
    p.val * MvPolynomial.X j ^ (N - d) = q.val * MvPolynomial.X i ^ (N - d) := by
  let k : ℕ := N - d
  have hk : k + d = N := Nat.sub_add_cancel hdN
  have hc : coordinateRatioSection R n i j ^ k * homogeneousRatioSection R n N p i =
      homogeneousRatioSection R n N q i := by
    apply standardOpen_overlap_restrict_injective R n i j
    rw [map_mul, map_pow, h, ← mul_assoc, ← pow_add, hk]
    exact (homogeneousRatioSection_transition R n N q i j inf_le_left inf_le_right).symm
  let P : 𝒜 (N + k) := homogeneousMulCoordinatePow R n N p j k
  let Q : 𝒜 (N + k) := homogeneousMulCoordinatePow R n N q i k
  have hQ : homogeneousRatioSection R n (N + k) Q i =
      homogeneousRatioSection R n N q i :=
    homogeneousRatioSection_eq_of_mul_coordinate_pow R n (Nat.le_add_right N k) q Q i
      (by simp only [Q, homogeneousMulCoordinatePow, Nat.add_sub_cancel_left])
  have hP : homogeneousRatioSection R n (N + k) P i =
      homogeneousRatioSection R n N q i := by
    rw [homogeneousRatioSection_mulCoordinatePow, mul_comm]
    exact hc
  exact congrArg Subtype.val
    (homogeneousRatioSection_injective R n (N + k) i (hP.trans hQ.symm))

/-- The coefficients in the actual coordinate frames have precisely the
powered transition function of the twisting sheaf. -/
theorem exists_twistingSection_coefficients (d : ℕ)
    (z : Γ((twistingSheaf R n).tensorPow d, ⊤)) :
    ∃ c : ∀ i : Fin (n + 1), Γ(Proj 𝒜, standardOpen R n i),
      (∀ i : Fin (n + 1), c i • res ((twistingSheaf R n).tensorPow d)
          (le_top : standardOpen R n i ≤ ⊤)
          (tensorPowSection (twistingCoordinateSection R n i) d) =
        res ((twistingSheaf R n).tensorPow d) (le_top : standardOpen R n i ≤ ⊤) z) ∧
      ∀ i j : Fin (n + 1),
        rO (inf_le_left : standardOpen R n i ⊓ standardOpen R n j ≤ standardOpen R n i)
            (c i) =
          rO (inf_le_left : standardOpen R n i ⊓ standardOpen R n j ≤ standardOpen R n i)
              (coordinateRatioSection R n i j) ^ d *
            rO (inf_le_right : standardOpen R n i ⊓ standardOpen R n j ≤ standardOpen R n j)
              (c j) := by
  classical
  let M : (Proj 𝒜).Modules := (twistingSheaf R n).tensorPow d
  choose c hc using fun i : Fin (n + 1) =>
    (((isFrameOn_twistingCoordinateSection R n i).tensorPowSection_monoidalV2 d)
      (le_top : standardOpen R n i ≤ ⊤) le_rfl).2
        (res M (le_top : standardOpen R n i ≤ ⊤) z)
  refine ⟨c, hc, fun i j => ?_⟩
  let V : (Proj 𝒜).Opens := standardOpen R n i ⊓ standardOpen R n j
  have hi := congrArg (res M (inf_le_left : V ≤ standardOpen R n i)) (hc i)
  have hj := congrArg (res M (inf_le_right : V ≤ standardOpen R n j)) (hc j)
  rw [res_smul, res_res, res_res] at hi hj
  have hframe := congrArg (res M (inf_le_left : V ≤ standardOpen R n i))
    (coordinateRatioSection_pow_smul_twistingCoordinateSection R n d i j)
  change res M (inf_le_left : V ≤ standardOpen R n i)
      (coordinateRatioSection R n i j ^ d • res M (le_top : standardOpen R n i ≤ ⊤)
        (tensorPowSection (twistingCoordinateSection R n i) d)) =
    res M (inf_le_left : V ≤ standardOpen R n i)
      (res M (le_top : standardOpen R n i ≤ ⊤)
      (tensorPowSection (twistingCoordinateSection R n j) d)) at hframe
  rw [res_smul, map_pow, res_res, res_res] at hframe
  apply (((isFrameOn_twistingCoordinateSection R n i).tensorPowSection_monoidalV2 d)
    (le_top : V ≤ ⊤) inf_le_left).1
  calc
    rO (inf_le_left : V ≤ standardOpen R n i) (c i) • res M (le_top : V ≤ ⊤)
        (tensorPowSection (twistingCoordinateSection R n i) d) =
      res M (le_top : V ≤ ⊤) z := hi
    _ = rO (inf_le_right : V ≤ standardOpen R n j) (c j) • res M (le_top : V ≤ ⊤)
        (tensorPowSection (twistingCoordinateSection R n j) d) := hj.symm
    _ = (rO (inf_le_left : V ≤ standardOpen R n i) (coordinateRatioSection R n i j) ^ d *
        rO (inf_le_right : V ≤ standardOpen R n j) (c j)) •
        res M (le_top : V ≤ ⊤) (tensorPowSection (twistingCoordinateSection R n i) d) := by
      rw [← hframe, ← mul_smul, mul_comm]

/-- Every actual global section of a nonnegative twisting power is represented
by a homogeneous polynomial of the corresponding degree. -/
theorem polynomialTwistingSection_surjective (d : ℕ) :
    Function.Surjective (polynomialTwistingSection R n d) := by
  intro z
  obtain ⟨c, hc, hcompat⟩ := exists_twistingSection_coefficients R n d z
  obtain ⟨N, hdN, p, hp⟩ := exists_common_homogeneousRatioSection R n c d
  have hcross (i j : Fin (n + 1)) :
      (p i).val * MvPolynomial.X j ^ (N - d) =
        (p j).val * MvPolynomial.X i ^ (N - d) := by
    apply homogeneous_cross_mul_of_overlap R n hdN (p i) (p j) i j
    rw [hp i, hp j]
    exact hcompat i j
  have hhom : (p 0).val.IsHomogeneous (d + (N - d)) := by
    rw [Nat.add_sub_of_le hdN]
    change (p 0).val ∈ 𝒜 N
    exact (p 0).property
  have hdiv : (MvPolynomial.X (0 : Fin (n + 1))) ^ (N - d) ∣ (p 0).val := by
    cases n with
    | zero =>
      exact MvPolynomial.IsHomogeneous.X_pow_dvd_of_subsingleton (σ := Fin 1) hhom 0
    | succ n =>
      apply MvPolynomial.X_pow_dvd_of_cross_mul (Fin.zero_ne_one' (n := n + 1)) (N - d)
        (q := (p 1).val)
      calc
        MvPolynomial.X 0 ^ (N - d) * (p 1).val =
            (p 1).val * MvPolynomial.X 0 ^ (N - d) := mul_comm _ _
        _ = (p 0).val * MvPolynomial.X 1 ^ (N - d) := (hcross 0 1).symm
        _ = MvPolynomial.X 1 ^ (N - d) * (p 0).val := mul_comm _ _
  let q : 𝒜 d := ⟨(p 0).val.divMonomial (Finsupp.single 0 (N - d)),
    hhom.divMonomial_single 0⟩
  have hq : MvPolynomial.X 0 ^ (N - d) * q.val = (p 0).val :=
    MvPolynomial.X_pow_mul_divMonomial_single 0 (N - d) hdiv
  have hpi (i : Fin (n + 1)) : (p i).val = q.val * MvPolynomial.X i ^ (N - d) := by
    apply (MvPolynomial.isRegular_X_pow (R := R) (n := (0 : Fin (n + 1))) (N - d)).left
    calc
      MvPolynomial.X 0 ^ (N - d) * (p i).val =
          (p i).val * MvPolynomial.X 0 ^ (N - d) := mul_comm _ _
      _ = (p 0).val * MvPolynomial.X i ^ (N - d) := (hcross 0 i).symm
      _ = (MvPolynomial.X 0 ^ (N - d) * q.val) * MvPolynomial.X i ^ (N - d) := by rw [hq]
      _ = MvPolynomial.X 0 ^ (N - d) * (q.val * MvPolynomial.X i ^ (N - d)) :=
        mul_assoc _ _ _
  refine ⟨q, ?_⟩
  apply (eq_of_forall_map_homOfLE_eq_and_exists_of_compatible
    ((twistingSheaf R n).tensorPow d) (twistingCover R n) ⊤
    (fun _ => le_top) (iSup_twistingCover R n).ge).1
  intro i
  rw [polynomialTwistingSection_restrict]
  change homogeneousRatioSection R n d q i.down •
      res ((twistingSheaf R n).tensorPow d) (le_top : standardOpen R n i.down ≤ ⊤)
        (tensorPowSection (twistingCoordinateSection R n i.down) d) =
    res ((twistingSheaf R n).tensorPow d) (le_top : standardOpen R n i.down ≤ ⊤) z
  rw [← homogeneousRatioSection_eq_of_mul_coordinate_pow R n hdN q (p i.down) i.down
    (hpi i.down), hp i.down]
  exact hc i.down

/-- The actual homogeneous-polynomial/global-section comparison, including its
addition law, with the inverse obtained by coordinate denominator removal. -/
def polynomialTwistingSectionAddEquiv (d : ℕ) :
    𝒜 d ≃+ Γ((twistingSheaf R n).tensorPow d, ⊤) :=
  AddEquiv.ofBijective (polynomialTwistingSectionAddHom R n d)
    ⟨polynomialTwistingSection_injective R n d, polynomialTwistingSection_surjective R n d⟩

end AlgebraicGeometry.ProjSpace
