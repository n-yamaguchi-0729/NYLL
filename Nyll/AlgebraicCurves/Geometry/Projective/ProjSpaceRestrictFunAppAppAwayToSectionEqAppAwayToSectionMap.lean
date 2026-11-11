/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Nyll.AlgebraicCurves.Geometry.Projective.ChartSectionsBaseChange
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.Scheme
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.Cover
public import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum

/-!
# Proj Space restrict Fun app app away To Section eq app away To Section map
-/

@[expose] public section

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

open HomogeneousLocalization

namespace RM9Sol

section Setup

variable {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
  (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
  (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
  (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B))
  (e : Z' ⟶ Z)

local notation "𝒜A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A
local notation "𝒜B" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B

theorem X_eq_mvMapGraded_mul_one (i : Fin (n + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) B) = (ProjSpace.mvMapGraded A B n)
      (MvPolynomial.X i) * 1 :=
  ProjSpace.ChartSectionsBaseChange.X_eq_mvMapGraded_mul_one (A := A) B i

theorem one_mem_zero : (1 : MvPolynomial (Fin (n + 1)) B) ∈ (MvPolynomial.homogeneousSubmodule (Fin
  (n + 1)) B) 0 :=
  ProjSpace.ChartSectionsBaseChange.one_mem_zero (n := n) B

/-- The coordinate localization map induced by the coefficient base change. -/
noncomputable def toB (i : Fin (n + 1)) : Away 𝒜A (MvPolynomial.X i) →+* Away 𝒜B (MvPolynomial.X i)
  :=
  ProjSpace.ChartSectionsBaseChange.toB (A := A) B i

theorem toB_ratio (i j : Fin (n + 1)) : toB (A := A) B i (ProjSpace.ratio A n i j) =
  ProjSpace.ratio B n i j :=
  ProjSpace.ChartSectionsBaseChange.toB_ratio (A := A) B i j

theorem restrictFun_app_pullAway (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (i : Fin (n + 1))
    (a : Away 𝒜A (MvPolynomial.X i)) {W' : Z'.Opens}
    (h₁ : W' ≤ e ⁻¹ᵁ ProjSpace.pullbackChart ι i) (h₂ : W' ≤ ProjSpace.pullbackChart ι' i) :
    ProjSpace.restrictFun h₁ ((e.app (ProjSpace.pullbackChart ι i)).hom
        ((ι.app (Proj.basicOpen 𝒜A (MvPolynomial.X i))).hom ((Proj.awayToSection 𝒜A (MvPolynomial.X
          i)).hom a)))
      = ProjSpace.restrictFun h₂ ((ι'.app (Proj.basicOpen 𝒜B (MvPolynomial.X i))).hom
          ((Proj.awayToSection 𝒜B (MvPolynomial.X i)).hom (toB (A := A) B i a))) :=
  ProjSpace.ChartSectionsBaseChange.restrictFun_app_pullAway ι B ι' e hcomp i a h₁ h₂

theorem toB_mkDeg (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF :
  F.IsHomogeneous d) :
    toB (A := A) B i (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ } : Away 𝒜A (MvPolynomial.X i)) =
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨MvPolynomial.map (algebraMap A B) F,
            (MvPolynomial.mem_homogeneousSubmodule d _).mpr (hF.map (algebraMap A B))⟩
          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
            (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ } : Away 𝒜B (MvPolynomial.X i)) :=
  ProjSpace.ChartSectionsBaseChange.toB_mkDeg (A := A) B i d F hF

end Setup

end RM9Sol

theorem
  _root_.AlgebraicGeometry.ProjSpace.restrictFun_app_app_awayToSection_eq_app_awayToSection_map
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B))
    (e : Z' ⟶ Z) (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n)
    (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d) (i : Fin (n + 1))
    (h : ι' ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (MvPolynomial.X
      i) ≤
      e ⁻¹ᵁ (ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
        (MvPolynomial.X i))) :
    ProjSpace.restrictFun h
        ((e.app (ι ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
          (MvPolynomial.X i)))
          ((ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
            (MvPolynomial.X i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) =
      ((ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B) (MvPolynomial.X
        i)))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)
                (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨MvPolynomial.map (algebraMap A B) F,
                      (MvPolynomial.mem_homogeneousSubmodule d (MvPolynomial.map (algebraMap A B)
                      F)).mpr (hF.map (algebraMap A B))⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) := by
  have key := RM9Sol.restrictFun_app_pullAway ι B ι' e hcomp i
    (HomogeneousLocalization.mk
      { deg := d
        num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
        den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
          (MvPolynomial.isHomogeneous_X_pow i d)⟩
        den_mem := ⟨d, rfl⟩ }) h (le_refl (ProjSpace.pullbackChart ι' i))
  rw [RM9Sol.toB_mkDeg B i d F hF] at key
  exact key.trans (ProjSpace.restrictFun_refl _)
end ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
