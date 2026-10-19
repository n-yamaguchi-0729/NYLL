/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedSection
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealZeroSchemeIdealEqSpan
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.ZeroSchemeIdealCompEq
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.IEqZeroSchemeIdealNeZero
import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.InvertibleI

/-!
# Actual divisors of normalized sections

A section equal to one in the chosen modulus trivialization has zero scheme
disjoint from the full modulus. On a proper smooth geometric curve, a nonzero
such section cuts out an actual relative effective Cartier divisor, and its
canonical rigidification recovers the given line bundle.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

private theorem zeroSchemeIdeal_unit_identity (X : Scheme.{u}) :
    zeroSchemeIdeal (𝟙 (𝟙_ X.Modules)) = ⊤ := by
  apply Scheme.IdealSheafData.ext
  funext U
  have hid : Scheme.Modules.Hom.app (𝟙 (𝟙_ X.Modules)) ⊤ (toUnitSection ⊤ 1) =
      (1 : Γ(X, ⊤)) • unitSection (⊤ : X.Opens) := by
    rw [Scheme.Modules.Hom.id_app]
    exact (one_smul Γ(X, ⊤) (unitSection (⊤ : X.Opens))).symm
  have h := IsInvertible.ideal_zeroSchemeIdeal_eq_span_of_app_eq_smul
    (Scheme.Modules.isInvertible_unit X) (unitSection (⊤ : X.Opens))
    (isFrameOn_unitSection (X := X) (U := ⊤) ⊤) (𝟙 (𝟙_ X.Modules)) 1 hid U le_top
  rw [map_one, Ideal.span_singleton_one] at h
  exact h

variable {X D : Scheme.{u}} {i : D ⟶ X}

/-- The zero scheme of a normalized section avoids the modulus. This is
proved from equality of the actual restricted sheaf morphisms. -/
theorem normalizedSection_avoids (M : RigidifiedLineBundle i)
    (s : 𝟙_ X.Modules ⟶ M.L)
    (hs : pullbackSection i s ≫ M.trivialization.hom = 𝟙 (𝟙_ D.Modules)) :
    ∀ y : D, i.base y ∉ (zeroSchemeIdeal s).support := by
  have hzero : zeroSchemeIdeal (pullbackSection i s) = ⊤ := by
    calc
      zeroSchemeIdeal (pullbackSection i s) =
          zeroSchemeIdeal (pullbackSection i s ≫ M.trivialization.hom) :=
        (zeroSchemeIdeal_comp_eq_of_isIso (pullbackSection i s)
          M.trivialization.hom).symm
      _ = zeroSchemeIdeal (𝟙 (𝟙_ D.Modules)) := congrArg zeroSchemeIdeal hs
      _ = ⊤ := zeroSchemeIdeal_unit_identity D
  have hcomap : (zeroSchemeIdeal s).comap i = ⊤ :=
    (Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal i M.isInvertible s).trans hzero
  intro y hy
  have hp : y ∈ ((zeroSchemeIdeal s).comap i).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hy
  rw [hcomap, Scheme.IdealSheafData.support_top] at hp
  exact hp

/-- A normalized nonzero section constructs an actual effective Cartier divisor
away from the modulus and a compatible isomorphism with its canonical bundle.
The Cartier property and support disjointness are conclusions. -/
theorem exists_effectiveDivisor_of_normalizedSection
    {C S : Scheme.{u}} {c : C ⟶ S} [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ S)
    {D : Scheme.{u}} {i : D ⟶ Limits.pullback c x} (M : RigidifiedLineBundle i)
    (s : 𝟙_ (Limits.pullback c x).Modules ⟶ M.L) (hs0 : s ≠ 0)
    (hs : pullbackSection i s ≫ M.trivialization.hom = 𝟙 (𝟙_ D.Modules)) :
    ∃ (n : ℕ) (E : RelEffCartierDiv c n x)
      (ha : ∀ y : D, i.base y ∉ E.I.support),
      E.I = zeroSchemeIdeal s ∧
      Nonempty (Iso M (ofInvertibleIdeal i E.I (RelEffCartierDiv.isInvertible_I E) ha)) := by
  obtain ⟨n, E, hE⟩ :=
    RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_ne_zero_of_isProper x M.isInvertible s hs0
  have ha : ∀ y : D, i.base y ∉ E.I.support := by
    rw [hE]
    exact normalizedSection_avoids M s hs
  exact ⟨n, E, ha, hE, ⟨zeroDivisorIso M s hs E.I
    (RelEffCartierDiv.isInvertible_I E) hE.symm ha⟩⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
