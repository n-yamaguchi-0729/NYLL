/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.NormalizedSectionNonzero
import Nyll.JacobianVarieties.Generalized.RigidifiedNormalizedPullback
import Nyll.JacobianVarieties.Generalized.PicardFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.IEqZeroSchemeIdeal
import Nyll.AlgebraicCurves.Cohomology.Sheaves.EulerCharacteristic.RelativeDivisorIEqZeroSchemeIdealEulerCharEqSmoothFibre
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Effective divisors of normalized families

A section normalized along a fibrewise nonempty modulus is nonzero on every
geometric fibre. The fibre Euler characteristic determines the degree, and
the actual zero scheme is a finite flat relative Cartier divisor. Its
canonical modulus rigidification recovers the original family.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
  [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  (i : D ⟶ C) [Surjective (i ≫ c)]

/-- The actual normalized family cuts out a divisor of its prescribed geometric degree. -/
theorem exists_relativeDivisor_of_normalizedSection
    {T : Scheme.{u}} [IsLocallyNoetherian T] (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle (modulusBaseChange c i t))
    (s : 𝟙_ (Limits.pullback c t).Modules ⟶ M.L)
    (hs : pullbackSection (modulusBaseChange c i t) s ≫ M.trivialization.hom =
      𝟙 (𝟙_ (Limits.pullback (i ≫ c) t).Modules))
    (n : ℕ)
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ T),
      ∃ 𝒱 : (Limits.pullback c (x ≫ t)).TwoAffineOpenCover,
        let π := pullback.snd c (x ≫ t)
        let F := (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M.L
        (Module.finrank k (𝒱.sectionsOf π F).H0 : ℤ) -
            Module.finrank k (𝒱.sectionsOf π F).H1 =
          (Module.finrank k (𝒱.sectionsOf π (𝟙_ _)).H0 : ℤ) -
            Module.finrank k (𝒱.sectionsOf π (𝟙_ _)).H1 + n) :
    ∃ (E : RelEffCartierDiv c n t)
      (ha : ∀ y : (Limits.pullback (i ≫ c) t : Scheme.{u}),
        modulusBaseChange c i t y ∉ E.I.support),
      E.I = zeroSchemeIdeal s ∧
        Nonempty (Iso M (ofInvertibleIdeal (modulusBaseChange c i t) E.I
          (RelEffCartierDiv.isInvertible_I E) ha)) := by
  have hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ T),
      ∃ E : RelEffCartierDiv c n (x ≫ t),
        E.I = (zeroSchemeIdeal s).comap (mapOnProdOver c x rfl) := by
    intro k _ _ x
    let ψ : SchemeHomOver (x ≫ t) t := ⟨x, rfl⟩
    let f := baseChangeSnd c ψ
    let g := baseChangeSnd (i ≫ c) ψ
    let Mx := M.pullback f g (modulusBaseChange_naturality c i ψ)
    have hsurj : Surjective (pullback.snd (i ≫ c) (x ≫ t)) := inferInstance
    have : Nonempty (Limits.pullback (i ≫ c) (x ≫ t) : Scheme.{u}) := by
      obtain ⟨z, _⟩ := (pullback.snd (i ≫ c) (x ≫ t)).surjective
        (IsLocalRing.closedPoint k)
      exact ⟨z⟩
    have hsx := pullback_normalized_section f g (modulusBaseChange_naturality c i ψ) M s hs
    have hs0 : pullbackSection f s ≠ 0 := normalizedSection_ne_zero Mx _ hsx
    have : MorphismProperty.IsStableUnderBaseChange
        (fun {X Y : Scheme.{u}} (a : X ⟶ Y) => SmoothOfRelativeDimension 1 a) :=
      smoothOfRelativeDimension_isStableUnderBaseChange 1
    have : SmoothOfRelativeDimension 1 (pullback.snd c (x ≫ t)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun {X Y : Scheme.{u}} (a : X ⟶ Y) => SmoothOfRelativeDimension 1 a)
        (IsPullback.of_hasPullback c (x ≫ t)) inferInstance
    obtain ⟨𝒱, h𝒱⟩ := hχ k x
    obtain ⟨E, hE, _⟩ :=
      RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq_of_smooth_fibre
        (x ≫ t) Mx.isInvertible (pullbackSection f s) hs0 𝒱 n h𝒱
    exact ⟨E, hE.trans (M.isInvertible.comap_zeroSchemeIdeal f s).symm⟩
  obtain ⟨E, hE, _⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal M.isInvertible s n hfib
  have ha : ∀ y : (Limits.pullback (i ≫ c) t : Scheme.{u}),
      modulusBaseChange c i t y ∉ E.I.support := by
    rw [hE]
    exact normalizedSection_avoids M s hs
  exact ⟨E, ha, hE, ⟨zeroDivisorIso M s hs E.I
    (RelEffCartierDiv.isInvertible_I E) hE.symm ha⟩⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
