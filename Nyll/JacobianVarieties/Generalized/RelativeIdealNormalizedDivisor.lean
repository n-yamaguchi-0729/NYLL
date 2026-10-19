/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RelativeNormalizedDivisor
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # The divisor cut out by a family normalized along a positive relative modulus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {R : Type u} [CommRing R] {C T : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
  [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  [IsLocallyNoetherian T] (t : T ⟶ Spec (CommRingCat.of R))
  {d : ℕ} (J : RelEffCartierDiv c d t) (hd : 0 < d)

include hd in
/-- A normalized section of the actual family has an effective divisor of its geometric degree. -/
theorem exists_relativeDivisor_of_ideal_normalizedSection
    (M : RigidifiedLineBundle J.I.subschemeι)
    (s : 𝟙_ (Limits.pullback c t).Modules ⟶ M.L)
    (hs : pullbackSection J.I.subschemeι s ≫ M.trivialization.hom =
      𝟙 (𝟙_ J.I.subscheme.Modules))
    (n : ℕ)
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T),
      ∃ 𝒱 : (Limits.pullback c (x ≫ t)).TwoAffineOpenCover,
        let π := pullback.snd c (x ≫ t)
        let F := (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M.L
        (Module.finrank k (𝒱.sectionsOf π F).H0 : ℤ) -
            Module.finrank k (𝒱.sectionsOf π F).H1 =
          (Module.finrank k (𝒱.sectionsOf π (𝟙_ _)).H0 : ℤ) -
            Module.finrank k (𝒱.sectionsOf π (𝟙_ _)).H1 + n) :
    ∃ (E : RelEffCartierDiv c n t)
      (ha : ∀ y : J.I.subscheme, J.I.subschemeι.base y ∉ E.I.support),
      E.I = zeroSchemeIdeal s ∧ Nonempty (Iso M
        (ofInvertibleIdeal J.I.subschemeι E.I (RelEffCartierDiv.isInvertible_I E) ha)) := by
  have hfib : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ T),
      ∃ E : RelEffCartierDiv c n (x ≫ t),
        E.I = (zeroSchemeIdeal s).comap (mapOnProdOver c x rfl) := by
    intro k _ _ x
    let Jx := J.pullbackAlong x rfl
    let f : Limits.pullback c (x ≫ t) ⟶ Limits.pullback c t := mapOnProdOver c x rfl
    let g := comapSubschemeMapOver J.I x rfl
    have w : Jx.I.subschemeι ≫ f = g ≫ J.I.subschemeι :=
      (isPullback_comapSubschemeMapOver J.I x rfl).w.symm
    let Mx := M.pullback f g w
    have : IsFinite (Jx.I.subschemeι ≫ pullback.snd c (x ≫ t)) := Jx.isFinite
    have : Flat (Jx.I.subschemeι ≫ pullback.snd c (x ≫ t)) := Jx.flat
    have : LocallyOfFinitePresentation (Jx.I.subschemeι ≫ pullback.snd c (x ≫ t)) :=
      Jx.locallyOfFinitePresentation
    have : Surjective (Jx.I.subschemeι ≫ pullback.snd c (x ≫ t)) :=
      (Scheme.Hom.one_le_finrank_iff_surjective _).mp (fun z => by
        rw [Jx.finrank_eq]
        exact hd)
    have : Nonempty (J.I.comap (mapOnProdOver c x (rfl : x ≫ t = x ≫ t))).subscheme := by
      obtain ⟨z, _⟩ := (Jx.I.subschemeι ≫ pullback.snd c (x ≫ t)).surjective
        (IsLocalRing.closedPoint k)
      exact ⟨z⟩
    have hsx := pullback_normalized_section f g w M s hs
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
  have ha : ∀ y : J.I.subscheme, J.I.subschemeι.base y ∉ E.I.support := by
    rw [hE]
    exact normalizedSection_avoids M s hs
  exact ⟨E, ha, hE, ⟨zeroDivisorIso M s hs E.I
    (RelEffCartierDiv.isInvertible_I E) hE.symm ha⟩⟩

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
