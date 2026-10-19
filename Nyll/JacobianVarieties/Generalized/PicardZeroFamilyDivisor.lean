/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroFamilyNormalizedSection
import Nyll.JacobianVarieties.Generalized.PicardZeroFamilyTwistDegree
import Nyll.JacobianVarieties.Generalized.RelativeIdealNormalizedDivisor
import Nyll.JacobianVarieties.Generalized.ModulusFamilyDisjointSupport
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveTwoAffineCover

/-! # Concrete divisor representatives of actual affine Picard-zero families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
  [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (R : Type u) [CommRing R] [IsNoetherianRing R] [Algebra K R]

include hd in
/-- Actual affine families have large-degree divisor representatives away from the full modulus. -/
theorem picardZeroFamily_eventually_divisor
    (M : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) (specMap K R)))
    (hM : RigidifiedLineBundle.classOf M ∈
      (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj (op (Over.mk (specMap K R)))) :
    let t := specMap K R
    let J := modulusFamilyDivisor D t
    let N := modulusFamilyIdealBundle D t M
    let x : SchemeHomOver t ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
      ⟨t ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
    let P := RelEffCartierDiv.ofPoint c
      (x.1 ≫ (modulusComplement (modulusCurveMap D)).ι) ((Category.assoc _ _ _).trans x.2)
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ (E : RelEffCartierDiv c n t)
        (ha : ∀ y : J.I.subscheme, J.I.subschemeι.base y ∉ E.I.support)
        (hp : ∀ y : J.I.subscheme, J.I.subschemeι.base y ∉ (P.I ^ n).support),
        E.SupportedIn (modulusComplement (modulusCurveMap D)) ∧
          Nonempty (RigidifiedLineBundle.Iso
            (N.tensor (RigidifiedLineBundle.ofInvertibleIdeal J.I.subschemeι (P.I ^ n)
              ((RelEffCartierDiv.isInvertible_I P).pow n) hp))
            (RigidifiedLineBundle.ofInvertibleIdeal J.I.subschemeι E.I
              (RelEffCartierDiv.isInvertible_I E) ha)) := by
  let t := specMap K R
  let J := modulusFamilyDivisor D t
  let N := modulusFamilyIdealBundle D t M
  let εc : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c :=
    ⟨ε.1 ≫ (modulusComplement (modulusCurveMap D)).ι, (Category.assoc _ _ _).trans ε.2⟩
  let x : SchemeHomOver t ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
    ⟨t ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  let P := RelEffCartierDiv.ofPoint c
    (x.1 ≫ (modulusComplement (modulusCurveMap D)).ι) ((Category.assoc _ _ _).trans x.2)
  obtain ⟨𝒱, _, _⟩ := exists_twoAffineOpenCover_of_section K c εc
  obtain ⟨b, hb⟩ := picardZeroFamily_eventually_normalizedSection c D ε R (𝒱.pullback c R) M hM
  refine ⟨b, ?_⟩
  intro n hn
  obtain ⟨hp, s, hs⟩ := hb n hn
  let Q := RigidifiedLineBundle.ofInvertibleIdeal J.I.subschemeι (P.I ^ n)
    ((RelEffCartierDiv.isInvertible_I P).pow n) hp
  have hzero : ∀ (k : Type u) [Field k] [IsAlgClosed k] (z : Spec (CommRingCat.of k) ⟶ Spec
      (CommRingCat.of R)),
      IsAlgEquivZero (fibreAt c t z)
        ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) z)).obj N.L) := by
    intro k _ _ z
    exact (hM k z).of_iso ((Scheme.Modules.pullback
      (pullback.fst (pullback.snd c t) z)).mapIso ((Scheme.Modules.pullbackId _).app M.L)).symm
  have hP : P.I = sectionIdeal c εc t := by
    change (graphOver c _ _).ker = (rigSection c t εc).ker
    congr 1
  have hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (z : Spec (CommRingCat.of k) ⟶ Spec
      (CommRingCat.of R)),
      ∃ 𝒲 : (pullback c (z ≫ t)).TwoAffineOpenCover,
        let π := pullback.snd c (z ≫ t)
        let F := (Scheme.Modules.pullback (mapOnProdOver c z rfl)).obj (N.tensor Q).L
        (Module.finrank k (𝒲.sectionsOf π F).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf π F).H1 =
          (Module.finrank k (𝒲.sectionsOf π (𝟙_ _)).H0 : ℤ) -
            Module.finrank k (𝒲.sectionsOf π (𝟙_ _)).H1 + n := by
    intro k _ _ z
    have : MorphismProperty.IsStableUnderBaseChange
        (fun {X Y : Scheme.{u}} (a : X ⟶ Y) => SmoothOfRelativeDimension 1 a) :=
      smoothOfRelativeDimension_isStableUnderBaseChange 1
    have : SmoothOfRelativeDimension 1 (pullback.snd c (z ≫ t)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := fun {X Y : Scheme.{u}} (a : X ⟶ Y) => SmoothOfRelativeDimension 1 a)
        (IsPullback.of_hasPullback c (z ≫ t)) inferInstance
    obtain ⟨𝒲, _, _⟩ := exists_twoAffineOpenCover_of_section k (pullback.snd c (z ≫ t))
      ⟨rigSection c (z ≫ t) εc, pullback.lift_snd _ _ _⟩
    refine ⟨𝒲, ?_⟩
    have h := eulerChar_fibre_zero_pointTwist c εc t N.L N.isInvertible hzero n k z 𝒲
    dsimp only [sectionTwist] at h
    rw [← hP] at h
    exact h
  obtain ⟨E, ha, _, he⟩ :=
    RigidifiedLineBundle.exists_relativeDivisor_of_ideal_normalizedSection
      c t J hd (N.tensor Q) s hs n hχ
  exact ⟨E, ha, hp, supportedIn_of_avoids_modulusFamily D t E ha, he⟩

end AlgebraicGeometry.GeneralizedJacobian
