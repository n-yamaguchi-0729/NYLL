/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.UniformRelativeNormalizedSection
import Nyll.JacobianVarieties.Generalized.RelativeDivisorGeometricDegree
import Nyll.JacobianVarieties.Generalized.ModulusFamilyIdeal
import Nyll.JacobianVarieties.Generalized.ModulusCanonicalPointBundle
import Nyll.JacobianVarieties.Generalized.PicardZero

/-! # Actual Picard-zero families admit normalized point twists over affine bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
  [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (R : Type u) [CommRing R] [IsNoetherianRing R] [Algebra K R]

/-- The actual Picard-zero condition supplies all fibre hypotheses for a normalized family. -/
theorem picardZeroFamily_eventually_normalizedSection
    (𝒱 : (pullback c (specMap K R)).TwoAffineOpenCover)
    (M : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) (specMap K R)))
    (hM : RigidifiedLineBundle.classOf M ∈
      (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj (op (Over.mk (specMap K R)))) :
    let t := specMap K R
    let J := modulusFamilyDivisor D t
    let N := modulusFamilyIdealBundle D t M
    let x : SchemeHomOver t ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
      ⟨t ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
    let E := RelEffCartierDiv.ofPoint c
      (x.1 ≫ (modulusComplement (modulusCurveMap D)).ι) ((Category.assoc _ _ _).trans x.2)
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ ha : ∀ y : J.I.subscheme, J.I.subschemeι.base y ∉ (E.I ^ n).support,
        ∃ s : 𝟙_ (pullback c t).Modules ⟶ N.L ⊗ (E.I ^ n).invModule,
          pullbackSection J.I.subschemeι s ≫
              (N.tensor (RigidifiedLineBundle.ofInvertibleIdeal J.I.subschemeι (E.I ^ n)
                ((RelEffCartierDiv.isInvertible_I E).pow n) ha)).trivialization.hom =
            𝟙 (𝟙_ J.I.subscheme.Modules) := by
  let t := specMap K R
  let J := modulusFamilyDivisor D t
  let N := modulusFamilyIdealBundle D t M
  let x : SchemeHomOver t ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
    ⟨t ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  let p := graphOver c (x.1 ≫ (modulusComplement (modulusCurveMap D)).ι)
    ((Category.assoc _ _ _).trans x.2)
  have hp : p ≫ pullback.snd c t = 𝟙 _ := graphOver_snd _ _ _
  have ha : ∀ y : J.I.subscheme, J.I.subschemeι.base y ∉ p.ker.support := by
    intro y
    have hw : J.I.subschemeι =
        (modulusFamilyIdealIso D t).hom ≫ modulusBaseChange c (modulusCurveMap D) t :=
      (Category.comp_id _).symm.trans (modulusFamilyIdealIso_square D t)
    change J.I.subschemeι y ∉ p.ker.support
    rw [hw, Scheme.Hom.comp_apply]
    exact modulusPointDivisor_avoids c (modulusCurveMap D) x
      ((modulusFamilyIdealIso D t).hom y)
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (a : X ⟶ Y) => SmoothOfRelativeDimension 1 a) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {X Y : Scheme.{u}} (a : X ⟶ Y) => SmoothOfRelativeDimension 1 a)
      (IsPullback.of_hasPullback c t) inferInstance
  apply RigidifiedLineBundle.eventually_exists_normalizedSection_of_geometric_zero
    (pullback.snd c t) 𝒱 J.I (RelEffCartierDiv.isInvertible_I J) p hp ha N (d := d)
  · intro k _ _ _
    exact relativeDivisor_fibre_degree J (Scheme.TwoAffineOpenCover.specMap R k)
  · intro k _ _ _
    let σ := Scheme.TwoAffineOpenCover.specMap R k
    let f := pullback.fst (pullback.snd c t) σ
    exact (hM k σ).of_iso
      ((Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackId _).app M.L)).symm

end AlgebraicGeometry.GeneralizedJacobian
