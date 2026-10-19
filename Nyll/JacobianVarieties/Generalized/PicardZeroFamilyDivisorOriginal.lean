/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroFamilyDivisor
import Nyll.JacobianVarieties.Generalized.ModulusFamilyIdealClasses

/-! # Actual divisor representatives with the original modulus frame -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
  [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (R : Type u) [CommRing R] [IsNoetherianRing R] [Algebra K R]

include hd in
/-- Large-degree divisor families recover the original specified rigidification exactly. -/
theorem picardZeroFamily_eventually_divisor_original
    (M : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) (specMap K R)))
    (hM : RigidifiedLineBundle.classOf M ∈
      (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj (op (Over.mk (specMap K R)))) :
    let t := specMap K R
    let i := modulusBaseChange c (modulusCurveMap D) t
    let x : SchemeHomOver t ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
      ⟨t ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
    let P := RelEffCartierDiv.ofPoint c
      (x.1 ≫ (modulusComplement (modulusCurveMap D)).ι) ((Category.assoc _ _ _).trans x.2)
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ (E : RelEffCartierDiv c n t)
        (ha : ∀ y : (pullback (modulusCurveMap D ≫ c) t : Scheme.{u}), i.base y ∉ E.I.support)
        (hp : ∀ y : (pullback (modulusCurveMap D ≫ c) t : Scheme.{u}),
          i.base y ∉ (P.I ^ n).support),
        E.SupportedIn (modulusComplement (modulusCurveMap D)) ∧
          Nonempty (RigidifiedLineBundle.Iso
            (M.tensor (RigidifiedLineBundle.ofInvertibleIdeal i (P.I ^ n)
              ((RelEffCartierDiv.isInvertible_I P).pow n) hp))
            (RigidifiedLineBundle.ofInvertibleIdeal i E.I
              (RelEffCartierDiv.isInvertible_I E) ha)) := by
  let t := specMap K R
  let x : SchemeHomOver t ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
    ⟨t ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  let P := RelEffCartierDiv.ofPoint c
    (x.1 ≫ (modulusComplement (modulusCurveMap D)).ι) ((Category.assoc _ _ _).trans x.2)
  obtain ⟨b, hb⟩ := picardZeroFamily_eventually_divisor c D hd ε R M hM
  refine ⟨b, ?_⟩
  intro n hn
  obtain ⟨E, ha, hp, hE, he⟩ := hb n hn
  exact ⟨E, modulusFamilyAvoidance D t E.I ha,
    modulusFamilyAvoidance D t (P.I ^ n) hp, hE,
    modulusFamilyIdeal_tensorIso D t M (P.I ^ n) E.I
      ((RelEffCartierDiv.isInvertible_I P).pow n) (RelEffCartierDiv.isInvertible_I E) hp ha he⟩

end AlgebraicGeometry.GeneralizedJacobian
