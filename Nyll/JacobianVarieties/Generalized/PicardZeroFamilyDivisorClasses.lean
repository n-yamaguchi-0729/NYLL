/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroFamilyDivisorOriginal
import Nyll.JacobianVarieties.Generalized.ModulusDivisorFamily
import Nyll.JacobianVarieties.Generalized.RigidifiedDivisorProducts

/-! # Normalized divisor classes on arbitrary noetherian affine bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
  [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
  {d : ℕ} (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))) (hd : 0 < d)
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c))
  (R : Type u) [CommRing R] [IsNoetherianRing R]

include hd in
/-- Actual large divisor families satisfy the normalized equality in the full class group. -/
theorem picardZeroFamily_eventually_divisor_class_specMap [Algebra K R]
    (M : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) (specMap K R)))
    (hM : RigidifiedLineBundle.classOf M ∈
      (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj (op (Over.mk (specMap K R)))) :
    let x : SchemeHomOver (specMap K R)
        ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
      ⟨specMap K R ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∃ E : RelEffCartierDiv c n (specMap K R),
      ∃ hE : E.SupportedIn (modulusComplement (modulusCurveMap D)),
        RigidifiedLineBundle.classOf M *
            RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c (modulusCurveMap D) x) ^ n =
          modulusDivisorFamilyClass c (modulusCurveMap D) E hE := by
  let x : SchemeHomOver (specMap K R)
      ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
    ⟨specMap K R ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  let P := RelEffCartierDiv.ofPoint c
    (x.1 ≫ (modulusComplement (modulusCurveMap D)).ι) ((Category.assoc _ _ _).trans x.2)
  obtain ⟨b, hb⟩ := picardZeroFamily_eventually_divisor_original c D hd ε R M hM
  refine ⟨b, ?_⟩
  intro n hn
  obtain ⟨E, ha, hp, hE, he⟩ := hb n hn
  refine ⟨E, hE, ?_⟩
  have hc := (RigidifiedLineBundle.classOf_eq_iff _ _).mpr he
  change RigidifiedLineBundle.classOf M *
      RigidifiedLineBundle.classOf
        (RigidifiedLineBundle.ofInvertibleIdeal
          (modulusBaseChange c (modulusCurveMap D) (specMap K R)) (P.I ^ n)
          ((RelEffCartierDiv.isInvertible_I P).pow n) hp) =
    modulusDivisorFamilyClass c (modulusCurveMap D) E hE at hc
  rw [RigidifiedLineBundle.classOf_ofInvertibleIdeal_pow
    (modulusBaseChange c (modulusCurveMap D) (specMap K R)) P.I
    (RelEffCartierDiv.isInvertible_I P)
    (modulusPointDivisor_avoids c (modulusCurveMap D) x) n] at hc
  exact hc

include hd in
/-- The normalized family construction works for every map from a noetherian affine scheme. -/
theorem picardZeroFamily_eventually_divisor_class
    (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of K))
    (M : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) t))
    (hM : RigidifiedLineBundle.classOf M ∈
      (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj (op (Over.mk t))) :
    let x : SchemeHomOver t ((modulusComplement (modulusCurveMap D)).ι ≫ c) :=
      ⟨t ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → ∃ E : RelEffCartierDiv c n t,
      ∃ hE : E.SupportedIn (modulusComplement (modulusCurveMap D)),
        RigidifiedLineBundle.classOf M *
            RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c (modulusCurveMap D) x) ^ n =
          modulusDivisorFamilyClass c (modulusCurveMap D) E hE := by
  let : Algebra K R := (Spec.preimage t).hom.toAlgebra
  have ht : specMap K R = t := Spec.map_preimage t
  revert M hM
  rw [← ht]
  intro M hM
  exact picardZeroFamily_eventually_divisor_class_specMap c D hd ε R M hM

end AlgebraicGeometry.GeneralizedJacobian
