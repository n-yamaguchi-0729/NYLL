/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.PicardZeroChartCompatibility
import Nyll.JacobianVarieties.Generalized.ModulusBasepointDivisorClass
import Nyll.JacobianVarieties.Generalized.ModulusDivisorDifferenceClass

/-! # The actual chart class is its corrected divisor class -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian.ModulusDivisorAtlas

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)}
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  {d : ℕ} {D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K)))}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
    ((modulusComplement (modulusCurveMap D)).ι ≫ c)}
  {T : Over (Spec (CommRingCat.of K))}
  {x : (modulusPicardZeroSheaf c (modulusCurveMap D)).obj.obj (op T)}
  (A : ModulusDivisorAtlas c D ε T x)

/-- The actual rational basepoint divisor used by the atlas. -/
def basepointDivisor (_A : ModulusDivisorAtlas c D ε T x) :
    RelEffCartierDiv c 1 (𝟙 (Spec (CommRingCat.of K))) :=
  RelEffCartierDiv.ofPoint c (ε.1 ≫ (modulusComplement (modulusCurveMap D)).ι)
    ((Category.assoc _ _ _).trans ε.2)

/-- The specified basepoint divisor avoids the full modulus. -/
theorem basepointDivisor_supported :
    A.basepointDivisor.SupportedIn (modulusComplement (modulusCurveMap D)) :=
  RelEffCartierDiv.supportedIn_ofPoint (f := c)
    (ε.1 ≫ (modulusComplement (modulusCurveMap D)).ι)
    ((Category.assoc _ _ _).trans ε.2) (modulusComplement (modulusCurveMap D))
    (fun z => (ε.1 z).property)

/-- On each actual chart the normalized divisor class is the chosen original raw class. -/
theorem differenceClass_eq_rawClass (j : A.cover.I₀) :
    modulusDivisorDifferenceClass c (modulusCurveMap D)
      (A.divisor j) (A.supported j)
      (A.basepointDivisor.pullbackAlong (A.cover.f j ≫ T.hom) (Category.comp_id _))
      (A.basepointDivisor_supported.pullbackAlong (A.cover.f j ≫ T.hom) (Category.comp_id _))
      (A.degree j) = (A.rawClass j).val := by
  change modulusDivisorFamilyClass c (modulusCurveMap D) (A.divisor j) (A.supported j) /
      modulusDivisorFamilyClass c (modulusCurveMap D)
        (A.basepointDivisor.pullbackAlong (A.cover.f j ≫ T.hom) (Category.comp_id _))
        (A.basepointDivisor_supported.pullbackAlong (A.cover.f j ≫ T.hom)
          (Category.comp_id _)) ^ A.degree j = RigidifiedLineBundle.classOf (A.bundle j)
  have hb : modulusDivisorFamilyClass c (modulusCurveMap D)
      (A.basepointDivisor.pullbackAlong (A.cover.f j ≫ T.hom) (Category.comp_id _))
      (A.basepointDivisor_supported.pullbackAlong (A.cover.f j ≫ T.hom)
        (Category.comp_id _)) =
      RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c (modulusCurveMap D)
        (GoodReductionJacobian.schemeHomOverComp (A.cover.f j ≫ T.hom)
          (Category.comp_id _) ε)) :=
    modulusDivisorFamilyClass_basepoint_pullback c (modulusCurveMap D) ε _
  rw [hb, ← A.class_eq j, mul_div_cancel_right]

omit [IsProper c] [SmoothOfRelativeDimension 1 c] in
private theorem constant_divisor_pullback {n : ℕ}
    (P : RelEffCartierDiv c n (𝟙 (Spec (CommRingCat.of K))))
    {V W : Scheme.{u}} (s : V ⟶ Spec (CommRingCat.of K))
    (t : W ⟶ Spec (CommRingCat.of K)) (f : W ⟶ V) (hf : f ≫ s = t) :
    (P.pullbackAlong s (Category.comp_id s)).pullbackAlong f hf =
      P.pullbackAlong t (Category.comp_id t) := by
  rw [RelEffCartierDiv.pullbackAlong_comp]
  subst t
  rfl

/-- Pulling a chart divisor to any test scheme preserves its precise corrected raw class. -/
theorem differenceClass_pullback_eq_rawClass
    {V : Scheme.{u}} {t : V ⟶ Spec (CommRingCat.of K)}
    (j : A.cover.I₀) (f : V ⟶ Spec (A.cover.X j)) (hf : f ≫ (A.cover.f j ≫ T.hom) = t) :
    modulusDivisorDifferenceClass c (modulusCurveMap D)
      ((A.divisor j).pullbackAlong f hf) ((A.supported j).pullbackAlong f hf)
      (A.basepointDivisor.pullbackAlong t (Category.comp_id t))
      (A.basepointDivisor_supported.pullbackAlong t (Category.comp_id t)) (A.degree j) =
      ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map
        (Over.homMk f hf : Over.mk t ⟶ Over.mk (A.cover.f j ≫ T.hom)).op (A.rawClass j)).val := by
  have hn := modulusDivisorDifferenceClass_naturality c (modulusCurveMap D)
    (A.divisor j) (A.supported j)
    (A.basepointDivisor.pullbackAlong (A.cover.f j ≫ T.hom) (Category.comp_id _))
    (A.basepointDivisor_supported.pullbackAlong (A.cover.f j ≫ T.hom) (Category.comp_id _))
    (A.degree j) f hf
  rw [A.differenceClass_eq_rawClass j] at hn
  have hclass : ∀ (P Q : RelEffCartierDiv c 1 t)
      (hP : P.SupportedIn (modulusComplement (modulusCurveMap D)))
      (hQ : Q.SupportedIn (modulusComplement (modulusCurveMap D))), P = Q →
      modulusDivisorFamilyClass c (modulusCurveMap D) P hP =
        modulusDivisorFamilyClass c (modulusCurveMap D) Q hQ := by
    intro P Q hP hQ he
    subst Q
    rfl
  have hden := hclass _ _
    ((A.basepointDivisor_supported.pullbackAlong (A.cover.f j ≫ T.hom)
      (Category.comp_id _)).pullbackAlong f hf)
    (A.basepointDivisor_supported.pullbackAlong t (Category.comp_id t))
    (constant_divisor_pullback A.basepointDivisor (A.cover.f j ≫ T.hom) t f hf)
  unfold modulusDivisorDifferenceClass at hn ⊢
  rw [hden] at hn
  exact hn.symm

/-- The same exact comparison with the canonical constant point as denominator. -/
theorem familyClass_div_point_pow_pullback_eq_rawClass
    {V : Scheme.{u}} {t : V ⟶ Spec (CommRingCat.of K)}
    (j : A.cover.I₀) (f : V ⟶ Spec (A.cover.X j)) (hf : f ≫ (A.cover.f j ≫ T.hom) = t) :
    modulusDivisorFamilyClass c (modulusCurveMap D)
        ((A.divisor j).pullbackAlong f hf) ((A.supported j).pullbackAlong f hf) /
      RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c (modulusCurveMap D)
        (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) ε)) ^ A.degree j =
      ((modulusPicardZeroPresheaf c (modulusCurveMap D)).map
        (Over.homMk f hf : Over.mk t ⟶ Over.mk (A.cover.f j ≫ T.hom)).op (A.rawClass j)).val := by
  have h := A.differenceClass_pullback_eq_rawClass j f hf
  have hb : modulusDivisorFamilyClass c (modulusCurveMap D)
      (A.basepointDivisor.pullbackAlong t (Category.comp_id t))
      (A.basepointDivisor_supported.pullbackAlong t (Category.comp_id t)) =
      RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c (modulusCurveMap D)
        (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) ε)) :=
    modulusDivisorFamilyClass_basepoint_pullback c (modulusCurveMap D) ε t
  unfold modulusDivisorDifferenceClass at h
  rw [hb] at h
  exact h

/-- Two restrictions of the actual atlas have the same original zero-sheaf class. -/
theorem overlap_zeroClasses
    {V : Scheme.{u}} {t : V ⟶ Spec (CommRingCat.of K)} (i j : A.cover.I₀)
    (f : V ⟶ Spec (A.cover.X i)) (hf : f ≫ (A.cover.f i ≫ T.hom) = t)
    (g : V ⟶ Spec (A.cover.X j)) (hg : g ≫ (A.cover.f j ≫ T.hom) = t)
    (hfg : f ≫ A.cover.f i = g ≫ A.cover.f j) :
    let e := RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c
      (modulusCurveMap D) (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) ε))
    let z₀ := modulusDivisorFamilyClass c (modulusCurveMap D)
      ((A.divisor i).pullbackAlong f hf) ((A.supported i).pullbackAlong f hf) /
        e ^ A.degree i
    let z₁ := modulusDivisorFamilyClass c (modulusCurveMap D)
      ((A.divisor j).pullbackAlong g hg) ((A.supported j).pullbackAlong g hg) /
        e ^ A.degree j
    ∃ (hz₀ : z₀ ∈ (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj
        (op (Over.mk t)))
      (hz₁ : z₁ ∈ (modulusPicardZeroSubfunctor c (modulusCurveMap D)).obj
        (op (Over.mk t))),
      (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))).app
          (op (Over.mk t)) ⟨z₀, hz₀⟩ =
        (toSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K)))
          (modulusPicardZeroPresheaf c (modulusCurveMap D))).app
          (op (Over.mk t)) ⟨z₁, hz₁⟩ := by
  let fOver : Over.mk t ⟶ Over.mk (A.cover.f i ≫ T.hom) := Over.homMk f hf
  let gOver : Over.mk t ⟶ Over.mk (A.cover.f j ≫ T.hom) := Over.homMk g hg
  let raw₀ : (modulusPicardZeroPresheaf c (modulusCurveMap D)).obj (op (Over.mk t)) :=
    (modulusPicardZeroPresheaf c (modulusCurveMap D)).map fOver.op (A.rawClass i)
  let raw₁ : (modulusPicardZeroPresheaf c (modulusCurveMap D)).obj (op (Over.mk t)) :=
    (modulusPicardZeroPresheaf c (modulusCurveMap D)).map gOver.op (A.rawClass j)
  have h₀ := A.familyClass_div_point_pow_pullback_eq_rawClass i f hf
  have h₁ := A.familyClass_div_point_pow_pullback_eq_rawClass j g hg
  have hcomp : fOver ≫ (Over.homMk (A.cover.f i) :
      Over.mk (A.cover.f i ≫ T.hom) ⟶ T) =
      gOver ≫ (Over.homMk (A.cover.f j) : Over.mk (A.cover.f j ≫ T.hom) ⟶ T) := by
    apply Over.OverMorphism.ext
    exact hfg
  have hη := A.rawClass_toSheafify_overlap i j fOver gOver hcomp
  dsimp only
  rw [h₀, h₁]
  exact ⟨raw₀.property, raw₁.property, hη⟩


end AlgebraicGeometry.GeneralizedJacobian.ModulusDivisorAtlas
