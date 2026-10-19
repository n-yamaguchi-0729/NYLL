/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDivisorFamily
import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.PullbackOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.Support.SupportedInOfPoint

/-! # The corrected denominator is the actual constant basepoint frame -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]

private theorem familyClass_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    {n : ℕ} (E E' : RelEffCartierDiv c n t) (h : E = E')
    (hE : E.SupportedIn (modulusComplement i)) (hE' : E'.SupportedIn (modulusComplement i)) :
    modulusDivisorFamilyClass c i E hE = modulusDivisorFamilyClass c i E' hE' := by
  subst E'
  rfl

private theorem familyClass_ofPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c))
    (hx : (RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
      ((Category.assoc _ _ _).trans x.2)).SupportedIn (modulusComplement i)) :
    modulusDivisorFamilyClass c i
        (RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
          ((Category.assoc _ _ _).trans x.2)) hx =
      RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c i x) := rfl

/-- Pulling the actual basepoint divisor to a test scheme gives its canonical point frame. -/
theorem modulusDivisorFamilyClass_basepoint_pullback
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) ((modulusComplement i).ι ≫ c))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    let P := RelEffCartierDiv.ofPoint c (ε.1 ≫ (modulusComplement i).ι)
      ((Category.assoc _ _ _).trans ε.2)
    let hP := RelEffCartierDiv.supportedIn_ofPoint (f := c)
      (ε.1 ≫ (modulusComplement i).ι) ((Category.assoc _ _ _).trans ε.2)
      (modulusComplement i) (fun z => (ε.1 z).property)
    let x : SchemeHomOver t ((modulusComplement i).ι ≫ c) :=
      ⟨t ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
    modulusDivisorFamilyClass c i (P.pullbackAlong t (Category.comp_id t))
        (hP.pullbackAlong t (Category.comp_id t)) =
      RigidifiedLineBundle.classOf (modulusCanonicalPointBundle c i x) := by
  intro P hP x
  have he : P.pullbackAlong t (Category.comp_id t) =
      RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
        ((Category.assoc _ _ _).trans x.2) := by
    rw [RelEffCartierDiv.pullbackAlong_ofPoint]
    apply RelEffCartierDiv.ext
    change (graphOver c (t ≫ (ε.1 ≫ (modulusComplement i).ι)) _).ker =
      (graphOver c ((t ≫ ε.1) ≫ (modulusComplement i).ι) _).ker
    congr 1
  have hx : (RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
      ((Category.assoc _ _ _).trans x.2)).SupportedIn (modulusComplement i) :=
    RelEffCartierDiv.supportedIn_ofPoint (f := c) (x.1 ≫ (modulusComplement i).ι)
      ((Category.assoc _ _ _).trans x.2) (modulusComplement i) (fun z => (x.1 z).property)
  exact (familyClass_congr c i _ _ he (hP.pullbackAlong t (Category.comp_id t)) hx).trans
    (familyClass_ofPoint c i x hx)

end AlgebraicGeometry.GeneralizedJacobian
