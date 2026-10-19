/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusDivisorFamily

/-! # The actual full-modulus class of a corrected divisor family -/

noncomputable section

universe u

open CategoryTheory Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]

/-- Divide the specified canonical divisor frame by a power of another specified frame. -/
def modulusDivisorDifferenceClass {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {r s : ℕ} (E : RelEffCartierDiv c r t) (hE : E.SupportedIn (modulusComplement i))
    (P : RelEffCartierDiv c s t) (hP : P.SupportedIn (modulusComplement i)) (n : ℕ) :
    RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
  modulusDivisorFamilyClass c i E hE / modulusDivisorFamilyClass c i P hP ^ n

/-- The actual corrected class preserves every parameter pullback. -/
theorem modulusDivisorDifferenceClass_naturality
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {r s : ℕ}
    (E : RelEffCartierDiv c r t) (hE : E.SupportedIn (modulusComplement i))
    (P : RelEffCartierDiv c s t) (hP : P.SupportedIn (modulusComplement i)) (n : ℕ)
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    (modulusPicardGroupPresheaf c i).map
        (Over.homMk f hf : Over.mk t' ⟶ Over.mk t).op
        (modulusDivisorDifferenceClass c i E hE P hP n) =
      modulusDivisorDifferenceClass c i (E.pullbackAlong f hf) (hE.pullbackAlong f hf)
        (P.pullbackAlong f hf) (hP.pullbackAlong f hf) n := by
  let H : RigidifiedLineBundle.Classes (modulusBaseChange c i t) →*
      RigidifiedLineBundle.Classes (modulusBaseChange c i t') :=
    RigidifiedLineBundle.classesPullbackHom (baseChangeSnd c ⟨f, hf⟩)
      (baseChangeSnd (i ≫ c) ⟨f, hf⟩) (modulusBaseChange_naturality c i ⟨f, hf⟩)
  have hE' : H (modulusDivisorFamilyClass c i E hE) =
      modulusDivisorFamilyClass c i (E.pullbackAlong f hf) (hE.pullbackAlong f hf) :=
    modulusDivisorFamilyClass_naturality c i E hE f hf
  have hP' : H (modulusDivisorFamilyClass c i P hP) =
      modulusDivisorFamilyClass c i (P.pullbackAlong f hf) (hP.pullbackAlong f hf) :=
    modulusDivisorFamilyClass_naturality c i P hP f hf
  change H (modulusDivisorFamilyClass c i E hE /
    modulusDivisorFamilyClass c i P hP ^ n) = _
  rw [map_div, map_pow, hE', hP']
  rfl

end AlgebraicGeometry.GeneralizedJacobian
