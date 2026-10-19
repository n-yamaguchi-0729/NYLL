/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusCanonicalPointBundle
import Nyll.JacobianVarieties.Generalized.RigidifiedIdealPullbackComparison
import Nyll.JacobianVarieties.Generalized.PicardGroupFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.Support.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.RelativeDivisors.Representability.RelEffCartierDivFunctor

/-! # The actual full-modulus class of a supported divisor family -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NeronModelInfra Opposite
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
/-- A supported divisor avoids the whole pulled-back modulus, including nilpotents. -/
theorem modulusDivisorFamily_avoids {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn (modulusComplement i))
    (y : (pullback (i ≫ c) t : Scheme.{u})) :
    modulusBaseChange c i t y ∉ E.I.support := by
  intro hy
  have hu := hE hy
  change pullback.fst c t (modulusBaseChange c i t y) ∈ modulusComplement i at hu
  rw [← Scheme.Hom.comp_apply, modulusBaseChange_fst, Scheme.Hom.comp_apply] at hu
  exact modulus_not_mem_complement i _ hu

/-- The inverse divisor ideal with its actual section normalized along the full modulus. -/
def modulusDivisorFamilyBundle {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn (modulusComplement i)) :
    RigidifiedLineBundle (modulusBaseChange c i t) :=
  RigidifiedLineBundle.ofInvertibleIdeal (modulusBaseChange c i t) E.I
    (RelEffCartierDiv.isInvertible_I E) (modulusDivisorFamily_avoids c i E hE)

/-- The class of the specified canonical divisor rigidification on the actual family. -/
def modulusDivisorFamilyClass {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn (modulusComplement i)) :
    RigidifiedLineBundle.Classes (modulusBaseChange c i t) :=
  RigidifiedLineBundle.classOf (modulusDivisorFamilyBundle c i E hE)

/-- Arbitrary parameter pullback preserves the specified canonical divisor frame. -/
def modulusDivisorFamilyPullbackIso
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn (modulusComplement i))
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    RigidifiedLineBundle.Iso
      ((modulusDivisorFamilyBundle c i E hE).pullback
        (baseChangeSnd c ⟨f, hf⟩) (baseChangeSnd (i ≫ c) ⟨f, hf⟩)
        (modulusBaseChange_naturality c i ⟨f, hf⟩))
      (modulusDivisorFamilyBundle c i (E.pullbackAlong f hf) (hE.pullbackAlong f hf)) :=
  RigidifiedLineBundle.ofInvertibleIdealPullbackIsoOfEq
    (baseChangeSnd c ⟨f, hf⟩) (baseChangeSnd (i ≫ c) ⟨f, hf⟩)
    (modulusBaseChange_naturality c i ⟨f, hf⟩)
    E.I (RelEffCartierDiv.isInvertible_I E) (modulusDivisorFamily_avoids c i E hE)
    (E.pullbackAlong f hf).I (RelEffCartierDiv.isInvertible_I (E.pullbackAlong f hf))
    (modulusDivisorFamily_avoids c i (E.pullbackAlong f hf) (hE.pullbackAlong f hf)) rfl

/-- The actual divisor class is natural on the original modulus Picard group presheaf. -/
theorem modulusDivisorFamilyClass_naturality
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {n : ℕ}
    (E : RelEffCartierDiv c n t) (hE : E.SupportedIn (modulusComplement i))
    (f : T' ⟶ T) (hf : f ≫ t = t') :
    (modulusPicardGroupPresheaf c i).map
        (Over.homMk f hf : Over.mk t' ⟶ Over.mk t).op (modulusDivisorFamilyClass c i E hE) =
      modulusDivisorFamilyClass c i (E.pullbackAlong f hf) (hE.pullbackAlong f hf) :=
  (RigidifiedLineBundle.classOf_eq_iff _ _).mpr
    ⟨modulusDivisorFamilyPullbackIso c i E hE f hf⟩

end AlgebraicGeometry.GeneralizedJacobian
