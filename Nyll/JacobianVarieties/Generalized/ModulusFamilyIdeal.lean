/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFramePicard
import Nyll.AlgebraicCurves.RelativeDivisors.Representability.RelEffCartierDivFunctor

/-! # The actual modulus family as the subscheme of its pulled-back ideal -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))

/-- The relative divisor giving the full modulus on the actual test-curve family. -/
def modulusFamilyDivisor : RelEffCartierDiv c d t :=
  D.pullbackAlong t (Category.comp_id t)

/-- The full modulus family is the subscheme of the pulled-back Cartier ideal. -/
def modulusFamilyIdealIso :
    (modulusFamilyDivisor D t).I.subscheme ≅ pullback (modulusCurveMap D ≫ c) t :=
  (isPullback_comap_snd_over D.I t (Category.comp_id t)).isoPullback ≪≫
    modulusFamilyDomainIso D t

/-- This actual subscheme isomorphism identifies both modulus inclusions. -/
theorem modulusFamilyIdealIso_square :
    (modulusFamilyDivisor D t).I.subschemeι ≫ 𝟙 (pullback c t) =
      (modulusFamilyIdealIso D t).hom ≫ modulusBaseChange c (modulusCurveMap D) t := by
  let h := isPullback_comap_snd_over D.I t (Category.comp_id t)
  change (D.I.comap (mapOnProdOver c t (Category.comp_id t))).subschemeι ≫
      𝟙 (pullback c t) =
    (h.isoPullback.hom ≫ (modulusFamilyDomainIso D t).hom) ≫ _
  rw [Category.assoc, ← modulusFamilyDomainIso_square, Category.comp_id,
    Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc, modulusFamilyInclusion_fst, ← Category.assoc,
      h.isoPullback_hom_fst]
    have hw := (isPullback_comapSubschemeMapOver D.I t (Category.comp_id t)).w_assoc
      (pullback.fst c (𝟙 _))
    exact ((congrArg ((D.I.comap (mapOnProdOver c t (Category.comp_id t))).subschemeι ≫ ·)
      (mapOnProdOver_fst c t (Category.comp_id t))).symm.trans hw.symm)
  · rw [Category.assoc, modulusFamilyInclusion_snd, h.isoPullback_hom_snd]

/-- The same specified rigidification, now on the canonical pulled-back ideal subscheme. -/
def modulusFamilyIdealBundle
    (M : RigidifiedLineBundle (modulusBaseChange c (modulusCurveMap D) t)) :
    RigidifiedLineBundle (modulusFamilyDivisor D t).I.subschemeι :=
  M.pullback (𝟙 _) (modulusFamilyIdealIso D t).hom (modulusFamilyIdealIso_square D t)

end AlgebraicGeometry.GeneralizedJacobian
