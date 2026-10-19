/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFrameClass
import Nyll.JacobianVarieties.Generalized.RigidifiedCongr
import Nyll.JacobianVarieties.Generalized.PicardFunctor

/-!
# Frame classes in the existing modulus Picard presheaf

The finite divisor's structure map and its inclusion followed by the curve map
agree. The resulting actual pullback isomorphism transfers chosen rigidifications
to the modulus convention used by the Picard presheaf. The intrinsic frame classes
therefore inject into its values on every test scheme. Naturality and the
sheaf-level classification remain separate.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The actual changed modulus agrees with the modulus used by the Picard functor. -/
def modulusFamilyDomainIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    pullback (modulusBaseMap D) t ≅ pullback (modulusCurveMap D ≫ c) t :=
  pullback.congrHom (modulusCurveMap_toBase D).symm rfl

/-- The two modulus inclusions are identified by that same geometric isomorphism. -/
theorem modulusFamilyDomainIso_square {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    modulusFamilyInclusion D t ≫ 𝟙 (pullback c t) =
      (modulusFamilyDomainIso D t).hom ≫ modulusBaseChange c (modulusCurveMap D) t := by
  apply pullback.hom_ext
  · simp only [Category.comp_id, modulusFamilyInclusion, modulusFamilyDomainIso,
      modulusBaseChange, pullback.congrHom_hom, pullback.map, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.comp_id, modulusFamilyInclusion, modulusFamilyDomainIso,
      modulusBaseChange, pullback.congrHom_hom, pullback.map, Category.assoc,
      pullback.lift_snd]

/-- The chosen-rigidified class is preserved under the actual modulus convention change. -/
def modulusFamilyClassEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    RigidifiedLineBundle.Classes (modulusFamilyInclusion D t) ≃
      (modulusPicardPresheaf c (modulusCurveMap D)).obj (op (Over.mk t)) :=
  (RigidifiedLineBundle.classesPullbackEquiv (Iso.refl (pullback c t))
    (modulusFamilyDomainIso D t) (modulusFamilyDomainIso_square D t)).symm

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) {L : (pullback c s).Modules}
  (hL : Scheme.Modules.IsInvertible L)

/-- Intrinsic frame classes determine actual values of the existing modulus Picard functor. -/
def modulusFramePicardClass (T : Over S) :
    (scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T) →
        (modulusPicardPresheaf c (modulusCurveMap D)).obj (op ((Over.map s).obj T)) :=
  modulusFamilyClassEquiv D (T.hom ≫ s) ∘ modulusFrameClass D s hL T

/-- The comparison with the existing Picard functor preserves distinct frame classes. -/
theorem modulusFramePicardClass_injective (T : Over S) :
    Function.Injective (modulusFramePicardClass D s hL T) :=
  (modulusFamilyClassEquiv D (T.hom ≫ s)).injective.comp (modulusFrameClass_injective D s hL T)

end AlgebraicGeometry.GeneralizedJacobian
