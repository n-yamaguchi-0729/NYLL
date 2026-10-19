/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFramePicard
import Nyll.JacobianVarieties.Generalized.ModulusFrameNaturality
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! A natural comparison from actual scalar frames to the existing modulus Picard presheaf. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of K)} {d : ℕ}
  (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of K))))

/-- The isomorphism between the two actual modulus conventions is natural. -/
theorem modulusFamilyDomainIso_naturality {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)}
    (f : SchemeHomOver t' t) :
    (modulusFamilyDomainIso D t').hom ≫ baseChangeSnd (modulusCurveMap D ≫ c) f =
      baseChangeSnd (modulusBaseMap D) f ≫ (modulusFamilyDomainIso D t).hom := by
  apply pullback.hom_ext
  · simp only [modulusFamilyDomainIso, baseChangeSnd, pullback.congrHom_hom, pullback.map,
      Category.assoc, pullback.lift_fst, Category.comp_id]
  · simp only [modulusFamilyDomainIso, baseChangeSnd, pullback.congrHom_hom, pullback.map,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.comp_id]

/-- The inverse convention change preserves the same restriction maps. -/
theorem modulusFamilyDomainIso_inv_naturality {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)}
    (f : SchemeHomOver t' t) :
    baseChangeSnd (modulusCurveMap D ≫ c) f ≫ (modulusFamilyDomainIso D t).inv =
      (modulusFamilyDomainIso D t').inv ≫ baseChangeSnd (modulusBaseMap D) f := by
  apply (cancel_mono (modulusFamilyDomainIso D t).hom).mp
  simp only [Category.assoc, CategoryTheory.Iso.inv_hom_id, Category.comp_id]
  rw [← modulusFamilyDomainIso_naturality D f, CategoryTheory.Iso.inv_hom_id_assoc]

/-- Changing the modulus convention preserves pullback of chosen-rigidified classes. -/
theorem modulusFamilyClassEquiv_naturality {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of K)} {t' : T' ⟶ Spec (CommRingCat.of K)}
    (f : SchemeHomOver t' t) (x : RigidifiedLineBundle.Classes (modulusFamilyInclusion D t)) :
    RigidifiedLineBundle.classesPullback (baseChangeSnd c f)
        (baseChangeSnd (modulusCurveMap D ≫ c) f)
        (modulusBaseChange_naturality c (modulusCurveMap D) f)
        (modulusFamilyClassEquiv D t x) =
      modulusFamilyClassEquiv D t'
        (RigidifiedLineBundle.classesPullback (baseChangeSnd c f)
          (baseChangeSnd (modulusBaseMap D) f) (modulusFamilyInclusion_naturality D f) x) := by
  change RigidifiedLineBundle.classesPullback _ _ _
      (RigidifiedLineBundle.classesPullback (𝟙 _) (modulusFamilyDomainIso D t).inv _ x) =
    RigidifiedLineBundle.classesPullback (𝟙 _) (modulusFamilyDomainIso D t').inv _
      (RigidifiedLineBundle.classesPullback _ _ _ x)
  rw [RigidifiedLineBundle.classesPullback_comp, RigidifiedLineBundle.classesPullback_comp]
  exact RigidifiedLineBundle.classesPullback_congr
    ((Category.comp_id (baseChangeSnd c f)).trans (Category.id_comp (baseChangeSnd c f)).symm)
    (modulusFamilyDomainIso_inv_naturality D f) _ _ x

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) {L : (pullback c s).Modules}
  (hL : Scheme.Modules.IsInvertible L)

/-- The intrinsic frame classification is natural in maps of actual parameter schemes. -/
theorem modulusFramePicardClass_naturality {T T' : Over S} (f : T' ⟶ T)
    (x : (scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
      ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).obj (op T)) :
    (modulusPicardPresheaf c (modulusCurveMap D)).map ((Over.map s).map f).op
        (modulusFramePicardClass D s hL T x) =
      modulusFramePicardClass D s hL T'
        ((scalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
          ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L)).map f.op x) :=
  (modulusFamilyClassEquiv_naturality D (parameterHom s f)
    (modulusFrameClass D s hL T x)).trans
    (congrArg (modulusFamilyClassEquiv D (T'.hom ≫ s))
      (modulusFrameClass_naturality s D hL f x))

/-- The actual scalar-frame presheaf maps naturally to the modulus Picard presheaf. -/
def modulusFramesToPicard :
    liftedScalarFramePresheaf (pullback.snd (modulusBaseMap D) s)
        ((Scheme.Modules.pullback (modulusFamilyInclusion D s)).obj L) ⟶
      (Over.map s).op ⋙ modulusPicardPresheaf c (modulusCurveMap D) where
  app T := TypeCat.ofHom (fun x => modulusFramePicardClass D s hL T.unop x.down)
  naturality {T T'} f := by
    apply TypeCat.homEquiv.injective
    funext x
    exact (modulusFramePicardClass_naturality D s hL f.unop x.down).symm

/-- The natural comparison is injective on every test scheme before sheafification. -/
theorem modulusFramesToPicard_app_injective (T : Over S) :
    Function.Injective ((modulusFramesToPicard D s hL).app (op T)) := by
  intro x y h
  apply ULift.ext
  exact modulusFramePicardClass_injective D s hL T h

/-- No additional frame identifications occur in the modulus Picard presheaf. -/
instance modulusFramesToPicard_mono : Mono (modulusFramesToPicard D s hL) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  exact (CategoryTheory.mono_iff_injective _).mpr
    (modulusFramesToPicard_app_injective D s hL T.unop)

end AlgebraicGeometry.GeneralizedJacobian
