/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusScalarExtension
import Nyll.JacobianVarieties.Generalized.PicardGroupFunctor
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupFunctor
import Nyll.JacobianVarieties.Generalized.RigidifiedPullback

/-! # Restricting an actual modulus rigidification

A commuting morphism of whole moduli pulls back the chosen trivialization,
leaves the underlying line-bundle class unchanged, and preserves tensor product.
No inverse to the modulus morphism is needed.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  (j : D' ⟶ D) (w : i' = j ≫ i)

/-- The given morphism of whole moduli on every test scheme. -/
def modulusRestrictionPullback {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback (i' ≫ c) t ⟶ pullback (i ≫ c) t :=
  pullback.lift (pullback.fst (i' ≫ c) t ≫ j) (pullback.snd (i' ≫ c) t) (by
    rw [Category.assoc, ← Category.assoc j i c, ← w, pullback.condition])

theorem modulusRestrictionPullback_square {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    modulusBaseChange c i' t ≫ 𝟙 _ =
      modulusRestrictionPullback c j w t ≫ modulusBaseChange c i t := by
  apply pullback.hom_ext
  · simp only [Category.comp_id, Category.assoc, modulusBaseChange_fst,
      modulusRestrictionPullback, pullback.lift_fst_assoc, w]
  · simp only [Category.comp_id, Category.assoc, modulusBaseChange_snd,
      modulusRestrictionPullback, pullback.lift_snd]

theorem modulusRestrictionPullback_naturality {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (f : SchemeHomOver t' t) :
    baseChangeSnd (i' ≫ c) f ≫ modulusRestrictionPullback c j w t =
      modulusRestrictionPullback c j w t' ≫ baseChangeSnd (i ≫ c) f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, modulusRestrictionPullback, baseChangeSnd,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Category.assoc, modulusRestrictionPullback, baseChangeSnd,
      pullback.lift_snd, pullback.lift_snd_assoc]

theorem modulusRestrictionPullback_id {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    modulusRestrictionPullback c (𝟙 D) (Category.id_comp i).symm t = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [modulusRestrictionPullback, pullback.lift_fst, Category.comp_id,
      Category.id_comp]
  · simp only [modulusRestrictionPullback, pullback.lift_snd, Category.id_comp]

theorem modulusRestrictionPullback_comp {D'' : Scheme.{u}} {i'' : D'' ⟶ C}
    (k : D'' ⟶ D') (w' : i'' = k ≫ i') {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    modulusRestrictionPullback c k w' t ≫ modulusRestrictionPullback c j w t =
      modulusRestrictionPullback c (k ≫ j)
        (by rw [w', w, Category.assoc]) t := by
  apply pullback.hom_ext
  · simp only [modulusRestrictionPullback, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc]
  · simp only [modulusRestrictionPullback, Category.assoc, pullback.lift_snd]

/-- Restriction of chosen trivializations is a tensor-product homomorphism. -/
def modulusRestrictionClasses {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    RigidifiedLineBundle.Classes (modulusBaseChange c i t) →*
      RigidifiedLineBundle.Classes (modulusBaseChange c i' t) :=
  RigidifiedLineBundle.classesPullbackHom (𝟙 _) (modulusRestrictionPullback c j w t)
    (modulusRestrictionPullback_square c j w t)

/-- Restriction leaves the relative line-bundle class unchanged. -/
theorem modulusRestrictionClasses_forget {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t)) :
    forgetModulusClasses c i' t (modulusRestrictionClasses c j w t x) =
      forgetModulusClasses c i t x := by
  induction x using Quotient.ind with
  | _ M => exact Quot.sound (Unrigidified.baseTwist_of_iso
      ((Scheme.Modules.pullbackId _).app M.L))

theorem modulusRestrictionClasses_zero_iff {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t)) :
    modulusRestrictionClasses c j w t x ∈
        (modulusPicardZeroSubfunctor c i').obj (op (Over.mk t)) ↔
      x ∈ (modulusPicardZeroSubfunctor c i).obj (op (Over.mk t)) := by
  change Unrigidified.classesZero t (forgetModulusClasses c i' t _) ↔
    Unrigidified.classesZero t (forgetModulusClasses c i t _)
  rw [modulusRestrictionClasses_forget]

theorem modulusRestrictionClasses_naturality {T T' : Over (Spec (CommRingCat.of R))}
    (f : T' ⟶ T) (x : (modulusPicardGroupPresheaf c i).obj (op T)) :
    modulusRestrictionClasses c j w T'.hom ((modulusPicardGroupPresheaf c i).map f.op x) =
      (modulusPicardGroupPresheaf c i').map f.op (modulusRestrictionClasses c j w T.hom x) := by
  change RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) at x
  let ψ : SchemeHomOver T'.hom T.hom := ⟨f.left, f.w⟩
  change RigidifiedLineBundle.classesPullback (𝟙 _) (modulusRestrictionPullback c j w T'.hom)
      (modulusRestrictionPullback_square c j w T'.hom)
      (RigidifiedLineBundle.classesPullback (baseChangeSnd c ψ) (baseChangeSnd (i ≫ c) ψ)
        (modulusBaseChange_naturality c i ψ) x) =
    RigidifiedLineBundle.classesPullback (baseChangeSnd c ψ) (baseChangeSnd (i' ≫ c) ψ)
      (modulusBaseChange_naturality c i' ψ)
      (RigidifiedLineBundle.classesPullback (𝟙 _) (modulusRestrictionPullback c j w T.hom)
        (modulusRestrictionPullback_square c j w T.hom) x)
  rw [RigidifiedLineBundle.classesPullback_comp, RigidifiedLineBundle.classesPullback_comp]
  simp only [Category.id_comp, Category.comp_id, modulusRestrictionPullback_naturality]

theorem modulusRestrictionClasses_id {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t)) :
    modulusRestrictionClasses c (𝟙 D) (Category.id_comp i).symm t x = x := by
  change RigidifiedLineBundle.classesPullback (𝟙 _)
    (modulusRestrictionPullback c (𝟙 D) (Category.id_comp i).symm t) _ x = x
  simp only [modulusRestrictionPullback_id, RigidifiedLineBundle.classesPullback_id]

theorem modulusRestrictionClasses_comp {D'' : Scheme.{u}} {i'' : D'' ⟶ C}
    (k : D'' ⟶ D') (w' : i'' = k ≫ i') {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t)) :
    modulusRestrictionClasses c k w' t (modulusRestrictionClasses c j w t x) =
      modulusRestrictionClasses c (k ≫ j) (by rw [w', w, Category.assoc]) t x := by
  change RigidifiedLineBundle.classesPullback (𝟙 _) (modulusRestrictionPullback c k w' t) _
      (RigidifiedLineBundle.classesPullback (𝟙 _) (modulusRestrictionPullback c j w t) _ x) = _
  rw [RigidifiedLineBundle.classesPullback_comp]
  simp only [Category.id_comp, modulusRestrictionPullback_comp]
  rfl

end AlgebraicGeometry.GeneralizedJacobian
