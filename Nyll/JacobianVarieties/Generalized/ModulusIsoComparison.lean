/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusScalarExtension

/-! # Modulus comparison along an actual isomorphism over the curve -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D D' : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) {i : D ⟶ C} {i' : D' ⟶ C}
  (a : D' ≅ D) (w : i' = a.hom ≫ i)

/-- The same whole modulus isomorphism on every test scheme. -/
def modulusIsoPullback {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback (i' ≫ c) t ≅ pullback (i ≫ c) t where
  hom := pullback.lift (pullback.fst (i' ≫ c) t ≫ a.hom)
    (pullback.snd (i' ≫ c) t) (by
      rw [Category.assoc, ← Category.assoc a.hom i c, ← w, pullback.condition])
  inv := pullback.lift (pullback.fst (i ≫ c) t ≫ a.inv)
    (pullback.snd (i ≫ c) t) (by
      simp only [w, Category.assoc, a.inv_hom_id_assoc, pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        a.hom_inv_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        a.inv_hom_id, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]

theorem modulusIsoPullback_square {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    modulusBaseChange c i' t ≫ 𝟙 _ =
      (modulusIsoPullback c a w t).hom ≫ modulusBaseChange c i t := by
  apply pullback.hom_ext
  · simp only [Category.comp_id, Category.assoc, modulusBaseChange_fst,
      modulusIsoPullback, pullback.lift_fst_assoc, w]
  · simp only [Category.comp_id, Category.assoc, modulusBaseChange_snd,
      modulusIsoPullback, pullback.lift_snd]

theorem modulusIsoPullback_naturality {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (f : SchemeHomOver t' t) :
    baseChangeSnd (i' ≫ c) f ≫ (modulusIsoPullback c a w t).hom =
      (modulusIsoPullback c a w t').hom ≫ baseChangeSnd (i ≫ c) f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, modulusIsoPullback, baseChangeSnd,
      pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Category.assoc, modulusIsoPullback, baseChangeSnd,
      pullback.lift_snd, pullback.lift_snd_assoc]

/-- An isomorphism of the whole modulus preserves the actual chosen trivialization. -/
def modulusIsoClassesEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    RigidifiedLineBundle.Classes (modulusBaseChange c i t) ≃*
      RigidifiedLineBundle.Classes (modulusBaseChange c i' t) :=
  RigidifiedLineBundle.classesPullbackMulEquiv (Iso.refl _) (modulusIsoPullback c a w t)
    (modulusIsoPullback_square c a w t)

/-- The underlying relative line-bundle class is unchanged. -/
theorem modulusIsoClassesEquiv_forget {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t)) :
    forgetModulusClasses c i' t (modulusIsoClassesEquiv c a w t x) =
      forgetModulusClasses c i t x := by
  induction x using Quotient.ind with
  | _ M => exact Quot.sound (Unrigidified.baseTwist_of_iso
      ((Scheme.Modules.pullbackId _).app M.L))

theorem modulusIsoClassesEquiv_zero_iff {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (x : RigidifiedLineBundle.Classes (modulusBaseChange c i t)) :
    modulusIsoClassesEquiv c a w t x ∈ (modulusPicardZeroSubfunctor c i').obj (op (Over.mk t)) ↔
      x ∈ (modulusPicardZeroSubfunctor c i).obj (op (Over.mk t)) := by
  change Unrigidified.classesZero t (forgetModulusClasses c i' t _) ↔
    Unrigidified.classesZero t (forgetModulusClasses c i t _)
  rw [modulusIsoClassesEquiv_forget]

/-- This equivalence commutes with every change of parameter. -/
theorem modulusIsoClassesEquiv_naturality {T T' : Over (Spec (CommRingCat.of R))}
    (f : T' ⟶ T) (x : (modulusPicardGroupPresheaf c i).obj (op T)) :
    modulusIsoClassesEquiv c a w T'.hom ((modulusPicardGroupPresheaf c i).map f.op x) =
      (modulusPicardGroupPresheaf c i').map f.op (modulusIsoClassesEquiv c a w T.hom x) := by
  change RigidifiedLineBundle.Classes (modulusBaseChange c i T.hom) at x
  let ψ : SchemeHomOver T'.hom T.hom := ⟨f.left, f.w⟩
  change RigidifiedLineBundle.classesPullback (𝟙 _) (modulusIsoPullback c a w T'.hom).hom
      (modulusIsoPullback_square c a w T'.hom)
      (RigidifiedLineBundle.classesPullback (baseChangeSnd c ψ) (baseChangeSnd (i ≫ c) ψ)
        (modulusBaseChange_naturality c i ψ) x) =
    RigidifiedLineBundle.classesPullback (baseChangeSnd c ψ) (baseChangeSnd (i' ≫ c) ψ)
      (modulusBaseChange_naturality c i' ψ)
      (RigidifiedLineBundle.classesPullback (𝟙 _) (modulusIsoPullback c a w T.hom).hom
        (modulusIsoPullback_square c a w T.hom) x)
  rw [RigidifiedLineBundle.classesPullback_comp, RigidifiedLineBundle.classesPullback_comp]
  simp only [Category.id_comp, Category.comp_id, modulusIsoPullback_naturality]

end AlgebraicGeometry.GeneralizedJacobian
