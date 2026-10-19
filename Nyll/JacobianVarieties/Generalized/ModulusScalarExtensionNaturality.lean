/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusScalarExtension

/-! # Naturality of scalar extension for the actual modulus Picard groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard AlgebraicGeometry.RelPicard.BaseChange
open AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)
  (R' : Type u) [CommRing R'] [Algebra R R']

@[reassoc] theorem modulusScalarExtensionIso_hom_fst {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) :
    (modulusScalarExtensionIso c i R' t).hom ≫
        pullback.fst (i ≫ c) (t ≫ specMap R R') =
      pullback.fst (modulusBaseChange c i (specMap R R') ≫ baseChange R c R') t ≫
        pullback.fst (i ≫ c) (specMap R R') := by
  simp only [modulusScalarExtensionIso, Iso.trans_hom, Category.assoc, κ_hom_fst,
    pullback.congrHom_hom, pullback.map, pullback.lift_fst_assoc, Category.comp_id]

@[reassoc] theorem modulusScalarExtensionIso_hom_snd {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) :
    (modulusScalarExtensionIso c i R' t).hom ≫
        pullback.snd (i ≫ c) (t ≫ specMap R R') =
      pullback.snd (modulusBaseChange c i (specMap R R') ≫ baseChange R c R') t := by
  simp only [modulusScalarExtensionIso, Iso.trans_hom, Category.assoc, κ_hom_snd,
    pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The full modulus comparison commutes with every parameter restriction. -/
theorem modulusScalarExtensionIso_hom_naturality {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R')} {t' : T' ⟶ Spec (CommRingCat.of R')}
    (ψ : SchemeHomOver t' t) :
    baseChangeSnd (modulusBaseChange c i (specMap R R') ≫ baseChange R c R') ψ ≫
        (modulusScalarExtensionIso c i R' t).hom =
      (modulusScalarExtensionIso c i R' t').hom ≫ baseChangeSnd (i ≫ c) (overR R' ψ) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, modulusScalarExtensionIso_hom_fst,
      baseChangeSnd, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
  · simp only [Category.assoc, modulusScalarExtensionIso_hom_snd,
      baseChangeSnd, pullback.lift_snd, modulusScalarExtensionIso_hom_snd_assoc]
    rfl

theorem modulusScalarExtensionIso_inv_naturality {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R')} {t' : T' ⟶ Spec (CommRingCat.of R')}
    (ψ : SchemeHomOver t' t) :
    baseChangeSnd (i ≫ c) (overR R' ψ) ≫ (modulusScalarExtensionIso c i R' t).inv =
      (modulusScalarExtensionIso c i R' t').inv ≫
        baseChangeSnd (modulusBaseChange c i (specMap R R') ≫ baseChange R c R') ψ := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← modulusScalarExtensionIso_hom_naturality,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Scalar extension transports the actual tensor classes naturally on all test schemes. -/
theorem scalarExtensionClassesEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of R'))} (f : T' ⟶ T)
    (x : (modulusPicardGroupPresheaf (baseChange R c R')
      (modulusBaseChange c i (specMap R R'))).obj (op T)) :
    scalarExtensionClassesEquiv c i R' T'.hom
        ((modulusPicardGroupPresheaf (baseChange R c R')
          (modulusBaseChange c i (specMap R R'))).map f.op x) =
      (modulusPicardGroupPresheaf c i).map ((Over.map (specMap R R')).map f).op
        (scalarExtensionClassesEquiv c i R' T.hom x) := by
  change RigidifiedLineBundle.Classes
    (modulusBaseChange (baseChange R c R') (modulusBaseChange c i (specMap R R')) T.hom) at x
  let ψ : SchemeHomOver T'.hom T.hom := ⟨f.left, f.w⟩
  change RigidifiedLineBundle.classesPullback (κ c R' T'.hom).inv
      (modulusScalarExtensionIso c i R' T'.hom).inv
      (RigidifiedLineBundle.inverse_square _ _ (modulusScalarExtension_square c i R' T'.hom))
      (RigidifiedLineBundle.classesPullback (baseChangeSnd (baseChange R c R') ψ)
        (baseChangeSnd (modulusBaseChange c i (specMap R R') ≫ baseChange R c R') ψ)
        (modulusBaseChange_naturality (baseChange R c R')
          (modulusBaseChange c i (specMap R R')) ψ) x) =
    RigidifiedLineBundle.classesPullback (baseChangeSnd c (overR R' ψ))
      (baseChangeSnd (i ≫ c) (overR R' ψ)) (modulusBaseChange_naturality c i (overR R' ψ))
      (RigidifiedLineBundle.classesPullback (κ c R' T.hom).inv
        (modulusScalarExtensionIso c i R' T.hom).inv
        (RigidifiedLineBundle.inverse_square _ _ (modulusScalarExtension_square c i R' T.hom)) x)
  rw [RigidifiedLineBundle.classesPullback_comp, RigidifiedLineBundle.classesPullback_comp]
  simp only [← baseChangeSnd_κ_inv, ← modulusScalarExtensionIso_inv_naturality]

/-- The actual group presheaves agree after scalar extension, before sheafification. -/
def modulusPicardGroupScalarExtensionIso :
    modulusPicardGroupPresheaf (baseChange R c R') (modulusBaseChange c i (specMap R R')) ≅
      (Over.map (specMap R R')).op ⋙ modulusPicardGroupPresheaf c i :=
  NatIso.ofComponents (fun T => (scalarExtensionClassesEquiv c i R' T.unop.hom).toCommGrpIso)
    (fun f => by
      refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
      exact scalarExtensionClassesEquiv_naturality c i R' f.unop x)

/-- Restricting the same multiplicative equivalence to the actual geometric-fibre zero classes. -/
def scalarExtensionZeroClassesEquiv (T : Over (Spec (CommRingCat.of R'))) :
    (modulusPicardZeroGroupPresheaf (baseChange R c R')
      (modulusBaseChange c i (specMap R R'))).obj (op T) ≃*
    (modulusPicardZeroGroupPresheaf c i).obj (op ((Over.map (specMap R R')).obj T)) where
  toFun x := ⟨scalarExtensionClassesEquiv c i R' T.hom x.val,
    (scalarExtensionClassesEquiv_zero_iff c i R' T.hom x.val).mpr x.property⟩
  invFun y := ⟨(scalarExtensionClassesEquiv c i R' T.hom).symm y.val,
    (scalarExtensionClassesEquiv_zero_iff c i R' T.hom _).mp (by
      rw [MulEquiv.apply_symm_apply]
      exact y.property)⟩
  left_inv x := Subtype.ext ((scalarExtensionClassesEquiv c i R' T.hom).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((scalarExtensionClassesEquiv c i R' T.hom).apply_symm_apply y.val)
  map_mul' x y := Subtype.ext ((scalarExtensionClassesEquiv c i R' T.hom).map_mul x.val y.val)

/-- The Picard-zero group presheaf base-change comparison is the restriction of the same map. -/
def modulusPicardZeroGroupScalarExtensionIso :
    modulusPicardZeroGroupPresheaf (baseChange R c R')
        (modulusBaseChange c i (specMap R R')) ≅
      (Over.map (specMap R R')).op ⋙ modulusPicardZeroGroupPresheaf c i :=
  NatIso.ofComponents (fun T => (scalarExtensionZeroClassesEquiv c i R' T.unop).toCommGrpIso)
    (fun f => by
      refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
      apply Subtype.ext
      exact scalarExtensionClassesEquiv_naturality c i R' f.unop x.val)

end AlgebraicGeometry.GeneralizedJacobian
