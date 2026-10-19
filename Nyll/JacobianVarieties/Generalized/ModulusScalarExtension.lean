/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedSquareEquivalence
import Nyll.JacobianVarieties.Generalized.PicardZeroGroupFunctor
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedBaseChange

/-! # Actual modulus classes under scalar extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.RelPicard.BaseChange AlgebraicGeometry.SmoothProperCurve

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)

/-- The base-changed modulus retains its actual projection to the parameter. -/
@[reassoc] theorem modulusBaseChange_snd {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    modulusBaseChange c i t ≫ pullback.snd c t = pullback.snd (i ≫ c) t := by
  simp only [modulusBaseChange, pullback.map, pullback.lift_snd, Category.comp_id]

@[reassoc] theorem modulusBaseChange_fst {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    modulusBaseChange c i t ≫ pullback.fst c t = pullback.fst (i ≫ c) t ≫ i := by
  simp only [modulusBaseChange, pullback.map, pullback.lift_fst]

variable (R' : Type u) [CommRing R'] [Algebra R R']

/-- The full iterated modulus pullback agrees with the composite pullback. -/
def modulusScalarExtensionIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    pullback (modulusBaseChange c i (specMap R R') ≫ baseChange R c R') t ≅
      pullback (i ≫ c) (t ≫ specMap R R') :=
  pullback.congrHom (modulusBaseChange_snd c i (specMap R R')) rfl ≪≫ κ (i ≫ c) R' t

/-- The canonical isomorphisms preserve the actual inclusion of the entire modulus. -/
theorem modulusScalarExtension_square {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R')) :
    modulusBaseChange (baseChange R c R') (modulusBaseChange c i (specMap R R')) t ≫
        (κ c R' t).hom =
      (modulusScalarExtensionIso c i R' t).hom ≫
        modulusBaseChange c i (t ≫ specMap R R') := by
  apply pullback.hom_ext
  · simp only [Category.assoc, κ_hom_fst,
      reassoc_of% κ_hom_fst (i ≫ c) R' t, modulusBaseChange_fst_assoc,
      modulusBaseChange_fst, modulusScalarExtensionIso, Iso.trans_hom,
      pullback.congrHom_hom, pullback.map, pullback.lift_fst_assoc,
      Category.comp_id]
  · simp only [Category.assoc, κ_hom_snd, modulusBaseChange_snd,
      modulusScalarExtensionIso, Iso.trans_hom, pullback.congrHom_hom,
      pullback.map, pullback.lift_snd, Category.comp_id]

/-- Transport preserves tensor classes and their chosen modulus trivializations. -/
def scalarExtensionClassesEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) :
    RigidifiedLineBundle.Classes
        (modulusBaseChange (baseChange R c R') (modulusBaseChange c i (specMap R R')) t) ≃*
      RigidifiedLineBundle.Classes (modulusBaseChange c i (t ≫ specMap R R')) :=
  RigidifiedLineBundle.classesPullbackMulEquiv (κ c R' t).symm
    (modulusScalarExtensionIso c i R' t).symm
    (RigidifiedLineBundle.inverse_square (κ c R' t) (modulusScalarExtensionIso c i R' t)
      (modulusScalarExtension_square c i R' t))

/-- The actual scalar-extension equivalence preserves geometric-fibre Picard-zero. -/
theorem scalarExtensionClassesEquiv_zero_iff {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R'))
    (x : RigidifiedLineBundle.Classes
      (modulusBaseChange (baseChange R c R') (modulusBaseChange c i (specMap R R')) t)) :
    scalarExtensionClassesEquiv c i R' t x ∈
        (modulusPicardZeroSubfunctor c i).obj (op (Over.mk (t ≫ specMap R R'))) ↔
      x ∈ (modulusPicardZeroSubfunctor (baseChange R c R')
        (modulusBaseChange c i (specMap R R'))).obj (op (Over.mk t)) := by
  induction x using Quotient.ind with
  | _ M =>
    exact RelPicard.Unrigidified.fibrewiseZero_restrict_iff c R' ⟨M.L, M.isInvertible⟩

end AlgebraicGeometry.GeneralizedJacobian
