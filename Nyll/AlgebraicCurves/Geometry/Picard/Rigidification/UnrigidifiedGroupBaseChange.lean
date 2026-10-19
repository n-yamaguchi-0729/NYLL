/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedBaseChange
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.UnrigidifiedGroup

/-! # Scalar extension of the actual unrigidified Picard-zero group presheaf -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.RelPicard.BaseChange

namespace AlgebraicGeometry.RelPicard.Unrigidified

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R']

/-- The actual pullback-pasting equivalence preserves tensor products of relative zero classes. -/
def zeroBaseChangeMulEquiv (T : Over (Spec (CommRingCat.of R'))) :
    (zeroCommGrpPresheaf (baseChange R c R')).obj (op T) ≃*
      (zeroCommGrpPresheaf c).obj (op ((Over.map (specMap R R')).obj T)) where
  toEquiv := zeroBaseChangeClassesEquiv c R' T.hom
  map_mul' x y := by
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    apply Subtype.ext
    induction x using Quot.ind with
    | _ M =>
      induction y using Quot.ind with
      | _ N =>
        exact Quot.sound (baseTwist_of_iso
          (Scheme.Modules.pullbackTensorObjIso (κ c R' T.hom).inv M.val N.val))

/-- Scalar extension is an isomorphism of the actual ordinary group presheaves. -/
def zeroCommGrpBaseChangeIso :
    zeroCommGrpPresheaf (baseChange R c R') ≅
      (Over.map (specMap R R')).op ⋙ zeroCommGrpPresheaf c :=
  NatIso.ofComponents (fun T => (zeroBaseChangeMulEquiv c R' T.unop).toCommGrpIso)
    (fun f => by
      refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
      exact ConcreteCategory.congr_hom ((zeroBaseChangeIso c R').hom.naturality f) x)

end AlgebraicGeometry.RelPicard.Unrigidified
