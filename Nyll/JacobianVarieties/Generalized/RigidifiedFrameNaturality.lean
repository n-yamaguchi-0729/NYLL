/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.FixedBundleFrames
import Nyll.JacobianVarieties.Generalized.FrameFunctor

/-!
# Naturality of rigidifications constructed from actual restriction frames

The canonical module comparison preserves the chosen frame when commuting
curve-modulus squares are pasted. This statement retains both the underlying
line bundle and the compatibility of its trivialization.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X D : Scheme.{u}} (i : D ⟶ X) {M : X.Modules}
  (hM : Scheme.Modules.IsInvertible M)

/-- A frame of the restricted family supplies an actual chosen rigidification. -/
def fromRestrictionFrame (U : Over X) (V : Over D) (j : V.left ⟶ U.left)
    (w : j ≫ U.hom = V.hom ≫ i)
    (e : (framePresheaf ((Scheme.Modules.pullback i).obj M)).obj (op V)) :
    RigidifiedLineBundle j :=
  withFrame j (hM.pullback U.hom)
    ((restrictionComparison U.hom V.hom w).app M ≪≫ e)

/-- The actual pullback comparison preserves the transported restriction frame. -/
def fromRestrictionFramePullbackIso {U U' : Over X} {V V' : Over D}
    (j : V.left ⟶ U.left) (j' : V'.left ⟶ U'.left)
    (w : j ≫ U.hom = V.hom ≫ i) (w' : j' ≫ U'.hom = V'.hom ≫ i)
    (f : U' ⟶ U) (g : V' ⟶ V) (h : j' ≫ f.left = g.left ≫ j)
    (e : (framePresheaf ((Scheme.Modules.pullback i).obj M)).obj (op V)) :
    Iso ((fromRestrictionFrame i hM U V j w e).pullback f.left g.left h)
      (fromRestrictionFrame i hM U' V' j' w'
        (frameMap ((Scheme.Modules.pullback i).obj M) g e)) where
  toIso := frameComparison M f
  compatible := by
    have hp := Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
      f.left U.hom U'.hom f.w j' j i g.left V.hom V'.hom g.w h w w' M
    change (restrictionComparison f.left g.left h).hom.app
        ((Scheme.Modules.pullback U.hom).obj M) ≫
          (Scheme.Modules.pullback g.left).map
            ((restrictionComparison U.hom V.hom w).hom.app M) ≫
          (frameComparison ((Scheme.Modules.pullback i).obj M) g).hom =
        (Scheme.Modules.pullback j').map (frameComparison M f).hom ≫
          (restrictionComparison U'.hom V'.hom w').hom.app M at hp
    change (Scheme.Modules.pullback j').map (frameComparison M f).hom ≫
        (restrictionComparison U'.hom V'.hom w').hom.app M ≫
          (frameMap ((Scheme.Modules.pullback i).obj M) g e).hom =
        (restrictionComparison f.left g.left h).hom.app
          ((Scheme.Modules.pullback U.hom).obj M) ≫
          (Scheme.Modules.pullback g.left).map
            ((restrictionComparison U.hom V.hom w).hom.app M ≫ e.hom) ≫
          (Scheme.Modules.pullbackTensorUnitObjIso g.left).hom
    rw [← Category.assoc, ← hp]
    simp only [Category.assoc, Functor.map_comp]
    exact congrArg
      (fun z => (restrictionComparison f.left g.left h).hom.app
        ((Scheme.Modules.pullback U.hom).obj M) ≫
          (Scheme.Modules.pullback g.left).map
            ((restrictionComparison U.hom V.hom w).hom.app M) ≫ z)
      (frameMap_fac ((Scheme.Modules.pullback i).obj M) (T := V) (T' := V') g e)

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
