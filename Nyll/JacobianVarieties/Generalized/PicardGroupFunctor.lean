/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.PicardFunctor
import Nyll.JacobianVarieties.Generalized.RigidifiedCommutativity
import Nyll.JacobianVarieties.Generalized.RigidifiedPullbackTensor
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Hom.Defs

/-!
# The group-valued modulus Picard presheaf

Tensor product equips naive compatible-isomorphism classes with a commutative group
structure. The actual pullback tensor comparison proves that changes of test scheme
are group homomorphisms. The underlying set presheaf is the chosen-rigidification
presheaf, with no representability or sheaf condition assumed.
-/

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.GeneralizedJacobian

namespace RigidifiedLineBundle

/-- Pullback of chosen rigidifications is a homomorphism for tensor product. -/
def classesPullbackHom {X X' D D' : Scheme.{u}}
    {i : D ⟶ X} {i' : D' ⟶ X'}
    (f : X' ⟶ X) (g : D' ⟶ D) (w : i' ≫ f = g ≫ i) : Classes i →* Classes i' :=
  MonoidHom.mk' (classesPullback f g w) (classesPullback_tensor f g w)

end RigidifiedLineBundle

variable {R : Type u} [CommRing R] {X D : Scheme.{u}}
  (c : X ⟶ Spec (CommRingCat.of R)) (i : D ⟶ X)

/-- The commutative-group-valued presheaf of naive chosen-rigidified line-bundle classes. -/
def modulusPicardGroupPresheaf :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj T := CommGrpCat.of (RigidifiedLineBundle.Classes (modulusBaseChange c i T.unop.hom))
  map {T T'} s := CommGrpCat.ofHom
    (MonoidHom.mk' ((modulusPicardPresheaf c i).map s)
      (fun x y => RigidifiedLineBundle.classesPullback_tensor _ _ _ x y))
  map_id T := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    change ((modulusPicardPresheaf c i).map (𝟙 T)) x = x
    exact ConcreteCategory.congr_hom ((modulusPicardPresheaf c i).map_id T) x
  map_comp s r := by
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    change ((modulusPicardPresheaf c i).map (s ≫ r)) x =
      ((modulusPicardPresheaf c i).map r) (((modulusPicardPresheaf c i).map s) x)
    exact ConcreteCategory.congr_hom ((modulusPicardPresheaf c i).map_comp s r) x

/-- Forgetting tensor product recovers exactly the chosen-rigidification presheaf. -/
theorem modulusPicardGroupPresheaf_forget :
    modulusPicardGroupPresheaf c i ⋙ forget CommGrpCat = modulusPicardPresheaf c i := rfl

end AlgebraicGeometry.GeneralizedJacobian
