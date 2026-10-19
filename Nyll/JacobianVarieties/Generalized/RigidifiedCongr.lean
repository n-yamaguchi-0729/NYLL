/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.RigidifiedPullback

/-! Actual isomorphic curve-modulus diagrams have equivalent chosen-rigidified classes. -/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle

variable {X X' D D' : Scheme.{u}} {i : D ⟶ X} {i' : D' ⟶ X'}

/-- Equal morphisms of actual modulus diagrams induce the same pullback of classes. -/
theorem classesPullback_congr {f f' : X' ⟶ X} {g g' : D' ⟶ D}
    (hf : f = f') (hg : g = g') (w : i' ≫ f = g ≫ i) (w' : i' ≫ f' = g' ≫ i)
    (x : Classes i) : classesPullback f g w x = classesPullback f' g' w' x := by
  cases hf
  cases hg
  rfl

/-- The inverse of an actual commuting isomorphism square still commutes. -/
theorem inverse_square (f : X' ≅ X) (g : D' ≅ D) (w : i' ≫ f.hom = g.hom ≫ i) :
    i ≫ f.inv = g.inv ≫ i' := by
  apply (cancel_mono f.hom).mp
  simp only [Category.assoc, f.inv_hom_id, Category.comp_id]
  rw [w, g.inv_hom_id_assoc]

/-- Pullback along an actual isomorphism square preserves the entire rigidified class. -/
def classesPullbackEquiv (f : X' ≅ X) (g : D' ≅ D) (w : i' ≫ f.hom = g.hom ≫ i) :
    Classes i ≃ Classes i' where
  toFun := classesPullback f.hom g.hom w
  invFun := classesPullback f.inv g.inv (inverse_square f g w)
  left_inv x := by
    have h := classesPullback_comp f.hom g.hom w f.inv g.inv (inverse_square f g w) x
    simpa only [f.inv_hom_id, g.inv_hom_id, classesPullback_id] using h
  right_inv x := by
    have h := classesPullback_comp f.inv g.inv (inverse_square f g w) f.hom g.hom w x
    simpa only [f.hom_inv_id, g.hom_inv_id, classesPullback_id] using h

end AlgebraicGeometry.GeneralizedJacobian.RigidifiedLineBundle
