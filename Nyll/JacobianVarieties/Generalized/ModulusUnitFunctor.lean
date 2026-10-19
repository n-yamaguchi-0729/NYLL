/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusFrameFunctor
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Units of the actual base-changed modulus modulo parameter scalars

The values are global units on the actual scheme fibre product, rather than
on an assumed tensor-algebra model. The scalar subgroup is the image of the
actual projection to the test scheme. Its quotient is functorial on all tests.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

variable {Y S : Scheme.{u}} (q : Y ⟶ S)

/-- Actual units on the base-changed modulus. -/
abbrev ModulusUnits (T : Over S) := Γ(((Over.pullback q).obj T).left, ⊤)ˣ

/-- The image of the test scheme's scalar units. -/
def modulusScalars (T : Over S) : Subgroup (ModulusUnits q T) :=
  (Units.map (modulusProjection q T).appTop.hom.toMonoidHom).range

/-- Pullback of actual modulus units along a parameter morphism. -/
def modulusUnitMap {T T' : Over S} (f : T' ⟶ T) :
    ModulusUnits q T →* ModulusUnits q T' :=
  Units.map ((Over.pullback q).map f).left.appTop.hom.toMonoidHom

theorem modulusUnitMap_id (T : Over S) (a : ModulusUnits q T) :
    modulusUnitMap q (𝟙 T) a = a := by
  apply Units.ext
  change ((Over.pullback q).map (𝟙 T)).left.appTop (a : Γ(((Over.pullback q).obj T).left, ⊤)) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem modulusUnitMap_comp {T T' T'' : Over S} (f : T' ⟶ T) (g : T'' ⟶ T')
    (a : ModulusUnits q T) :
    modulusUnitMap q (g ≫ f) a = modulusUnitMap q g (modulusUnitMap q f a) := by
  apply Units.ext
  change ((Over.pullback q).map (g ≫ f)).left.appTop (a : Γ(((Over.pullback q).obj T).left, ⊤)) = _
  rw [CategoryTheory.Functor.map_comp]
  exact congrArg (fun h : Γ(((Over.pullback q).obj T).left, ⊤) ⟶
    Γ(((Over.pullback q).obj T'').left, ⊤) => h (a : Γ(((Over.pullback q).obj T).left, ⊤)))
      (Scheme.Hom.comp_appTop ((Over.pullback q).map g).left
        ((Over.pullback q).map f).left)

theorem modulusUnitMap_scalar {T T' : Over S} (f : T' ⟶ T) (a : Γ(T.left, ⊤)ˣ) :
    modulusUnitMap q f (Units.map (modulusProjection q T).appTop.hom.toMonoidHom a) =
      Units.map (modulusProjection q T').appTop.hom.toMonoidHom
        (Units.map f.left.appTop.hom.toMonoidHom a) := by
  apply scalarUnits_square
  simp only [Over.pullback_map_left, modulusProjection, pullback.lift_fst]

theorem modulusUnitMap_scalars {T T' : Over S} (f : T' ⟶ T) :
    modulusScalars q T ≤ (modulusScalars q T').comap (modulusUnitMap q f) := by
  rintro a ⟨s, rfl⟩
  exact ⟨Units.map f.left.appTop.hom.toMonoidHom s, (modulusUnitMap_scalar q f s).symm⟩

/-- The genuine quotient map on units modulo parameter scalars. -/
def modulusUnitQuotientMap {T T' : Over S} (f : T' ⟶ T) :
    ModulusUnits q T ⧸ modulusScalars q T →* ModulusUnits q T' ⧸ modulusScalars q T' :=
  QuotientGroup.map _ _ (modulusUnitMap q f) (modulusUnitMap_scalars q f)

/-- The group presheaf of actual modulus units modulo base scalars. -/
def modulusUnitQuotientPresheaf : (Over S)ᵒᵖ ⥤ CommGrpCat.{u} where
  obj T := CommGrpCat.of (ModulusUnits q T.unop ⧸ modulusScalars q T.unop)
  map f := CommGrpCat.ofHom (modulusUnitQuotientMap q f.unop)
  map_id T := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      change QuotientGroup.mk (modulusUnitMap q (𝟙 T.unop) a) = QuotientGroup.mk a
      rw [modulusUnitMap_id]
  map_comp f g := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H a =>
      change QuotientGroup.mk (modulusUnitMap q (g.unop ≫ f.unop) a) =
        QuotientGroup.mk (modulusUnitMap q g.unop (modulusUnitMap q f.unop a))
      rw [modulusUnitMap_comp]

end AlgebraicGeometry.GeneralizedJacobian.ScalarFrames
