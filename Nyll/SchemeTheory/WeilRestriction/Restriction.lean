/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Yoneda

/-!
# Restricting local relative representers

If a presheaf on schemes over `S` is represented after restriction to schemes
over `X`, then its restriction along `Y ⟶ X ⟶ S` is represented by the pullback
of that local representer to `Y`. This transfers local representers to refinements
of a cover.
-/


@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u w

namespace SchemeTheory.WeilRestriction

/-- Restriction to a new base is represented by the actual pullback, in any value universe. -/
def representableByBaseChange {S X : Scheme.{u}} (f : X ⟶ S)
    {F : (Over S)ᵒᵖ ⥤ Type w} {W : Over S} (h : F.RepresentableBy W) :
    ((Over.map f).op ⋙ F).RepresentableBy ((Over.pullback f).obj W) where
  homEquiv {T} := ((Over.mapPullbackAdj f).homEquiv T W).symm.trans h.homEquiv
  homEquiv_comp a b := by
    change h.homEquiv (((Over.mapPullbackAdj f).homEquiv _ W).symm (a ≫ b)) = _
    rw [(Over.mapPullbackAdj f).homEquiv_naturality_left_symm, h.homEquiv_comp]
    rfl

/-- Restriction along a composite is represented by the pullback of a local representer. -/
def representableByRestrictionBaseChange {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    (F : (Over S)ᵒᵖ ⥤ Type w) (W : Over X)
    (h : ((Over.map f).op ⋙ F).RepresentableBy W) :
    ((Over.map (g ≫ f)).op ⋙ F).RepresentableBy ((Over.pullback g).obj W) :=
  (representableByBaseChange g h).ofIso <|
      (Functor.associator (Over.map g).op (Over.map f).op F).symm.trans <|
        Functor.isoWhiskerRight (NatIso.op (Over.mapComp g f)) F

end SchemeTheory.WeilRestriction
