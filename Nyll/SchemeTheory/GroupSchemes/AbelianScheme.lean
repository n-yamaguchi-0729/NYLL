/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Abelian schemes on actual commutative group schemes

The property belongs to the given group object and its actual structure morphism.
Over a field this is the usual smooth, proper, geometrically connected definition
of an abelian variety. Products and base changes retain their actual scheme carriers.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

variable {S S' : Scheme.{u}}

/-- A commutative group scheme is abelian when its structure morphism is smooth and
proper with geometrically connected fibres. -/
class IsAbelianScheme (G : CommGrp (Over S)) : Prop extends
    Smooth G.X.hom, IsProper G.X.hom, GeometricallyConnected G.X.hom

namespace GroupSchemes

/-- The canonical group pullback, using the product-preserving scheme pullback functor. -/
def baseChange (f : S' ⟶ S) : CommGrp (Over S) ⥤ CommGrp (Over S') where
  obj H :=
    { X := (Over.pullback f).obj H.X
      grp := ((Over.pullback f).mapCommGrp.obj H).grp
      comm := ((Over.pullback f).mapCommGrp.obj H).comm }
  map g := (Over.pullback f).mapCommGrp.map g
  map_id H := (Over.pullback f).mapCommGrp.map_id H
  map_comp g h := (Over.pullback f).mapCommGrp.map_comp g h

/-- The literal-carrier presentation retains the original group pullback functor. -/
theorem baseChange_eq_mapCommGrp (f : S' ⟶ S) :
    baseChange f = (Over.pullback f).mapCommGrp := rfl

/-- The carrier of group base change is the literal fibre product. -/
theorem baseChange_carrier (f : S' ⟶ S) (G : CommGrp (Over S)) :
    ((baseChange f).obj G).X.left = pullback G.X.hom f := rfl

/-- The structure map of group base change is the actual second projection. -/
theorem baseChange_toBase (f : S' ⟶ S) (G : CommGrp (Over S)) :
    ((baseChange f).obj G).X.hom = pullback.snd G.X.hom f := rfl

/-- The product group on the actual fibre product, with componentwise group operations. -/
def product (G H : CommGrp (Over S)) : CommGrp (Over S) :=
  ⟨G.X ⊗ H.X⟩

/-- The product structure map uses the actual first fibre-product projection. -/
theorem product_toBase (G H : CommGrp (Over S)) :
    (product G H).X.hom = pullback.fst G.X.hom H.X.hom ≫ G.X.hom := rfl

/-- Any property stable under base change transports across an isomorphism over the base. -/
theorem property_of_overIso (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {X Y : Over S} (e : X ≅ Y) (h : P X.hom) : P Y.hom := by
  have hs : e.inv.left ≫ X.hom = Y.hom ≫ 𝟙 S := by
    rw [Category.comp_id]
    exact Over.w e.inv
  exact P.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk hs)) h

end GroupSchemes

namespace IsAbelianScheme

variable {G H : CommGrp (Over S)}

/-- Abelianity transports by an actual group-scheme isomorphism. -/
theorem of_iso (e : G ≅ H) [IsAbelianScheme G] : IsAbelianScheme H where
  toSmooth := GroupSchemes.property_of_overIso (@Smooth) ((CommGrp.forget _).mapIso e)
    (inferInstanceAs (Smooth G.X.hom))
  toIsProper := GroupSchemes.property_of_overIso (@IsProper) ((CommGrp.forget _).mapIso e)
    (inferInstanceAs (IsProper G.X.hom))
  toGeometricallyConnected := GroupSchemes.property_of_overIso (@GeometricallyConnected)
    ((CommGrp.forget _).mapIso e) (inferInstanceAs (GeometricallyConnected G.X.hom))

/-- An actual isomorphism preserves and reflects the abelian-scheme property. -/
theorem iso_iff (e : G ≅ H) : IsAbelianScheme G ↔ IsAbelianScheme H :=
  ⟨fun _ => of_iso e, fun _ => of_iso e.symm⟩

/-- Abelian schemes remain abelian under arbitrary scheme base change. -/
instance baseChange (f : S' ⟶ S) [IsAbelianScheme G] :
    IsAbelianScheme ((GroupSchemes.baseChange f).obj G) where
  toSmooth := by
    change Smooth (pullback.snd G.X.hom f)
    infer_instance
  toIsProper := by
    change IsProper (pullback.snd G.X.hom f)
    infer_instance
  toGeometricallyConnected := by
    change GeometricallyConnected (pullback.snd G.X.hom f)
    infer_instance

/-- The componentwise group on a fibre product of abelian schemes is abelian. -/
instance product [IsAbelianScheme G] [IsAbelianScheme H] :
    IsAbelianScheme (GroupSchemes.product G H) where
  toSmooth := by
    change Smooth (pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
    infer_instance
  toIsProper := by
    change IsProper (pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
    infer_instance
  toGeometricallyConnected := by
    change GeometricallyConnected (pullback.fst G.X.hom H.X.hom ≫ G.X.hom)
    exact GeometricallyConnected.comp _ _

end IsAbelianScheme

end AlgebraicGeometry
