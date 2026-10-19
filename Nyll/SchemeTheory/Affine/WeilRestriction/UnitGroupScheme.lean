/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.UnitNormPolynomial
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# The smooth affine commutative group of units of a finite free algebra

The actual tensor-algebra units form a commutative-group-valued functor.
Its proven norm-open corepresentation gives a commutative group object
in opposite algebras. The product-preserving spectrum functor transports
this group to the same smooth affine norm open over the coefficient ring.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Module
open scoped TensorProduct

universe u

namespace SchemeTheory.Affine.UnitGroupScheme

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- Units, with their actual multiplication, as a commutative group functor. -/
def unitsCommGroupFunctor : CommAlgCat R ⥤ CommGrpCat.{u} where
  obj C := CommGrpCat.of Cˣ
  map f := CommGrpCat.ofHom (Units.map f.hom.toRingHom.toMonoidHom)
  map_id C := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Units.ext
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    apply Units.ext
    rfl

/-- The group functor of units after scalar extension of the given algebra. -/
def tensorUnitsCommGroupFunctor : CommAlgCat R ⥤ CommGrpCat.{u} :=
  tensorRightAlg (R := R) (A := A) ⋙ unitsCommGroupFunctor R

/-- The same group functor as a presheaf on opposite algebras. -/
def tensorUnitsCommGroupPresheaf : ((CommAlgCat R)ᵒᵖ)ᵒᵖ ⥤ CommGrpCat.{u} :=
  (opOpEquivalence (CommAlgCat R)).functor ⋙ tensorUnitsCommGroupFunctor R A

variable {R A} {m : ℕ} (b : Basis (Fin m) R A)

/-- The explicit norm algebra represents the group-valued units functor
after forgetting its group structure. -/
def normUnitsRepresentable :
    (tensorUnitsCommGroupPresheaf R A ⋙ forget CommGrpCat).RepresentableBy
      (op (CommAlgCat.of R (UnitNormPolynomial.CoordinateRing b))) where
  homEquiv {_} :=
    { toFun := fun f => UnitNormPolynomial.homEquivUnits b f.unop.hom
      invFun := fun a => (CommAlgCat.ofHom (UnitNormPolynomial.unitToHom b a)).op
      left_inv := fun f => by
        apply Quiver.Hom.unop_inj
        exact CommAlgCat.hom_ext (UnitNormPolynomial.unitToHom_homToUnit b f.unop.hom)
      right_inv := UnitNormPolynomial.homToUnit_unitToHom b }
  homEquiv_comp f g := UnitNormPolynomial.homEquivUnits_comp b g.unop.hom f.unop.hom

/-- The actual norm coordinate algebra, viewed oppositely, is a
commutative group object through its classification of tensor units. -/
def normUnitsCommGroup : CommGrp ((CommAlgCat R)ᵒᵖ) := by
  let : CommGrpObj (op (CommAlgCat.of R (UnitNormPolynomial.CoordinateRing b))) :=
    CommGrpObj.ofRepresentableBy _ (tensorUnitsCommGroupPresheaf R A) (normUnitsRepresentable b)
  exact ⟨op (CommAlgCat.of R (UnitNormPolynomial.CoordinateRing b))⟩

/-- The smooth affine commutative group scheme of units of the finite free
algebra. Its carrier is the determinant open already constructed explicitly. -/
def unitCommGroupScheme : CommGrp (Over (Spec (CommRingCat.of R))) := by
  let F : (CommAlgCat.{u} R)ᵒᵖ ⥤ Over (Spec (CommRingCat.of R)) :=
    AlgebraicGeometry.algSpec (CommRingCat.of R)
  let : F.Braided := AlgebraicGeometry.braidedAlgSpec (R := CommRingCat.of R)
  exact F.mapCommGrp.obj (normUnitsCommGroup b)

theorem unitCommGroupScheme_carrier :
    (unitCommGroupScheme b).X.left = UnitNormPolynomial.unitOpen b := rfl

theorem unitCommGroupScheme_toBase :
    (unitCommGroupScheme b).X.hom = UnitNormPolynomial.unitOpenToBase b := rfl

/-- Smoothness belongs to the constructed group scheme, with the same
carrier and structure morphism as the norm open. -/
theorem smooth_unitCommGroupScheme : Smooth (unitCommGroupScheme b).X.hom :=
  UnitNormPolynomial.smooth_unitOpenToBase b

end SchemeTheory.Affine.UnitGroupScheme
