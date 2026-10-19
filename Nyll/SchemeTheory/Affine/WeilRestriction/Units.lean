/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Affine.WeilRestriction.Global
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Norm.Defs

/-!
# The units of a finite free algebra as a represented functor

The localization `R[X, X⁻¹]` is constructed first, together with its natural
classification of units over every commutative test algebra. The existing
finite-free Weil restriction then gives a concrete affine representer for
`C ↦ (C ⊗[R] A)ˣ`. Neither `A` nor `C` is assumed reduced or étale.

The associated scheme represents maps from the base change of `Spec A` to
the multiplicative-group carrier on arbitrary test schemes. The projective
scalar quotient and its geometric properties are separate constructions.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Polynomial TensorProduct

universe u

namespace SchemeTheory.Affine.WeilRestrictionUnits

variable (R : Type u) [CommRing R]

/-- The coordinate algebra of the multiplicative group, constructed by
inverting the polynomial variable. -/
abbrev CoordinateRing := Localization.Away (Polynomial.X : R[X])

instance coordinateRingFinitePresentation :
    Algebra.FinitePresentation R (CoordinateRing R) := by
  have : Algebra.FinitePresentation R[X] (CoordinateRing R) :=
    IsLocalization.Away.finitePresentation (Polynomial.X : R[X])
  exact Algebra.FinitePresentation.trans R R[X] (CoordinateRing R)

/-- The universal unit in the coordinate algebra. -/
def coordinateUnit : (CoordinateRing R)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := CoordinateRing R)
    (Polynomial.X : R[X])).unit

@[simp]
theorem coordinateUnit_val :
    (coordinateUnit R : CoordinateRing R) =
      algebraMap R[X] (CoordinateRing R) Polynomial.X :=
  IsUnit.unit_spec _

variable {R} {S T : Type u} [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- Evaluation at a unit extends uniquely across the localization. -/
def unitToHom (s : Sˣ) : CoordinateRing R →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (Polynomial.X : R[X])
    (f := Polynomial.aeval (s : S)) (by
      rw [Polynomial.aeval_X]
      exact s.isUnit)

@[simp]
theorem unitToHom_algebraMap (s : Sˣ) (p : R[X]) :
    unitToHom s (algebraMap R[X] (CoordinateRing R) p) = Polynomial.aeval (s : S) p :=
  IsLocalization.Away.lift_eq (Polynomial.X : R[X])
    (g := (Polynomial.aeval (s : S)).toRingHom) (by
      change IsUnit (Polynomial.aeval (s : S) Polynomial.X)
      rw [Polynomial.aeval_X]
      exact s.isUnit) p

/-- A map out of the coordinate algebra supplies an actual unit. -/
def homToUnit (f : CoordinateRing R →ₐ[R] S) : Sˣ :=
  Units.map f.toRingHom.toMonoidHom (coordinateUnit R)

@[simp]
theorem homToUnit_val (f : CoordinateRing R →ₐ[R] S) :
    (homToUnit f : S) = f (algebraMap R[X] (CoordinateRing R) Polynomial.X) := by
  change f (coordinateUnit R : CoordinateRing R) = _
  rw [coordinateUnit_val]

@[simp]
theorem homToUnit_unitToHom (s : Sˣ) :
    homToUnit (unitToHom (R := R) s) = s := by
  apply Units.ext
  rw [homToUnit_val, unitToHom_algebraMap, Polynomial.aeval_X]

@[simp]
theorem unitToHom_homToUnit (f : CoordinateRing R →ₐ[R] S) :
    unitToHom (homToUnit f) = f := by
  apply IsLocalization.algHom_ext (Submonoid.powers (Polynomial.X : R[X]))
  apply Polynomial.algHom_ext
  change unitToHom (homToUnit f)
      (algebraMap R[X] (CoordinateRing R) Polynomial.X) =
    f (algebraMap R[X] (CoordinateRing R) Polynomial.X)
  rw [unitToHom_algebraMap, Polynomial.aeval_X, homToUnit_val]

/-- The universal property of `R[X, X⁻¹]`, for arbitrary test algebras. -/
def homEquivUnits : (CoordinateRing R →ₐ[R] S) ≃ Sˣ where
  toFun := homToUnit
  invFun := unitToHom
  left_inv := unitToHom_homToUnit
  right_inv := homToUnit_unitToHom

/-- Unit classification commutes with every homomorphism of test algebras. -/
theorem homEquivUnits_comp (f : CoordinateRing R →ₐ[R] S) (g : S →ₐ[R] T) :
    homEquivUnits (g.comp f) = Units.map g.toRingHom.toMonoidHom (homEquivUnits f) := by
  apply Units.ext
  rfl

/-- The units functor on commutative `R`-algebras. -/
def unitsFunctor (R : Type u) [CommRing R] : CommAlgCat.{u} R ⥤ Type u where
  obj C := Cˣ
  map f := ↾fun s => Units.map f.hom.toRingHom.toMonoidHom s
  map_id C := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Units.ext
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Units.ext
    rfl

/-- The coordinate algebra classifies units in the bundled algebra category. -/
def categoryHomEquivUnits (C : CommAlgCat.{u} R) :
    (CommAlgCat.of R (CoordinateRing R) ⟶ C) ≃ Cˣ where
  toFun f := homEquivUnits f.hom
  invFun s := CommAlgCat.ofHom (unitToHom s)
  left_inv f := by
    apply CommAlgCat.hom_ext
    exact unitToHom_homToUnit f.hom
  right_inv s := homToUnit_unitToHom s

theorem categoryHomEquivUnits_comp {C D : CommAlgCat.{u} R}
    (f : CommAlgCat.of R (CoordinateRing R) ⟶ C) (g : C ⟶ D) :
    categoryHomEquivUnits D (f ≫ g) =
      (unitsFunctor R).map g (categoryHomEquivUnits C f) := by
  apply Units.ext
  rfl

variable (R) (A : Type u) [CommRing A] [Algebra R A]

/-- The units of the scalar extension of a fixed algebra. -/
abbrev tensorUnitsFunctor : CommAlgCat.{u} R ⥤ Type u :=
  tensorRightAlg (R := R) (A := A) ⋙ unitsFunctor R

variable [Module.Free R A] [Module.Finite R A]

/-- An actual algebra obtained from the finite-free affine Weil restriction. -/
abbrev unitsRepresentingAlgebra : CommAlgCat.{u} R :=
  algebraRepresenter (R := R) (A := A) (B := CoordinateRing R)

/-- The finite-free algebra construction corepresents units on every
commutative test algebra, with naturality included. -/
def tensorUnitsCorepresentable :
    (tensorUnitsFunctor R A).CorepresentableBy (unitsRepresentingAlgebra R A) where
  homEquiv {C} :=
    (algebraCorepresentableBy (R := R) (A := A) (B := CoordinateRing R)).homEquiv.trans
      (categoryHomEquivUnits ((tensorRightAlg (R := R) (A := A)).obj C))
  homEquiv_comp g f := by
    change categoryHomEquivUnits _
        ((algebraCorepresentableBy (R := R) (A := A) (B := CoordinateRing R)).homEquiv
          (f ≫ g)) = _
    rw [(algebraCorepresentableBy (R := R) (A := A)
      (B := CoordinateRing R)).homEquiv_comp]
    exact categoryHomEquivUnits_comp _ _

/-- The affine scheme carrying the finite-free restriction of the
multiplicative group. -/
abbrev unitsScheme : Over (Spec (CommRingCat.of R)) :=
  globalInternalHomSpecRepresenter (R := R) (A := A) (B := CoordinateRing R)

/-- On arbitrary test schemes, the same carrier represents maps from the
base change of `Spec A` to the multiplicative-group carrier. -/
def unitsSchemeRepresentable :
    (globalInternalHomFunctor (R := R) (A := A) (B := CoordinateRing R)).RepresentableBy
      (unitsScheme R A) :=
  globalInternalHomSpecRepresentable (R := R) (A := A) (B := CoordinateRing R)

/-- The determinant of multiplication detects units, including for
nonreduced finite free algebras. This is the criterion for the unit open. -/
theorem isUnit_norm_iff (a : A) : IsUnit (Algebra.norm R a) ↔ IsUnit a := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det, Algebra.lmul_isUnit_iff]

end SchemeTheory.Affine.WeilRestrictionUnits
