/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.ProjectiveUnitOrbits
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitGroupScheme
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The scalar quotient presheaf and its projective norm-open map

This is the literal quotient of tensor-algebra units by scalar units.
Its map to the norm open is defined by scalar invariance. The normalized
chart results prove local surjectivity and local injectivity of this map.
The passage from this presheaf to its fppf sheaf remains a separate step.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Module
open scoped TensorProduct

universe u

namespace SchemeTheory.Affine.ScalarQuotientPresheaf

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R A S T : Type u} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
  [Algebra R A] [Algebra R S] [Algebra R T]

/-- The actual scalar homomorphism into the units of the tensor algebra. -/
def scalarHom : Sˣ →* (S ⊗[R] A)ˣ :=
  Units.map (algebraMap S (S ⊗[R] A)).toMonoidHom

/-- The subgroup consisting of scalar units. -/
def scalarSubgroup : Subgroup (S ⊗[R] A)ˣ := (scalarHom (R := R) (A := A) (S := S)).range

/-- The literal quotient of tensor-algebra units by scalar units. -/
abbrev ScalarQuotient := (S ⊗[R] A)ˣ ⧸ scalarSubgroup (R := R) (A := A) (S := S)

/-- Base change of an actual tensor-algebra unit. -/
def unitMap (g : S →ₐ[R] T) : (S ⊗[R] A)ˣ →* (T ⊗[R] A)ˣ :=
  Units.map (Algebra.TensorProduct.map g (AlgHom.id R A)).toRingHom.toMonoidHom

theorem unitMap_scalarHom (g : S →ₐ[R] T) (r : Sˣ) :
    unitMap (A := A) g (scalarHom (R := R) (A := A) r) =
      scalarHom (R := R) (A := A) (Units.map g.toRingHom.toMonoidHom r) := by
  apply Units.ext
  change Algebra.TensorProduct.map g (AlgHom.id R A) ((r : S) ⊗ₜ[R] (1 : A)) =
    g (r : S) ⊗ₜ[R] (1 : A)
  rw [Algebra.TensorProduct.map_tmul, map_one]

/-- Scalar subgroups are preserved by every map of test algebras. -/
theorem scalarSubgroup_le_comap (g : S →ₐ[R] T) :
    scalarSubgroup (R := R) (A := A) (S := S) ≤
      (scalarSubgroup (R := R) (A := A) (S := T)).comap (unitMap g) := by
  rintro _ ⟨r, rfl⟩
  exact ⟨Units.map g.toRingHom.toMonoidHom r, (unitMap_scalarHom g r).symm⟩

/-- Base change descends to the scalar quotient. -/
def quotientMap (g : S →ₐ[R] T) :
    ScalarQuotient (R := R) (A := A) (S := S) →*
      ScalarQuotient (R := R) (A := A) (S := T) :=
  QuotientGroup.map _ _ (unitMap g) (scalarSubgroup_le_comap g)

/-- The scalar quotient as a commutative-group-valued algebra functor. -/
def quotientFunctor (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    CommAlgCat.{u} R ⥤ CommGrpCat.{u} where
  obj S := CommGrpCat.of (ScalarQuotient (R := R) (A := A) (S := S))
  map f := CommGrpCat.ofHom (quotientMap f.hom)
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro q
    refine QuotientGroup.induction_on q fun a => ?_
    change QuotientGroup.mk (unitMap (AlgHom.id R S) a) = QuotientGroup.mk a
    congr 1
    apply Units.ext
    change Algebra.TensorProduct.map (AlgHom.id R S) (AlgHom.id R A) _ = _
    rw [Algebra.TensorProduct.map_id]
    rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    refine QuotientGroup.induction_on q fun a => ?_
    change QuotientGroup.mk (unitMap (g.hom.comp f.hom) a) =
      QuotientGroup.mk (unitMap g.hom (unitMap f.hom a))
    congr 1
    apply Units.ext
    change Algebra.TensorProduct.map (g.hom.comp f.hom) (AlgHom.id R A) _ =
      Algebra.TensorProduct.map g.hom (AlgHom.id R A)
        (Algebra.TensorProduct.map f.hom (AlgHom.id R A) _)
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
    rfl

variable {n : ℕ} (b : Basis (Fin (n + 1)) R A)

/-- The projective-class map is a map of coefficient algebras. -/
def projectivePointAlgHom (a : (S ⊗[R] A)ˣ) :
    ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S where
  __ := ProjectiveUnitOpen.projectivePoint b a
  commutes' r := by
    change UnitNormPolynomial.unitToHom b a
      (algebraMap R (UnitNormPolynomial.CoordinateRing b) r) = algebraMap R S r
    exact (UnitNormPolynomial.unitToHom b a).commutes r

/-- A scalar multiple has the same class in the literal group quotient. -/
theorem mk_scalarMul (r : Sˣ) (a : (S ⊗[R] A)ˣ) :
    (QuotientGroup.mk (ProjectiveUnitOpen.scalarMul r a) :
      ScalarQuotient (R := R) (A := A) (S := S)) = QuotientGroup.mk a := by
  change QuotientGroup.mk' (scalarSubgroup (R := R) (A := A) (S := S))
    (scalarHom r * a) = _
  rw [map_mul]
  have h : (QuotientGroup.mk (scalarHom (R := R) (A := A) r) :
      ScalarQuotient (R := R) (A := A) (S := S)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨r, rfl⟩
  change (QuotientGroup.mk (scalarHom (R := R) (A := A) r) :
    ScalarQuotient (R := R) (A := A) (S := S)) * _ = _
  rw [h]
  exact one_mul (QuotientGroup.mk a : ScalarQuotient (R := R) (A := A) (S := S))

/-- The invariant map from the literal scalar quotient to the projective norm open. -/
def quotientPoint : ScalarQuotient (R := R) (A := A) (S := S) →
    (ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S) :=
  Quotient.lift (projectivePointAlgHom b) (by
    intro a c h
    obtain ⟨r, hr⟩ := QuotientGroup.leftRel_apply.mp h
    have he : c = ProjectiveUnitOpen.scalarMul r a := by
      change c = scalarHom r * a
      rw [hr]
      exact (mul_inv_cancel_left a c).symm.trans (mul_comm _ _)
    apply AlgHom.coe_ringHom_injective
    change ProjectiveUnitOpen.projectivePoint b a = ProjectiveUnitOpen.projectivePoint b c
    rw [he, ProjectiveUnitOpen.projectivePoint_scalarMul])

theorem quotientPoint_mk (a : (S ⊗[R] A)ˣ) :
    quotientPoint b (QuotientGroup.mk a) = projectivePointAlgHom b a := rfl

/-- Every point over a normalized chart lifts to the scalar quotient. -/
theorem quotientPoint_surjective_on_chart
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (ProjectiveUnitCharts.chartElement b j))) :
    ∃ q, quotientPoint b q = f := by
  refine ⟨QuotientGroup.mk (ProjectiveUnitCharts.normalizedUnit b f j hj), ?_⟩
  apply AlgHom.coe_ringHom_injective
  exact ProjectiveUnitCharts.projectivePoint_normalizedUnit b f j hj

/-- Two scalar-quotient sections over the same normalized chart are equal
as soon as their actual projective points agree. -/
theorem quotientPoint_injective_on_chart
    (f : ProjectiveUnitOpen.CoordinateRing b →ₐ[R] S)
    (j : Fin (n + 1)) (hj : IsUnit (f (ProjectiveUnitCharts.chartElement b j)))
    (q q' : ScalarQuotient (R := R) (A := A) (S := S))
    (hq : quotientPoint b q = f) (hq' : quotientPoint b q' = f) : q = q' := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective q'
  obtain ⟨r, hr, _⟩ := ProjectiveUnitCharts.existsUnique_scalar_normalizedUnit b f j hj a
    (congrArg AlgHom.toRingHom hq)
  obtain ⟨r', hr', _⟩ := ProjectiveUnitCharts.existsUnique_scalar_normalizedUnit b f j hj a'
    (congrArg AlgHom.toRingHom hq')
  rw [hr, hr', mk_scalarMul, mk_scalarMul]

end SchemeTheory.Affine.ScalarQuotientPresheaf
