/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.PointSections
import Nyll.SchemeTheory.FiniteEtale.PointSectionsBaseChange
import Nyll.SchemeTheory.FiniteEtale.Algebra.PointSpecializationNaturality
import Nyll.EtaleFundamentalGroups.GeometricFiber.HenselianSpecialization
import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroup
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Naturality of the actual Henselian specialization fiber isomorphism

Changing the coefficient field of a geometric point acts by the original
spectrum morphism and defines a natural transformation of the actual
finite étale fiber functors. Compatible maps of normal Henselian rings
and their fraction fields give a commutative square with the previously
constructed generic-to-residue fiber isomorphisms.

The ring-level commutativity is proved in `PointSpecializationNaturality`.
Here the section-algebra comparison identifies it with commutativity on
actual over-points and geometric fibers, with no additional comparison
assumption.

These are fiber functors of covers of a fixed affine base `Spec H`.
This file does not assert the construction of specialization maps between
fundamental groups of fibers of an arbitrary proper family.

Mathematical context: https://stacks.math.columbia.edu/tag/0BUP
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

section CoefficientMap

variable (H Ω Ω' : Type u) [CommRing H]
  [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  [Algebra H Ω] [Algebra H Ω']

/-- A coefficient-field map acts on the actual geometric fiber by
precomposition of its representing point with the spectrum map. -/
def coefficientFiberMap (σ : Ω →ₐ[H] Ω') :
    fiber (Spec.algebraMap H Ω) ⟶ fiber (Spec.algebraMap H Ω') where
  app X := FintypeCat.homMk fun x =>
    (fiberObjEquivHom (Spec.algebraMap H Ω') X).symm
      (pointHomBaseChange H Ω Ω' σ X
        (fiberObjEquivHom (Spec.algebraMap H Ω) X x))
  naturality X Y f := by
    apply FintypeCat.hom_ext
    intro x
    change (fiberObjEquivHom (Spec.algebraMap H Ω') Y).symm
        (pointHomBaseChange H Ω Ω' σ Y
          (fiberObjEquivHom (Spec.algebraMap H Ω) Y
            ((fiber (Spec.algebraMap H Ω)).map f x))) =
      (fiber (Spec.algebraMap H Ω')).map f
        ((fiberObjEquivHom (Spec.algebraMap H Ω') X).symm
          (pointHomBaseChange H Ω Ω' σ X
            (fiberObjEquivHom (Spec.algebraMap H Ω) X x)))
    rw [fiberObjEquivHom_symm_naturality,
      ← fiberObjEquivHom_naturality, pointHomBaseChange_naturality]

/-- The fiber map retains the actual coefficient change of its over-point. -/
theorem coefficientFiberMap_point (σ : Ω →ₐ[H] Ω')
    (X : FiniteEtale (Spec (.of H)))
    (x : (fiber (Spec.algebraMap H Ω)).obj X) :
    fiberObjEquivHom (Spec.algebraMap H Ω') X
        ((coefficientFiberMap H Ω Ω' σ).app X x) =
      pointHomBaseChange H Ω Ω' σ X
        (fiberObjEquivHom (Spec.algebraMap H Ω) X x) :=
  Equiv.apply_symm_apply (fiberObjEquivHom (Spec.algebraMap H Ω') X)
    (pointHomBaseChange H Ω Ω' σ X
      (fiberObjEquivHom (Spec.algebraMap H Ω) X x))

/-- The natural transformations of actual geometric fibers respect
composition of the supplied coefficient-field maps. -/
theorem coefficientFiberMap_comp
    (Ω'' : Type u) [Field Ω''] [IsSepClosed Ω''] [Algebra H Ω'']
    (σ : Ω →ₐ[H] Ω') (τ : Ω' →ₐ[H] Ω'') :
    coefficientFiberMap H Ω Ω' σ ≫ coefficientFiberMap H Ω' Ω'' τ =
      coefficientFiberMap H Ω Ω'' (τ.comp σ) := by
  ext X x
  apply (fiberObjEquivHom (Spec.algebraMap H Ω'') X).injective
  change fiberObjEquivHom (Spec.algebraMap H Ω'') X
      ((coefficientFiberMap H Ω' Ω'' τ).app X
        ((coefficientFiberMap H Ω Ω' σ).app X x)) =
    fiberObjEquivHom (Spec.algebraMap H Ω'') X
      ((coefficientFiberMap H Ω Ω'' (τ.comp σ)).app X x)
  rw [coefficientFiberMap_point, coefficientFiberMap_point,
    coefficientFiberMap_point, pointHomBaseChange_comp]

end CoefficientMap

section Specialization

variable (H R S L M : Type u)
  [CommRing H] [CommRing R] [HenselianLocalRing R] [IsIntegrallyClosed R]
  [CommRing S] [HenselianLocalRing S] [IsIntegrallyClosed S]
  [Field L] [Field M] [Algebra H R] [Algebra H S]
  [Algebra R L] [IsFractionRing R L]
  [Algebra S M] [IsFractionRing S M]
  [Algebra H L] [IsScalarTower H R L]
  [Algebra H M] [IsScalarTower H S M]

/-- The actual over-point specialization commutes with a compatible local
ring map and fraction-field map. The residue point uses the native map
of residue fields of that local map. -/
theorem henselianSpecializationOverEquiv_map
    (ι : R →ₐ[H] S) [IsLocalHom ι] (j : L →ₐ[H] M)
    (hι : ∀ r : R, j (algebraMap R L r) = algebraMap S M (ι r))
    (X : FiniteEtale (Spec (.of H)))
    (x : Over.mk (Spec.algebraMap H L) ⟶ X.toComma) :
    henselianSpecializationOverEquiv H S M X (pointHomBaseChange H L M j X x) =
      pointHomBaseChange H (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (IsLocalRing.ResidueField.mapAlgHom ι) X
        (henselianSpecializationOverEquiv H R L X x) := by
  have hfinite : Module.Finite H Γ(X.left, ⊤) := sections_moduleFinite H X
  apply (pointHomAlgEquiv H (IsLocalRing.ResidueField S) X).injective
  calc
    _ = SchemeTheory.finiteEtalePointSpecialization H S M Γ(X.left, ⊤)
        (pointHomAlgEquiv H M X (pointHomBaseChange H L M j X x)) :=
      pointHomAlgEquiv_henselianSpecializationOverEquiv H S M X
        (pointHomBaseChange H L M j X x)
    _ = SchemeTheory.finiteEtalePointSpecialization H S M Γ(X.left, ⊤)
        (j.comp (pointHomAlgEquiv H L X x)) :=
      congrArg (SchemeTheory.finiteEtalePointSpecialization H S M Γ(X.left, ⊤))
        (pointHomAlgEquiv_pointHomBaseChange H L M j X x)
    _ = (IsLocalRing.ResidueField.mapAlgHom ι).comp
        (SchemeTheory.finiteEtalePointSpecialization H R L Γ(X.left, ⊤)
          (pointHomAlgEquiv H L X x)) :=
      SchemeTheory.finiteEtalePointSpecialization_map H R S L M Γ(X.left, ⊤)
        ι j hι (pointHomAlgEquiv H L X x)
    _ = (IsLocalRing.ResidueField.mapAlgHom ι).comp
        (pointHomAlgEquiv H (IsLocalRing.ResidueField R) X
          (henselianSpecializationOverEquiv H R L X x)) :=
      congrArg (fun z : Γ(X.left, ⊤) →ₐ[H] IsLocalRing.ResidueField R =>
        (IsLocalRing.ResidueField.mapAlgHom ι).comp z)
        (pointHomAlgEquiv_henselianSpecializationOverEquiv H R L X x).symm
    _ = _ :=
      (pointHomAlgEquiv_pointHomBaseChange H (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField.mapAlgHom ι) X
        (henselianSpecializationOverEquiv H R L X x)).symm

variable [IsSepClosed L] [IsSepClosed M]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  [IsSepClosed (IsLocalRing.ResidueField S)]

/-- The square of actual geometric-fiber natural transformations commutes
with the constructed Henselian specialization isomorphisms. -/
theorem henselianSpecializationFiberIso_map
    (ι : R →ₐ[H] S) [IsLocalHom ι] (j : L →ₐ[H] M)
    (hι : ∀ r : R, j (algebraMap R L r) = algebraMap S M (ι r)) :
    coefficientFiberMap H L M j ≫ (henselianSpecializationFiberIso H S M).hom =
      (henselianSpecializationFiberIso H R L).hom ≫
        coefficientFiberMap H (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
          (IsLocalRing.ResidueField.mapAlgHom ι) := by
  ext X x
  apply (fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField S)) X).injective
  change fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField S)) X
      (henselianSpecializationFiberEquiv H S M X
        ((coefficientFiberMap H L M j).app X x)) =
    fiberObjEquivHom (Spec.algebraMap H (IsLocalRing.ResidueField S)) X
      ((coefficientFiberMap H (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
        (IsLocalRing.ResidueField.mapAlgHom ι)).app X
          (henselianSpecializationFiberEquiv H R L X x))
  rw [fiberObjEquivHom_henselianSpecializationFiberEquiv, coefficientFiberMap_point,
    coefficientFiberMap_point, fiberObjEquivHom_henselianSpecializationFiberEquiv]
  exact henselianSpecializationOverEquiv_map H R S L M ι j hι X
    (fiberObjEquivHom (Spec.algebraMap H L) X x)

end Specialization

end AlgebraicGeometry.FiniteEtale
