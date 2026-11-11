/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineAlgebra
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineEtaleCoefficient
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineEtaleCoefficientComparison
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineProjective
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.QuotientRingComparison
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Etale

/-!
# The completed quotient coefficients of the actual cover tower

The completed quotient ring maps to the original cover section ring through
the constructed comparison with the original ideal-power quotient. This
map induces the already fixed completed coefficient action on the stage.
Its étaleness follows from the actual cover's coefficient map and the
quotient comparison, and the same named algebra structure supplies the
scalar tower needed for finite étale effectivity over the completed ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))

/-- Original section coefficients, viewed as coefficients over the literal
ideal-power quotient of the completed affine ring. -/
def affineSectionCompletedQuotientAlgebraMap (U : X.affineOpens) (n : ℕ) :
    (AdicCompletion (sectionsIdeal f I U) Γ(X, U) ⧸
      ((sectionsIdeal f I U).map
        (algebraMap Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U)))) ^
          (n + 1)) →ₐ[Γ(X, U)] affineSectionRing f I V U n := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  exact (affineSectionQuotientAlgebraMap f I V U n).comp
    (AdicCompletion.quotientPowAlgEquiv (R := Γ(X, U)) (sectionsIdeal f I U)
      (IsNoetherian.noetherian (sectionsIdeal f I U)) (n + 1)).toAlgHom

/-- The quotient coefficient map induces precisely the already constructed
completed coefficient map on the actual section ring. -/
theorem affineSectionCompletedQuotientAlgebraMap_mk (U : X.affineOpens) (n : ℕ)
    (a : AdicCompletion (sectionsIdeal f I U) Γ(X, U)) :
    affineSectionCompletedQuotientAlgebraMap f I V U n (Ideal.Quotient.mk _ a) =
      affineSectionCompletionCoefficient f I V U n a := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  change affineSectionQuotientAlgebraMap f I V U n
      (AdicCompletion.quotientPowAlgEquiv (R := Γ(X, U)) (sectionsIdeal f I U)
        (IsNoetherian.noetherian (sectionsIdeal f I U)) (n + 1)
          (Ideal.Quotient.mk _ a)) =
    affineSectionQuotientAlgebraMap f I V U n
      (AdicCompletion.evalₐ (sectionsIdeal f I U) (n + 1) a)
  exact congrArg (affineSectionQuotientAlgebraMap f I V U n)
    (AdicCompletion.quotientPowAlgEquiv_mk (R := Γ(X, U)) (sectionsIdeal f I U)
      (IsNoetherian.noetherian (sectionsIdeal f I U)) (n + 1) a)

/-- The single stage algebra structure over the completed quotient ring. -/
@[instance_reducible]
def affineSectionCompletedQuotientAlgebra (U : X.affineOpens) (n : ℕ) :
    Algebra
      (AdicCompletion (sectionsIdeal f I U) Γ(X, U) ⧸
        ((sectionsIdeal f I U).map
          (algebraMap Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U)))) ^
            (n + 1))
      (affineSectionRing f I V U n) :=
  (affineSectionCompletedQuotientAlgebraMap f I V U n).toRingHom.toAlgebra

/-- The named quotient action and the existing completed action form the
actual scalar tower, by their coefficient computation. -/
theorem affineSectionCompletedQuotient_isScalarTower (U : X.affineOpens) (n : ℕ) :
    let _ : Algebra
      (AdicCompletion (sectionsIdeal f I U) Γ(X, U) ⧸
        ((sectionsIdeal f I U).map
          (algebraMap Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U)))) ^
            (n + 1))
      (affineSectionRing f I V U n) := affineSectionCompletedQuotientAlgebra f I V U n
    IsScalarTower (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (AdicCompletion (sectionsIdeal f I U) Γ(X, U) ⧸
        ((sectionsIdeal f I U).map
          (algebraMap Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U)))) ^
            (n + 1))
      (affineSectionRing f I V U n) := by
  intro _stageAlgebra
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change affineSectionCompletionCoefficient f I V U n a =
    affineSectionCompletedQuotientAlgebraMap f I V U n (Ideal.Quotient.mk _ a)
  exact (affineSectionCompletedQuotientAlgebraMap_mk f I V U n a).symm

/-- Each actual cover section ring is étale over the completed quotient,
with precisely the named quotient algebra structure. -/
theorem affineSectionCompletedQuotient_etale (U : X.affineOpens) (n : ℕ) :
    let _ : Algebra
      (AdicCompletion (sectionsIdeal f I U) Γ(X, U) ⧸
        ((sectionsIdeal f I U).map
          (algebraMap Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U)))) ^
            (n + 1))
      (affineSectionRing f I V U n) := affineSectionCompletedQuotientAlgebra f I V U n
    Algebra.Etale
      (AdicCompletion (sectionsIdeal f I U) Γ(X, U) ⧸
        ((sectionsIdeal f I U).map
          (algebraMap Γ(X, U) (AdicCompletion (sectionsIdeal f I U) Γ(X, U)))) ^
            (n + 1))
      (affineSectionRing f I V U n) := by
  intro _stageAlgebra
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
  have hmap : (affineSectionCompletedQuotientAlgebraMap f I V U n).toRingHom.Etale := by
    change ((affineSectionQuotientAlgebraMap f I V U n).toRingHom.comp
      (AdicCompletion.quotientPowAlgEquiv (R := Γ(X, U)) (sectionsIdeal f I U)
        (IsNoetherian.noetherian (sectionsIdeal f I U)) (n + 1)).toRingHom).Etale
    apply RingHom.Etale.stableUnderComposition
    · exact RingHom.Etale.of_bijective
        (AdicCompletion.quotientPowAlgEquiv (R := Γ(X, U)) (sectionsIdeal f I U)
          (IsNoetherian.noetherian (sectionsIdeal f I U)) (n + 1)).bijective
    · rw [affineSectionQuotientAlgebraMap_toRingHom]
      exact affineSectionCoefficient_etale f I V U n
  exact hmap.toAlgebra

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
