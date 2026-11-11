/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineAlgebra
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverCompletedStageEtale
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.AdicCompletionNoetherian
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteEtaleSystem
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Étaleness of the actual completed affine cover algebra

The original stage cover algebras are étale over the actual quotients of
the completed affine coefficient ring. Their original transitions have
the exact extended adic kernels and are surjective. The finite étale
adic-system theorem therefore proves étaleness of the already constructed
algebra of compatible original sections.

This assertion concerns that algebra over the completed affine ring.
It does not assert algebraization on the ordinary scheme.
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

/-- The actual compatible-section algebra of the finite étale tower is
étale over the completed original affine coefficient ring. -/
theorem completedAffineAlgebra_etale (U : X.affineOpens) :
    Algebra.Etale (AdicCompletion (sectionsIdeal f I U) Γ(X, U))
      (completedAffineAlgebra f I V U) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let J : Ideal R := sectionsIdeal f I U
  let Rh : Type u := AdicCompletion J R
  let Jh : Ideal Rh := J.map (algebraMap R Rh)
  let B : ℕ → CommRingCat.{u} := fun n => affineSectionRing f I V U n
  let t : ∀ n : ℕ, B (n + 1) →ₐ[Rh] B n :=
    fun n => affineSectionCompletedTransition f I V U n
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  have : IsNoetherianRing Rh := AdicCompletion.isNoetherianRing_of_isNoetherianRing J
  have hcomplete : IsAdicComplete J Rh :=
    AdicCompletion.isAdicComplete (I := J) (M := R) (IsNoetherian.noetherian J)
  have : IsAdicComplete Jh Rh :=
    (IsAdicComplete.map_algebraMap_iff (I := J) (S := Rh) (M := Rh)).mpr hcomplete
  have : ∀ n : ℕ, Module.Finite R (B n) :=
    fun n => (coverToOriginal f I V n).finite_app U U.property
  have : ∀ n : ℕ, Module.Finite Rh (B n) :=
    fun n => Module.Finite.of_restrictScalars_finite R Rh (B n)
  let _stageAlgebra : ∀ n : ℕ, Algebra (Rh ⧸ Jh ^ (n + 1)) (B n) :=
    fun n => affineSectionCompletedQuotientAlgebra f I V U n
  have : ∀ n : ℕ, IsScalarTower Rh (Rh ⧸ Jh ^ (n + 1)) (B n) :=
    fun n => affineSectionCompletedQuotient_isScalarTower f I V U n
  have : ∀ n : ℕ, Algebra.Etale (Rh ⧸ Jh ^ (n + 1)) (B n) :=
    fun n => affineSectionCompletedQuotient_etale f I V U n
  have ht : ∀ n : ℕ, Function.Surjective (t n) :=
    fun n => algebraTransition_app_surjective f I V n U U.property
  have hker : ∀ n : ℕ, RingHom.ker (t n).toRingHom =
      (Jh ^ (n + 1)).map (algebraMap Rh (B (n + 1))) := by
    intro n
    calc
      RingHom.ker (t n).toRingHom =
          (J ^ (n + 1)).map (algebraMap R (B (n + 1))) :=
        algebraTransition_app_ker f I V n U U.property
      _ = (Jh ^ (n + 1)).map (algebraMap Rh (B (n + 1))) := by
        change (J ^ (n + 1)).map (algebraMap R (B (n + 1))) =
          ((J.map (algebraMap R Rh)) ^ (n + 1)).map (algebraMap Rh (B (n + 1)))
        rw [← Ideal.map_pow, Ideal.map_map,
          ← IsScalarTower.algebraMap_eq R Rh (B (n + 1))]
  exact AdicAlgebraSystem.etale (R := Rh) (fun n => B n) t Jh ht hker

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
