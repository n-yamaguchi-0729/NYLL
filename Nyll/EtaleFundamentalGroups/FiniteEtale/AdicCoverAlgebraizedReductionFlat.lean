/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedPullbackSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineProjective
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelUnit
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveQuotientLifting
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Flat original affine reductions of an algebraized cover module

The original closed-level unit has the prescribed ideal-power kernel.
An actual morphism becoming invertible on that level identifies its
quotient with the original finite étale cover module. The quotient
coefficient action is retained when transporting the original cover's
proved projectivity.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (M : X.Modules) [M.IsQuasicoherent]

/-- The actual affine quotient of an algebraized cover module is flat
over its actual quotient coordinate ring. Its identification is induced
by the original closed-level unit and original supplied morphism. -/
theorem affineReduction_flat_of_levelPullback_isIso
    (n : ℕ) (σ : M ⟶ moduleSheaf f I V n)
    [IsIso ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I n))).map σ)]
    (U : X.affineOpens) :
    Module.Flat (Γ(X, U) ⧸ (sectionsIdeal f I U) ^ (n + 1))
      (Γ(M, U) ⧸
        ((sectionsIdeal f I U) ^ (n + 1) •
          (⊤ : Submodule Γ(X, U) Γ(M, U)))) := by
  let R : CommRingCat.{u} := Γ(X, U)
  let J : Ideal R := (sectionsIdeal f I U) ^ (n + 1)
  let P : ModuleCat.{u} R := (moduleSectionsFunctor U.1).obj M
  let T : ModuleCat.{u} R :=
    (moduleSectionsFunctor U.1).obj (levelPullbackModule f I M n)
  let η : P →ₗ[R] T :=
    ((moduleSectionsFunctor U.1).map (levelPullbackUnit f I M n)).hom
  have hη : Function.Surjective η :=
    levelPullbackUnit_app_surjective f I M n U
  have hker : η.ker = J • (⊤ : Submodule R P) := by
    ext x
    exact levelPullbackUnit_app_eq_zero_iff f I M n U x
  let e₀ : (P ⧸ (J • (⊤ : Submodule R P))) ≃ₗ[R] T :=
    (Submodule.quotEquivOfEq (J • (⊤ : Submodule R P)) η.ker hker.symm).trans
      (LinearMap.quotKerEquivOfSurjective η hη)
  let e₁ : T ≃ₗ[R] affineSectionModule f I V U n :=
    ((moduleSectionsFunctor U.1).mapIso
      (moduleSheafLevelQuotientIso f I V M n σ)).toLinearEquiv
  let e : (P ⧸ (J • (⊤ : Submodule R P))) ≃ₗ[R]
      affineSectionModule f I V U n := e₀.trans e₁
  let Q := R ⧸ J
  let _moduleQ : Module Q (affineSectionModule f I V U n) :=
    affineSectionQuotientModule f I V U n
  have : IsScalarTower R Q (affineSectionModule f I V U n) :=
    affineSectionQuotient_isScalarTower f I V U n
  have : Module.Projective Q (affineSectionModule f I V U n) :=
    affineSectionQuotient_projective f I V U n
  let eQ : (P ⧸ (J • (⊤ : Submodule R P))) ≃ₗ[Q]
      affineSectionModule f I V U n :=
    LinearEquiv.ofBijective (AdicModuleSystem.overQuotientLinearMap J e.toLinearMap)
      e.bijective
  exact Module.Flat.of_linearEquiv eQ

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
