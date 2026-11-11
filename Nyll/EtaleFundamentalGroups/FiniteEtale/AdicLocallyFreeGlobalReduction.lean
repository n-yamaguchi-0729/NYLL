/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedProjectiveHomLift
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveSyzygyVanishing
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicTwistingGlobalReduction
public import Nyll.SchemeTheory.Cohomology.Sheaves.ReesClosedProjectiveSerre
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeLocus
public import Nyll.SchemeTheory.Modules.Tensor.AffineTensorSections
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.ProjectiveSpace.ClosedProjectiveTwistingFrames
public import Mathlib.RingTheory.Flat.Stability

/-!
# Actual compatible sections with a finite locally free coefficient

The existing finite-free-locus theorem gives flat affine sections of the
original coefficient sheaf. Actual tensor sections and the existing
coordinate frames transport this flatness to each positive twist.
The already constructed ideal-tensor kernel comparison and Rees vanishing
therefore apply to the original quotient units for this coefficient.

This supplies the positive-twist section lifting needed to reconstruct
maps into an algebraized finite locally free sheaf. The local-freeness
condition is a property of the original sheaf; no compatible-map lift or
completion comparison is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules FiniteEtale.AdicCoverTower
open AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j] (N : Y.Modules) [N.IsQuasicoherent] [N.IsFiniteType]
  (hN : finiteFreeLocus N = ⊤)

include hN

local notation "𝒇" => j ≫ π R n
local notation "ℒ" => Functor.obj (Scheme.Modules.pullback j) (twistingSheaf R n)
local notation "𝔪" => IsLocalRing.maximalIdeal R

/-- A single original twist bound gives surjectivity onto every closed
level for a finite locally free coefficient sheaf. -/
theorem exists_closedProjective_locallyFreeTwist_bound_globalReduction_surjective :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Function.Surjective ((levelPullbackUnit 𝒇 I (N ⊗ (ℒ).tensorPow d) k).app ⊤) := by
  obtain ⟨c, hc⟩ :=
    exists_closedImmersion_idealTensor_coefficient_twisting_bound_subsingleton_HSucc R I n j N
  refine ⟨c, ?_⟩
  intro d hd k
  let T : Y.Modules := (ℒ).tensorPow d
  let M : Y.Modules := N ⊗ T
  let C := stdCoverPullback (A := R) (n := n) j
  have : T.IsQuasicoherent := closedProjectiveTwistingPow_isQuasicoherent R n j d
  have : M.IsQuasicoherent :=
    IsInvertible.isQuasicoherent_tensorPow N
      (IsInvertible.pullback j (isInvertible_twistingSheaf R n)) d
  have : Subsingleton ((ReesTensor.idealTensorPresheaf 𝒇 I M (k + 1)).HSucc C 0) :=
    hc d hd (k + 1) 0
  apply levelPullbackUnit_globalSections_surjective_of_idealTensor_H1 𝒇 I M C
  intro r s
  let U : Y.Opens := C.inter s
  have hU : IsAffineOpen U := C.isAffineOpen_inter 𝒇 s
  have : Module.Flat Γ(Y, U) Γ(N, U) :=
    moduleFlat_sections_of_finiteFreeLocus_eq_top N hN U hU
  obtain ⟨t, ht⟩ := exists_twistingPow_frame_stdCoverPullback_inter R n j d r s
  have : Module.Flat Γ(Y, U) Γ(T, U) := ht.sections_flat
  have : Module.Flat Γ(Y, U) (Γ(N, U) ⊗[Γ(Y, U)] Γ(T, U)) := inferInstance
  exact Module.Flat.of_linearEquiv (affineTensorSectionsEquiv N T U hU).symm

omit hN in
private theorem compatibleFreeMaps_of_uniform_globalReduction
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) [IsProper g]
    (M : ℕ → X.Modules)
    [∀ d : ℕ, (M d).IsQuasicoherent] [∀ d : ℕ, (M d).IsFiniteType]
    (hsurj : ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Function.Surjective
        ((levelPullbackUnit g (IsLocalRing.maximalIdeal A) (M d) k).app ⊤)) :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ (J : Type u)
      (β : ∀ k : ℕ, (show X.Modules from SheafOfModules.free J) ⟶
        levelPullbackModule g (IsLocalRing.maximalIdeal A) (M d) k),
      (∀ k : ℕ, β (k + 1) ≫
        levelPullbackTransition g (IsLocalRing.maximalIdeal A) (M d) k = β k) →
      ∃ φ : (show X.Modules from SheafOfModules.free J) ⟶ M d,
        ∀ k : ℕ, φ ≫ levelPullbackUnit g (IsLocalRing.maximalIdeal A) (M d) k = β k := by
  obtain ⟨c, hc⟩ := hsurj
  refine ⟨c, ?_⟩
  intro d hd J β hβ
  exact exists_freeHom_of_compatible_levelMaps (R := A) (X := X)
    g (M d) (hc d hd) J β hβ

omit I hN [IsNoetherianRing R] [IsClosedImmersion j] [N.IsFiniteType] in
private theorem closedProjective_twistFamily_isQuasicoherent :
    ∀ d : ℕ, (N ⊗ (ℒ).tensorPow d).IsQuasicoherent := by
  intro d
  exact IsInvertible.isQuasicoherent_tensorPow N
    (IsInvertible.pullback j (isInvertible_twistingSheaf R n)) d

omit I hN [IsNoetherianRing R] [IsClosedImmersion j] [N.IsQuasicoherent] in
private theorem closedProjective_twistFamily_isFiniteType :
    ∀ d : ℕ, (N ⊗ (ℒ).tensorPow d).IsFiniteType := by
  intro d
  exact IsInvertible.isFiniteType_tensorPow N
    (IsInvertible.pullback j (isInvertible_twistingSheaf R n)) d

omit I hN in
private theorem compatibleFreeMaps_of_closedProjectiveTwist_globalReduction
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    let M : ℕ → Y.Modules := fun d => N ⊗ (ℒ).tensorPow d
    (∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Function.Surjective ((levelPullbackUnit 𝒇 𝔪 (M d) k).app ⊤)) →
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ (J : Type u)
      (β : ∀ k : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶
        levelPullbackModule 𝒇 𝔪 (M d) k),
      (∀ k : ℕ, β (k + 1) ≫
        levelPullbackTransition 𝒇 𝔪 (M d) k = β k) →
      ∃ φ : (show Y.Modules from SheafOfModules.free J) ⟶ M d,
        ∀ k : ℕ, φ ≫ levelPullbackUnit 𝒇 𝔪 (M d) k = β k := by
  intro M hsurj
  have : IsProper 𝒇 := inferInstance
  have : ∀ d : ℕ, (M d).IsQuasicoherent := by
    intro d
    exact closedProjective_twistFamily_isQuasicoherent R n j N d
  have : ∀ d : ℕ, (M d).IsFiniteType := by
    intro d
    exact closedProjective_twistFamily_isFiniteType R n j N d
  exact compatibleFreeMaps_of_uniform_globalReduction (A := R) (X := Y)
    𝒇 M hsurj

omit I in
/-- Compatible original quotient maps from a free sheaf lift to a
sufficiently positive twist of the actual locally free coefficient.
The bound is independent of the source index type and of the maps. -/
theorem exists_closedProjective_locallyFreeTwist_bound_compatibleFreeHom_lift
    [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    let M : ℕ → Y.Modules := fun d => N ⊗ (ℒ).tensorPow d
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ (J : Type u)
      (β : ∀ k : ℕ, (show Y.Modules from SheafOfModules.free J) ⟶
        levelPullbackModule 𝒇 𝔪 (M d) k),
      (∀ k : ℕ, β (k + 1) ≫
        levelPullbackTransition 𝒇 𝔪 (M d) k = β k) →
      ∃ φ : (show Y.Modules from SheafOfModules.free J) ⟶ M d,
        ∀ k : ℕ, φ ≫ levelPullbackUnit 𝒇 𝔪 (M d) k = β k := by
  exact compatibleFreeMaps_of_closedProjectiveTwist_globalReduction R n j N
    (exists_closedProjective_locallyFreeTwist_bound_globalReduction_surjective
      R (IsLocalRing.maximalIdeal R) n j N hN)

end AlgebraicGeometry.ProjSpace
