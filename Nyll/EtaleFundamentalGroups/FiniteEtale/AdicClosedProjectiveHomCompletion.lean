/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedProjectiveHomFaithfulness
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedProjectiveHomLift
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveSyzygyVanishing
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLocallyFreeGlobalReduction
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelTensorComparison
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeKernel
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeLocus
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentKernelGlobal
public import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.ProjectiveSpace.ClosedImmersionGlobalGeneration
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafPresentation
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Projective.InvertibleTensorPowMonoidalV2
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleIsoEvAppTensorUnit
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Actual Hom reconstruction into a finite locally free sheaf

Twist the original source and target together. Existing projective
generation gives an actual finite free epimorphism onto the twisted
source. The positive-twist global reduction theorem lifts the original
compatible columns into the original twisted target. Faithfulness of all
closed reductions kills the original kernel of the epimorphism, so
`Abelian.epiDesc` produces the desired morphism. The existing equivalence
for tensoring with an invertible sheaf then removes the twist.

No presentation lift, Hom comparison, or compatibility of a constructed
map is assumed. The target's finite local freeness is an explicit
geometric property; it is supplied separately for the algebraized finite
étale module.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules FiniteEtale.AdicCoverTower
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit.AlgebraicGeometry.Scheme.Modules.CoevAux

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem tensorComparison_compatibleMaps
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) (I : Ideal A) (P Q T : X.Modules)
    [Q.IsQuasicoherent] [T.IsQuasicoherent]
    (γ : ∀ k : ℕ, P ⟶ levelPullbackModule g I Q k)
    (hγ : ∀ k : ℕ, γ (k + 1) ≫ levelPullbackTransition g I Q k = γ k)
    (k : ℕ) :
    ((γ (k + 1) ▷ T) ≫ (levelPullbackTensorIso g I Q T (k + 1)).hom) ≫
        levelPullbackTransition g I (Q ⊗ T) k =
      (γ k ▷ T) ≫ (levelPullbackTensorIso g I Q T k).hom := by
  calc
    ((γ (k + 1) ▷ T) ≫ (levelPullbackTensorIso g I Q T (k + 1)).hom) ≫
        levelPullbackTransition g I (Q ⊗ T) k =
        (γ (k + 1) ▷ T) ≫
          ((levelPullbackTensorIso g I Q T (k + 1)).hom ≫
            levelPullbackTransition g I (Q ⊗ T) k) := Category.assoc _ _ _
    _ = (γ (k + 1) ▷ T) ≫ ((levelPullbackTransition g I Q k ▷ T) ≫
        (levelPullbackTensorIso g I Q T k).hom) :=
      congrArg (fun b => (γ (k + 1) ▷ T) ≫ b)
        (levelPullbackTensorIso_transition g I Q T k)
    _ = ((γ (k + 1) ▷ T) ≫ (levelPullbackTransition g I Q k ▷ T)) ≫
        (levelPullbackTensorIso g I Q T k).hom := (Category.assoc _ _ _).symm
    _ = ((γ (k + 1) ≫ levelPullbackTransition g I Q k) ▷ T) ≫
        (levelPullbackTensorIso g I Q T k).hom :=
      congrArg (fun b => b ≫ (levelPullbackTensorIso g I Q T k).hom)
        ((tensorRight T).map_comp (γ (k + 1)) (levelPullbackTransition g I Q k)).symm
    _ = (γ k ▷ T) ≫ (levelPullbackTensorIso g I Q T k).hom :=
      congrArg (fun b => (b ▷ T) ≫ (levelPullbackTensorIso g I Q T k).hom) (hγ k)

private theorem homOfLevelMaps_descend_epi
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j] (P Q B : Y.Modules)
    [P.IsQuasicoherent] [P.IsFiniteType] [Q.IsQuasicoherent]
    [B.IsQuasicoherent] [B.IsFiniteType]
    (α : P ⟶ Q) [Epi α]
    (δ : ∀ k : ℕ, Q ⟶ levelPullbackModule (j ≫ π R n) (IsLocalRing.maximalIdeal R) B k)
    (ψ₀ : P ⟶ B)
    (hψ₀ : ∀ k : ℕ, ψ₀ ≫
      levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) B k = α ≫ δ k) :
    ∃ ψ : Q ⟶ B, ∀ k : ℕ, ψ ≫
      levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) B k = δ k := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (j ≫ π R n)
  have : (kernel α).IsQuasicoherent := isQuasicoherent_kernel α
  have : (kernel α).IsFiniteType := by
    let e : Y.Modules ≌ SheafOfModules.{u} Y.ringCatSheaf := sheafOfModulesEquivalence Y
    let κ : kernel α ⟶ P := kernel.ι α
    have : Mono κ := inferInstanceAs (Mono (kernel.ι α))
    have : (e.functor.obj (kernel α)).IsQuasicoherent := isQuasicoherent_kernel α
    have : (e.functor.obj P).IsQuasicoherent :=
      (show P.IsQuasicoherent from inferInstance)
    have : (e.functor.obj P).IsFiniteType :=
      (show P.IsFiniteType from inferInstance)
    have : Mono (e.functor.map κ) := Functor.map_mono e.functor κ
    exact SheafOfModules.isFiniteType_of_mono_on_locallyNoetherian
      (X := Y) (M := e.functor.obj (kernel α)) (N := e.functor.obj P) (e.functor.map κ)
  have hzero : kernel.ι α ≫ ψ₀ = 0 := by
    apply hom_eq_zero_of_forall_levelPullbackUnit_comp_eq_zero R n j (kernel α) B
    intro k
    calc
      (kernel.ι α ≫ ψ₀) ≫
          levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) B k =
          kernel.ι α ≫
            (ψ₀ ≫ levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) B k) :=
        Category.assoc _ _ _
      _ = kernel.ι α ≫ (α ≫ δ k) := congrArg (fun b => kernel.ι α ≫ b) (hψ₀ k)
      _ = (kernel.ι α ≫ α) ≫ δ k := (Category.assoc _ _ _).symm
      _ = 0 ≫ δ k := congrArg (fun b => b ≫ δ k) (kernel.condition α)
      _ = 0 := zero_comp
  let ψ : Q ⟶ B := Abelian.epiDesc α ψ₀ hzero
  refine ⟨ψ, ?_⟩
  intro k
  apply (cancel_epi α).mp
  exact (Category.assoc α ψ
    (levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) B k)).symm.trans
    ((congrArg
      (fun b => b ≫ levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) B k)
      (Abelian.comp_epiDesc α ψ₀ hzero)).trans (hψ₀ k))

private theorem homOfLevelMaps_untwist
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) (I : Ideal A) (M N T : X.Modules)
    [N.IsQuasicoherent] [T.IsQuasicoherent] (hT : IsInvertible T)
    (γ : ∀ k : ℕ, M ⟶ levelPullbackModule g I N k)
    (ψ : M ⊗ T ⟶ N ⊗ T)
    (hψ : ∀ k : ℕ, ψ ≫ levelPullbackUnit g I (N ⊗ T) k =
      (γ k ▷ T) ≫ (levelPullbackTensorIso g I N T k).hom) :
    ∃ φ : M ⟶ N, ∀ k : ℕ, φ ≫ levelPullbackUnit g I N k = γ k := by
  have : (tensorRight T).IsEquivalence := isEquivalence_tensorRight hT
  let E (k : ℕ) := levelPullbackTensorIso g I N T k
  let φ : M ⟶ N := (tensorRight T).preimage ψ
  refine ⟨φ, ?_⟩
  intro k
  apply (tensorRight T).map_injective
  apply (cancel_mono (E k).hom).mp
  calc
    ((tensorRight T).map (φ ≫ levelPullbackUnit g I N k)) ≫ (E k).hom =
        ((φ ▷ T) ≫ (levelPullbackUnit g I N k ▷ T)) ≫ (E k).hom :=
      congrArg (fun b => b ≫ (E k).hom)
        ((tensorRight T).map_comp φ (levelPullbackUnit g I N k))
    _ = (φ ▷ T) ≫ ((levelPullbackUnit g I N k ▷ T) ≫ (E k).hom) :=
      Category.assoc _ _ _
    _ = (φ ▷ T) ≫ levelPullbackUnit g I (N ⊗ T) k :=
      congrArg (fun b => (φ ▷ T) ≫ b) (levelPullbackUnit_tensor_comparison g I N T k)
    _ = ψ ≫ levelPullbackUnit g I (N ⊗ T) k :=
      congrArg (fun b => b ≫ levelPullbackUnit g I (N ⊗ T) k)
        ((tensorRight T).map_preimage (X := M) (Y := N) ψ)
    _ = (γ k ▷ T) ≫ (E k).hom := hψ k

private theorem homOfLevelMaps_of_twisted_free_epi
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (n : ℕ) {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j] (M N T : Y.Modules)
    [N.IsQuasicoherent] [T.IsQuasicoherent]
    [(M ⊗ T).IsQuasicoherent] [(N ⊗ T).IsQuasicoherent] [(N ⊗ T).IsFiniteType]
    (hT : IsInvertible T)
    (hsurj : ∀ k : ℕ, Function.Surjective
      ((levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) (N ⊗ T) k).app ⊤))
    (J : Type u) [Finite J]
    (α : (show Y.Modules from SheafOfModules.free J) ⟶ M ⊗ T) [Epi α]
    (γ : ∀ k : ℕ, M ⟶ levelPullbackModule (j ≫ π R n) (IsLocalRing.maximalIdeal R) N k)
    (hγ : ∀ k : ℕ, γ (k + 1) ≫
      levelPullbackTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) N k = γ k) :
    ∃ φ : M ⟶ N, ∀ k : ℕ, φ ≫
      levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) N k = γ k := by
  have : IsProper (j ≫ π R n) := inferInstance
  have : (show Y.Modules from SheafOfModules.free J).IsQuasicoherent := inferInstance
  have : (show Y.Modules from SheafOfModules.free J).IsFiniteType := finiteType_free J
  let E (k : ℕ) := levelPullbackTensorIso (j ≫ π R n) (IsLocalRing.maximalIdeal R) N T k
  let δ (k : ℕ) : M ⊗ T ⟶
      levelPullbackModule (j ≫ π R n) (IsLocalRing.maximalIdeal R) (N ⊗ T) k :=
    (γ k ▷ T) ≫ (E k).hom
  have hδ : ∀ k : ℕ, δ (k + 1) ≫
      levelPullbackTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) (N ⊗ T) k = δ k := by
    intro k
    dsimp only [δ, E]
    exact tensorComparison_compatibleMaps (j ≫ π R n) (IsLocalRing.maximalIdeal R)
      M N T γ (fun k => hγ k) k
  let β (k : ℕ) : (show Y.Modules from SheafOfModules.free J) ⟶
      levelPullbackModule (j ≫ π R n) (IsLocalRing.maximalIdeal R) (N ⊗ T) k := α ≫ δ k
  have hβ : ∀ k : ℕ, β (k + 1) ≫
      levelPullbackTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) (N ⊗ T) k = β k := by
    intro k
    exact (Category.assoc α (δ (k + 1))
      (levelPullbackTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) (N ⊗ T) k)).trans
      (congrArg (fun b => α ≫ b) (hδ k))
  obtain ⟨ψ₀, hψ₀⟩ := exists_freeHom_of_compatible_levelMaps (R := R) (X := Y)
    (j ≫ π R n) (N ⊗ T) hsurj J β (fun k => hβ k)
  obtain ⟨ψ, hψ⟩ := homOfLevelMaps_descend_epi R n j
    (show Y.Modules from SheafOfModules.free J) (M ⊗ T) (N ⊗ T) α δ ψ₀
    (fun k => by simpa only [β] using hψ₀ k)
  dsimp only [δ, E] at hψ
  exact homOfLevelMaps_untwist (j ≫ π R n) (IsLocalRing.maximalIdeal R)
    M N T hT γ ψ (fun k => hψ k)

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j] (M N : Y.Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]

local notation "𝔪" => IsLocalRing.maximalIdeal R
local notation "𝒇" => j ≫ π R n

/-- Original compatible maps into every actual quotient of a finite
locally free target come from a unique morphism on the original family.
The source may be any quasicoherent finite-type module. -/
theorem existsUnique_hom_of_compatible_levelMaps_to_locallyFree
    (hN : finiteFreeLocus N = ⊤)
    (γ : ∀ k : ℕ, M ⟶
      levelPullbackModule (j ≫ π R n) (IsLocalRing.maximalIdeal R) N k)
    (hγ : ∀ k : ℕ, γ (k + 1) ≫
      levelPullbackTransition (j ≫ π R n) (IsLocalRing.maximalIdeal R) N k = γ k) :
    ∃! φ : M ⟶ N, ∀ k : ℕ, φ ≫
      levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) N k = γ k := by
  let L := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
  obtain ⟨c₀, hc₀⟩ := exists_closedImmersion_twisting_bound_finiteFree_epi R n j M
  obtain ⟨c₁, hc₁⟩ :=
    exists_closedProjective_locallyFreeTwist_bound_globalReduction_surjective
      R 𝔪 n j N hN
  let d := max c₀ c₁
  let T : Y.Modules := L.tensorPow d
  have hL : IsInvertible L := IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  have hT : IsInvertible T := hL.tensorPow_monoidalV2 d
  have : T.IsQuasicoherent := closedProjectiveTwistingPow_isQuasicoherent R n j d
  have : (M ⊗ T).IsQuasicoherent := IsInvertible.isQuasicoherent_tensorPow M hL d
  have : (N ⊗ T).IsQuasicoherent := IsInvertible.isQuasicoherent_tensorPow N hL d
  have : (N ⊗ T).IsFiniteType := IsInvertible.isFiniteType_tensorPow N hL d
  have hsurj : ∀ k : ℕ,
      Function.Surjective ((levelPullbackUnit 𝒇 𝔪 (N ⊗ T) k).app ⊤) := by
    intro k
    dsimp only [T, L]
    exact hc₁ d (le_max_right c₀ c₁) k
  obtain ⟨J, hJ, α, hα⟩ := hc₀ d (le_max_left c₀ c₁)
  change (show Y.Modules from SheafOfModules.free J) ⟶ M ⊗ T at α
  have : Finite J := hJ
  have : Epi α := hα
  obtain ⟨φ, hφ⟩ := homOfLevelMaps_of_twisted_free_epi R n j M N T hT hsurj
    J α γ (fun k => hγ k)
  refine ⟨φ, hφ, ?_⟩
  intro φ' hφ'
  apply sub_eq_zero.mp
  apply hom_eq_zero_of_forall_levelPullbackUnit_comp_eq_zero R n j M N (φ' - φ)
  intro k
  exact (Preadditive.sub_comp φ' φ (levelPullbackUnit 𝒇 𝔪 N k)).trans
    ((congrArg₂ (fun b c => b - c) (hφ' k) (hφ k)).trans (sub_self (γ k)))

end AlgebraicGeometry.ProjSpace
