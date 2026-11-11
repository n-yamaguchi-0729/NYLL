/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Sheaves.Projective.InvertibleTensorPowMonoidalV2
public import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleIsoEvAppTensorUnit
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicClosedPullbackSections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverClosedProjectiveSyzygyVanishing
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelTensorComparison
public import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeAffineSections
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.ProjectiveSpace.Basic
public import Nyll.SchemeTheory.ProjectiveSpace.ClosedImmersionGlobalGeneration
public import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.EpiMono
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Original module maps detected by all closed adic levels

The existing Krull-intersection theorem annihilates an affine section
which vanishes at every level by a function congruent to one on the
closed fibre. Thus the section vanishes on an original open neighbourhood
of that fibre. The existing proper closed-map neighbourhood theorem
makes these opens cover the whole scheme.

For a closed projective scheme, the existing finite global generation
theorem supplies an epimorphism from a free sheaf after twisting the
source. Section detection then detects the original morphism, and the
existing invertible tensor equivalence removes the twist. No comparison
with a proposed algebraization is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
  (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]

/-- Original global sections of a coherent module on a proper local
scheme are detected by all its actual adic closed-level units. -/
theorem globalSection_eq_zero_of_forall_levelPullbackUnit_eq_zero
    (s : Γ(M, ⊤))
    (hs : ∀ k : ℕ,
      (levelPullbackUnit f (IsLocalRing.maximalIdeal R) M k).app ⊤ s = 0) :
    s = 0 := by
  let I := IsLocalRing.maximalIdeal R
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let res (U : X.Opens) : Γ(M, U) :=
    M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s
  have hrestrict (U : X.affineOpens) (k : ℕ) :
      (levelPullbackUnit f I M k).app U.1 (res U.1) = 0 := by
    let q := levelPullbackUnit f I M k
    have h := congrArg
      (fun p : Γ(M, ⊤) ⟶ Γ(levelPullbackModule f I M k, U.1) => p s)
      (q.mapPresheaf.naturality (homOfLE (le_top : U.1 ≤ ⊤)).op)
    change q.app U.1 (res U.1) =
      (levelPullbackModule f I M k).presheaf.map
        (homOfLE (le_top : U.1 ≤ ⊤)).op (q.app ⊤ s) at h
    exact h.trans ((congrArg
      ((levelPullbackModule f I M k).presheaf.map
        (homOfLE (le_top : U.1 ≤ ⊤)).op) (hs k)).trans (map_zero _))
  have hlocal (x : X) (hx : f x = IsLocalRing.closedPoint R) :
      ∃ D : X.Opens, x ∈ D ∧ res D = 0 := by
    obtain ⟨U, hU, hxU, _⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (show x ∈ (⊤ : X.Opens) from trivial)
    have : IsNoetherianRing Γ(X, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have : Module.Finite Γ(X, U) Γ(M, U) :=
      moduleFinite_sections_of_isFiniteType M U hU
    have hall : res U ∈
        (⨅ a : ℕ, (sectionsIdeal f I U) ^ a •
          (⊤ : Submodule Γ(X, U) Γ(M, U))) := by
      apply (Submodule.mem_iInf _).mpr
      intro a
      cases a with
      | zero =>
          rw [pow_zero, one_smul]
          exact Submodule.mem_top
      | succ k =>
          exact (levelPullbackUnit_app_eq_zero_iff f I M k ⟨U, hU⟩ (res U)).mp
            (hrestrict ⟨U, hU⟩ k)
    obtain ⟨r, hr⟩ :=
      ((sectionsIdeal f I U).mem_iInf_smul_pow_eq_bot_iff (res U)).mp hall
    let a : Γ(X, U) := 1 - r.val
    let D : X.Opens := X.basicOpen a
    let i : level f I 0 ⟶ X := pullback.fst f (baseInclusion I 0)
    have hri : (i.app U).hom r.val = 0 := by
      have hmem : r.val ∈ RingHom.ker (i.app U).hom := by
        change r.val ∈ RingHom.ker ((pullback.fst f (baseInclusion I 0)).app U).hom
        rw [levelProjection_app_ker f I 0 ⟨U, hU⟩, Nat.zero_add, pow_one]
        exact r.property
      exact hmem
    have hD : i ⁻¹ᵁ D = i ⁻¹ᵁ U := by
      change i ⁻¹ᵁ X.basicOpen (1 - r.val) = i ⁻¹ᵁ U
      rw [Scheme.preimage_basicOpen, map_sub, map_one, hri, sub_zero, Scheme.basicOpen_one]
    let x₀ : base I 0 :=
      (show Spec (.of (IsLocalRing.ResidueField R)) from default)
    have hx₀ : baseInclusion I 0 x₀ = IsLocalRing.closedPoint R :=
      IsLocalRing.PrimeSpectrum.comap_residue R x₀
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := baseInclusion I 0) x x₀ (hx.trans hx₀.symm)
    have hxD : x ∈ D := by
      have hzU : z ∈ i ⁻¹ᵁ U := by
        change i z ∈ U
        exact hz.symm ▸ hxU
      have hzD : z ∈ i ⁻¹ᵁ D := hD.symm ▸ hzU
      change i z ∈ D at hzD
      exact hz ▸ hzD
    have hzero : a • res U = 0 := by
      change (1 - r.val) • res U = 0
      rw [sub_smul, one_smul, hr, sub_self]
    have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
      RingedSpace.isUnit_res_basicOpen X.toRingedSpace a
    have hresZero :
        M.presheaf.map (homOfLE (X.basicOpen_le a)).op (res U) = 0 := by
      apply hunit.smul_left_cancel.mp
      rw [smul_zero]
      calc
        X.presheaf.map (homOfLE (X.basicOpen_le a)).op a •
            M.presheaf.map (homOfLE (X.basicOpen_le a)).op (res U) =
          M.presheaf.map (homOfLE (X.basicOpen_le a)).op (a • res U) :=
          (Scheme.Modules.map_smul M (homOfLE (X.basicOpen_le a)) a (res U)).symm
        _ = 0 := by rw [hzero, map_zero]
    have hcomp : M.presheaf.map (homOfLE (X.basicOpen_le a)).op (res U) = res D := by
      change (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
        M.presheaf.map (homOfLE (X.basicOpen_le a)).op) s = res D
      rw [← Functor.map_comp]
      rfl
    exact ⟨D, hxD, hcomp.symm.trans hresZero⟩
  let J := {U : X.Opens // res U = 0}
  let V : X.Opens := ⨆ U : J, U.val
  have hfiber : ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ V := by
    intro x hx
    obtain ⟨D, hxD, hD⟩ := hlocal x hx
    exact Opens.mem_iSup.mpr ⟨⟨D, hD⟩, hxD⟩
  obtain ⟨W, hW, hWV⟩ := f.exists_preimage_le_of_fiber_subset
    (IsLocalRing.closedPoint R) V hfiber
  have hWtop : W = ⊤ := (IsLocalRing.closedPoint_mem_iff W).mp hW
  have hcover : ∀ x : X, x ∈ (⊤ : X.Opens) → x ∈ ⨆ U : J, U.val := by
    intro x _
    apply hWV
    change f x ∈ W
    rw [hWtop]
    trivial
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
  apply F.eq_of_locally_eq' (fun U : J => U.val) ⊤
    (fun U => homOfLE (le_top : U.val ≤ ⊤)) hcover s 0
  intro U
  exact U.property.trans (map_zero _).symm

end AlgebraicGeometry.FiniteEtale.AdicCoverTower

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules FiniteEtale.AdicCoverTower
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_IsInvertible_isIso_ev_app_tensorUnit.AlgebraicGeometry.Scheme.Modules.CoevAux

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Original maps of coherent modules on a closed projective scheme
are detected by the original unit maps to all closed adic levels. -/
theorem hom_eq_zero_of_forall_levelPullbackUnit_comp_eq_zero
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) {Y : Scheme.{u}}
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
    [IsClosedImmersion j]
    (M N : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    [N.IsQuasicoherent] [N.IsFiniteType] (φ : M ⟶ N)
    (hφ : ∀ k : ℕ, φ ≫
      levelPullbackUnit (j ≫ π R n) (IsLocalRing.maximalIdeal R) N k = 0) :
    φ = 0 := by
  let f := j ≫ π R n
  let I := IsLocalRing.maximalIdeal R
  let L : Y.Modules := (Scheme.Modules.pullback j).obj (twistingSheaf R n)
  have hL : IsInvertible L := IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  obtain ⟨d, hd⟩ := exists_closedImmersion_twisting_bound_finiteFree_epi R n j M
  obtain ⟨J, _hJ, α, hα⟩ := hd d le_rfl
  have : Epi α := hα
  let T := L.tensorPow d
  have hT : IsInvertible T := hL.tensorPow_monoidalV2 d
  have : T.IsQuasicoherent := closedProjectiveTwistingPow_isQuasicoherent R n j d
  have : (N ⊗ T).IsQuasicoherent := IsInvertible.isQuasicoherent_tensorPow N hL d
  have : (N ⊗ T).IsFiniteType := IsInvertible.isFiniteType_tensorPow N hL d
  let ψ : M ⊗ T ⟶ N ⊗ T := φ ▷ T
  have hψ (k : ℕ) : ψ ≫ levelPullbackUnit f I (N ⊗ T) k = 0 := by
    rw [← levelPullbackUnit_tensor_comparison f I N T k, ← Category.assoc]
    change ((φ ▷ T) ≫ (levelPullbackUnit f I N k ▷ T)) ≫
      (levelPullbackTensorIso f I N T k).hom = 0
    rw [← comp_whiskerRight, hφ k]
    change (tensorRight T).map (0 : M ⟶ levelPullbackModule f I N k) ≫
      (levelPullbackTensorIso f I N T k).hom = 0
    rw [Functor.map_zero, zero_comp]
  have hfree : α ≫ ψ = 0 := by
    apply (freeHomTopSectionsEquiv (N ⊗ T) J).injective
    funext b
    change freeHomTopSectionsEquiv (N ⊗ T) J (α ≫ ψ) b = 0
    have hz := globalSection_eq_zero_of_forall_levelPullbackUnit_eq_zero f (N ⊗ T)
      (freeHomTopSectionsEquiv (N ⊗ T) J (α ≫ ψ) b) (fun k => by
        have hcomp : (α ≫ ψ) ≫ levelPullbackUnit f I (N ⊗ T) k = 0 := by
          rw [Category.assoc, hψ k, comp_zero]
        exact (freeHomTopSectionsEquiv_comp (N ⊗ T) J (α ≫ ψ)
          (levelPullbackUnit f I (N ⊗ T) k) b).symm.trans
          (congrArg (fun q => freeHomTopSectionsEquiv
            (levelPullbackModule f I (N ⊗ T) k) J q b) hcomp))
    exact hz
  have hψzero : ψ = 0 := by
    apply (cancel_epi α).mp
    exact hfree.trans comp_zero.symm
  exact (whiskerRight_eq_zero_iff hT φ).mp hψzero

end AlgebraicGeometry.ProjSpace
