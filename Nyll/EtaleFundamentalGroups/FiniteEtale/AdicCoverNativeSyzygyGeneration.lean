/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygySections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverNativeSyzygyNilpotence
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.LocalMorphisms
public import Nyll.SchemeTheory.Modules.Sections.AffineEpi
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleExactness
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorNilpotentSections
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowerFrames
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.NilpotentSurjectivity
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Topology.Sets.Opens

/-!
# Compatible generators of the native syzygy tower

Compatible lifts of generators of the first native syzygy generate every
native syzygy after the same twist. On affine opens subordinate to an
original frame, the proved kernel formula and native power-annihilation
theorem give the nilpotent quotient criterion. The original tensor frame
transports this criterion to the further twist.

Only the first lifted map is assumed epimorphic. No higher-stage
generation or global lifting assertion is an input.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

/-- The actual section functor and native sheaf evaluation have the
same kernel; keep this boundary abstract before substituting a syzygy. -/
private theorem evaluated_kernel_eq {Y : Scheme.{u}} {M N : Y.Modules}
    (φ : M ⟶ N) (U : Y.Opens) :
    (((moduleSectionsFunctor U).map φ).hom).ker =
      ((φ.val.app (op U)).hom).ker := rfl

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) (d : ℕ) [(L.tensorPow d).IsQuasicoherent]
  (K : Type u) [Finite K]
  (α : ∀ n : ℕ, (show X.Modules from SheafOfModules.free K) ⟶
    moduleSheaf f I V n ⊗ L.tensorPow d)
  (hα : ∀ n : ℕ, α (n + 1) ≫ (moduleTransition f I V n ▷ L.tensorPow d) = α n)
  (hL : IsInvertible L) (hgen : ∀ n : ℕ, Epi (α n))

include hL hgen in
/-- Compatible lifted generators of the first twisted native syzygy
generate all stages. The proof derives the required local nilpotent
quotient properties from the original presentations. -/
theorem levelPresentationKernel_epi_of_compatible_twisted_lifts
    (P : X.Modules) [P.IsQuasicoherent] (e : ℕ) :
    let M : ℕ → X.Modules := fun k => levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) k (α k)
    let q : ∀ k : ℕ, M (k + 1) ⟶ M k := fun k =>
      levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα k
    ∀ β : ∀ k : ℕ, P ⟶ M k ⊗ L.tensorPow e,
      Epi (β 0) →
      (∀ k : ℕ, β (k + 1) ≫ (q k ▷ L.tensorPow e) = β k) →
      ∀ k : ℕ, Epi (β k) := by
  intro M q β hzero hβ k
  induction k with
  | zero => exact hzero
  | succ k ih =>
      have : (tensor (M k) (L.tensorPow e)).IsQuasicoherent :=
        IsInvertible.isQuasicoherent_tensorPow (M k) hL e
      have : Epi (β (k + 1) ≫ (q k ▷ L.tensorPow e)) :=
        Eq.mp (congrArg Epi (hβ k).symm) ih
      obtain ⟨C, t, ht, hcover⟩ := hL.exists_frame_cover
      apply (Hom.epi_iff_locallySurjective (β (k + 1))).mpr
      intro O z x hx
      have hxC : x ∈ ⨆ i : X, C i := by
        rw [hcover]
        exact Set.mem_univ x
      obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxC
      obtain ⟨W, hW, hxW, hWO⟩ :=
        exists_isAffineOpen_mem_and_subset (show x ∈ O ⊓ C i from ⟨hx, hxi⟩)
      have hWC : W ≤ C i := hWO.trans inf_le_right
      have hWO' : W ≤ O := hWO.trans inf_le_left
      let td : Γ(L.tensorPow d, W) :=
        (L.tensorPow d).presheaf.map (homOfLE hWC).op (tensorPowSection (t i) d)
      have htd : IsFrameOn td W :=
        (((ht i).tensorPowSection_monoidalV2 d).map (homOfLE hWC)).mono hWC
      have hkerEq : (((q k).val.app (op W)).hom).ker =
          (sectionsIdeal f I W) ^ (k + 1) •
            (⊤ : Submodule Γ(X, W) Γ(M (k + 1), W)) :=
        (evaluated_kernel_eq (q k) W).symm.trans
          (levelPresentationKernelTransition_sections_ker
            f I K ⟨W, hW⟩ V L d α td htd hα hL k (hgen (k + 1)))
      have hker : (((q k).val.app (op W)).hom).ker ≤
          sectionsIdeal f I W • (⊤ : Submodule Γ(X, W) Γ(M (k + 1), W)) :=
        hkerEq.le.trans
          (Submodule.smul_mono (Ideal.pow_le_self (Nat.succ_ne_zero k)) le_rfl)
      have hpow : (sectionsIdeal f I W) ^ (k + 2) •
          (⊤ : Submodule Γ(X, W) Γ(M (k + 1), W)) = ⊥ :=
        levelPresentationKernel_sections_annihilated
          f I V (L.tensorPow d) K (k + 1) (α (k + 1)) ⟨W, hW⟩
      let ψW : Γ(P, W) →ₗ[Γ(X, W)] Γ(M (k + 1) ⊗ L.tensorPow e, W) :=
        ((β (k + 1)).val.app (op W)).hom
      let qW : Γ(M (k + 1) ⊗ L.tensorPow e, W) →ₗ[Γ(X, W)]
          Γ(M k ⊗ L.tensorPow e, W) :=
        ((q k ▷ L.tensorPow e).val.app (op W)).hom
      have hcomp : Function.Surjective (qW.comp ψW) :=
        Hom.app_surjective_of_epi_of_isAffineOpen
          (β (k + 1) ≫ (q k ▷ L.tensorPow e)) W hW
      have hsurj : Function.Surjective ψW :=
        LinearMap.surjective_of_comp_surjective_of_ker_le_smul_of_pow_smul_eq_bot
          ψW qW (sectionsIdeal f I W) (k + 2) hcomp
          (((ht i).tensorPowSection_monoidalV2 e).whiskerRight_app_ker_le_smul
            hWC hWC (q k) (sectionsIdeal f I W) hker)
          (((ht i).tensorPowSection_monoidalV2 e).smul_top_tensor_eq_bot
            hWC hWC ((sectionsIdeal f I W) ^ (k + 2)) hpow)
      obtain ⟨y, hy⟩ := hsurj
        ((M (k + 1) ⊗ L.tensorPow e).presheaf.map (homOfLE hWO').op z)
      exact ⟨W, hWO', hxW, y, hy⟩

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
