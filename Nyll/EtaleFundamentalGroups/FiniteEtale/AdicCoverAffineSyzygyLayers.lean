/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.ProjectiveSystemLayersOverCompletion
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Original ideal-power layers of the actual affine syzygies

The actual quotient-free presentation kernels are finite projective over
our original coefficient quotients. Their proved transition surjectivity,
exact adic kernels, and annihilation supply the projective module-system
comparison over the completion. It identifies the actual syzygy-transition
kernel with the original ideal power tensored with the first syzygy.

The uniquely characterized comparison retains the original scalar multiplication and compatible
section evaluations. Neither completeness of the original affine ring nor
a tensor-kernel comparison is assumed. Restriction naturality and global
cohomological comparisons are subsequent steps.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules AdicModuleSystem

private theorem existsUnique_originalTransitionKernelTensorEquiv
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : ℕ → ModuleCat.{u} R)
    (q : ∀ k : ℕ, M (k + 1) →ₗ[R] M k) (J : Ideal R)
    [∀ k : ℕ, Module.Finite R (M k)]
    [∀ k : ℕ, Module (R ⧸ J ^ (k + 1)) (M k)]
    [∀ k : ℕ, IsScalarTower R (R ⧸ J ^ (k + 1)) (M k)]
    [∀ k : ℕ, Module.Projective (R ⧸ J ^ (k + 1)) (M k)]
    (hpow : ∀ k : ℕ, J ^ (k + 1) • (⊤ : Submodule R (M k)) = ⊥)
    (hq : ∀ k : ℕ, Function.Surjective (q k))
    (hker : ∀ k : ℕ, (q k).ker = J ^ (k + 1) • (⊤ : Submodule R (M (k + 1))))
    (n : ℕ) :
    ∃! e : (↥(J ^ (n + 1)) ⊗[R] M 0) ≃ₗ[R] (q n).ker,
      ∀ (a : ↥(J ^ (n + 1))) (x : sections (R := R) (fun k => M k) q),
        (e (a ⊗ₜ[R] eval (R := R) (fun k => M k) q 0 x)).val =
          a.val • eval (R := R) (fun k => M k) q (n + 1) x := by
  let e : (↥(J ^ (n + 1)) ⊗[R] M 0) ≃ₗ[R] (q n).ker :=
    projectiveOriginalTransitionKernelEquiv (R := R) (fun k => M k) q J hpow hq hker n
  have he (a : ↥(J ^ (n + 1))) (x : sections (R := R) (fun k => M k) q) :
      (e (a ⊗ₜ[R] eval (R := R) (fun k => M k) q 0 x)).val =
          a.val • eval (R := R) (fun k => M k) q (n + 1) x :=
    projectiveOriginalTransitionKernelEquiv_tmul_eval (R := R) (fun k => M k) q J hpow hq hker n a x
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := eval_zero_surjective (R := R) (fun k => M k) q hq y
  apply Subtype.ext
  exact (he' a x).trans (he a x).symm

variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (.of A)) (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) (d : ℕ) (K : Type u) [Finite K]
  (s : ∀ n : ℕ, K → Γ(tensor (moduleSheaf f I V n) (L.tensorPow d), ⊤))
  (U : X.affineOpens) (t : Γ(L.tensorPow d, U)) (ht : IsFrameOn t (U : X.Opens))
  (hs : ∀ (n : ℕ) (k : K),
    (moduleTransition f I V n ▷ L.tensorPow d).app ⊤ (s (n + 1) k) = s n k)
  (hL : IsInvertible L)
  (hgen : ∀ n : ℕ, Epi ((freeHomTopSectionsEquiv
    (tensor (moduleSheaf f I V n) (L.tensorPow d)) K).symm (s n)))

include hL hgen in
/-- The actual affine syzygy-transition kernel is computed from its original
first stage. A unique equivalence retains the literal coefficient
and evaluations of each original compatible section. -/
theorem existsUnique_affineSyzygyTransitionKernelTensorEquiv (n : ℕ) :
    let R : CommRingCat.{u} := Γ(X, U)
    let J : Ideal R := sectionsIdeal f I U
    let M : ℕ → ModuleCat.{u} R := fun k =>
      ModuleCat.of R (affineSyzygyKernel f I V L d K s U t ht k)
    let q : ∀ k : ℕ, M (k + 1) →ₗ[R] M k :=
      fun k => affineSyzygyTransition f I V L d K s U t ht hs k
    ∃! e : (↥(J ^ (n + 1)) ⊗[R] M 0) ≃ₗ[R] (q n).ker,
      ∀ (a : ↥(J ^ (n + 1))) (x : sections (R := R) (fun k => M k) q),
        (e (a ⊗ₜ[R] eval (R := R) (fun k => M k) q 0 x)).val =
          a.val • eval (R := R) (fun k => M k) q (n + 1) x := by
  intro R J M q
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian U
  have : ∀ k : ℕ, Module.Finite R (M k) := fun k => by
    change Module.Finite R (affineSyzygyKernel f I V L d K s U t ht k)
    infer_instance
  let _moduleQ : ∀ k : ℕ, Module (R ⧸ J ^ (k + 1)) (M k) :=
    fun k => affineSyzygyQuotientModule f I V L d K s U t ht k
  have : ∀ k : ℕ, IsScalarTower R (R ⧸ J ^ (k + 1)) (M k) :=
    fun k => affineSyzygyQuotient_isScalarTower f I V L d K s U t ht k
  have : ∀ k : ℕ, Module.Projective (R ⧸ J ^ (k + 1)) (M k) :=
    fun k => (affineSyzygyKernel_finite_projective f I V L d K s U t ht hL k (hgen k)).2
  have hpow : ∀ k : ℕ, J ^ (k + 1) • (⊤ : Submodule R (M k)) = ⊥ :=
    fun k => affineSyzygyKernel_annihilated f I V L d K s U t ht k
  have hq : ∀ k : ℕ, Function.Surjective (q k) :=
    fun k => affineSyzygyTransition_surjective f I V L d K s U t ht hs hL k (hgen (k + 1))
  have hker : ∀ k : ℕ, (q k).ker = J ^ (k + 1) • (⊤ : Submodule R (M (k + 1))) :=
    fun k => affineSyzygyTransition_ker f I V L d K s U t ht hs hL k (hgen (k + 1))
  exact existsUnique_originalTransitionKernelTensorEquiv (R := R) M q J hpow hq hker n

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
