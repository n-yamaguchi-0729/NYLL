/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverAffineSyzygyLayers
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygySections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Sections.FreeHomSections
public import Nyll.SchemeTheory.Modules.Sections.KernelSections
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The native syzygy-transition kernel on a framed affine open

The original section equivalences and their original commuting transition
squares transport the proved affine layer isomorphism to the actual
categorical kernel sheaf. The inclusion formula uses the original native
kernel inclusion and compatible native section evaluations.

The resulting isomorphism is uniquely determined by this formula. No
kernel comparison, formal algebraization, or global lifting is an input.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules AdicModuleSystem

private def linearKernelEquiv
    {R M₀ M₁ N₀ N₁ : Type u} [CommRing R]
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup N₀] [Module R N₀] [AddCommGroup N₁] [Module R N₁]
    (q : M₁ →ₗ[R] M₀) (r : N₁ →ₗ[R] N₀)
    (e₀ : M₀ ≃ₗ[R] N₀) (e₁ : M₁ ≃ₗ[R] N₁)
    (h : e₀.toLinearMap.comp q = r.comp e₁.toLinearMap) :
    q.ker ≃ₗ[R] r.ker where
  toFun x := ⟨e₁ x.val, by
    change r (e₁ x.val) = 0
    exact (LinearMap.congr_fun h x.val).symm.trans
      ((congrArg e₀ x.property).trans e₀.map_zero)⟩
  invFun y := ⟨e₁.symm y.val, by
    apply e₀.injective
    change e₀ (q (e₁.symm y.val)) = e₀ 0
    exact (LinearMap.congr_fun h (e₁.symm y.val)).trans
      ((congrArg r (e₁.apply_symm_apply y.val)).trans (y.property.trans e₀.map_zero.symm))⟩
  left_inv x := Subtype.ext (e₁.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e₁.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e₁.map_add x.val y.val)
  map_smul' a x := Subtype.ext (e₁.map_smul a x.val)

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
  (U : X.affineOpens) (t : Γ(L.tensorPow d, U)) (ht : IsFrameOn t (U : X.Opens))

include hL hgen ht in
/-- The actual native transition kernel is uniquely identified with the
original ideal tensor of the first native syzygy by its inclusion formula. -/
theorem existsUnique_levelPresentationKernelTensorEquiv (n : ℕ) :
    let M : ℕ → X.Modules := fun k => levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) k (α k)
    let q : ∀ k : ℕ, M (k + 1) ⟶ M k := fun k =>
      levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα k
    ∃! e : (↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] Γ(M 0, U)) ≃ₗ[Γ(X, U)]
        Γ(kernel (q n), U),
      ∀ (a : ↥((sectionsIdeal f I U) ^ (n + 1)))
        (x : sections (R := Γ(X, U)) (fun k => Γ(M k, U))
          (fun k => ((moduleSectionsFunctor (U : X.Opens)).map (q k)).hom)),
        (kernel.ι (q n)).app U (e (a ⊗ₜ[Γ(X, U)] x.val 0)) =
          a.val • x.val (n + 1) := by
  intro M q
  let R : CommRingCat.{u} := Γ(X, U)
  let J : Ideal R := sectionsIdeal f I U
  let s : ∀ k : ℕ, K → Γ(moduleSheaf f I V k ⊗ L.tensorPow d, ⊤) :=
    fun k => freeHomTopSectionsEquiv (moduleSheaf f I V k ⊗ L.tensorPow d) K (α k)
  have hs : ∀ (k : ℕ) (i : K),
      (moduleTransition f I V k ▷ L.tensorPow d).app ⊤ (s (k + 1) i) = s k i := by
    intro k i
    exact (freeHomTopSectionsEquiv_comp
      (moduleSheaf f I V (k + 1) ⊗ L.tensorPow d) K (α (k + 1))
      (moduleTransition f I V k ▷ L.tensorPow d) i).symm.trans
        (congrArg (fun a => freeHomTopSectionsEquiv
          (moduleSheaf f I V k ⊗ L.tensorPow d) K a i) (hα k))
  have hg : ∀ k : ℕ, Epi ((freeHomTopSectionsEquiv
      (moduleSheaf f I V k ⊗ L.tensorPow d) K).symm (s k)) := by
    intro k
    change Epi ((freeHomTopSectionsEquiv
      (moduleSheaf f I V k ⊗ L.tensorPow d) K).symm
        (freeHomTopSectionsEquiv (moduleSheaf f I V k ⊗ L.tensorPow d) K (α k)))
    rw [Equiv.symm_apply_apply]
    exact hgen k
  let N : ℕ → ModuleCat.{u} R := fun k =>
    ModuleCat.of R (affineSyzygyKernel f I V L d K s U t ht k)
  let r : ∀ k : ℕ, N (k + 1) →ₗ[R] N k :=
    fun k => affineSyzygyTransition f I V L d K s U t ht hs k
  let Q : ∀ k : ℕ, Γ(M (k + 1), U) →ₗ[R] Γ(M k, U) :=
    fun k => ((moduleSectionsFunctor (U : X.Opens)).map (q k)).hom
  let E : ∀ k : ℕ, Γ(M k, U) ≃ₗ[R] N k :=
    fun k => levelPresentationKernelSectionsEquiv f I K U V L d α t ht k
  have hE : ∀ k : ℕ, (E k).toLinearMap.comp (Q k) =
      (r k).comp (E (k + 1)).toLinearMap :=
    fun k => levelPresentationKernelSectionsEquiv_transition_linear f I K U V L d α t ht hα k
  obtain ⟨eA, heA, _hunique⟩ :=
    existsUnique_affineSyzygyTransitionKernelTensorEquiv f I V L d K s U t ht hs hL hg n
  let eK : (Q n).ker ≃ₗ[R] (r n).ker :=
    linearKernelEquiv (R := R) (M₀ := Γ(M n, U)) (M₁ := Γ(M (n + 1), U))
      (N₀ := N n) (N₁ := N (n + 1)) (Q n) (r n) (E n) (E (n + 1)) (hE n)
  let eS : Γ(kernel (q n), U) ≃ₗ[R] (Q n).ker := kernelSectionsEquiv (q n) (U : X.Opens)
  let e : (↥(J ^ (n + 1)) ⊗[R] Γ(M 0, U)) ≃ₗ[R] Γ(kernel (q n), U) :=
    (TensorProduct.congr (LinearEquiv.refl R ↥(J ^ (n + 1))) (E 0)).trans
      (eA.trans (eK.symm.trans eS.symm))
  have he (a : ↥(J ^ (n + 1))) (x : sections (R := Γ(X, U)) (fun k => Γ(M k, U)) Q) :
      (kernel.ι (q n)).app U (e (a ⊗ₜ[R] x.val 0)) = a.val • x.val (n + 1) := by
    let y : sections (R := R) (fun k => N k) r := ⟨fun k => E k (x.val k), by
      intro k
      exact (LinearMap.congr_fun (hE k) (x.val (k + 1))).symm.trans
        (congrArg (E k) (x.property k))⟩
    have hA : (eA (a ⊗ₜ[R] E 0 (x.val 0))).val = a.val • E (n + 1) (x.val (n + 1)) :=
      heA a y
    have hTensor :
        TensorProduct.congr (LinearEquiv.refl R ↥(J ^ (n + 1))) (E 0)
          (a ⊗ₜ[R] x.val 0) = a ⊗ₜ[R] E 0 (x.val 0) :=
      TensorProduct.congr_tmul _ _ _ _
    have hStart := congrArg
      (fun z => (kernel.ι (q n)).app U (eS.symm (eK.symm (eA z)))) hTensor
    have hS := kernelSectionsEquiv_symm_apply (q n) (U : X.Opens)
      (eK.symm (eA (a ⊗ₜ[R] E 0 (x.val 0))))
    refine hStart.trans (hS.trans ?_)
    change (E (n + 1)).symm (eA (a ⊗ₜ[R] E 0 (x.val 0))).val = _
    exact (congrArg (E (n + 1)).symm hA).trans
      (((E (n + 1)).symm.map_smul a.val (E (n + 1) (x.val (n + 1)))).trans
        (congrArg (fun z : Γ(M (n + 1), U) => a.val • z)
          ((E (n + 1)).symm_apply_apply (x.val (n + 1)))))
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro z
  have hQ : ∀ k : ℕ, Function.Surjective (Q k) :=
    fun k => levelPresentationKernelTransition_sections_surjective
      f I K U V L d α t ht hα hL k (hgen (k + 1))
  obtain ⟨x, rfl⟩ := eval_zero_surjective (R := R) (fun k => Γ(M k, U)) Q hQ z
  apply eS.injective
  apply Subtype.ext
  exact (kernelSectionsEquiv_apply (q n) (U : X.Opens) _).trans
    ((he' a x).trans ((he a x).symm.trans
      (kernelSectionsEquiv_apply (q n) (U : X.Opens) _).symm))

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
