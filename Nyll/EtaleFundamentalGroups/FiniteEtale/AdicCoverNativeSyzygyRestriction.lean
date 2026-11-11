/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverKernelRestriction
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygySections
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverNativeSyzygyLayers
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.LocalMorphisms
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Original restrictions of the native syzygy layers

The actual native syzygy transition kernels admit the ideal-tensor
comparisons constructed in `AdicCoverNativeSyzygyLayers`. On two nested
affine opens these comparisons can be chosen with their original
inclusion formulas and with a commuting restriction square.

The proof uses the actual existence theorem on each affine open, then
restricts compatible sequences componentwise. The frames on the two
affine opens may be chosen independently.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules AdicModuleSystem

/-- Native sheaf naturality expressed using the original evaluation
functor, before a concrete syzygy transition is substituted. -/
private theorem evaluated_restriction_naturality {Y : Scheme.{u}}
    {M N : Y.Modules} (φ : M ⟶ N) {U W : Y.Opens} (h : W ≤ U) (x : Γ(M, U)) :
    ((moduleSectionsFunctor W).map φ).hom
        (M.val.restrictₛₗ (homOfLE h).op x) =
      N.val.restrictₛₗ (homOfLE h).op
        (((moduleSectionsFunctor U).map φ).hom x) := by
  exact congrArg (fun r : Γ(M, U) ⟶ Γ(N, W) => r x)
    (φ.mapPresheaf.naturality (homOfLE h).op)

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
/-- The actual native syzygy layers on nested affine opens have tensor
comparisons which retain the original inclusion formulas and commute
with the original scalar and sheaf restrictions. The two frames need
not be compatible. -/
theorem exists_levelPresentationKernelTensorEquiv_restriction
    (U W : X.affineOpens) (h : (W : X.Opens) ≤ U)
    (tU : Γ(L.tensorPow d, U)) (htU : IsFrameOn tU (U : X.Opens))
    (tW : Γ(L.tensorPow d, W)) (htW : IsFrameOn tW (W : X.Opens)) (n : ℕ) :
    let M : ℕ → X.Modules := fun k => levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) k (α k)
    let q : ∀ k : ℕ, M (k + 1) ⟶ M k := fun k =>
      levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα k
    ∃ (eU : (↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] Γ(M 0, U))
        ≃ₗ[Γ(X, U)] Γ(kernel (q n), U))
      (eW : (↥((sectionsIdeal f I W) ^ (n + 1)) ⊗[Γ(X, W)] Γ(M 0, W))
        ≃ₗ[Γ(X, W)] Γ(kernel (q n), W)),
      (∀ (a : ↥((sectionsIdeal f I U) ^ (n + 1)))
        (x : sections (R := Γ(X, U)) (fun k => Γ(M k, U))
          (fun k => ((moduleSectionsFunctor (U : X.Opens)).map (q k)).hom)),
        (kernel.ι (q n)).app U (eU (a ⊗ₜ[Γ(X, U)] x.val 0)) =
          a.val • x.val (n + 1)) ∧
      (∀ (a : ↥((sectionsIdeal f I W) ^ (n + 1)))
        (x : sections (R := Γ(X, W)) (fun k => Γ(M k, W))
          (fun k => ((moduleSectionsFunctor (W : X.Opens)).map (q k)).hom)),
        (kernel.ι (q n)).app W (eW (a ⊗ₜ[Γ(X, W)] x.val 0)) =
          a.val • x.val (n + 1)) ∧
      ∀ z : ↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] Γ(M 0, U),
        (kernel (q n)).val.restrictₛₗ (homOfLE h).op (eU z) =
          eW (TensorProduct.map (idealPowerRestriction f I h (n + 1))
            (show Γ(M 0, U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(M 0, W)
              from (M 0).val.restrictₛₗ (homOfLE h).op) z) := by
  intro M q
  obtain ⟨eU, heU, _huniqueU⟩ :=
    existsUnique_levelPresentationKernelTensorEquiv
      f I V L d K α hα hL hgen U tU htU n
  obtain ⟨eW, heW, _huniqueW⟩ :=
    existsUnique_levelPresentationKernelTensorEquiv
      f I V L d K α hα hL hgen W tW htW n
  refine ⟨eU, eW, heU, heW, ?_⟩
  intro z
  let QU : ∀ k : ℕ, Γ(M (k + 1), U) →ₗ[Γ(X, U)] Γ(M k, U) :=
    fun k => ((moduleSectionsFunctor (U : X.Opens)).map (q k)).hom
  let QW : ∀ k : ℕ, Γ(M (k + 1), W) →ₗ[Γ(X, W)] Γ(M k, W) :=
    fun k => ((moduleSectionsFunctor (W : X.Opens)).map (q k)).hom
  induction z using TensorProduct.inductionOn with
  | tmul a y =>
      have hQU : ∀ k : ℕ, Function.Surjective (QU k) :=
        fun k => levelPresentationKernelTransition_sections_surjective
          f I K U V L d α tU htU hα hL k (hgen (k + 1))
      obtain ⟨x, rfl⟩ := eval_zero_surjective (R := Γ(X, U)) (fun k => Γ(M k, U)) QU hQU y
      let xW : sections (R := Γ(X, W)) (fun k => Γ(M k, W)) QW :=
        ⟨fun k => (M k).val.restrictₛₗ (homOfLE h).op (x.val k), by
          intro k
          exact (evaluated_restriction_naturality (q k) h (x.val (k + 1))).trans
            (congrArg ((M k).val.restrictₛₗ (homOfLE h).op) (x.property k))⟩
      apply (Scheme.Modules.Hom.mono_iff_injective (kernel.ι (q n))).mp
        (inferInstance : Mono (kernel.ι (q n))) W
      let k : Γ(kernel (q n), U) := eU (a ⊗ₜ[Γ(X, U)] x.val 0)
      have hnat := congrArg
        (fun r : Γ(kernel (q n), U) ⟶ Γ(M (n + 1), W) => r k)
        ((kernel.ι (q n)).mapPresheaf.naturality (homOfLE h).op)
      have hU := heU a x
      have hW := heW (idealPowerRestriction f I h (n + 1) a) xW
      rw [TensorProduct.map_tmul]
      exact hnat.trans
        ((congrArg ((M (n + 1)).val.restrictₛₗ (homOfLE h).op) hU).trans
          ((((M (n + 1)).val.restrictₛₗ (homOfLE h).op).map_smulₛₗ
            a.val (x.val (n + 1))).trans hW.symm))
  | add x y hx hy =>
      let r : Γ(kernel (q n), U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
          Γ(kernel (q n), W) := (kernel (q n)).val.restrictₛₗ (homOfLE h).op
      let T : (↥((sectionsIdeal f I U) ^ (n + 1)) ⊗[Γ(X, U)] Γ(M 0, U))
          →ₛₗ[(X.presheaf.map (homOfLE h).op).hom]
          (↥((sectionsIdeal f I W) ^ (n + 1)) ⊗[Γ(X, W)] Γ(M 0, W)) :=
        TensorProduct.map (idealPowerRestriction f I h (n + 1))
          (show Γ(M 0, U) →ₛₗ[(X.presheaf.map (homOfLE h).op).hom] Γ(M 0, W)
            from (M 0).val.restrictₛₗ (homOfLE h).op)
      change r (eU (x + y)) = eW (T (x + y))
      exact (congrArg r (eU.map_add x y)).trans
        ((r.map_add (eU x) (eU y)).trans
          ((congrArg₂ (fun a b : Γ(kernel (q n), W) => a + b) hx hy).trans
            ((eW.map_add (T x) (T y)).symm.trans
              (congrArg eW (T.map_add x y).symm))))

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
