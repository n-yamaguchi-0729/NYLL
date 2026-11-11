/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygies
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverLevelSyzygySurjective
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
public import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
public import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafGlobalLifting
public import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
public import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
public import Nyll.SchemeTheory.Modules.Invertible.Invertible
public import Nyll.SchemeTheory.Modules.Sections.InverseLimit
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
public import Nyll.SchemeTheory.Modules.Tensor.InvertibleExactness
public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Compatible global lifts in the native syzygy tower

The original native syzygy transitions are epimorphic. Their actual
kernel sequences are therefore short exact and remain short exact under
an invertible twist. Vanishing of the actual kernel's first Čech
cohomology makes each original twisted transition surjective on global
sections.

A common twist with this vanishing at every stage lifts every original
first-stage section to a compatible family. The vanishing hypotheses
here are the inputs supplied by the separate uniform Rees calculation;
no new kernel comparison, generation, or algebraization is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

private theorem mono_native_kernel {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) : Mono (kernel.ι φ) := inferInstance

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsSeparated f] (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (L : X.Modules) (d : ℕ) [(L.tensorPow d).IsQuasicoherent]
  (K : Type u) [Finite K]
  (α : ∀ n : ℕ, (show X.Modules from SheafOfModules.free K) ⟶
    moduleSheaf f I V n ⊗ L.tensorPow d)
  (hα : ∀ n : ℕ, α (n + 1) ≫ (moduleTransition f I V n ▷ L.tensorPow d) = α n)
  (hL : IsInvertible L) (hgen : ∀ n : ℕ, Epi (α n))

include hL hgen in
/-- Actual first-cohomology vanishing for the twisted native transition
kernel gives surjectivity of the original twisted global-section map. -/
theorem levelPresentationKernelTransition_tensorPow_globalSections_surjective
    (C : X.OrderedAffineCover) (e n : ℕ) :
    let M : ℕ → X.Modules := fun k => levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) k (α k)
    let q : ∀ k : ℕ, M (k + 1) ⟶ M k := fun k =>
      levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα k
    Subsingleton ((toOModulePresheaf f (kernel (q n) ⊗ L.tensorPow e)).HSucc C 0) →
      Function.Surjective ((q n ▷ L.tensorPow e).app ⊤) := by
  intro M q hH1
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι (q n)) (q n) (kernel.condition (q n))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_kernel (q n)
      mono_f := mono_native_kernel (q n)
      epi_g := levelPresentationKernelTransition_epi
        f I V L d K α hα hL n (hgen (n + 1)) }
  let T : ShortComplex X.Modules := S.map (tensorRight (L.tensorPow e))
  have hT : T.ShortExact := hL.shortExact_tensorRight_tensorPow e S hS
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) T.X₂ :=
    IsInvertible.isQuasicoherent_tensorPow (M (n + 1)) hL e
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) T.X₃ :=
    IsInvertible.isQuasicoherent_tensorPow (M n) hL e
  have : Subsingleton ((toOModulePresheaf f T.X₁).HSucc C 0) := hH1
  exact globalSections_surjective_of_shortExact_of_subsingleton_H1 f C T hT

include hL hgen in
/-- A common twist with vanishing first cohomology for all original
native transition kernels extends each first-stage global section to an
actual family compatible with every original twisted transition. -/
theorem exists_compatible_levelPresentationKernel_tensorPow_globalSections
    (C : X.OrderedAffineCover) (e : ℕ) :
    let M : ℕ → X.Modules := fun k => levelPresentationKernel f I V (L.tensorPow d)
      (show X.Modules from SheafOfModules.free K) k (α k)
    let q : ∀ k : ℕ, M (k + 1) ⟶ M k := fun k =>
      levelPresentationKernelTransition f I V (L.tensorPow d)
        (show X.Modules from SheafOfModules.free K) α hα k
    (∀ n : ℕ, Subsingleton
      ((toOModulePresheaf f (kernel (q n) ⊗ L.tensorPow e)).HSucc C 0)) →
      ∀ z : Γ(M 0 ⊗ L.tensorPow e, ⊤),
        ∃ s : ∀ n : ℕ, Γ(M n ⊗ L.tensorPow e, ⊤),
          s 0 = z ∧ ∀ n : ℕ, (q n ▷ L.tensorPow e).app ⊤ (s (n + 1)) = s n := by
  intro M q hH1 z
  let P : ℕ → ModuleCat.{u} Γ(X, ⊤) := fun n =>
    (moduleSectionsFunctor (⊤ : X.Opens)).obj (M n ⊗ L.tensorPow e)
  let t : ∀ n : ℕ, P (n + 1) →ₗ[Γ(X, ⊤)] P n := fun n =>
    ((moduleSectionsFunctor (⊤ : X.Opens)).map (q n ▷ L.tensorPow e)).hom
  have ht : ∀ n : ℕ, Function.Surjective (t n) := fun n =>
    levelPresentationKernelTransition_tensorPow_globalSections_surjective
      f I V L d K α hα hL hgen C e n (hH1 n)
  obtain ⟨s, hs⟩ := AdicModuleSystem.eval_zero_surjective (R := Γ(X, ⊤))
    (fun n : ℕ => P n) t ht z
  exact ⟨s.val, hs, s.property⟩

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
