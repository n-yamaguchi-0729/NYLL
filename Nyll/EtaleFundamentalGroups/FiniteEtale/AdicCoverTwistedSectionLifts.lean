/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTransitionKernels
import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafGlobalLifting
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.Sections.InverseLimit
import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
import Nyll.SchemeTheory.Modules.Tensor.InvertibleExactness
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Global lifts in the original finite étale tower after an invertible twist

The original transition-kernel sequence remains short exact after every
nonnegative invertible twist. Its terms are genuinely quasicoherent,
as follows from the original cover modules and the local tensor frames.
Vanishing of the actual kernel's first Čech cohomology therefore makes
the original twisted transition surjective on global sections.

When the same twist kills that first cohomology at every stage, the
existing successive-lift construction extends each original stage-zero
section to an actual family compatible with all the original transitions.
No generation or presentation of the formal system is assumed here.
The concrete kernel cohomology premise is the target of the separate
Rees comparison and uniform vanishing construction.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsSeparated f] (I : Ideal A)
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level f I 0))
  (K : X.OrderedAffineCover) (L : X.Modules) (d : ℕ)

/-- Vanishing for the actual twisted kernel gives global surjectivity of the original
twisted cover transition, with no separately chosen replacement map. -/
theorem moduleTransition_tensorPow_globalSections_surjective
    (hL : IsInvertible L) (n : ℕ)
    [Subsingleton ((toOModulePresheaf f
      (transitionKernelSheaf f I V n ⊗ L.tensorPow d)).HSucc K 0)] :
    Function.Surjective ((moduleTransition f I V n ▷ L.tensorPow d).app ⊤) := by
  let S : ShortComplex X.Modules := transitionKernelSequence f I V n
  let T : ShortComplex X.Modules := S.map (tensorRight (L.tensorPow d))
  have hT : T.ShortExact := hL.shortExact_tensorRight_tensorPow d S
    (transitionKernelSequence_shortExact f I V n)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) T.X₂ :=
    IsInvertible.isQuasicoherent_tensorPow (moduleSheaf f I V (n + 1)) hL d
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) T.X₃ :=
    IsInvertible.isQuasicoherent_tensorPow (moduleSheaf f I V n) hL d
  have : Subsingleton ((toOModulePresheaf f T.X₁).HSucc K 0) :=
    inferInstanceAs (Subsingleton ((toOModulePresheaf f
      (transitionKernelSheaf f I V n ⊗ L.tensorPow d)).HSucc K 0))
  exact globalSections_surjective_of_shortExact_of_subsingleton_H1 f K T hT

/-- A common twist whose actual kernel cohomology vanishes at every stage extends each
first-stage global section to a family satisfying the original transition equations. -/
theorem exists_compatible_tensorPow_globalSections
    (hL : IsInvertible L)
    (hH1 : ∀ n : ℕ, Subsingleton ((toOModulePresheaf f
      (transitionKernelSheaf f I V n ⊗ L.tensorPow d)).HSucc K 0))
    (z : Γ(moduleSheaf f I V 0 ⊗ L.tensorPow d, ⊤)) :
    ∃ s : ∀ n : ℕ, Γ(moduleSheaf f I V n ⊗ L.tensorPow d, ⊤),
      s 0 = z ∧ ∀ n : ℕ, (moduleTransition f I V n ▷ L.tensorPow d).app ⊤
        (s (n + 1)) = s n := by
  let P : ℕ → ModuleCat.{u} Γ(X, ⊤) := fun n =>
    (moduleSectionsFunctor (⊤ : X.Opens)).obj (moduleSheaf f I V n ⊗ L.tensorPow d)
  let t : ∀ n : ℕ, P (n + 1) →ₗ[Γ(X, ⊤)] P n := fun n =>
    ((moduleSectionsFunctor (⊤ : X.Opens)).map
      (moduleTransition f I V n ▷ L.tensorPow d)).hom
  have ht : ∀ n : ℕ, Function.Surjective (t n) := by
    intro n
    have : Subsingleton ((toOModulePresheaf f
        (transitionKernelSheaf f I V n ⊗ L.tensorPow d)).HSucc K 0) := hH1 n
    exact moduleTransition_tensorPow_globalSections_surjective f I V K L d hL n
  obtain ⟨s, hs⟩ := AdicModuleSystem.eval_zero_surjective
    (fun n : ℕ => P n) t ht z
  exact ⟨s.val, hs, s.property⟩

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
