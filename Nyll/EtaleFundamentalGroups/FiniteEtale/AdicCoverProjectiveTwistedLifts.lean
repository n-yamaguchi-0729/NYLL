/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverKernelCech
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTransitionKernels
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTwistedSectionLifts
import Nyll.SchemeTheory.Cohomology.Cech.ReesTensorUniformVanishing
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
import Nyll.SchemeTheory.Modules.Quasicoherent.DirectImageAlgebraQuasicoherent
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Uniform global lifts in the actual projective finite étale tower

The native Rees tensor construction gives one twist bound for all ideal
powers of the first-stage coherent cover module. The original affine
kernel comparison transfers it to every original transition kernel.
Thus every first-stage global section after any sufficiently large twist
extends to a family of original global sections compatible at all stages.

All vanishing statements are proved from the original cover over the
first infinitesimal thickening and the Noetherian coefficient ring.
No kernel vanishing or formal presentation is an additional input.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace
open AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ)

local notation "X" => Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

private theorem twistingPow_quasicoherent (d : ℕ) :
    SheafOfModules.IsQuasicoherent (R := (X).ringCatSheaf)
      ((twistingSheaf R n).tensorPow d) := by
  let U : (X).Modules := 𝟙_ (X).Modules
  let T : (X).Modules := (twistingSheaf R n).tensorPow d
  have : SheafOfModules.IsQuasicoherent (R := (X).ringCatSheaf) U :=
    isQuasicoherent_unit X
  have ht : SheafOfModules.IsQuasicoherent (R := (X).ringCatSheaf) (tensor U T) :=
    isQuasicoherent_tensor_twistingSheaf R n U d
  let E : (X).Modules ≌ SheafOfModules.{u} (X).ringCatSheaf := sheafOfModulesEquivalence X
  let e : E.functor.obj (tensor U T) ≅ E.functor.obj T := E.functor.mapIso (λ_ T)
  exact (SheafOfModules.isQuasicoherent (C := (X).Opens) (X).ringCatSheaf).prop_of_iso e ht

variable [IsNoetherianRing R]
  (V : MorphismProperty.Over
    ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level (π R n) I 0))

/-- One twist bound kills all positive Čech cohomology groups of all
original transition kernels in the projective cover tower. -/
theorem exists_projective_twisting_bound_kernel_HSucc :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ a k : ℕ,
      Subsingleton ((toOModulePresheaf (π R n)
        (tensor (transitionKernelSheaf (π R n) I V a)
          ((twistingSheaf R n).tensorPow d))).HSucc (stdCoverPullback (𝟙 X)) k) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (π R n)
  let M : (X).Modules := moduleSheaf (π R n) I V 0
  obtain ⟨c, hc⟩ :=
    exists_idealTensor_coefficient_twisting_bound_subsingleton_HSucc R I n M
  refine ⟨c, ?_⟩
  intro d hd a k
  let N : (X).Modules := (twistingSheaf R n).tensorPow d
  have : SheafOfModules.IsQuasicoherent (R := (X).ringCatSheaf) N :=
    twistingPow_quasicoherent R n d
  have : Subsingleton ((ReesTensor.idealTensorPresheaf (π R n) I
      (tensor M N) (a + 1)).HSucc (stdCoverPullback (𝟙 X)) k) := hc d hd (a + 1) k
  let e := transitionKernelIdealTensorHSuccEquiv (π R n) I V N
    (stdCoverPullback (𝟙 X)) a k
  exact ⟨fun x y => e.symm.injective (Subsingleton.elim (e.symm x) (e.symm y))⟩

/-- Every sufficiently large twist permits each original first-stage
global section to lift through all actual cover transitions at once. -/
theorem exists_projective_twisting_bound_globalLifts :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d →
      ∀ z : Γ(tensor (moduleSheaf (π R n) I V 0) ((twistingSheaf R n).tensorPow d), ⊤),
        ∃ s : ∀ a : ℕ,
          Γ(tensor (moduleSheaf (π R n) I V a) ((twistingSheaf R n).tensorPow d), ⊤),
          s 0 = z ∧ ∀ a : ℕ,
            (moduleTransition (π R n) I V a ▷ (twistingSheaf R n).tensorPow d).app ⊤
              (s (a + 1)) = s a := by
  obtain ⟨c, hc⟩ := exists_projective_twisting_bound_kernel_HSucc R I n V
  refine ⟨c, ?_⟩
  intro d hd z
  exact exists_compatible_tensorPow_globalSections (π R n) I V
    (stdCoverPullback (𝟙 X)) (twistingSheaf R n) d (isInvertible_twistingSheaf R n)
    (fun a => hc d hd a 0) z

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
