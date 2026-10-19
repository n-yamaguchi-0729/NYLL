/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverKernelCech
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTwistedSectionLifts
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesClosedProjectiveSerre
import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Uniform lifts on a closed projective family

The actual Rees vanishing theorem for a closed projective subscheme
supplies one bound for every transition kernel of its finite étale tower.
Each sufficiently twisted section of the original closed cover therefore
lifts compatibly through all infinitesimal levels. No flatness of the
projective family, or vanishing premise, is required.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules ProjSpace
open AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
  {Y : Scheme.{u}}
  (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))
  [IsClosedImmersion j]


omit [IsNoetherianRing R] [IsClosedImmersion j] in
private theorem closedTwistingPow_quasicoherent (d : ℕ) :
    SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) (((Scheme.Modules.pullback j).obj
      (twistingSheaf R n)).tensorPow d) := by
  let U : Y.Modules := 𝟙_ Y.Modules
  let T : Y.Modules := ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d
  have : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) U :=
    isQuasicoherent_unit Y
  have hL : IsInvertible ((Scheme.Modules.pullback j).obj (twistingSheaf R n)) :=
    IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  have ht : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) (tensor U T) :=
    IsInvertible.isQuasicoherent_tensorPow U hL d
  let E : Y.Modules ≌ SheafOfModules.{u} Y.ringCatSheaf := sheafOfModulesEquivalence Y
  exact (SheafOfModules.isQuasicoherent (C := Y.Opens) Y.ringCatSheaf).prop_of_iso
    (E.functor.mapIso (λ_ T)) ht

variable (V : MorphismProperty.Over
  ((@IsFinite : MorphismProperty Scheme.{u}) ⊓ @Etale) ⊤ (level (j ≫ π R n) I 0))

/-- One bound works for every actual transition kernel and every positive degree. -/
theorem exists_closedProjective_twisting_bound_kernel_HSucc :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ a k : ℕ,
      Subsingleton ((toOModulePresheaf (j ≫ π R n)
        (tensor (transitionKernelSheaf (j ≫ π R n) I V a) (((Scheme.Modules.pullback j).obj
          (twistingSheaf R n)).tensorPow d))).HSucc (stdCoverPullback (A := R) (n := n) j) k) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (j ≫ π R n)
  obtain ⟨c, hc⟩ :=
    exists_closedImmersion_idealTensor_coefficient_twisting_bound_subsingleton_HSucc
      R I n j (moduleSheaf (j ≫ π R n) I V 0)
  refine ⟨c, ?_⟩
  intro d hd a k
  have : (((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d).IsQuasicoherent :=
    closedTwistingPow_quasicoherent R n j d
  have : Subsingleton ((ReesTensor.idealTensorPresheaf (j ≫ π R n) I
      (tensor (moduleSheaf (j ≫ π R n) I V 0) (((Scheme.Modules.pullback j).obj (twistingSheaf R
        n)).tensorPow d)) (a + 1)).HSucc (stdCoverPullback (A := R) (n := n) j) k) :=
    hc d hd (a + 1) k
  let e := transitionKernelIdealTensorHSuccEquiv (j ≫ π R n) I V (((Scheme.Modules.pullback
    j).obj (twistingSheaf R n)).tensorPow d) (stdCoverPullback (A := R) (n := n) j) a k
  exact ⟨fun x y => e.symm.injective (Subsingleton.elim (e.symm x) (e.symm y))⟩

/-- Original closed-level sections admit compatible lifts at all levels after one twist. -/
theorem exists_closedProjective_twisting_bound_globalLifts :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d →
      ∀ z : Γ(tensor (moduleSheaf (j ≫ π R n) I V 0) (((Scheme.Modules.pullback j).obj
        (twistingSheaf R n)).tensorPow d), ⊤),
        ∃ s : ∀ a : ℕ, Γ(tensor (moduleSheaf (j ≫ π R n) I V a) (((Scheme.Modules.pullback j).obj
          (twistingSheaf R n)).tensorPow d), ⊤),
          s 0 = z ∧ ∀ a : ℕ,
            (moduleTransition (j ≫ π R n) I V a ▷ ((Scheme.Modules.pullback j).obj (twistingSheaf
              R n)).tensorPow d).app ⊤ (s (a + 1)) = s a := by
  obtain ⟨c, hc⟩ := exists_closedProjective_twisting_bound_kernel_HSucc R I n j V
  refine ⟨c, ?_⟩
  intro d hd z
  exact exists_compatible_tensorPow_globalSections (j ≫ π R n) I V (stdCoverPullback (A := R) (n
    := n) j) ((Scheme.Modules.pullback j).obj (twistingSheaf R n)) d
    (IsInvertible.pullback j (isInvertible_twistingSheaf R n))
    (fun a => hc d hd a 0) z

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
