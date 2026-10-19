/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ModuleSheafCohomologyIso
import Nyll.SchemeTheory.Cohomology.Cech.ReesTensorCechComparison
import Nyll.SchemeTheory.Cohomology.Cech.ReesTensorCechVanishing
import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafDEqDDMemPow
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorModule
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
import Nyll.SchemeTheory.Modules.Invertible.Invertible
import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.ClosedImmersionSerreBaseChange
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Uniform ideal-power Serre vanishing on an actual projective closed subscheme

The literal Rees coefficient pullback of the original closed subscheme
has its constructed projective closed embedding. Apply native Serre
vanishing there to the actual Rees image tensored with the actual pulled
back coefficient module. The constructed tensor/pullback isomorphism
places the twisting power back on the original coefficient module.

The actual affine and cochain comparisons then return to the original
Rees tensor complex. Each original ideal-power tensor complex is its
homogeneous retract. Thus one twist bound works for every ideal power
and every positive cohomological degree, without assuming flatness of
the coefficient module or any vanishing of formal-system kernels.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

open AlgebraicGeometry AlgebraicGeometry.ProjSpace Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ)


variable {Y : Scheme.{u}} (j : Y ⟶ (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))
  [IsClosedImmersion j]


/-- The original ordered Rees cover is the original coordinate cover
pulled back through the actual first projection and closed embedding. -/
theorem reesClosedProjectiveCover_eq_firstProjection :
    K' I (j ≫ π R n) (stdCoverPullback (A := R) (n := n) j) = stdCoverPullback (A := R) (n := n)
      (fst' I (j ≫ π R n) ≫ j) := rfl

/-- One twist bound kills every positive native Čech degree of a
coherent sheaf on the literal Rees pullback of the closed subscheme. -/
theorem exists_rees_closedImmersion_twisting_bound_subsingleton_HSucc
    [IsNoetherianRing R] (F : (P' I (j ≫ π R n)).Modules)
    [SheafOfModules.IsQuasicoherent (R := (P' I (j ≫ π R n)).ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := (P' I (j ≫ π R n)).ringCatSheaf) F] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Subsingleton ((toOModulePresheaf (R := Rr I) (π' I (j ≫ π R n))
        (F ⊗ ((Scheme.Modules.pullback (fst' I (j ≫ π R n))).obj ((Scheme.Modules.pullback j).obj
          (twistingSheaf R n))).tensorPow d)).HSucc
          (K' I (j ≫ π R n) (stdCoverPullback (A := R) (n := n) j)) k) := by
  obtain ⟨c, hc⟩ :=
    exists_closedImmersion_baseChange_twisting_bound_subsingleton_HSucc R (Rr I) n j F
  refine ⟨c, ?_⟩
  intro d hd k
  rw [reesClosedProjectiveCover_eq_firstProjection R I n j]
  exact hc d hd k

/-- The same uniform bound applies with twisting on the original
coefficient sheaf in the actual Rees image construction. -/
theorem exists_imageTensor_closedImmersion_coefficient_twisting_bound_subsingleton_HSucc
    [IsNoetherianRing R] (M : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M]
    [SheafOfModules.IsFiniteType (R := Y.ringCatSheaf) M] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ k : ℕ,
      Subsingleton ((toOModulePresheaf (R := Rr I) (π' I (j ≫ π R n))
        (imageTensorModule I (j ≫ π R n) (M ⊗ ((Scheme.Modules.pullback j).obj (twistingSheaf R
          n)).tensorPow d))).HSucc (K' I (j ≫ π R n) (stdCoverPullback (A := R) (n := n) j)) k)
          := by
  have hQC : (imageTensorModule I (j ≫ π R n) M).IsQuasicoherent :=
    imageTensorModule_isQuasicoherent I (j ≫ π R n) M
  have hFT : (imageTensorModule I (j ≫ π R n) M).IsFiniteType := imageTensorModule_isFiniteType I
    (j ≫ π R n) M
  obtain ⟨c, hc⟩ := exists_rees_closedImmersion_twisting_bound_subsingleton_HSucc R I n j
    (imageTensorModule I (j ≫ π R n) M)
  refine ⟨c, ?_⟩
  intro d hd k
  have hVan : Subsingleton ((toOModulePresheaf (R := Rr I) (π' I (j ≫ π R n))
      (imageTensorModule I (j ≫ π R n) M ⊗ ((Scheme.Modules.pullback (fst' I (j ≫ π R n))).obj
        ((Scheme.Modules.pullback j).obj (twistingSheaf R n))).tensorPow d)).HSucc
        (K' I (j ≫ π R n) (stdCoverPullback (A := R) (n := n) j)) k) := hc d hd k
  exact subsingleton_HSucc_of_iso (π' I (j ≫ π R n)) (K' I (j ≫ π R n) (stdCoverPullback (A := R)
    (n := n) j)) (imageTensorTwistIso I (j ≫ π R n) M ((Scheme.Modules.pullback j).obj
    (twistingSheaf R n)) d).symm k

/-- One nonnegative twist bound kills the original ideal-power tensor
cohomology on the actual closed subscheme, for every ideal power and
every positive degree on its original coordinate cover. -/
theorem exists_closedImmersion_idealTensor_coefficient_twisting_bound_subsingleton_HSucc
    [IsNoetherianRing R] (M : Y.Modules)
    [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) M]
    [SheafOfModules.IsFiniteType (R := Y.ringCatSheaf) M] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ a k : ℕ,
      Subsingleton ((ReesTensor.idealTensorPresheaf (j ≫ π R n) I (M ⊗ ((Scheme.Modules.pullback
        j).obj (twistingSheaf R n)).tensorPow d) a).HSucc (stdCoverPullback (A := R) (n := n) j)
        k) := by
  obtain ⟨c, hc⟩ :=
    exists_imageTensor_closedImmersion_coefficient_twisting_bound_subsingleton_HSucc R I n j M
  refine ⟨c, ?_⟩
  intro d hd a k
  let N : Y.Modules := M ⊗ ((Scheme.Modules.pullback j).obj (twistingSheaf R n)).tensorPow d
  have hL : IsInvertible ((Scheme.Modules.pullback j).obj (twistingSheaf R n)) :=
    IsInvertible.pullback j (isInvertible_twistingSheaf R n)
  have hN : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) N :=
    IsInvertible.isQuasicoherent_tensorPow M hL d
  have hNative : Subsingleton ((toOModulePresheaf (R := Rr I) (π' I (j ≫ π R n))
      (imageTensorModule I (j ≫ π R n) N)).HSucc (K' I (j ≫ π R n) (stdCoverPullback (A := R) (n
        := n) j)) k) := hc d hd k
  have hRees : Subsingleton ((ReesTensor.reesTensorPresheaf (j ≫ π R n) I N).HSucc
    (stdCoverPullback (A := R) (n := n) j) k) :=
    imageTensor_subsingleton_reesTensorHSucc I (j ≫ π R n) (stdCoverPullback (A := R) (n := n) j)
      N k
  exact ReesTensor.subsingleton_idealTensorHSucc (j ≫ π R n) I N (stdCoverPullback (A := R) (n :=
    n) j) a k

end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS
