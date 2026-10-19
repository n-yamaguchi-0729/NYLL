/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Cech.ReesTensorCechComparison
import Nyll.SchemeTheory.Cohomology.Cech.ReesTensorCechVanishing
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorModule
import Nyll.SchemeTheory.Cohomology.Sheaves.ReesTensorPresheaf
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafFiniteType
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# One twist bound for every actual ideal-power tensor complex

For a native coherent module on projective space over a Noetherian ring,
Serre vanishing for its constructed Rees coefficient sheaf gives one
twist bound for all positive degrees. The actual affine and cochain
comparisons transport that vanishing to the original Rees tensor complex.

Every original ideal-power tensor complex is a homogeneous retract of
this complex. The same bound therefore works simultaneously for every
ideal power and every positive cohomological degree on the original
standard ordered cover. Neither flatness of the coefficient sheaf nor
vanishing of any formal-system kernel is an additional assumption.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

open AlgebraicGeometry AlgebraicGeometry.ProjSpace Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)

local notation "X" => Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

/-- One nonnegative twist bound kills every positive Čech degree of
every original ideal-power tensor with the actual twisted module. -/
theorem exists_idealTensor_coefficient_twisting_bound_subsingleton_HSucc
    (M : (X).Modules)
    [SheafOfModules.IsQuasicoherent (R := (X).ringCatSheaf) M]
    [SheafOfModules.IsFiniteType (R := (X).ringCatSheaf) M] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ a k : ℕ,
      Subsingleton ((ReesTensor.idealTensorPresheaf (π R n) I
        (M ⊗ (twistingSheaf R n).tensorPow d) a).HSucc (stdCoverPullback (𝟙 X)) k) := by
  obtain ⟨c, hc⟩ :=
    exists_imageTensor_coefficient_twisting_bound_subsingleton_HSucc R I n M
  refine ⟨c, ?_⟩
  intro d hd a k
  let N : (X).Modules := M ⊗ (twistingSheaf R n).tensorPow d
  have : SheafOfModules.IsQuasicoherent (R := (X).ringCatSheaf) N :=
    isQuasicoherent_tensor_twistingSheaf R n M d
  have : Subsingleton ((toOModulePresheaf (π' I (π R n))
      (imageTensorModule I (π R n) N)).HSucc
        (K' I (π R n) (stdCoverPullback (𝟙 X))) k) := hc d hd k
  have : Subsingleton ((ReesTensor.reesTensorPresheaf (π R n) I N).HSucc
      (stdCoverPullback (𝟙 X)) k) :=
    imageTensor_subsingleton_reesTensorHSucc I (π R n) (stdCoverPullback (𝟙 X)) N k
  exact ReesTensor.subsingleton_idealTensorHSucc (π R n) I N
    (stdCoverPullback (𝟙 X)) a k

end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS
