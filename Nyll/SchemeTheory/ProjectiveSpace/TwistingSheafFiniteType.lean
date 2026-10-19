/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.Modules.Tensor.InvertibleCoherence
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Quasicoherence and finite type of actual projective twists

Powers of the coordinate frames give actual native slice isomorphisms
between a module and each of its nonnegative twists. Quasicoherence and
finite type therefore pass to the tensor twists through their defining
locality theorems.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.ProjSpace

open Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- Tensoring by a power of the actual twisting sheaf preserves
quasicoherence. -/
theorem isQuasicoherent_tensor_twistingSheaf (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf) F] (d : ℕ) :
    SheafOfModules.IsQuasicoherent (R := (Proj 𝒜).ringCatSheaf)
      (Scheme.Modules.tensor (X := Proj 𝒜) F ((twistingSheaf R n).tensorPow d)) :=
  IsInvertible.isQuasicoherent_tensorPow F (isInvertible_twistingSheaf R n) d

/-- Tensoring by a power of the actual twisting sheaf preserves finite type. -/
theorem isFiniteType_tensor_twistingSheaf (F : (Proj 𝒜).Modules)
    [SheafOfModules.IsFiniteType (R := (Proj 𝒜).ringCatSheaf) F] (d : ℕ) :
    SheafOfModules.IsFiniteType (R := (Proj 𝒜).ringCatSheaf)
      (Scheme.Modules.tensor (X := Proj 𝒜) F ((twistingSheaf R n).tensorPow d)) :=
  IsInvertible.isFiniteType_tensorPow F (isInvertible_twistingSheaf R n) d

end AlgebraicGeometry.ProjSpace
