/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Modules.Tensor.Monoidal
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The actual tensor comparison for open restriction

The native restriction functor is the left adjoint to pushforward along
an open immersion. Its original comparison with pullback, together with
the constructed pullback tensor isomorphism, identifies restriction of
the actual tensor with the tensor of the actual restrictions.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The original open restriction commutes with the native tensor
product through its actual adjunction comparison with pullback. -/
def restrictTensorIso {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M N : Y.Modules) :
    (tensor M N).restrict j ≅ tensor (M.restrict j) (N.restrict j) :=
  (restrictFunctorIsoPullback j).app (tensor M N) ≪≫
    pullbackTensorObjIso j M N ≪≫
      (((restrictFunctorIsoPullback j).app M).symm ⊗ᵢ
        ((restrictFunctorIsoPullback j).app N).symm)

end AlgebraicGeometry.Scheme.Modules
