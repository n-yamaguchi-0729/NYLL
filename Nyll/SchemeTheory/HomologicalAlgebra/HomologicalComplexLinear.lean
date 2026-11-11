/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Linearity of homology of complexes

The short complex associated to a degree is linear componentwise, so its
existing linear homology functor supplies linearity of complex homology.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable (R : Type*) [Semiring R] (C : Type*) [Category* C] [Preadditive C]
  [CategoryTheory.Linear R C] {ι : Type*} (c : ComplexShape ι)

instance shortComplexFunctor_linear (j : ι) :
    Functor.Linear R (shortComplexFunctor C c j) where
  map_smul _ _ := rfl

instance homologyFunctor_linear [CategoryWithHomology C] (j : ι) :
    Functor.Linear R (homologyFunctor C c j) :=
  Functor.linear_of_iso R (homologyFunctorIso C c j).symm

end HomologicalComplex
