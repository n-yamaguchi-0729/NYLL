/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FiniteSchemeAlgebra
import Nyll.SchemeTheory.Affine.SpecFlatBaseChangeSections

/-! The actual finite-scheme coordinate algebra commutes with extension of field coefficients. -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace SchemeTheory.Affine.FiniteScheme

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of K)) [IsFinite q]

/-- The coordinate algebra of the actual base-changed finite scheme is
the tensor product, with the original coefficient algebra as scalar owner. -/
def coordinateAlgebraBaseChangeEquiv :
    A ⊗[K] coordinateAlgebra q ≃ₐ[A]
      coordinateAlgebra (pullback.snd q
        (Spec.map (CommRingCat.ofHom (algebraMap K A)))) :=
  specPullbackSectionsTensorEquiv (A := A) q

/-- The right tensor factor maps by the actual geometric pullback of sections. -/
theorem coordinateAlgebraBaseChangeEquiv_one_tmul (x : coordinateAlgebra q) :
    coordinateAlgebraBaseChangeEquiv (A := A) q (1 ⊗ₜ[K] x) =
      (pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap K A)))).appTop x :=
  specPullbackSectionsTensorEquiv_one_tmul (A := A) q x

end SchemeTheory.Affine.FiniteScheme
