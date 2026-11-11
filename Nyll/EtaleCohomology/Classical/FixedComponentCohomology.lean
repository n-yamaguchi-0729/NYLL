/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.ComponentCohomologyTrace
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.SchemeTheory.Divisors.FixedComponentIsomorphism
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.LinearAlgebra.Pi

/-!
# The original diagonal block is the actual fixed-component pullback

The original component diagonal uses a projection and a single-coordinate
inclusion to transport between equal component indices. The actual
scheme isomorphism on a fixed component uses equality transport of
that same index. These two original transports induce the same
pullback on the original rational cohomology in every degree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {X : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime]

private theorem component_pullback_transport (i : ℕ) [DecidableEq (irreducibleComponents X)]
    (Z W : irreducibleComponents X)
    (a : X.reducedIrreducibleComponent Z.1 Z.2 ≅ X.reducedIrreducibleComponent W.1 W.2)
    (h : W = Z) :
    (rationalEllAdicCohomologyPullback ℓ a.hom i).comp
        ((LinearMap.proj W).comp (LinearMap.single ℚ_[ℓ]
          (fun U : irreducibleComponents X =>
            rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent U.1 U.2) i) Z)) =
      rationalEllAdicCohomologyPullback ℓ
        (a.trans (eqToIso (congrArg (fun U : irreducibleComponents X =>
          X.reducedIrreducibleComponent U.1 U.2) h))).hom i := by
  classical
  subst W
  change (rationalEllAdicCohomologyPullback ℓ a.hom i).comp
      ((LinearMap.proj Z).comp (LinearMap.single ℚ_[ℓ]
        (fun U : irreducibleComponents X =>
          rationalEllAdicCohomology ℓ (X.reducedIrreducibleComponent U.1 U.2) i) Z)) =
    rationalEllAdicCohomologyPullback ℓ (a.hom ≫ 𝟙 _) i
  rw [LinearMap.proj_comp_single_same, LinearMap.comp_id, Category.comp_id]

/-- The original diagonal block on a fixed component is the pullback
of the actual automorphism of that same original component. -/
theorem rationalEllAdicComponentDiagonal_eq_fixedComponentPullback
    (e : X ≅ X) (i : ℕ) (Z : irreducibleComponents X)
    (hZ : Scheme.irreducibleComponentsIsoEquiv e Z = Z) :
    rationalEllAdicComponentDiagonal e ℓ i Z =
      rationalEllAdicCohomologyPullback ℓ
        (Scheme.reducedIrreducibleFixedComponentIso e Z hZ).hom i := by
  let _ : DecidableEq (irreducibleComponents X) := Classical.decEq _
  have h := component_pullback_transport ℓ i Z (Scheme.irreducibleComponentsIsoEquiv e Z)
    (Scheme.reducedIrreducibleComponentIso e Z) hZ
  exact h

end EtaleCohomology
