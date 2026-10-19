/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FiniteSchemeScalarNaturality
import Nyll.SchemeTheory.Descent.FGSubalgebra
import Nyll.SchemeTheory.Descent.SubalgebraStages
import Nyll.SchemeTheory.Descent.SubalgebraStagesIsLimitCone
import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.RingTheory.Adjoin.FG

/-!
# Finite coefficient models for constant extension

A finite étale cover after extending constants descends to an actual finitely
generated coefficient subalgebra. The source is the given cover, and the
recovery isomorphism uses the native finite étale pullback along the actual
coefficient inclusion. Quasicompactness and quasiseparatedness suffice here.

This is the finite-presentation descent step in Stacks Project, Lemma 58.9.3,
https://stacks.math.columbia.edu/tag/0A49. The comparison with a rational fibre
is a separate step.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open SchemeTheory.Affine.FiniteScheme

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- Every finite étale cover after constant extension has a finite étale
model over a finitely generated subalgebra, recovering the original cover
under the literal coefficient map. -/
theorem exists_fg_constant_extension_model
    (k L : Type u) [Field k] [CommRing L] [Algebra k L]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [QuasiSeparated f]
    (W : FiniteEtale (Limits.pullback f (coefficientMap (K := k) L))) :
    ∃ A : Subalgebra k L, A.FG ∧
      ∃ N : FiniteEtale (Limits.pullback f (coefficientMap (K := k) A)),
        Nonempty ((FiniteEtale.pullback (coefficientPullbackMap f A.val)).obj N ≅ W) := by
  classical
  let S : FGSubalgebra k L →o Subalgebra k L :=
    { toFun := fun A => A.1
      monotone' := fun _ _ h => h }
  have hS : ∀ a : L, ∃ i : FGSubalgebra k L, a ∈ S i := by
    intro a
    refine ⟨⟨Algebra.adjoin k (↑({a} : Finset L) : Set L),
      Subalgebra.fg_adjoin_finset ({a} : Finset L)⟩, ?_⟩
    exact Algebra.subset_adjoin (Finset.mem_singleton_self a)
  let hlimit : IsLimit (SubalgebraStages.cone S f) :=
    Classical.choice (SubalgebraStages.nonempty_isLimit_cone S hS f)
  obtain ⟨i, N, hN⟩ := exists_inverse_limit_model
    (SubalgebraStages.diagram S f) (SubalgebraStages.cone S f) hlimit W
  exact ⟨i.unop.1, i.unop.2, N, hN⟩

end AlgebraicGeometry.FiniteEtale
