/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.FGSubalgebra
import Nyll.SchemeTheory.Descent.SubalgebraStages
import Nyll.SchemeTheory.Descent.SubalgebraStagesIsLimitCone
import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Order.Hom.Basic
import Mathlib.RingTheory.Adjoin.FG

/-!
# Finite coefficient models over an arbitrary commutative ring

Let `A → B` be any algebra and let `X` be quasicompact and quasiseparated
over `Spec A`. An actual finite étale cover of `X_B` descends to `X_C` for
an actual finitely generated `A`-subalgebra `C` of `B`.

The proof uses the directed family of all finitely generated subalgebras,
the constructed inverse-limit cone of their base changes, and finite étale
inverse-limit descent. Recovery is along `SubalgebraStages.leg`, whose two
projections are the original map to `X` and the original inclusion `C → B`.
No field, injectivity, Noetherian, or properness assumption is needed.

This is the finite-coefficient step useful in the approximation argument of
Stacks Project, Lemma 58.9.1, https://stacks.math.columbia.edu/tag/0A48.
It starts from an actual cover over `B`; it does not construct a cover over
a completion or a homomorphism from the coefficient algebra back to `A`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

/-- An actual finite étale cover after any extension of commutative
coefficient rings has a model over an actual finitely generated subalgebra.
The recovery functor uses the literal coefficient inclusion. -/
theorem exists_fg_coefficient_model
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [QuasiCompact f] [QuasiSeparated f]
    (W : FiniteEtale (Limits.pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap A B))))) :
    ∃ C : Subalgebra A B, C.FG ∧
      ∃ N : FiniteEtale (Limits.pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap A C)))),
        Nonempty ((FiniteEtale.pullback (SubalgebraStages.leg
          (OrderHom.id : Subalgebra A B →o Subalgebra A B) f C)).obj N ≅ W) := by
  classical
  let S : FGSubalgebra A B →o Subalgebra A B :=
    { toFun := fun C => C.1
      monotone' := fun _ _ h => h }
  have hS : ∀ b : B, ∃ i : FGSubalgebra A B, b ∈ S i := by
    intro b
    refine ⟨⟨Algebra.adjoin A (↑({b} : Finset B) : Set B),
      Subalgebra.fg_adjoin_finset ({b} : Finset B)⟩, ?_⟩
    exact Algebra.subset_adjoin (Finset.mem_singleton_self b)
  let hc : IsLimit (SubalgebraStages.cone S f) :=
    Classical.choice (SubalgebraStages.nonempty_isLimit_cone S hS f)
  obtain ⟨i, N, hN⟩ := exists_inverse_limit_model
    (SubalgebraStages.diagram S f) (SubalgebraStages.cone S f) hc W
  exact ⟨i.unop.1, i.unop.2, N, hN⟩

end AlgebraicGeometry.FiniteEtale
