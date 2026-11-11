/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.ModulePullbackSiteComparison
public import Nyll.EtaleCohomology.Frobenius.ArithmeticComparison
public import Nyll.EtaleCohomology.Sites.PullbackEquivalence

/-!
# Inverse image by Frobenius after extension of constants

After an algebraic extension of the finite ground field, the actual étale
inverse image by base-changed Frobenius is an equivalence. The existing site
comparison identifies it with inverse image by the inverse arithmetic
automorphism of the constants. In particular, the general equivalence
instance supplies preservation of injective module sheaves.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

/-- Inverse image by the base change of finite-field Frobenius is an
equivalence on arbitrary module-valued étale sheaves. -/
instance etaleConstantBaseChangeFrobeniusPullback_isEquivalence
    (k Ω : Type u) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [Algebra.IsAlgebraic k Ω] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (R : Type u) [CommRing R] :
    (etalePullback (Scheme.constantBaseChangeFrobenius k Ω X) R).IsEquivalence := by
  have : IsIso (Scheme.constantFieldTwist k Ω X
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm) :=
    inferInstanceAs (IsIso ((Scheme.constantFieldTwistIso k Ω X
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm).hom))
  exact Functor.isEquivalence_of_iso
    (etalePullbackSiteIso (finiteFieldGeometricArithmeticSiteIso k Ω X) R).symm

end EtaleCohomology
