/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.EndomorphismPullbackComposition
import Nyll.EtaleCohomology.Classical.PullbackIdentity
import Nyll.EtaleCohomology.Frobenius.ArithmeticComparison
import Mathlib.Algebra.Group.Hom.End

/-!
# The actual constant-field action on abelian étale cohomology

Automorphisms of the extended constants act through the actual constant-field
scheme automorphisms and canonical constant-coefficient pullback. The group
law follows from the proved identity and composition laws in every degree.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of k))]

local notation "XΩ" => pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))

/-- The actual action of constant-field automorphisms on constant abelian
étale cohomology, with its composition law proved from actual inverse image. -/
def constantFieldAbelianCohomologyAction (A : AddCommGrpCat.{u}) (n : ℕ) :
    (Ω ≃ₐ[k] Ω) →*
      AddMonoid.End
        (Sheaf.H.{u} ((constantSheaf (XΩ).smallEtaleTopology AddCommGrpCat.{u}).obj A) n) where
  toFun σ :=
    (Sheaf.H.map ((etaleAbelianPullbackConstantIso
      (Scheme.constantFieldTwist k Ω X σ)).hom.app A) n).comp
        (etaleAbelianCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X σ)
          ((constantSheaf (XΩ).smallEtaleTopology AddCommGrpCat.{u}).obj A) n)
  map_one' := by
    apply AddMonoidHom.ext
    intro x
    change Sheaf.H.map ((etaleAbelianPullbackConstantIso
        (Scheme.constantFieldTwist k Ω X 1)).hom.app A) n
      (etaleAbelianCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X 1)
        ((constantSheaf (XΩ).smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) = x
    rw [Scheme.constantFieldTwist_one]
    exact etaleAbelianConstantCohomologyPullbackMap_id XΩ A n x
  map_mul' σ τ := by
    apply AddMonoidHom.ext
    intro x
    change Sheaf.H.map ((etaleAbelianPullbackConstantIso
        (Scheme.constantFieldTwist k Ω X (σ * τ))).hom.app A) n
        (etaleAbelianCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X (σ * τ))
          ((constantSheaf (XΩ).smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) =
      Sheaf.H.map ((etaleAbelianPullbackConstantIso
        (Scheme.constantFieldTwist k Ω X σ)).hom.app A) n
        (etaleAbelianCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X σ)
          ((constantSheaf (XΩ).smallEtaleTopology AddCommGrpCat.{u}).obj A) n
          (Sheaf.H.map ((etaleAbelianPullbackConstantIso
            (Scheme.constantFieldTwist k Ω X τ)).hom.app A) n
            (etaleAbelianCohomologyPullbackMap (Scheme.constantFieldTwist k Ω X τ)
              ((constantSheaf (XΩ).smallEtaleTopology AddCommGrpCat.{u}).obj A) n x)))
    rw [Scheme.constantFieldTwist_mul]
    exact etaleAbelianConstantCohomologyEndomorphismPullbackMap_comp
      (Scheme.constantFieldTwist k Ω X σ) (Scheme.constantFieldTwist k Ω X τ) A n x

variable [Fintype k] [Algebra.IsAlgebraic k Ω]

/-- Geometric Frobenius is inverse arithmetic Frobenius in the actual
constant-field action, whose identity and group law have been proved. -/
theorem geometricFrobenius_eq_constantFieldAction_inverseArithmetic
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u} ((constantSheaf (XΩ).smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    Sheaf.H.map
        ((etaleAbelianPullbackConstantIso
          (Scheme.constantBaseChangeFrobenius k Ω X)).hom.app A) n
        (etaleAbelianCohomologyPullbackMap (Scheme.constantBaseChangeFrobenius k Ω X)
          ((constantSheaf (XΩ).smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) =
      constantFieldAbelianCohomologyAction k Ω X A n
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Ω).symm x :=
  geometricFrobenius_eq_inverseArithmetic_on_constantCohomology k Ω X A n x

end EtaleCohomology
