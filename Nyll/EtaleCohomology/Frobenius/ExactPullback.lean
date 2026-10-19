/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.Etale
import Nyll.EtaleCohomology.Classical.PullbackCohomology
import Nyll.EtaleCohomology.Classical.PullbackCoefficients
import Nyll.EtaleCohomology.Frobenius.SheafComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Frobenius pullback preserves classical cohomology

Relative Frobenius on the small étale site supplies an equivalence of actual
sheaf categories. Its map on Ext groups is bijective in every degree, so the
constructed classical cohomology pullback is an additive equivalence and,
with module coefficients, a linear equivalence.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Abelian

namespace EtaleCohomology

variable (k : Type u) [Field k] [Fintype k] (X : Scheme.{u})
  [X.Over (Spec (.of k))]

/-- The actual abelian Frobenius inverse image induces an equivalence on
classical étale cohomology in every degree. -/
def etaleAbelianCohomologyFrobeniusPullbackEquiv
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u} F n ≃+
      Sheaf.H.{u} ((etaleAbelianPullback (X.finiteFieldFrobenius k)).obj F) n :=
  let L := etaleAbelianPullback (X.finiteFieldFrobenius k)
  let e := (etaleAbelianPullbackConstantIso (X.finiteFieldFrobenius k)).app
    (AddCommGrpCat.of (ULift ℤ))
  (AddEquiv.ofBijective (L.mapExtAddHom _ F n)
    (L.mapExt_bijective_of_preservesInjectiveObjects _ F n)).trans
      ((((extFunctor n).mapIso e.symm.op).app (L.obj F)).addCommGroupIsoToAddEquiv)

/-- This equivalence uses the previously constructed pullback map itself. -/
lemma etaleAbelianCohomologyFrobeniusPullbackEquiv_apply
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) (x : Sheaf.H.{u} F n) :
    etaleAbelianCohomologyFrobeniusPullbackEquiv k X F n x =
      etaleAbelianCohomologyPullbackMap (X.finiteFieldFrobenius k) F n x := rfl

variable (R : Type u) [CommRing R]

/-- Bijectivity of the original coefficient-linear Frobenius pullback. -/
theorem etaleCohomologyFrobeniusPullbackMap_bijective
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    Function.Bijective (etaleCohomologyPullbackMap (X.finiteFieldFrobenius k) R F n) := by
  let A := Classical.forgetCoefficients.{u + 1, u, u, u}.obj F
  let L := etaleAbelianPullback (X.finiteFieldFrobenius k)
  let B := Classical.forgetCoefficients.{u + 1, u, u, u}.obj
    ((etalePullback (X.finiteFieldFrobenius k) R).obj F)
  let eF := (etalePullbackForgetCoefficientsIso (X.finiteFieldFrobenius k) R).symm.app F
  let e : Sheaf.H.{u} (L.obj A) n ≃+ Sheaf.H.{u} B n :=
    ((Sheaf.functorH X.smallEtaleTopology n).mapIso eF).addCommGroupIsoToAddEquiv
  change Function.Bijective (fun x =>
    e (etaleAbelianCohomologyFrobeniusPullbackEquiv k X A n x))
  exact e.bijective.comp (etaleAbelianCohomologyFrobeniusPullbackEquiv k X A n).bijective

/-- The actual coefficient-linear Frobenius pullback is a linear equivalence. -/
def etaleCohomologyFrobeniusPullbackEquiv
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) (n : ℕ) :
    etaleCohomology X R F n ≃ₗ[R]
      etaleCohomology X R ((etalePullback (X.finiteFieldFrobenius k) R).obj F) n :=
  LinearEquiv.ofBijective (etaleCohomologyPullbackMap (X.finiteFieldFrobenius k) R F n)
    (etaleCohomologyFrobeniusPullbackMap_bijective k X R F n)

end EtaleCohomology
