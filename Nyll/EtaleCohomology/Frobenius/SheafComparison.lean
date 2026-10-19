/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.Frobenius
import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
import Nyll.EtaleCohomology.Sites.BaseChange
import Nyll.EtaleCohomology.Sites.SheafFunctors
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Sites.Continuous

/-!
# Frobenius invariance of étale sheaves

The isomorphism between each étale scheme and its Frobenius pullback gives
a natural comparison from actual direct image to the identity functor.
Uniqueness of left adjoints then identifies actual inverse image with the
identity functor. This applies to arbitrary module or abelian sheaves.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

variable (k : Type u) [Field k] [Fintype k] (X : Scheme.{u})
  [X.Over (Spec (.of k))]

/-- Actual direct image along finite-field Frobenius preserves each module sheaf. -/
def etaleFrobeniusPushforwardIso (R : Type u) [CommRing R] :
    etalePushforward (X.finiteFieldFrobenius k) R ≅
      𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  Functor.sheafPushforwardContinuousId'
    (show etaleBaseChange (X.finiteFieldFrobenius k) ≅ 𝟭 X.Etale from
      (Scheme.Etale.finiteFieldFrobeniusPullbackIso k X).symm)
    (ModuleCat.{u} R) X.smallEtaleTopology

/-- Actual inverse image along finite-field Frobenius preserves each module sheaf. -/
def etaleFrobeniusPullbackIso (R : Type u) [CommRing R] :
    etalePullback (X.finiteFieldFrobenius k) R ≅
      𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  (etalePullbackPushforwardAdjunction (X.finiteFieldFrobenius k) R).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (etaleFrobeniusPushforwardIso k X R).symm)

/-- Actual abelian direct image along finite-field Frobenius is the identity
up to the comparison supplied by relative Frobenius. -/
def etaleAbelianFrobeniusPushforwardIso :
    etaleAbelianPushforward (X.finiteFieldFrobenius k) ≅
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  Functor.sheafPushforwardContinuousId'
    (show etaleBaseChange (X.finiteFieldFrobenius k) ≅ 𝟭 X.Etale from
      (Scheme.Etale.finiteFieldFrobeniusPullbackIso k X).symm)
    AddCommGrpCat.{u} X.smallEtaleTopology

/-- Actual abelian inverse image along finite-field Frobenius is the identity
up to its adjunction-compatible comparison. -/
def etaleAbelianFrobeniusPullbackIso :
    etaleAbelianPullback (X.finiteFieldFrobenius k) ≅
      𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  (etaleAbelianPullbackPushforwardAdjunction (X.finiteFieldFrobenius k)).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight (etaleAbelianFrobeniusPushforwardIso k X).symm)

instance etaleFrobeniusPullback_isEquivalence (R : Type u) [CommRing R] :
    (etalePullback (X.finiteFieldFrobenius k) R).IsEquivalence :=
  Functor.isEquivalence_of_iso (etaleFrobeniusPullbackIso k X R).symm

instance etaleAbelianFrobeniusPullback_isEquivalence :
    (etaleAbelianPullback (X.finiteFieldFrobenius k)).IsEquivalence :=
  Functor.isEquivalence_of_iso (etaleAbelianFrobeniusPullbackIso k X).symm

end EtaleCohomology
