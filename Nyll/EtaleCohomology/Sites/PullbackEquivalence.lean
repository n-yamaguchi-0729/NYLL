/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Sites.BaseChangeIdentity
public import Nyll.EtaleCohomology.Sites.PullbackComposition
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Inverse image along a scheme isomorphism

The actual inverse image by the identity is identified with the identity
through its constructed adjunction. The composition comparison then makes
inverse image along a scheme isomorphism an equivalence. Its preservation
of injective objects follows from the general equivalence instance.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

/-- The actual module inverse image by the identity, compared using its
adjunction and the identity base-change comparison. -/
def etalePullbackIdIso (X : Scheme.{u}) (R : Type u) [CommRing R] :
    etalePullback (𝟙 X) R ≅ 𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) :=
  (etalePullbackPushforwardAdjunction (𝟙 X) R).leftAdjointUniq
    (Adjunction.id.ofNatIsoRight
      (Functor.sheafPushforwardContinuousId' (etaleBaseChangeIdIso X)
        (ModuleCat.{u} R) X.smallEtaleTopology).symm)

/-- Actual module inverse image along a scheme isomorphism is an
equivalence, with inverse image along the inverse scheme morphism. -/
instance etalePullback_isEquivalence_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (R : Type u) [CommRing R] :
    (etalePullback f R).IsEquivalence := by
  let eY : etalePullback (𝟙 Y) R ≅
      etalePullback f R ⋙ etalePullback (inv f) R := by
    simpa only [IsIso.inv_hom_id] using etalePullbackCompIso (inv f) f R
  let eX : etalePullback (𝟙 X) R ≅
      etalePullback (inv f) R ⋙ etalePullback f R := by
    simpa only [IsIso.hom_inv_id] using etalePullbackCompIso f (inv f) R
  exact Functor.IsEquivalence.mk' (etalePullback (inv f) R)
    ((etalePullbackIdIso Y R).symm ≪≫ eY)
    (eX.symm ≪≫ etalePullbackIdIso X R)

end EtaleCohomology
