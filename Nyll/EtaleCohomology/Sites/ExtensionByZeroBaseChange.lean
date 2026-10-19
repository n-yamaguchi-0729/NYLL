/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Sites.ExtensionByZero
import Nyll.EtaleCohomology.Sites.EtaleRestriction
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Extension by zero under arbitrary base change

The actual restriction/direct-image comparison for an open cartesian square
identifies the right adjoints of the two inverse-image/extension-by-zero
composites. Uniqueness of left adjoints gives their canonical comparison and
its literal adjunction-unit identity. No properness, finiteness, or field
hypothesis is required.

Reference: https://stacks.math.columbia.edu/tag/03S2
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {U X Y P : Scheme.{u}}
  (j : U ⟶ X) [IsOpenImmersion j] (f : Y ⟶ X)
  (p : P ⟶ U) (j' : P ⟶ Y) [IsOpenImmersion j']
  (H : IsPullback p j' j f) (R : Type u) [CommRing R]

/-- The actual inverse image along the open immersion commutes with direct
image around an arbitrary cartesian square. -/
def etaleOpenPullbackPushforwardBaseChangeIso :
    etalePushforward f R ⋙ etalePullback j R ≅
      etalePullback j' R ⋙ etalePushforward p R :=
  Functor.isoWhiskerLeft (etalePushforward f R) (etalePullbackOpenRestrictionIso j R) ≪≫
    etaleRestrictionPushforwardBaseChangeIsoOfIsPullback j f (ModuleCat.{u} R) p j' H ≪≫
      Functor.isoWhiskerRight (etalePullbackOpenRestrictionIso j' R).symm
        (etalePushforward p R)

/-- Actual extension by zero commutes with arbitrary inverse image in an
open cartesian square, using the existing four sheaf functors. -/
def etaleExtensionByZeroBaseChangeIsoOfIsPullback :
    etaleExtensionByZero j R ⋙ etalePullback f R ≅
      etalePullback p R ⋙ etaleExtensionByZero j' R :=
  ((etaleExtensionByZeroAdjunction j R).comp
    (etalePullbackPushforwardAdjunction f R)).leftAdjointUniq
      (((etalePullbackPushforwardAdjunction p R).comp
        (etaleExtensionByZeroAdjunction j' R)).ofNatIsoRight
          (etaleOpenPullbackPushforwardBaseChangeIso j f p j' H R).symm)

/-- The extension-by-zero base-change isomorphism retains the defining unit
square of the actual adjunctions, so its future uses can track coherence. -/
theorem etaleExtensionByZeroBaseChangeIsoOfIsPullback_unit
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} R)) :
    ((etaleExtensionByZeroAdjunction j R).comp
        (etalePullbackPushforwardAdjunction f R)).unit.app F ≫
      (etalePushforward f R ⋙ etalePullback j R).map
        ((etaleExtensionByZeroBaseChangeIsoOfIsPullback j f p j' H R).hom.app F) =
    ((etalePullbackPushforwardAdjunction p R).comp
        (etaleExtensionByZeroAdjunction j' R)).unit.app F ≫
      (etaleOpenPullbackPushforwardBaseChangeIso j f p j' H R).inv.app
        ((etalePullback p R ⋙ etaleExtensionByZero j' R).obj F) :=
  Adjunction.unit_leftAdjointUniq_hom_app
    ((etaleExtensionByZeroAdjunction j R).comp
      (etalePullbackPushforwardAdjunction f R))
    (((etalePullbackPushforwardAdjunction p R).comp
      (etaleExtensionByZeroAdjunction j' R)).ofNatIsoRight
        (etaleOpenPullbackPushforwardBaseChangeIso j f p j' H R).symm) F

/-- The canonical pullback square gives base change for actual extension by
zero along any scheme morphism. -/
def etaleExtensionByZeroBaseChangeIso :
    etaleExtensionByZero j R ⋙ etalePullback f R ≅
      etalePullback (pullback.fst j f) R ⋙
        etaleExtensionByZero (pullback.snd j f) R :=
  etaleExtensionByZeroBaseChangeIsoOfIsPullback j f
    (pullback.fst j f) (pullback.snd j f) (IsPullback.of_hasPullback j f) R

end EtaleCohomology
