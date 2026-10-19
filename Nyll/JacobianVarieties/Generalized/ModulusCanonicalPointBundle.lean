/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.JacobianVarieties.Generalized.ModulusAbelDifference
import Nyll.JacobianVarieties.Generalized.ModulusScalarExtension

/-! # Canonical test-point graph bundles with their actual modulus frames -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory NeronModelInfra
open AlgebraicGeometry.RelPicard

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C) [IsClosedImmersion i]
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]

omit [SmoothOfRelativeDimension 1 c] in
/-- A test point outside the modulus has graph disjoint from the whole pulled-back modulus. -/
theorem modulusPointDivisor_avoids {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c))
    (y : (pullback (i ≫ c) t : Scheme.{u})) :
    modulusBaseChange c i t y ∉
      (RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
        ((Category.assoc _ _ _).trans x.2)).I.support := by
  intro hy
  have hs := RelEffCartierDiv.supportedIn_ofPoint
    (f := c) (x.1 ≫ (modulusComplement i).ι)
      ((Category.assoc _ _ _).trans x.2) (modulusComplement i)
      (fun z => (x.1 z).property)
  have hz := hs hy
  change pullback.fst c t (modulusBaseChange c i t y) ∈ modulusComplement i at hz
  rw [← Scheme.Hom.comp_apply, modulusBaseChange_fst,
    Scheme.Hom.comp_apply] at hz
  exact modulus_not_mem_complement i _ hz

/-- The canonical inverse ideal of a test point's graph, with its specified modulus frame. -/
def modulusCanonicalPointBundle {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver t ((modulusComplement i).ι ≫ c)) :
    RigidifiedLineBundle (modulusBaseChange c i t) :=
  RigidifiedLineBundle.ofInvertibleIdeal (modulusBaseChange c i t)
    (RelEffCartierDiv.ofPoint c (x.1 ≫ (modulusComplement i).ι)
      ((Category.assoc _ _ _).trans x.2)).I
    (RelEffCartierDiv.isInvertible_I _) (modulusPointDivisor_avoids c i x)

end AlgebraicGeometry.GeneralizedJacobian
