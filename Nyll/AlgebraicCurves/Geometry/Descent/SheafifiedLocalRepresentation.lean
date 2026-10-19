/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Descent.NaturalRepresentationDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Sheafification on a cover with an actual local representation

The unit of fppf sheafification restricts to an isomorphism wherever the actual
presheaf is represented. Its local representation therefore has exactly the
same canonical descent action, even if the original presheaf is not a sheaf.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.DescentAction

variable {S S' : Scheme.{u}} (s : S' ⟶ S)
  (G : (Over S)ᵒᵖ ⥤ Type (u + 1))
  {X' : Scheme.{u}} (x' : X' ⟶ S')
  (eG : ((Over.map s).op ⋙ G).RepresentableBy (Over.mk x'))

include eG in
/-- The actual unit is invertible after restriction to the represented slice. -/
theorem isIso_restrict_toSheafify :
    IsIso (Functor.whiskerLeft (Over.map s).op
      (toSheafify (Scheme.fppfTopology.over S) G)) := by
  have : ((Over.map s).op ⋙ G).IsRepresentable := eG.isRepresentable
  have h : Presheaf.IsSheaf (Scheme.fppfTopology.over S') ((Over.map s).op ⋙ G) := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.fppfTopology.over S') ((Over.map s).op ⋙ G)
  have hUnit : IsIso (toSheafify (Scheme.fppfTopology.over S') ((Over.map s).op ⋙ G)) :=
    isIso_toSheafify _ h
  have hCompat : IsIso
      (((Over.map s).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
        (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).hom.app G).hom := by
    exact (sheafToPresheaf (Scheme.fppfTopology.over S') (Type (u + 1))).map_isIso
      (((Over.map s).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
        (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).hom.app G)
  rw [← Functor.toSheafify_pullbackSheafificationCompatibility
    (Over.map s) (Type (u + 1)) (Scheme.fppfTopology.over S')
      (Scheme.fppfTopology.over S)]
  exact IsIso.comp_isIso' hUnit hCompat

/-- The sheafification has the transported actual local representation. -/
def sheafifiedLocalRepresentation :
    ((Over.map s).op ⋙ sheafify (Scheme.fppfTopology.over S) G).RepresentableBy
      (Over.mk x') := by
  have := isIso_restrict_toSheafify s G x' eG
  exact localRepresentationOfNaturalIso s G (sheafify (Scheme.fppfTopology.over S) G)
    (toSheafify (Scheme.fppfTopology.over S) G) x' eG

/-- Sheafification has not changed the effective scheme descent action. -/
theorem repAct_sheafifiedLocalRepresentation :
    repAct s (sheafify (Scheme.fppfTopology.over S) G) x'
      (sheafifiedLocalRepresentation s G x' eG) = repAct s G x' eG := by
  have := isIso_restrict_toSheafify s G x' eG
  exact repAct_localRepresentationOfNaturalIso s G (sheafify (Scheme.fppfTopology.over S) G)
    (toSheafify (Scheme.fppfTopology.over S) G) x' eG

end AlgebraicGeometry.DescentAction
