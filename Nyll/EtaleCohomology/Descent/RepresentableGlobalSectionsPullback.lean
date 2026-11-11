/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.GeometricStalkEvaluationSetSections
public import Nyll.EtaleCohomology.Descent.RepresentablePullbackSections
public import Nyll.EtaleCohomology.Descent.SetSheafDescentSourceComposition
public import Nyll.EtaleCohomology.Sites.PullbackSectionFactors

/-!
# The original global section map on a represented sheaf

The actual inverse-image map on global sections sends the original
scheme section to its original scheme base change. The formula retains
the chosen unit, identity base-change comparison, and representable
pullback comparison.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace EtaleCohomology

variable {X Y : Scheme.{u}} (q : Y ⟶ X) (W : X.Etale)

/-- The actual pullback map on global sections is the base-change lift
of the original scheme section, under the original Yoneda comparison. -/
theorem etaleSetPullbackGlobalSectionsMap_yoneda
    (u : (Scheme.Etale.mk (𝟙 X) : X.Etale) ⟶ W) :
    (etaleSetPullbackYonedaObjIso q W).hom.hom.app (op (Scheme.Etale.mk (𝟙 Y)))
        (etaleSetPullbackGlobalSectionsMap q (X.smallEtaleTopology.yoneda.obj W) u) =
      etaleBaseChangeLift (U := Scheme.Etale.mk (𝟙 Y)) q (q ≫ u.left)
        ((Category.assoc q u.left W.hom).trans
          ((congrArg (fun k => q ≫ k) u.w).trans
            ((Category.comp_id q).trans (Category.id_comp q).symm))) := by
  let F := (etaleSetPullback q).obj (X.smallEtaleTopology.yoneda.obj W)
  let β := etaleSetPullbackYonedaObjIso q W
  let j := (baseChangeIdentityIso q).hom
  let v := ((etaleSetPullbackPushforwardAdjunction q).unit.app
    (X.smallEtaleTopology.yoneda.obj W)).hom.app (op (Scheme.Etale.mk (𝟙 X))) u
  have hn := ConcreteCategory.congr_hom (β.hom.hom.naturality j.op) v
  change β.hom.hom.app (op (Scheme.Etale.mk (𝟙 Y))) (F.obj.map j.op v) =
    j ≫ β.hom.hom.app (op ((etaleBaseChange q).obj (Scheme.Etale.mk (𝟙 X)))) v at hn
  refine hn.trans ?_
  have hu := etaleSetPullback_unit_yoneda_apply q W (Scheme.Etale.mk (𝟙 X)) u
  change j ≫ β.hom.hom.app
      (op ((etaleBaseChange q).obj (Scheme.Etale.mk (𝟙 X)))) v = _
  rw [hu]
  exact etaleBaseChangeLift_comp (U := Scheme.Etale.mk (𝟙 Y))
    (V := Scheme.Etale.mk (𝟙 X)) (W := W) q u q
    ((Category.comp_id q).trans (Category.id_comp q).symm)
    ((Category.assoc q u.left W.hom).trans
      ((congrArg (fun k => q ≫ k) u.w).trans
        ((Category.comp_id q).trans (Category.id_comp q).symm)))

/-- The original global pullback map is the existing represented
section equivalence applied to literal restriction of the original
scheme section. -/
theorem etaleSetPullbackGlobalSectionsMap_eq_representableSectionsEquiv
    (u : (Scheme.Etale.mk (𝟙 X) : X.Etale) ⟶ W) :
    etaleSetPullbackGlobalSectionsMap q (X.smallEtaleTopology.yoneda.obj W) u =
      etaleRepresentablePullbackSectionsEquiv q W
        (Over.homMk (q ≫ u.left)
          ((Category.assoc q u.left W.hom).trans
            ((congrArg (fun k => q ≫ k) u.w).trans (Category.comp_id q)))) := by
  let E := ((sheafSections Y.smallEtaleTopology (Type u)).obj
    (op (Scheme.Etale.mk (𝟙 Y)))).mapIso (etaleSetPullbackYonedaObjIso q W)
  apply E.toEquiv.injective
  exact (etaleSetPullbackGlobalSectionsMap_yoneda q W u).trans
    (etaleRepresentablePullbackSectionsEquiv_yoneda q W
      (Over.homMk (q ≫ u.left)
        ((Category.assoc q u.left W.hom).trans
          ((congrArg (fun k => q ≫ k) u.w).trans (Category.comp_id q))))).symm

end EtaleCohomology
