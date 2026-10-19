/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Semiabelian
import Nyll.SchemeTheory.GroupSchemes.SplitTorusBaseChange
import Nyll.SchemeTheory.GroupSchemes.SplitTorusZero

/-! # Abelian varieties as actual semiabelian extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsAbelianScheme G]

/-- An abelian variety is its own abelian quotient, with the actual rank-zero torus kernel. -/
def abelianSemiabelianExtension : SemiabelianExtension G where
  torus := GroupSchemes.splitTorus K 0
  quotient := G
  inclusion := InducedCategory.homMk (Grp.homMk
    (toUnit (GroupSchemes.splitTorus K 0).X ≫ η[G.X]))
  projection := 𝟙 G
  condition := Category.comp_id _
  isKernel := by
    let hT := GroupSchemes.splitTorusZeroIsTerminal K
    refine Fork.IsLimit.mk _ (fun s => hT.from s.pt) ?_ ?_
    · intro s
      change hT.from s.pt ≫ (1 : (GroupSchemes.splitTorus K 0).X ⟶ G.X) = s.ι
      rw [MonObj.comp_one]
      have h := s.condition
      change s.ι ≫ 𝟙 G.X = s.ι ≫ (1 : G.X ⟶ G.X) at h
      simpa only [Category.comp_id, MonObj.comp_one] using h.symm
    · intro s m _
      exact hT.hom_ext m (hT.from s.pt)
  projection_smooth := by
    change Smooth (𝟙 G.X.left)
    infer_instance
  projection_surjective := by
    change Surjective (𝟙 G.X.left)
    infer_instance

/-- Every abelian variety is semiabelian, via its genuine rank-zero kernel. -/
instance IsAbelianScheme.isSemiabelian : IsSemiabelian G :=
  (abelianSemiabelianExtension G).isSemiabelian

end AlgebraicGeometry
