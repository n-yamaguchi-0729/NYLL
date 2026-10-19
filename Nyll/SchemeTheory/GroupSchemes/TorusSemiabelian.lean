/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.Semiabelian
import Nyll.SchemeTheory.GroupSchemes.TorusGeometry
import Nyll.SchemeTheory.GroupSchemes.Trivial

/-! # Tori as actual semiabelian extensions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]
  (G : CommGrp (Over (Spec (CommRingCat.of K)))) [IsTorus G]

/-- A torus is its own kernel, with the actual trivial abelian quotient. -/
def torusSemiabelianExtension : SemiabelianExtension G where
  torus := G
  quotient := CommGrp.trivial (Over (Spec (CommRingCat.of K)))
  inclusion := 𝟙 G
  projection := InducedCategory.homMk (toUnit G.toGrp)
  condition := isTerminalTensorUnit.hom_ext _ _
  isKernel := Fork.IsLimit.mk _ (fun s => s.ι)
    (fun s => Category.comp_id s.ι)
    (fun _ _ h => (Category.comp_id _).symm.trans h)
  projection_smooth := by
    change Smooth G.X.hom
    infer_instance
  projection_surjective := by
    change Surjective G.X.hom
    infer_instance

/-- Every genuine torus is semiabelian via the structure morphism to its ground field. -/
instance IsTorus.isSemiabelian : IsSemiabelian G :=
  (torusSemiabelianExtension G).isSemiabelian

end AlgebraicGeometry
