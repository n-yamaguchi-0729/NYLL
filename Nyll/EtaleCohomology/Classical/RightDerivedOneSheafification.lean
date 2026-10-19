/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.CohomologyPresheafBoundary
import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
import Nyll.SchemeTheory.HomologicalAlgebra.RightDerivedOneCokernel
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual first direct image and the cohomology presheaf

The canonical injective presentation gives the same cokernel on both
sides. Sheafification and precomposition preserve that cokernel, and
the sheafification counit identifies its terms with the actual direct
images. This constructs the comparison as an isomorphism of sheaves.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace EtaleCohomology

/-- The actual first right derived direct image is the sheafification of
the actual degree-one cohomology presheaf evaluated on base changes. -/
def etaleRightDerivedOneSheafificationIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((etaleAbelianPushforward f).rightDerived 1).obj F ≅
      (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        ((etaleBaseChange f).op ⋙ F.cohomologyPresheaf 1) := by
  let G := etaleAbelianPushforward f
  let W := (Functor.whiskeringLeft Y.Etaleᵒᵖ X.Etaleᵒᵖ AddCommGrpCat.{u}).obj
    (etaleBaseChange f).op
  let A := presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  let H := W ⋙ A
  have : H.Additive := by dsimp [H, W, A]; infer_instance
  have : PreservesFiniteColimits H := by dsimp [H, W, A]; infer_instance
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
  let e₂ := asIso ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).counit.app
    (G.obj S.X₂))
  let e₃ := asIso ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).counit.app
    (G.obj S.X₃))
  have hn : H.map S.g.hom ≫ e₃.hom = e₂.hom ≫ G.map S.g := by
    have hn := (sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u}).counit.naturality
      (G.map S.g)
    change _ = _ at hn
    exact hn
  let ec := cokernel.mapIso (f := H.map S.g.hom) (G.map S.g) e₂ e₃ hn
  exact G.rightDerivedOneCokernelIso F ≪≫ ec.symm ≪≫
    (PreservesCokernel.iso H S.g.hom).symm ≪≫
      H.mapIso (cohomologyPresheafInjectiveCokernelIso X S hS)

end EtaleCohomology
