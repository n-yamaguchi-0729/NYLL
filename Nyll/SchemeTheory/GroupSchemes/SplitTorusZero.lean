/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.GroupSchemes.SplitTorus

/-! # The rank-zero split torus is the actual trivial group scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GroupSchemes

variable (R : Type u) [CommRing R]

/-- The rank-zero character algebra identifies the actual split torus with the base. -/
def splitTorusZeroBaseIso : (splitTorus R 0).X ≅ Over.mk (𝟙 (Spec (CommRingCat.of R))) := by
  let A : CommHopfAlgCat R := CommHopfAlgCat.of R R
  let e : (splitTorus R 0).X ≅ ((hopfSpec (CommRingCat.of R)).obj (op A)).X :=
    (Grp.forget _).mapIso ((hopfSpec (CommRingCat.of R)).mapIso
      (CommHopfAlgCat.isoMk
        (AddMonoidAlgebra.bialgEquivOfSubsingleton (R := R) (Fin 0 → ℤ)).symm).op)
  refine e ≪≫ Over.isoMk (Iso.refl _) ?_
  change 𝟙 (Spec (CommRingCat.of R)) ≫ 𝟙 _ =
    Spec.map (CommRingCat.ofHom (algebraMap R R))
  rw [Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- The underlying scheme of the rank-zero split torus is terminal over the base. -/
def splitTorusZeroIsTerminal : IsTerminal (splitTorus R 0).X :=
  Over.mkIdTerminal.ofIso (splitTorusZeroBaseIso R).symm

end AlgebraicGeometry.GroupSchemes
