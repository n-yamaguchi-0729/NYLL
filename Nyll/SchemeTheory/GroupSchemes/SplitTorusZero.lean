/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Nyll.SchemeTheory.GroupSchemes.SplitTorus

/-! # The rank-zero split torus is the actual trivial group scheme -/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.GroupSchemes

variable (R : Type u) [CommRing R]

/-- The rank-zero character bialgebra gives the same actual Hopf-algebra isomorphism. -/
def splitTorusZeroHopfIso :
    CommHopfAlgCat.of R R ≅ CommHopfAlgCat.of R (splitTorusAlgebra R 0) :=
  CommHopfAlgCat.isoMk
    (AddMonoidAlgebra.bialgEquivOfSubsingleton (R := R) (Fin 0 → ℤ)).symm

/-- The underlying over-scheme isomorphism induced by an actual Hopf-algebra isomorphism. -/
def hopfSpecUnderlyingIso {A B : CommHopfAlgCat.{u} R} (e : A ≅ B) :
    ((hopfSpec (CommRingCat.of R)).obj (op B)).X ≅
      ((hopfSpec (CommRingCat.of R)).obj (op A)).X :=
  (Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso
    ((hopfSpec (CommRingCat.of R)).mapIso e.op)

/-- The spectrum of the base-ring Hopf algebra is the identity object over the base. -/
def hopfSpecSelfBaseIso :
    ((hopfSpec (CommRingCat.of R)).obj (op (CommHopfAlgCat.of R R))).X ≅
      Over.mk (𝟙 (Spec (CommRingCat.of R))) := by
  refine Over.isoMk (Iso.refl (Spec (CommRingCat.of R))) ?_
  change 𝟙 (Spec (CommRingCat.of R)) ≫ 𝟙 _ =
    Spec.map (CommRingCat.ofHom (algebraMap R R))
  rw [Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- The rank-zero character algebra identifies the actual split torus with the base. -/
def splitTorusZeroBaseIso : (splitTorus R 0).X ≅ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
  hopfSpecUnderlyingIso R (splitTorusZeroHopfIso R) ≪≫ hopfSpecSelfBaseIso R

/-- The underlying scheme of the rank-zero split torus is terminal over the base. -/
def splitTorusZeroIsTerminal : IsTerminal (splitTorus R 0).X :=
  Over.mkIdTerminal.ofIso (splitTorusZeroBaseIso R).symm

end AlgebraicGeometry.GroupSchemes
