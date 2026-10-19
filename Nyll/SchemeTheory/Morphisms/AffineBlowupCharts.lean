/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.AffineBlowup
import Nyll.SchemeTheory.RingTheory.ReesChart

/-!
# Degree-one affine charts of the affine blowup

The actual degree-one generators of the Rees algebra give an affine open
cover of its Proj. The chart structure maps are the coefficient maps of
the homogeneous localizations, on which the extended ideal is principal.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The canonical open immersion from the homogeneous chart at `aT`. -/
def affineBlowupChartι (a : I) : Spec (.of (ReesAlgebra.Chart I a)) ⟶ affineBlowup I :=
  Proj.awayι (ReesAlgebra.homogeneousPart I) (ReesAlgebra.degreeOne I a)
    (ReesAlgebra.degreeOne_mem I a) Nat.zero_lt_one

instance (a : I) : IsOpenImmersion (affineBlowupChartι I a) :=
  inferInstanceAs (IsOpenImmersion
    (Proj.awayι (ReesAlgebra.homogeneousPart I) (ReesAlgebra.degreeOne I a)
      (ReesAlgebra.degreeOne_mem I a) Nat.zero_lt_one))

/-- The coefficient maps are literally the restrictions of the blowup map. -/
theorem affineBlowupChartι_map (a : I) :
    affineBlowupChartι I a ≫ affineBlowupMap I =
      Spec.map (CommRingCat.ofHom (ReesAlgebra.coefficientToChart I a)) := by
  change Proj.awayι (ReesAlgebra.homogeneousPart I) (ReesAlgebra.degreeOne I a)
      (ReesAlgebra.degreeOne_mem I a) Nat.zero_lt_one ≫
      (Proj.toSpecZero (ReesAlgebra.homogeneousPart I) ≫
        Spec.map (RingEquiv.toCommRingCatIso (R := R)
          (S := ↥(ReesAlgebra.homogeneousPart I 0))
          (ReesAlgebra.degreeZeroEquiv I)).hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- The degree-one charts cover the actual affine blowup. -/
theorem affineBlowup_iSup_basicOpen :
    (⨆ a : I, Proj.basicOpen (ReesAlgebra.homogeneousPart I) (ReesAlgebra.degreeOne I a)) =
      ⊤ :=
  Proj.iSup_basicOpen_eq_top' (ReesAlgebra.homogeneousPart I) (ReesAlgebra.degreeOne I)
    (fun a => ⟨1, ReesAlgebra.degreeOne_mem I a⟩)
    (ReesAlgebra.adjoin_degreeOne_degreeZero I)

/-- The native affine open cover indexed by elements of the original ideal. -/
def affineBlowupAffineCover : (affineBlowup I).AffineOpenCover where
  I₀ := I
  X a := .of (ReesAlgebra.Chart I a)
  f a := affineBlowupChartι I a
  idx x := (Opens.mem_iSup.mp ((affineBlowup_iSup_basicOpen I).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (affineBlowupChartι I _).opensRange
    change x ∈ (Proj.awayι (ReesAlgebra.homogeneousPart I) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (Opens.mem_iSup.mp
      ((affineBlowup_iSup_basicOpen I).ge (Set.mem_univ x))).choose_spec

end AlgebraicGeometry
