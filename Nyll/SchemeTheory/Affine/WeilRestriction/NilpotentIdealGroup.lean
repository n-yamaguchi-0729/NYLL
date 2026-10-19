/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.NilpotentUnitKernelSquare
import Nyll.SchemeTheory.Affine.WeilRestriction.NilpotentIdealBasis
import Nyll.SchemeTheory.Affine.WeilRestriction.UnitRestrictionFibers
import Nyll.SchemeTheory.Morphisms.SmoothGeometricallyIntegral

/-! # The actual smooth connected affine group of a nilpotent ideal -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Opposite Module

namespace SchemeTheory.Affine.UnitNormPolynomial

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
  (I : Ideal A) (hI : IsNilpotent I)

omit [FiniteDimensional K A] in
include hI in
/-- Nilpotence applies to the actual kernel of the original quotient map. -/
theorem idealQuotient_kernel_nilpotent :
    IsNilpotent (RingHom.ker (Ideal.Quotient.mkₐ K I).toRingHom) := by
  change IsNilpotent (RingHom.ker (Ideal.Quotient.mk I))
  rw [Ideal.mk_ker]
  exact hI

/-- The affine space of the actual ideal dimension represents its tensor-unit kernel.
Every basis and splitting in this statement is constructed from the given ideal. -/
def nilpotentIdealRepresentable :
    (tensorUnitKernelPresheaf (Ideal.Quotient.mkₐ K I) ⋙ forget CommGrpCat).RepresentableBy
      (nilpotentUnitKernelObject (R := K) (ι := Fin (Module.finrank K I))) :=
  nilpotentUnitKernelRepresentable (Ideal.Quotient.mkₐ K I)
    (idealSplitBasis (K := K) I) (Module.finBasis K (A ⧸ I))
    (idealSplitBasis_left (K := K) I) (idealSplitBasis_right (K := K) I)
    (Ideal.Quotient.mkₐ_surjective K I) (idealQuotient_kernel_nilpotent (K := K) I hI)

/-- The actual nilpotent-ideal unit group, with no representation or splitting hypotheses. -/
def nilpotentIdealGroup : CommGrp (Over (Spec (CommRingCat.of K))) :=
  RepresentedGroups.groupObject (tensorUnitKernelPresheaf (Ideal.Quotient.mkₐ K I))
    (nilpotentIdealRepresentable (K := K) I hI)

/-- Its underlying scheme is affine space of dimension equal to the original ideal. -/
theorem nilpotentIdealGroup_carrier :
    (nilpotentIdealGroup (K := K) I hI).X.left =
      Spec (CommRingCat.of (MvPolynomial (Fin (Module.finrank K I)) K)) := rfl

instance nilpotentIdealGroup_isAffine : IsAffine (nilpotentIdealGroup (K := K) I hI).X.left :=
  inferInstanceAs (IsAffine
    (Spec (CommRingCat.of (MvPolynomial (Fin (Module.finrank K I)) K))))

/-- Smoothness follows from the constructed polynomial affine-space carrier. -/
instance nilpotentIdealGroup_smooth : Smooth (nilpotentIdealGroup (K := K) I hI).X.hom := by
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap K (MvPolynomial (Fin (Module.finrank K I)) K))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr ⟨inferInstance, inferInstance⟩

/-- The actual nilpotent unit group is geometrically irreducible. -/
instance nilpotentIdealGroup_geometricallyIrreducible :
    GeometricallyIrreducible (nilpotentIdealGroup (K := K) I hI).X.hom :=
  geometricallyIrreducible_specMap_C K (Fin (Module.finrank K I))

/-- In particular, the actual nilpotent unit group is geometrically connected. -/
instance nilpotentIdealGroup_geometricallyConnected :
    GeometricallyConnected (nilpotentIdealGroup (K := K) I hI).X.hom := by
  constructor
  intro L _ y Z fst snd h
  have : IrreducibleSpace Z :=
    (nilpotentIdealGroup_geometricallyIrreducible (K := K) I hI).geometrically_irreducibleSpace
      y fst snd h
  infer_instance

/-- Smoothness and geometric connectedness yield geometric integrality. -/
instance nilpotentIdealGroup_geometricallyIntegral :
    GeometricallyIntegral (nilpotentIdealGroup (K := K) I hI).X.hom :=
  Smooth.geometricallyIntegral_of_geometricallyConnected (nilpotentIdealGroup (K := K) I hI).X.hom

/-- The constructed ideal group has its actual universal kernel inclusion. -/
def nilpotentIdealGroupIsKernel :=
  nilpotentUnitKernelIsLimit (Ideal.Quotient.mkₐ K I)
    (idealSplitBasis (K := K) I) (Module.finBasis K (A ⧸ I))
    (idealSplitBasis_left (K := K) I) (idealSplitBasis_right (K := K) I)
    (Ideal.Quotient.mkₐ_surjective K I) (idealQuotient_kernel_nilpotent (K := K) I hI)

end SchemeTheory.Affine.UnitNormPolynomial
