/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ExistingJacobianGroupCompatibility

/-!
# The saved ordinary Jacobian as a commutative group scheme

The group object uses the original `Unpointed.groupLaw`. The identity on its
carrier identifies it with the group object classified by the actual ordinary
Picard-zero sheaf.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.GeneralizedJacobian NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

namespace JacobianVarieties.Picard.Unpointed

variable (K : Type u) [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

/-- The original chosen Jacobian carrier with exactly its original relative group law. -/
def groupScheme : CommGrp (Over (Spec (CommRingCat.of K))) := by
  let : GrpObj (Over.mk (toBase K c)) := (groupLaw K c).grpObjOverMk
  have : IsCommMonObj (Over.mk (toBase K c)) :=
    (groupLaw K c).isCommMonObj_grpObjOverMk_iff_mul_comm.mpr (groupLaw_commutative K c)
  exact ⟨Over.mk (toBase K c)⟩

/-- The original multiplication on over-category morphisms classifies tensor products. -/
theorem groupSheafRepresentation_over_mul (T : Over (Spec (CommRingCat.of K)))
    (x y : T ⟶ Over.mk (toBase K c)) :
    let _ : GrpObj (Over.mk (toBase K c)) := (groupLaw K c).grpObjOverMk
    (groupSheafRepresentation K c).homEquiv (x * y) =
      (groupSheafRepresentation K c).homEquiv x * (groupSheafRepresentation K c).homEquiv y := by
  intro groupStructure
  have h := groupSheafRepresentation_mul K c T.hom
    (overHomEquivSchemeHomOver T (toBase K c) x)
    (overHomEquivSchemeHomOver T (toBase K c) y)
  rw [← (groupLaw K c).overHomEquivSchemeHomOver_mul T x y] at h
  exact h

/-- The original unit, expressed on over-category morphisms, classifies the tensor identity. -/
theorem groupSheafRepresentation_over_one (T : Over (Spec (CommRingCat.of K))) :
    let _ : GrpObj (Over.mk (toBase K c)) := (groupLaw K c).grpObjOverMk
    (groupSheafRepresentation K c).homEquiv (1 : T ⟶ Over.mk (toBase K c)) = 1 := by
  intro groupStructure
  have h := groupSheafRepresentation_one K c T.hom
  rw [← (groupLaw K c).overHomEquivSchemeHomOver_one T] at h
  exact h

/-- The identity on the saved carrier preserves the actual old and sheafified group laws. -/
def sheafGroupSchemeIso : sheafGroupScheme K c ≅ groupScheme K c := by
  let : CommGrpObj (Over.mk (toBase K c)) := CommGrpObj.ofRepresentableBy
    (Over.mk (toBase K c)) (ordinaryRelativePicardZeroGroupSheaf c).obj
      (groupSheafRepresentation K c)
  exact CommGrp.mkIso (Iso.refl (Over.mk (toBase K c)))
    (by
      simp only [Iso.refl_hom]
      apply (groupSheafRepresentation K c).homEquiv.injective
      rw [MonObj.one_eq_one, MonObj.one_eq_one]
      exact (SchemeTheory.RepresentedGroups.pointEquiv
        (ordinaryRelativePicardZeroGroupSheaf c).obj (groupSheafRepresentation K c)
          (𝟙_ (Over (Spec (CommRingCat.of K))))).map_one |>.trans
            (groupSheafRepresentation_over_one K c _).symm)
    (by
      simp only [Iso.refl_hom]
      apply (groupSheafRepresentation K c).homEquiv.injective
      rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul]
      erw [id_tensorHom_id, Category.id_comp, Category.comp_id]
      exact (SchemeTheory.RepresentedGroups.pointEquiv
        (ordinaryRelativePicardZeroGroupSheaf c).obj (groupSheafRepresentation K c)
          (Over.mk (toBase K c) ⊗ Over.mk (toBase K c))).map_mul
            (fst _ _) (snd _ _) |>.trans
              (groupSheafRepresentation_over_mul K c _ (fst _ _) (snd _ _)).symm)

end JacobianVarieties.Picard.Unpointed
