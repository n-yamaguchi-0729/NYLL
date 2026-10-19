/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitGroupRepresentation
import Nyll.JacobianVarieties.Generalized.RigidifiedScalarNaturality
import Nyll.JacobianVarieties.Generalized.PicardZeroForgetfulGroup
import Nyll.JacobianVarieties.Generalized.ParameterFrameClasses

/-! # The actual group boundary from modulus units to modulus Picard-zero -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {R : Type u} [CommRing R] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R)) (i : D ⟶ C)

/-- The two fibre-product conventions identify their actual unit groups. -/
def modulusBoundaryUnitsEquiv (T : Over (Spec (CommRingCat.of R))) :
    ModulusUnits (i ≫ c) T ≃* Γ(pullback (i ≫ c) T.hom, ⊤)ˣ :=
  Units.mapEquiv
    (Scheme.Γ.mapIso (pullbackSymmetry (i ≫ c) T.hom).op).commRingCatIsoToRingEquiv.toMulEquiv

/-- Parameter scalars become restrictions of the corresponding ambient curve scalars. -/
theorem modulusBoundaryUnitsEquiv_scalar (T : Over (Spec (CommRingCat.of R)))
    (a : Γ(T.left, ⊤)ˣ) :
    modulusBoundaryUnitsEquiv c i T
        (Units.map (modulusProjection (i ≫ c) T).appTop.hom.toMonoidHom a) =
      Units.map (modulusBaseChange c i T.hom).appTop.hom.toMonoidHom
        (Units.map (pullback.snd c T.hom).appTop.hom.toMonoidHom a) := by
  apply scalarUnits_square
  change (pullbackSymmetry (i ≫ c) T.hom).hom ≫ pullback.fst T.hom (i ≫ c) =
    modulusBaseChange c i T.hom ≫ pullback.snd c T.hom
  rw [pullbackSymmetry_hom_comp_fst]
  simp only [modulusBaseChange, pullback.map, pullback.lift_snd, Category.comp_id]

/-- An actual modulus unit equips the trivial curve bundle with its chosen trivialization. -/
def modulusUnitsBoundary (T : Over (Spec (CommRingCat.of R))) :
    ModulusUnits (i ≫ c) T →* modulusPicardZeroSubgroup c i T where
  toFun a := ⟨RigidifiedLineBundle.scalarClass (modulusBaseChange c i T.hom)
    (modulusBoundaryUnitsEquiv c i T a), one_mem_modulusPicardZero c i T⟩
  map_one' := Subtype.ext ((RigidifiedLineBundle.scalarClassHom
    (modulusBaseChange c i T.hom)).comp (modulusBoundaryUnitsEquiv c i T).toMonoidHom).map_one
  map_mul' a b := Subtype.ext (((RigidifiedLineBundle.scalarClassHom
    (modulusBaseChange c i T.hom)).comp (modulusBoundaryUnitsEquiv c i T).toMonoidHom).map_mul a b)

/-- Base scalars act trivially on the actual boundary, by an extending curve automorphism. -/
theorem modulusScalars_le_boundaryKernel (T : Over (Spec (CommRingCat.of R))) :
    modulusScalars (i ≫ c) T ≤ (modulusUnitsBoundary c i T).ker := by
  rintro a ⟨b, rfl⟩
  apply MonoidHom.mem_ker.mpr
  apply Subtype.ext
  change RigidifiedLineBundle.scalarClass (modulusBaseChange c i T.hom)
    (modulusBoundaryUnitsEquiv c i T
      (Units.map (modulusProjection (i ≫ c) T).appTop.hom.toMonoidHom b)) = 1
  rw [modulusBoundaryUnitsEquiv_scalar]
  exact ((RigidifiedLineBundle.scalarClass_eq_iff (modulusBaseChange c i T.hom) _ 1).mpr
    ⟨Units.map (pullback.snd c T.hom).appTop.hom.toMonoidHom b, mul_one _⟩).trans
      (RigidifiedLineBundle.scalarClassHom (modulusBaseChange c i T.hom)).map_one

/-- The canonical boundary on the actual quotient by parameter scalar units. -/
def modulusUnitQuotientBoundary (T : Over (Spec (CommRingCat.of R))) :
    ModulusUnits (i ≫ c) T ⧸ modulusScalars (i ≫ c) T →*
      modulusPicardZeroSubgroup c i T :=
  QuotientGroup.lift (modulusScalars (i ≫ c) T) (modulusUnitsBoundary c i T)
    (modulusScalars_le_boundaryKernel c i T)

/-- Pullback symmetry commutes with every change of parameters. -/
theorem modulusBoundaryUnitsEquiv_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (a : ModulusUnits (i ≫ c) T) :
    modulusBoundaryUnitsEquiv c i T' (modulusUnitMap (i ≫ c) f a) =
      Units.map (baseChangeSnd (i ≫ c)
        (⟨f.left, f.w⟩ : SchemeHomOver T'.hom T.hom)).appTop.hom.toMonoidHom
          (modulusBoundaryUnitsEquiv c i T a) := by
  apply scalarUnits_square
  change (pullbackSymmetry (i ≫ c) T'.hom).hom ≫
      ((Over.pullback (i ≫ c)).map f).left =
    baseChangeSnd (i ≫ c) (⟨f.left, f.w⟩ : SchemeHomOver T'.hom T.hom) ≫
      (pullbackSymmetry (i ≫ c) T.hom).hom
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst,
      pullbackSymmetry_hom_comp_fst_assoc, pullbackSymmetry_hom_comp_fst]
    exact (baseChangeSnd_snd (⟨f.left, f.w⟩ : SchemeHomOver T'.hom T.hom)).symm
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd,
      pullbackSymmetry_hom_comp_snd]
    simp only [baseChangeSnd, pullback.map, pullback.lift_fst, Category.comp_id]

/-- The quotient boundary commutes with actual rigidified pullback. -/
theorem modulusUnitQuotientBoundary_naturality
    {T T' : Over (Spec (CommRingCat.of R))} (f : T' ⟶ T)
    (a : ModulusUnits (i ≫ c) T ⧸ modulusScalars (i ≫ c) T) :
    modulusUnitQuotientBoundary c i T' (modulusUnitQuotientMap (i ≫ c) f a) =
      (modulusPicardZeroGroupPresheaf c i).map f.op
        (modulusUnitQuotientBoundary c i T a) := by
  refine QuotientGroup.induction_on a fun a => ?_
  apply Subtype.ext
  change RigidifiedLineBundle.scalarClass (modulusBaseChange c i T'.hom)
      (modulusBoundaryUnitsEquiv c i T' (modulusUnitMap (i ≫ c) f a)) =
    RigidifiedLineBundle.classesPullback
      (baseChangeSnd c (⟨f.left, f.w⟩ : SchemeHomOver T'.hom T.hom))
      (baseChangeSnd (i ≫ c) (⟨f.left, f.w⟩ : SchemeHomOver T'.hom T.hom))
      (modulusBaseChange_naturality c i (⟨f.left, f.w⟩ : SchemeHomOver T'.hom T.hom))
      (RigidifiedLineBundle.scalarClass (modulusBaseChange c i T.hom)
        (modulusBoundaryUnitsEquiv c i T a))
  rw [RigidifiedLineBundle.scalarClass_pullback, modulusBoundaryUnitsEquiv_naturality]

/-- The natural group boundary from literal scalar classes to actual modulus-zero classes. -/
def modulusUnitBoundaryPresheaf :
    liftedModulusUnitQuotientGroupPresheaf (i ≫ c) ⟶ modulusPicardZeroGroupPresheaf c i where
  app T := CommGrpCat.ofHom
    ((modulusUnitQuotientBoundary c i T.unop).comp (MulEquiv.ulift.toMonoidHom))
  naturality {T T'} f := by
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact modulusUnitQuotientBoundary_naturality c i f.unop a.down

/-- The boundary on fppf group sheaves is the sheafification of this actual class map. -/
def modulusUnitBoundarySheaf :
    modulusUnitQuotientGroupSheaf (i ≫ c) ⟶ modulusPicardZeroGroupSheaf c i :=
  (presheafToSheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of R)))
    CommGrpCat.{u + 1}).map (modulusUnitBoundaryPresheaf c i)

/-- Forgetting a scalar rigidification yields the actual trivial ordinary class. -/
theorem modulusUnitsBoundary_forget (T : Over (Spec (CommRingCat.of R)))
    (a : ModulusUnits (i ≫ c) T) :
    (forgetModulusZeroGroupPresheaf c i).app (op T) (modulusUnitsBoundary c i T a) = 1 := rfl

end AlgebraicGeometry.GeneralizedJacobian
