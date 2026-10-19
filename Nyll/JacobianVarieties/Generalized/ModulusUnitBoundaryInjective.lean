/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Generalized.ModulusUnitBoundary
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Injectivity and the actual image of the modulus-unit boundary -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GeneralizedJacobian.ScalarFrames

namespace AlgebraicGeometry.GeneralizedJacobian

variable {K : Type u} [Field K] {C D : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of K)) (i : D ⟶ C)
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

/-- The actual parameter-scalar quotient injects into compatible rigidified classes. -/
theorem modulusUnitQuotientBoundary_injective (T : Over (Spec (CommRingCat.of K))) :
    Function.Injective (modulusUnitQuotientBoundary c i T) := by
  intro x y
  refine QuotientGroup.induction_on x fun a => ?_
  refine QuotientGroup.induction_on y fun b => ?_
  intro hab
  obtain ⟨v, hv⟩ := (RigidifiedLineBundle.scalarClass_eq_iff
    (modulusBaseChange c i T.hom) _ _).mp (congrArg Subtype.val hab)
  obtain ⟨s, hs⟩ := (curveParameterUnitsEquiv c T.hom).surjective v
  apply QuotientGroup.eq_iff_div_mem.mpr
  refine ⟨s, ?_⟩
  apply (modulusBoundaryUnitsEquiv c i T).injective
  rw [map_div, modulusBoundaryUnitsEquiv_scalar]
  rw [← curveParameterUnitsEquiv_apply, hs]
  exact (eq_div_iff_mul_eq').mpr hv

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c] in
/-- Before sheafification, the image consists exactly of globally trivial underlying bundles. -/
theorem modulusUnitQuotientBoundary_range (T : Over (Spec (CommRingCat.of K))) :
    Set.range (modulusUnitQuotientBoundary c i T) =
      {x | RigidifiedLineBundle.IsGloballyTrivial (modulusBaseChange c i T.hom) x.val} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    refine QuotientGroup.induction_on a fun a => ?_
    exact ⟨Iso.refl _⟩
  · intro hx
    obtain ⟨a, ha⟩ := (Set.ext_iff.mp
      (RigidifiedLineBundle.scalarClass_range (modulusBaseChange c i T.hom)) x.val).mpr hx
    obtain ⟨b, rfl⟩ := (modulusBoundaryUnitsEquiv c i T).surjective a
    exact ⟨QuotientGroup.mk b, Subtype.ext ha⟩

/-- The scalar boundary is a monomorphism on actual presheaf classes. -/
instance modulusUnitBoundaryPresheaf_mono : Mono (modulusUnitBoundaryPresheaf c i) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro T
  apply (CommGrpCat.mono_iff_injective _).mpr
  intro a b h
  apply ULift.ext
  exact modulusUnitQuotientBoundary_injective c i T.unop h

/-- Left exact sheafification preserves the proved injection of actual scalar classes. -/
instance modulusUnitBoundarySheaf_mono : Mono (modulusUnitBoundarySheaf c i) :=
  inferInstanceAs (Mono ((presheafToSheaf
    (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) CommGrpCat.{u + 1}).map
      (modulusUnitBoundaryPresheaf c i)))

end AlgebraicGeometry.GeneralizedJacobian
