/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FiniteSchemeAlgebraBaseChange
import Nyll.SchemeTheory.Affine.WeilRestriction.ScalarQuotientBaseChange

/-!
# Scalar classes on an actual finite scheme after affine base change

The tensor-algebra quotient agrees with global units on the actual fibre
product modulo units restricted from the parameter spectrum. The scalar
subgroup is proved to be the same via the Gamma--Spec isomorphism; it is
not replaced by an assumed group of constants.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace SchemeTheory.Affine.FiniteScheme

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}

/-- Coefficient-ring units and units on its spectrum give the same scalar image. -/
theorem coordinateScalarRange (q : Z ⟶ Spec (CommRingCat.of R)) :
    (Units.map (algebraMap R (coordinateAlgebra q)).toMonoidHom).range =
      (Units.map q.appTop.hom.toMonoidHom).range := by
  ext a
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom r, rfl⟩
  · rintro ⟨r, rfl⟩
    refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom r, ?_⟩
    apply Units.ext
    exact congrArg (fun x : Γ(Spec (CommRingCat.of R), ⊤) => q.appTop x)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm_apply_apply
        (r : Γ(Spec (CommRingCat.of R), ⊤)))

/-- The coordinate-algebra scalar quotient is the literal geometric scalar quotient. -/
def coordinateScalarQuotientEquiv (q : Z ⟶ Spec (CommRingCat.of R)) :
    (coordinateAlgebra q)ˣ ⧸
        (Units.map (algebraMap R (coordinateAlgebra q)).toMonoidHom).range ≃*
      Γ(Z, ⊤)ˣ ⧸ (Units.map q.appTop.hom.toMonoidHom).range :=
  QuotientGroup.congr _ _ (MulEquiv.refl _)
    ((Subgroup.map_id _).trans (coordinateScalarRange q))

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  (q : Z ⟶ Spec (CommRingCat.of K)) [IsFinite q]

/-- The scalar-unit quotient of the actual finite scheme over an arbitrary test algebra. -/
abbrev BaseChangedScalarQuotient :=
  Γ(pullback q (Spec.map (CommRingCat.ofHom (algebraMap K A))), ⊤)ˣ ⧸
    (Units.map (pullback.snd q (Spec.map
      (CommRingCat.ofHom (algebraMap K A)))).appTop.hom.toMonoidHom).range

/-- Tensor-algebra scalar classes agree with actual geometric scalar classes,
including for nonreduced parameter algebras and nonreduced finite schemes. -/
def baseChangedScalarQuotientEquiv :
    ScalarQuotientPresheaf.ScalarQuotient
        (R := K) (A := coordinateAlgebra q) (S := A) ≃*
      BaseChangedScalarQuotient (A := A) q :=
  (ScalarQuotientPresheaf.scalarUnitQuotientEquiv
    (coordinateAlgebraBaseChangeEquiv (A := A) q)).trans
      (coordinateScalarQuotientEquiv
        (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap K A)))))

/-- The comparison sends each representative to its actual tensor-to-sections image. -/
theorem baseChangedScalarQuotientEquiv_mk (a : (A ⊗[K] coordinateAlgebra q)ˣ) :
    baseChangedScalarQuotientEquiv (A := A) q (QuotientGroup.mk a) =
      QuotientGroup.mk (Units.mapEquiv
        (coordinateAlgebraBaseChangeEquiv (A := A) q).toMulEquiv a) := rfl

end SchemeTheory.Affine.FiniteScheme
