/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.WeilRestriction.Global
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Extending affine-test comparisons to the big fppf site

Every scheme over an affine base is covered by affine schemes. An actual
natural comparison on affine tests therefore identifies the fppf
sheafifications on the whole big site. The proof uses the dense-subsite
equivalence and its compatibility with sheafification.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace SchemeTheory.Affine

variable (R : CommRingCat.{u})

/-- Affine tests cover every object of the relative big fppf site. -/
instance affineForgetFppfCoverDense :
    (affineForget R).IsCoverDense (Scheme.fppfTopology.over (Spec R)) where
  is_cover T := by
    have h := (affineForget R).is_cover_of_isCoverDense
      (Scheme.zariskiTopology.over (Spec R)) T
    rw [GrothendieckTopology.mem_over_iff] at h ⊢
    exact (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ h

variable {F G : (Over (Spec R))ᵒᵖ ⥤ Type (u + 1)}

/-- An isomorphism on affine tests induces one between the actual fppf sheafifications. -/
def fppfSheafificationIsoOfAffineRestriction
    (e : (affineForget R).op ⋙ F ≅ (affineForget R).op ⋙ G) :
    (presheafToSheaf (Scheme.fppfTopology.over (Spec R)) (Type (u + 1))).obj F ≅
      (presheafToSheaf (Scheme.fppfTopology.over (Spec R)) (Type (u + 1))).obj G := by
  let K := Scheme.fppfTopology.over (Spec R)
  let J := (affineForget R).restrictedTopology K
  let E := Functor.IsDenseSubsite.sheafEquiv J K (affineForget R) (Type (u + 1))
  let c := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility
    J K (affineForget R) (Type (u + 1))
  exact E.symm.fullyFaithfulFunctor.preimageIso
    ((c.app F).symm ≪≫ (presheafToSheaf J (Type (u + 1))).mapIso e ≪≫ c.app G)

/-- A comparison on spectra of coefficient algebras applies to every affine test scheme. -/
def affineRestrictionIsoOfSpecRestriction
    (e : (specOverFunctor R).op ⋙ F ≅ (specOverFunctor R).op ⋙ G) :
    (affineForget R).op ⋙ F ≅ (affineForget R).op ⋙ G :=
  Functor.isoWhiskerRight (NatIso.op (affineToSpecGammaIso R).symm) F ≪≫
    Functor.associator (affineAlgebraEquiv R).functor.rightOp.op (specOverFunctor R).op F ≪≫
      Functor.isoWhiskerLeft (affineAlgebraEquiv R).functor.rightOp.op e ≪≫
        (Functor.associator (affineAlgebraEquiv R).functor.rightOp.op
          (specOverFunctor R).op G).symm ≪≫
            (Functor.isoWhiskerRight (NatIso.op (affineToSpecGammaIso R).symm) G).symm

/-- Natural spectrum-valued comparisons determine the big fppf sheafification. -/
def fppfSheafificationIsoOfSpecRestriction
    (e : (specOverFunctor R).op ⋙ F ≅ (specOverFunctor R).op ⋙ G) :
    (presheafToSheaf (Scheme.fppfTopology.over (Spec R)) (Type (u + 1))).obj F ≅
      (presheafToSheaf (Scheme.fppfTopology.over (Spec R)) (Type (u + 1))).obj G :=
  fppfSheafificationIsoOfAffineRestriction R (affineRestrictionIsoOfSpecRestriction R e)

end SchemeTheory.Affine
