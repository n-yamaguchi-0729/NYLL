/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.AffineClosedImmersionFiniteThickening
public import Nyll.SchemeTheory.Descent.ClosedImmersionFinitePresentationBaseChange
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Finite closed thickenings with a closed immersion into an affine target

Eventual affineness of the actual closed-thickening limit reduces a
quasicompact quasiseparated source to the affine finite-equation result.
Finite-presentation descent then returns to the original finite-subideal
diagram, retaining its actual ambient inclusion.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- If a finite-type morphism to an affine scheme is a closed immersion on
an actual closed subscheme, it is a closed immersion on some actual finite
closed thickening of that subscheme. -/
theorem exists_finiteSubideal_isClosedImmersion_of_isAffine
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [IsAffine Y]
    (I : X.IdealSheafData) (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsClosedImmersion (I.subschemeι ≫ f)] :
    ∃ J : FiniteSubideal I, IsClosedImmersion (J.1.subschemeι ≫ f) := by
  have (J : (FiniteSubideal I)ᵒᵖ) :
      CompactSpace ((finiteSubschemeDiagram I).obj J) := by
    change CompactSpace J.unop.1.subscheme
    exact QuasiCompact.compactSpace_of_compactSpace J.unop.1.subschemeι
  have (J : (FiniteSubideal I)ᵒᵖ) :
      QuasiSeparatedSpace ((finiteSubschemeDiagram I).obj J) := by
    change QuasiSeparatedSpace J.unop.1.subscheme
    exact quasiSeparatedSpace_of_quasiSeparated J.unop.1.subschemeι
  have hIaff : IsAffine I.subscheme :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine (I.subschemeι ≫ f)).1
  have : IsAffine (finiteSubschemeCone I).pt := hIaff
  obtain ⟨J, hJ⟩ := Scheme.exists_isAffine_of_isLimit
    (finiteSubschemeDiagram I) (finiteSubschemeCone I) (finiteSubschemeConeIsLimit I)
  have : IsAffine J.unop.1.subscheme := hJ
  let i : I.subscheme ⟶ J.unop.1.subscheme := inclusion J.unop.2.1
  have hi : i ≫ (J.unop.1.subschemeι ≫ f) = I.subschemeι ≫ f :=
    (Category.assoc i J.unop.1.subschemeι f).symm.trans
      (congrArg (fun z : I.subscheme ⟶ X => z ≫ f) (inclusion_subschemeι J.unop.2.1))
  have : IsClosedImmersion (i ≫ (J.unop.1.subschemeι ≫ f)) := hi.symm ▸ inferInstance
  obtain ⟨C, c, a, hc, hcfp, hcf, hac⟩ :=
    ClosedImmersionApproximation.exists_affine_finitePresentation_thickening
      i (J.unop.1.subschemeι ≫ f)
  let k : C ⟶ X := c ≫ J.unop.1.subschemeι
  have : IsClosedImmersion k := inferInstance
  have : LocallyOfFinitePresentation k := inferInstance
  have hak : a ≫ k = I.subschemeι :=
    (Category.assoc a c J.unop.1.subschemeι).symm.trans
      ((congrArg (fun z : I.subscheme ⟶ J.unop.1.subscheme =>
        z ≫ J.unop.1.subschemeι) hac).trans (inclusion_subschemeι J.unop.2.1))
  have hkf : k ≫ f = c ≫ (J.unop.1.subschemeι ≫ f) :=
    Category.assoc c J.unop.1.subschemeι f
  have : IsClosedImmersion (k ≫ f) := hkf.symm ▸ hcf
  have hcompat : (finiteSubschemeCone I).π ≫ finiteSubschemeBaseMap I =
      (Functor.const _).map (a ≫ k) := by
    ext K
    change (finiteSubschemeCone I).π.app K ≫ K.unop.1.subschemeι = a ≫ k
    exact (finiteSubschemeCone_projection_subschemeι I K).trans hak.symm
  obtain ⟨K, b, -, hbk⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (finiteSubschemeDiagram I) (finiteSubschemeBaseMap I) k
      (finiteSubschemeCone I) (finiteSubschemeConeIsLimit I) a hcompat
  have hbk' : b ≫ k = K.unop.1.subschemeι := hbk
  have hKclosed : IsClosedImmersion (K.unop.1.subschemeι : K.unop.1.subscheme ⟶ X) :=
    inferInstance
  have : IsClosedImmersion (b ≫ k) := hbk'.symm ▸ hKclosed
  have : IsClosedImmersion b := IsClosedImmersion.of_comp_isClosedImmersion b k
  have heq : K.unop.1.subschemeι ≫ f = b ≫ (k ≫ f) :=
    (congrArg (fun z : K.unop.1.subscheme ⟶ X => z ≫ f) hbk'.symm).trans
      (Category.assoc b k f)
  exact ⟨K.unop, heq.symm ▸ inferInstanceAs (IsClosedImmersion (b ≫ (k ≫ f)))⟩

end AlgebraicGeometry.Scheme.IdealSheafData
