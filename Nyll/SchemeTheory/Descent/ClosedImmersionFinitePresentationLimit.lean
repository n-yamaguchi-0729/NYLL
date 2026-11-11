/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Sheaves.IdealSheafFiniteSubideals
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Finite-presentation approximation of an actual closed immersion

The finite subideals of an actual ideal sheaf give closed subschemes of finite
presentation. Their inverse limit is the original closed subscheme: the
existing kernel/subscheme adjunction transports the supremum of finite
subideals to a limit in the over category, and its forgetful functor preserves
this connected limit. The original source of any closed immersion is retained
using its existing canonical isomorphism to its scheme-theoretic image.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Finite generation on affine opens gives finite presentation of the
actual closed-subscheme inclusion. -/
theorem locallyOfFinitePresentation_subschemeι_of_fg (I : X.IdealSheafData)
    (hfg : ∀ U : X.affineOpens, (I.ideal U).FG) :
    LocallyOfFinitePresentation I.subschemeι := by
  constructor
  intro U hU V hV e
  have happ : (I.subschemeι.app U).hom.FinitePresentation := by
    apply RingHom.FinitePresentation.of_surjective _
      (I.subschemeι_app_surjective ⟨U, hU⟩)
    rw [I.ker_subschemeι_app ⟨U, hU⟩]
    exact hfg ⟨U, hU⟩
  have hres : (I.subscheme.presheaf.map (homOfLE e).op).hom.FinitePresentation := by
    have hid := HasRingHomProperty.appLE @LocallyOfFinitePresentation
      (𝟙 I.subscheme) inferInstance ⟨I.subschemeι ⁻¹ᵁ U, hU.preimage I.subschemeι⟩
      ⟨V, hV⟩ e
    have hmap : ((𝟙 I.subscheme : I.subscheme ⟶ I.subscheme).appLE
        (I.subschemeι ⁻¹ᵁ U) V e).hom =
        (I.subscheme.presheaf.map (homOfLE e).op).hom :=
      congrArg CommRingCat.Hom.hom
        (Category.id_comp (I.subscheme.presheaf.map (homOfLE e).op))
    exact hmap ▸ hid
  exact hres.comp happ

/-- The monotone inclusion of the finite subideals into all ideal sheaves. -/
def finiteSubidealOrder (I : X.IdealSheafData) :
    FiniteSubideal I →o X.IdealSheafData where
  toFun := Subtype.val
  monotone' := fun _ _ h => h

/-- The original ideal sheaf maps to each finite subideal in the opposite order. -/
def finiteSubidealCone (I : X.IdealSheafData) :
    Cone (finiteSubidealOrder I).toFunctor.op where
  pt := op I
  π :=
    { app := fun J => (homOfLE J.unop.2.1).op
      naturality := fun _ _ _ => Subsingleton.elim _ _ }

/-- Exhaustion by finite subideals gives the original ideal sheaf as the limit. -/
def finiteSubidealConeIsLimit [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) : IsLimit (finiteSubidealCone I) where
  lift s := (homOfLE (show I ≤ s.pt.unop from by
    exact (iSup_finiteSubideals I).ge.trans
      (iSup_le fun J => (s.π.app (op J)).unop.le))).op
  fac _ _ := Subsingleton.elim _ _
  uniq _ _ _ := Subsingleton.elim _ _

/-- The stages are the actual closed subschemes cut out by finite subideals. -/
def finiteSubschemeDiagram (I : X.IdealSheafData) :
    (FiniteSubideal I)ᵒᵖ ⥤ Scheme.{u} :=
  (finiteSubidealOrder I).toFunctor.op ⋙ subschemeFunctor X ⋙ Over.forget X

/-- The literal original closed subscheme maps to each finite stage. -/
def finiteSubschemeCone (I : X.IdealSheafData) :
    Cone (finiteSubschemeDiagram I) :=
  (subschemeFunctor X ⋙ Over.forget X).mapCone (finiteSubidealCone I)

theorem finiteSubschemeCone_projection (I : X.IdealSheafData)
    (J : (FiniteSubideal I)ᵒᵖ) :
    (finiteSubschemeCone I).π.app J = inclusion J.unop.2.1 := rfl

theorem finiteSubschemeCone_projection_subschemeι (I : X.IdealSheafData)
    (J : (FiniteSubideal I)ᵒᵖ) :
    (finiteSubschemeCone I).π.app J ≫ J.unop.1.subschemeι = I.subschemeι :=
  inclusion_subschemeι J.unop.2.1

instance (I : X.IdealSheafData) {J K : (FiniteSubideal I)ᵒᵖ} (h : J ⟶ K) :
    IsClosedImmersion ((finiteSubschemeDiagram I).map h) :=
  inferInstanceAs (IsClosedImmersion (inclusion (show K.unop.1 ≤ J.unop.1 from h.unop.le)))

instance (I : X.IdealSheafData) (J : (FiniteSubideal I)ᵒᵖ) :
    LocallyOfFinitePresentation J.unop.1.subschemeι :=
  locallyOfFinitePresentation_subschemeι_of_fg J.unop.1 J.unop.2.2

/-- The ideal/subscheme adjunction turns the actual exhaustive finite-subideal
family into the original closed subscheme's inverse limit. -/
def finiteSubschemeConeIsLimit [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) : IsLimit (finiteSubschemeCone I) := by
  have : IsConnected (FiniteSubideal I)ᵒᵖ := IsCofiltered.isConnected _
  have : PreservesLimitsOfShape (FiniteSubideal I)ᵒᵖ (subschemeFunctor X) :=
    X.kerAdjunction.rightOp.rightAdjoint_preservesLimits.preservesLimitsOfShape
  exact isLimitOfPreserves (subschemeFunctor X ⋙ Over.forget X) (finiteSubidealConeIsLimit I)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.ClosedImmersionApproximation

variable {Y X : Scheme.{u}} (f : Y ⟶ X)

/-- The finite-presentation closed-subscheme diagram attached to the actual
kernel of the original closed immersion. -/
abbrev diagram : (Scheme.IdealSheafData.FiniteSubideal f.ker)ᵒᵖ ⥤ Scheme.{u} :=
  f.ker.finiteSubschemeDiagram

/-- The cone retains the literal original source and its canonical stage maps. -/
def cone : Cone (diagram f) :=
  f.ker.finiteSubschemeCone.extend f.toImage

theorem cone_projection_subschemeι (J : (Scheme.IdealSheafData.FiniteSubideal f.ker)ᵒᵖ) :
    (cone f).π.app J ≫ J.unop.1.subschemeι = f := by
  change (f.toImage ≫ Scheme.IdealSheafData.inclusion J.unop.2.1) ≫
    J.unop.1.subschemeι = f
  rw [Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι,
    Scheme.Hom.toImage_imageι]

/-- Every closed immersion into a quasicompact quasiseparated scheme is the
inverse limit of its actual finite-presentation closed thickenings. -/
def coneIsLimit [IsClosedImmersion f] [CompactSpace X] [QuasiSeparatedSpace X] :
    IsLimit (cone f) := by
  let e₀ : Y ≅ f.ker.subscheme := asIso f.toImage
  let e : Y ≅ f.ker.finiteSubschemeCone.pt := e₀
  exact IsLimit.extendIso (s := f.ker.finiteSubschemeCone) e.hom
    f.ker.finiteSubschemeConeIsLimit

end AlgebraicGeometry.ClosedImmersionApproximation
