/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.ClosedImmersionFinitePresentationLimit
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Base change of the actual finite closed-thickening diagram

The original finite-subideal approximation is lifted to the over category.
The existing pullback functor preserves its limit, yielding the literal
base change of the original closed subscheme as the inverse limit of the
base-changed finite thickenings.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (g : Y ⟶ X)

/-- The native closed-thickening diagram over its fixed ambient scheme. -/
def finiteSubschemeBaseMap :
    finiteSubschemeDiagram I ⟶ (Functor.const _).obj X where
  app J := J.unop.1.subschemeι
  naturality J K h := by
    change inclusion (show K.unop.1 ≤ J.unop.1 from h.unop.le) ≫
      K.unop.1.subschemeι = J.unop.1.subschemeι ≫ 𝟙 X
    rw [inclusion_subschemeι, Category.comp_id]

/-- The actual base-changed finite closed thickenings. -/
def finiteSubschemeBaseChangeDiagram :
    (FiniteSubideal I)ᵒᵖ ⥤ Scheme.{u} :=
  Over.lift (finiteSubschemeDiagram I) (finiteSubschemeBaseMap I) ⋙
    Over.pullback g ⋙ Over.forget Y

/-- The cone has the literal original base-changed closed subscheme as vertex. -/
def finiteSubschemeBaseChangeCone : Cone (finiteSubschemeBaseChangeDiagram I g) :=
  (Over.pullback g ⋙ Over.forget Y).mapCone
    (Over.liftCone (finiteSubschemeDiagram I) (finiteSubschemeBaseMap I)
      (finiteSubschemeCone I) I.subschemeι (finiteSubschemeCone_projection_subschemeι I))

theorem finiteSubschemeBaseChangeDiagram_map_snd
    {J K : (FiniteSubideal I)ᵒᵖ} (h : J ⟶ K) :
    (finiteSubschemeBaseChangeDiagram I g).map h ≫ pullback.snd K.unop.1.subschemeι g =
      pullback.snd J.unop.1.subschemeι g :=
  pullback.lift_snd _ _ _

theorem finiteSubschemeBaseChangeCone_projection_snd (J : (FiniteSubideal I)ᵒᵖ) :
    (finiteSubschemeBaseChangeCone I g).π.app J ≫ pullback.snd J.unop.1.subschemeι g =
      pullback.snd I.subschemeι g :=
  pullback.lift_snd _ _ _

/-- The actual stage closed immersions into the new ambient scheme. -/
def finiteSubschemeBaseChangeMap :
    finiteSubschemeBaseChangeDiagram I g ⟶ (Functor.const _).obj Y where
  app J := pullback.snd J.unop.1.subschemeι g
  naturality J K h := by
    change (finiteSubschemeBaseChangeDiagram I g).map h ≫
      pullback.snd K.unop.1.subschemeι g = pullback.snd J.unop.1.subschemeι g ≫ 𝟙 Y
    rw [finiteSubschemeBaseChangeDiagram_map_snd, Category.comp_id]

instance {J K : (FiniteSubideal I)ᵒᵖ} (h : J ⟶ K) :
    IsClosedImmersion ((finiteSubschemeBaseChangeDiagram I g).map h) := by
  have hJ : IsClosedImmersion
      (pullback.snd (J.unop.1.subschemeι : J.unop.1.subscheme ⟶ X) g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
      (self := IsClosedImmersion.isStableUnderBaseChange)
      (IsPullback.of_hasPullback J.unop.1.subschemeι g) inferInstance
  have hK : IsClosedImmersion
      (pullback.snd (K.unop.1.subschemeι : K.unop.1.subscheme ⟶ X) g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
      (self := IsClosedImmersion.isStableUnderBaseChange)
      (IsPullback.of_hasPullback K.unop.1.subschemeι g) inferInstance
  have hcomp : IsClosedImmersion ((finiteSubschemeBaseChangeDiagram I g).map h ≫
      pullback.snd K.unop.1.subschemeι g) := by
    rw [finiteSubschemeBaseChangeDiagram_map_snd]
    exact hJ
  exact @IsClosedImmersion.of_comp_isClosedImmersion
    (pullback J.unop.1.subschemeι g) (pullback K.unop.1.subschemeι g) Y
    ((finiteSubschemeBaseChangeDiagram I g).map h)
    (pullback.snd K.unop.1.subschemeι g) hK hcomp

instance [CompactSpace Y] (J : (FiniteSubideal I)ᵒᵖ) :
    CompactSpace ((finiteSubschemeBaseChangeDiagram I g).obj J) := by
  change CompactSpace (pullback J.unop.1.subschemeι g : Scheme.{u})
  have : IsClosedImmersion
      (pullback.snd (J.unop.1.subschemeι : J.unop.1.subscheme ⟶ X) g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
      (self := IsClosedImmersion.isStableUnderBaseChange)
      (IsPullback.of_hasPullback J.unop.1.subschemeι g) inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd J.unop.1.subschemeι g)

instance [QuasiSeparatedSpace Y] (J : (FiniteSubideal I)ᵒᵖ) :
    QuasiSeparatedSpace ((finiteSubschemeBaseChangeDiagram I g).obj J) := by
  change QuasiSeparatedSpace (pullback J.unop.1.subschemeι g : Scheme.{u})
  have : IsClosedImmersion
      (pullback.snd (J.unop.1.subschemeι : J.unop.1.subscheme ⟶ X) g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
      (self := IsClosedImmersion.isStableUnderBaseChange)
      (IsPullback.of_hasPullback J.unop.1.subschemeι g) inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd J.unop.1.subschemeι g)

/-- Pullback preserves the actual limit in the over category; forgetting
the new ambient scheme preserves this connected limit. -/
def finiteSubschemeBaseChangeConeIsLimit [CompactSpace X] [QuasiSeparatedSpace X] :
    IsLimit (finiteSubschemeBaseChangeCone I g) := by
  have : IsConnected (FiniteSubideal I)ᵒᵖ := IsCofiltered.isConnected _
  exact isLimitOfPreserves (Over.pullback g ⋙ Over.forget Y)
    (Over.isLimitLiftCone (finiteSubschemeDiagram I) (finiteSubschemeBaseMap I)
      (finiteSubschemeCone I) I.subschemeι (finiteSubschemeCone_projection_subschemeι I)
      (finiteSubschemeConeIsLimit I))

end AlgebraicGeometry.Scheme.IdealSheafData
