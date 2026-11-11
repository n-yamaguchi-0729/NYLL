/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Descent.ClosedImmersionFinitePresentationBaseChange
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Exact finite-stage recovery after base change

If an actual closed subscheme becomes finitely presented after a qcqs base
change, some finite subideal already recovers that closed subscheme after
the same base change. The identity descends along the actual finite-stage
limit, and the closed immersion into the fixed base makes the descended
retraction an inverse.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- A finitely presented base change of an actual closed subscheme is
recovered by the native projection to an actual finite-subideal stage. -/
theorem exists_isIso_baseChangeProjection
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (I : X.IdealSheafData) (g : Y ⟶ X)
    [hfp : LocallyOfFinitePresentation (pullback.snd I.subschemeι g)] :
    ∃ J : (FiniteSubideal I)ᵒᵖ,
      IsIso ((finiteSubschemeBaseChangeCone I g).π.app J) := by
  let D := finiteSubschemeBaseChangeDiagram I g
  let c := finiteSubschemeBaseChangeCone I g
  let t := finiteSubschemeBaseChangeMap I g
  let i : c.pt ⟶ Y := pullback.snd I.subschemeι g
  have : LocallyOfFinitePresentation i := hfp
  have hcompat : c.π ≫ t = (Functor.const _).map (𝟙 c.pt ≫ i) := by
    ext J
    change c.π.app J ≫ pullback.snd J.unop.1.subschemeι g = 𝟙 c.pt ≫ i
    rw [Category.id_comp]
    exact finiteSubschemeBaseChangeCone_projection_snd I g J
  obtain ⟨J, a, ha, hai⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      D t i c (finiteSubschemeBaseChangeConeIsLimit I g) (𝟙 c.pt) hcompat
  have hJclosed : IsClosedImmersion (pullback.snd J.unop.1.subschemeι g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
      (self := IsClosedImmersion.isStableUnderBaseChange)
      (IsPullback.of_hasPullback J.unop.1.subschemeι g) inferInstance
  have hright : a ≫ c.π.app J = 𝟙 (D.obj J) := by
    apply (cancel_mono (pullback.snd J.unop.1.subschemeι g)).mp
    have hp : c.π.app J ≫ pullback.snd J.unop.1.subschemeι g = i :=
      finiteSubschemeBaseChangeCone_projection_snd I g J
    have hai' : a ≫ i = pullback.snd J.unop.1.subschemeι g := hai
    exact (Category.assoc a (c.π.app J) (pullback.snd J.unop.1.subschemeι g)).trans
      ((congrArg (fun z : c.pt ⟶ Y => a ≫ z) hp).trans
        (hai'.trans (Category.id_comp (pullback.snd J.unop.1.subschemeι g)).symm))
  exact ⟨J, ⟨⟨a, ha, hright⟩⟩⟩

end AlgebraicGeometry.Scheme.IdealSheafData
