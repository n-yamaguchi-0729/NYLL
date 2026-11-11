/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition

/-!
# Essential surjectivity through actual finite étale inverse-limit models

Given a morphism between inverse-system cones, every finite étale cover of
the source limit first descends to an actual source stage. A lift at that
stage is then pulled back from the corresponding target stage. The native
pullback-composition isomorphisms recover the original cover.

This proves the inverse-limit step used after the Noetherian henselian
case. It does not supply henselian approximation diagrams, Artin
approximation, or the essential surjectivity of the individual stages.
Those are separate mathematical inputs, displayed in the statement.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryInverseLimitEssSurj (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongInverseLimitEssSurj
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongInverseLimitEssSurj
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

/-- Actual stage lifts recover the original cover after pullback along the
map of cones. Only the source cone needs to be a limit: target-stage lifts
already pull back to the prescribed target vertex. -/
theorem exists_inverse_limit_lift_of_stage_essSurj
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (c : Cone D) (d : Cone E) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (a : D ⟶ E) (p : c.pt ⟶ d.pt)
    (hp : ∀ i : I, p ≫ d.π.app i = c.π.app i ≫ a.app i)
    (hstage : ∀ i : I, (FiniteEtale.pullback (a.app i)).EssSurj)
    (V : FiniteEtale c.pt) :
    ∃ (i : I) (W : FiniteEtale (E.obj i)),
      Nonempty ((FiniteEtale.pullback p).obj
        ((FiniteEtale.pullback (d.π.app i)).obj W) ≅ V) := by
  obtain ⟨i, V₀, ⟨eV⟩⟩ := exists_inverse_limit_model D c hc V
  have : (FiniteEtale.pullback (a.app i)).EssSurj := hstage i
  obtain ⟨W, ⟨eW⟩⟩ :=
    Functor.EssSurj.mem_essImage (FiniteEtale.pullback (a.app i)) V₀
  let e₁ : FiniteEtale.pullback (p ≫ d.π.app i) ≅
      FiniteEtale.pullback (d.π.app i) ⋙ FiniteEtale.pullback p :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      p (d.π.app i) (p ≫ d.π.app i) rfl
  let e₂ : FiniteEtale.pullback (p ≫ d.π.app i) ≅
      FiniteEtale.pullback (a.app i) ⋙ FiniteEtale.pullback (c.π.app i) :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      (c.π.app i) (a.app i) (p ≫ d.π.app i) (hp i)
  exact ⟨i, W, ⟨(e₁.app W).symm ≪≫ e₂.app W ≪≫
    (FiniteEtale.pullback (c.π.app i)).mapIso eW ≪≫ eV⟩⟩

/-- Essential surjectivity passes from the original stage restrictions
to the actual restriction between cone vertices. -/
theorem pullback_essSurj_of_inverse_limit_stage_essSurj
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (c : Cone D) (d : Cone E) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (a : D ⟶ E) (p : c.pt ⟶ d.pt)
    (hp : ∀ i : I, p ≫ d.π.app i = c.π.app i ≫ a.app i)
    (hstage : ∀ i : I, (FiniteEtale.pullback (a.app i)).EssSurj) :
    (FiniteEtale.pullback p).EssSurj where
  mem_essImage V := by
    obtain ⟨i, W, hW⟩ :=
      exists_inverse_limit_lift_of_stage_essSurj D E c d hc a p hp hstage V
    exact ⟨(FiniteEtale.pullback (d.π.app i)).obj W, hW⟩

end AlgebraicGeometry.FiniteEtale
