/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ProperFinitePresentationTwoFibers
import Nyll.SchemeTheory.FiniteEtale.InverseLimitFiniteFamily

/-!
# Two-fiber finite-presentation approximation carrying original covers

A finite family of covers of the original proper scheme descends along
its actual closed-thickening limit. Starting inside a proper finitely
presented ambient that already has the two original field fibers ensures
the resulting intermediate thickening retains both fiber identifications.
The output includes the original total-space morphism and native recovery
of every supplied cover. No Noetherian hypothesis is imposed on the base.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.IdealSheafData

private theorem intermediate_fiber_iso
    {X Z Y S T : Scheme.{u}} (a : X ⟶ Z) (b : Z ⟶ Y) [IsClosedImmersion b]
    (i : X ⟶ Y) (hai : a ≫ b = i) (f : X ⟶ S) (g : Y ⟶ S)
    (hi : i ≫ g = f) (s : T ⟶ S)
    (e : pullback f s ≅ pullback g s)
    (hefst : e.hom ≫ pullback.fst g s = pullback.fst f s ≫ i)
    (hesnd : e.hom ≫ pullback.snd g s = pullback.snd f s) :
    ∃ e' : pullback f s ≅ pullback (b ≫ g) s,
      e'.hom ≫ pullback.fst (b ≫ g) s = pullback.fst f s ≫ a ∧
      e'.hom ≫ pullback.snd (b ≫ g) s = pullback.snd f s := by
  have ha : a ≫ (b ≫ g) = f := by rw [← Category.assoc, hai, hi]
  let p : pullback f s ⟶ pullback (b ≫ g) s :=
    pullback.lift (pullback.fst f s ≫ a) (pullback.snd f s)
      (by rw [Category.assoc, ha, pullback.condition])
  let q : pullback (b ≫ g) s ⟶ pullback g s :=
    pullback.lift (pullback.fst (b ≫ g) s ≫ b) (pullback.snd (b ≫ g) s)
      (by rw [Category.assoc, pullback.condition])
  have hpfst : p ≫ pullback.fst (b ≫ g) s = pullback.fst f s ≫ a :=
    pullback.lift_fst _ _ _
  have hpsnd : p ≫ pullback.snd (b ≫ g) s = pullback.snd f s :=
    pullback.lift_snd _ _ _
  have hqfst : q ≫ pullback.fst g s = pullback.fst (b ≫ g) s ≫ b :=
    pullback.lift_fst _ _ _
  have hqsnd : q ≫ pullback.snd g s = pullback.snd (b ≫ g) s :=
    pullback.lift_snd _ _ _
  have outer : IsPullback (pullback.fst (b ≫ g) s)
      (q ≫ pullback.snd g s) (b ≫ g) s := by
    rw [hqsnd]
    exact IsPullback.of_hasPullback (b ≫ g) s
  have sq : IsPullback (pullback.fst (b ≫ g) s) q b (pullback.fst g s) :=
    outer.of_bot hqfst.symm (IsPullback.of_hasPullback g s)
  have : IsClosedImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
      (self := IsClosedImmersion.isStableUnderBaseChange) sq inferInstance
  have hpq : p ≫ q = e.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, hqfst, ← Category.assoc, hpfst,
        Category.assoc, hai, hefst]
    · rw [Category.assoc, hqsnd, hpsnd, hesnd]
  have hpInv : p ≫ (q ≫ e.inv) = 𝟙 _ := by
    rw [← Category.assoc, hpq, e.hom_inv_id]
  have hpInv' : (q ≫ e.inv) ≫ p = 𝟙 _ := by
    apply (cancel_mono q).mp
    calc
      ((q ≫ e.inv) ≫ p) ≫ q = q ≫ e.inv ≫ (p ≫ q) := by
        simp only [Category.assoc]
      _ = q ≫ e.inv ≫ e.hom := by rw [hpq]
      _ = 𝟙 _ ≫ q := by rw [e.inv_hom_id, Category.comp_id, Category.id_comp]
  have : IsIso p := ⟨⟨q ≫ e.inv, hpInv, hpInv'⟩⟩
  exact ⟨asIso p, hpfst, hpsnd⟩

/-- Finitely many original finite étale covers extend simultaneously to a
proper finitely presented closed thickening that retains the two supplied
field fibers and both original projection equations. -/
theorem exists_proper_finitePresentation_model_with_two_fiberIsos_and_covers
    {R kₛ kₜ : Type u} [CommRing R] [Field kₛ] [Field kₜ] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (s : Spec (CommRingCat.of kₛ) ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of kₜ) ⟶ Spec (CommRingCat.of R))
    {α : Type v} [Finite α] (V : α → FiniteEtale X) :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion i ∧ IsProper g ∧ LocallyOfFinitePresentation g ∧ i ≫ g = f ∧
      ∃ (eₛ : pullback f s ≅ pullback g s) (eₜ : pullback f t ≅ pullback g t)
        (W : α → FiniteEtale Y),
        eₛ.hom ≫ pullback.fst g s = pullback.fst f s ≫ i ∧
        eₛ.hom ≫ pullback.snd g s = pullback.snd f s ∧
        eₜ.hom ≫ pullback.fst g t = pullback.fst f t ≫ i ∧
        eₜ.hom ≫ pullback.snd g t = pullback.snd f t ∧
        ∀ a : α, Nonempty ((FiniteEtale.pullback i).obj (W a) ≅ V a) := by
  obtain ⟨Y, i, g, hi, hg, hfp, hig, eₛ, eₜ, heₛfst, heₛsnd, heₜfst, heₜsnd⟩ :=
    exists_proper_finitePresentation_model_with_two_fiberIsos f s t
  have : IsClosedImmersion i := hi
  have : IsProper g := hg
  have : LocallyOfFinitePresentation g := hfp
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  have (J : (FiniteSubideal i.ker)ᵒᵖ) :
      CompactSpace ((ClosedImmersionApproximation.diagram i).obj J) := by
    change CompactSpace J.unop.1.subscheme
    exact QuasiCompact.compactSpace_of_compactSpace J.unop.1.subschemeι
  have (J : (FiniteSubideal i.ker)ᵒᵖ) :
      QuasiSeparatedSpace ((ClosedImmersionApproximation.diagram i).obj J) := by
    change QuasiSeparatedSpace J.unop.1.subscheme
    exact quasiSeparatedSpace_of_quasiSeparated J.unop.1.subschemeι
  obtain ⟨J, W, hW⟩ := FiniteEtale.exists_inverse_limit_models_finite_family
    (ClosedImmersionApproximation.diagram i) (ClosedImmersionApproximation.cone i)
    (ClosedImmersionApproximation.coneIsLimit i) V
  let a : X ⟶ J.unop.1.subscheme := (ClosedImmersionApproximation.cone i).π.app J
  have hai : a ≫ J.unop.1.subschemeι = i :=
    ClosedImmersionApproximation.cone_projection_subschemeι i J
  have : IsClosedImmersion a := by
    change IsClosedImmersion (i.toImage ≫ inclusion J.unop.2.1)
    infer_instance
  have : LocallyOfFinitePresentation J.unop.1.subschemeι :=
    locallyOfFinitePresentation_subschemeι_of_fg J.unop.1 J.unop.2.2
  obtain ⟨dₛ, hdₛfst, hdₛsnd⟩ := intermediate_fiber_iso
    a J.unop.1.subschemeι i hai f g hig s eₛ heₛfst heₛsnd
  obtain ⟨dₜ, hdₜfst, hdₜsnd⟩ := intermediate_fiber_iso
    a J.unop.1.subschemeι i hai f g hig t eₜ heₜfst heₜsnd
  refine ⟨J.unop.1.subscheme, a, J.unop.1.subschemeι ≫ g,
    inferInstance, inferInstance, inferInstance, ?_,
    dₛ, dₜ, W, hdₛfst, hdₛsnd, hdₜfst, hdₜsnd, hW⟩
  rw [← Category.assoc, hai, hig]

end AlgebraicGeometry
