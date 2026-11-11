/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ProperFinitePresentationAmbient
public import Nyll.SchemeTheory.Descent.ClosedImmersionFinitePresentationLimit
public import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# A proper finite-presentation thickening carrying a given closed-fiber cover

The actual proper ambient construction embeds the original proper scheme
into a proper finitely presented scheme. Its finite-subideal closed
thickenings form the maintained inverse-limit diagram. Lifting that diagram
over the original base and pulling back its cone to the residue field
retains the literal original closed fiber at the limit vertex.

Finite-etale inverse-limit descent gives a cover of one actual thickening's
closed fiber whose native pullback is the given cover. This reduction does
not require henselianity and does not assert a lift off the closed fiber.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.FiniteEtale

open Scheme.IdealSheafData

/-- A given finite-etale cover of the closed fiber of an arbitrary proper
family descends to the closed fiber of an actual proper finitely presented
thickening. The original scheme, structure map, Cartesian closed-fiber
square, residue projection, and native cover recovery are all retained. -/
theorem exists_proper_finitePresentation_closedFiber_model
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (V : FiniteEtale (Limits.pullback f
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion i ∧ IsProper g ∧ LocallyOfFinitePresentation g ∧ i ≫ g = f ∧
      ∃ p : Limits.pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶
          Limits.pullback g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))),
        IsPullback
          (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) p i
          (pullback.fst g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ∧
        p ≫ pullback.snd g (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) =
          pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ∧
        ∃ W : FiniteEtale (Limits.pullback g
            (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))),
          Nonempty ((FiniteEtale.pullback p).obj W ≅ V) := by
  obtain ⟨Y, i, g, hi, hg, hgfp, hig⟩ := exists_proper_finitePresentation_ambient f
  have : IsClosedImmersion i := hi
  have : IsProper g := hg
  have : LocallyOfFinitePresentation g := hgfp
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  let I := i.ker
  let D := ClosedImmersionApproximation.diagram i
  let c := ClosedImmersionApproximation.cone i
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) :=
    { app := fun J => J.unop.1.subschemeι ≫ g
      naturality := fun J K h => by
        change inclusion (show K.unop.1 ≤ J.unop.1 from h.unop.le) ≫
          (K.unop.1.subschemeι ≫ g) = (J.unop.1.subschemeι ≫ g) ≫ 𝟙 _
        rw [← Category.assoc, inclusion_subschemeι, Category.comp_id] }
  have hct (J : (FiniteSubideal I)ᵒᵖ) : c.π.app J ≫ t.app J = f := by
    exact (Category.assoc
      (show X ⟶ J.unop.1.subscheme from c.π.app J) J.unop.1.subschemeι g).symm.trans
        ((congrArg (fun q : X ⟶ Y => q ≫ g)
          (ClosedImmersionApproximation.cone_projection_subschemeι i J)).trans hig)
  let ρ := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let B := Spec (CommRingCat.of (IsLocalRing.ResidueField R))
  let E : (FiniteSubideal I)ᵒᵖ ⥤ Scheme.{u} :=
    Over.lift D t ⋙ Over.pullback ρ ⋙ Over.forget B
  let d : Cone E := (Over.pullback ρ ⋙ Over.forget B).mapCone
    (Over.liftCone D t c f hct)
  have : CategoryTheory.IsConnected (FiniteSubideal I)ᵒᵖ := IsCofiltered.isConnected _
  have hd : IsLimit d :=
    isLimitOfPreserves (Over.pullback ρ ⋙ Over.forget B)
      (Over.isLimitLiftCone D t c f hct (ClosedImmersionApproximation.coneIsLimit i))
  have : ∀ {J K : (FiniteSubideal I)ᵒᵖ} (h : J ⟶ K),
      IsClosedImmersion (E.map h) := by
    intro J K h
    change IsClosedImmersion (((Over.pullback ρ).map ((Over.lift D t).map h)).left)
    exact MorphismProperty.overPullbackMap
      (P := (@IsClosedImmersion : MorphismProperty Scheme.{u})) ρ
      ((Over.lift D t).map h) (inferInstanceAs (IsClosedImmersion (D.map h)))
  have : ∀ {J K : (FiniteSubideal I)ᵒᵖ} (h : J ⟶ K), IsAffineHom (E.map h) :=
    fun _ => inferInstance
  have : ∀ J : (FiniteSubideal I)ᵒᵖ, CompactSpace (E.obj J) := by
    intro J
    change CompactSpace (Limits.pullback (J.unop.1.subschemeι ≫ g) ρ : Scheme.{u})
    exact QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (J.unop.1.subschemeι ≫ g) ρ)
  have : ∀ J : (FiniteSubideal I)ᵒᵖ, QuasiSeparatedSpace (E.obj J) := by
    intro J
    change QuasiSeparatedSpace (Limits.pullback (J.unop.1.subschemeι ≫ g) ρ : Scheme.{u})
    exact quasiSeparatedSpace_of_quasiSeparated
      (pullback.snd (J.unop.1.subschemeι ≫ g) ρ)
  obtain ⟨J, W, hW⟩ := exists_inverse_limit_model E d hd V
  let iJ : X ⟶ J.unop.1.subscheme := c.π.app J
  let gJ : J.unop.1.subscheme ⟶ Spec (CommRingCat.of R) := J.unop.1.subschemeι ≫ g
  let p : Limits.pullback f ρ ⟶ Limits.pullback gJ ρ := d.π.app J
  have : IsClosedImmersion iJ := by
    change IsClosedImmersion (i.toImage ≫ inclusion J.unop.2.1)
    infer_instance
  have : LocallyOfFinitePresentation J.unop.1.subschemeι :=
    locallyOfFinitePresentation_subschemeι_of_fg J.unop.1 J.unop.2.2
  have hiJ : iJ ≫ gJ = f := hct J
  have hpfst : p ≫ pullback.fst gJ ρ = pullback.fst f ρ ≫ iJ :=
    pullback.lift_fst _ _ _
  have hpsnd : p ≫ pullback.snd gJ ρ = pullback.snd f ρ :=
    pullback.lift_snd _ _ _
  have sq : IsPullback (pullback.fst f ρ) p iJ (pullback.fst gJ ρ) := by
    have houter : IsPullback (pullback.fst f ρ) (p ≫ pullback.snd gJ ρ)
        (iJ ≫ gJ) ρ := by
      rw [hpsnd, hiJ]
      exact IsPullback.of_hasPullback f ρ
    exact houter.of_bot hpfst.symm (IsPullback.of_hasPullback gJ ρ)
  exact ⟨J.unop.1.subscheme, iJ, gJ, inferInstance, inferInstance, inferInstance,
    hiJ, p, sq, hpsnd, W, hW⟩

end AlgebraicGeometry.FiniteEtale
