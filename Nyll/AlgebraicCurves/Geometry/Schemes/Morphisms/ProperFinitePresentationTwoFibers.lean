/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.ProperFinitePresentationAmbient
public import Nyll.SchemeTheory.Descent.FiniteClosedThickeningRecovery
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Proper finite-presentation approximation preserving two actual fibers

The two field fibers of a proper finite-presentation ambient are Noetherian.
The original closed subscheme therefore has finitely presented pullbacks to
both fibers. Exact finite-stage recovery gives finite subideals with the
same pulled-back ideals. A common finite subideal retains both equalities.

The resulting proper finite-presentation thickening contains the original
scheme, and its two fiber isomorphisms retain the original structure maps
and both projections. The base ring need not be Noetherian or henselian,
and the two fields need not be separably closed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.IdealSheafData

private theorem exists_fiber_comparison
    {X Y S T : Scheme.{u}} (i : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (hi : i ≫ g = f) (s : T ⟶ S) :
    ∃ p : pullback f s ⟶ pullback g s,
      IsPullback (pullback.fst f s) p i (pullback.fst g s) ∧
      p ≫ pullback.snd g s = pullback.snd f s := by
  let p : pullback f s ⟶ pullback g s :=
    pullback.lift (pullback.fst f s ≫ i) (pullback.snd f s)
      (by rw [Category.assoc, hi, pullback.condition])
  have hfst : p ≫ pullback.fst g s = pullback.fst f s ≫ i :=
    pullback.lift_fst _ _ _
  have hsnd : p ≫ pullback.snd g s = pullback.snd f s :=
    pullback.lift_snd _ _ _
  have outer : IsPullback (pullback.fst f s) (p ≫ pullback.snd g s) (i ≫ g) s := by
    rw [hsnd, hi]
    exact IsPullback.of_hasPullback f s
  exact ⟨p, outer.of_bot hfst.symm (IsPullback.of_hasPullback g s), hsnd⟩

private theorem ker_of_closed_pullback
    {X Y Z W : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ Z) (i : X ⟶ Y) (q : Z ⟶ Y)
    [IsClosedImmersion i] (sq : IsPullback a b i q) : b.ker = i.ker.comap q := by
  rw [← sq.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso,
    ← pullbackSymmetry_hom_comp_fst i q, Scheme.Hom.ker_comp_of_isIso]
  exact ker_fst_of_isClosedImmersion i q

private theorem exists_fiberIso_of_equal_ambient_ideals
    {X Y Z S T : Scheme.{u}} (i : X ⟶ Y) (j : Z ⟶ Y)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (a : X ⟶ Z) (ha : a ≫ j = i) (f : X ⟶ S) (g : Y ⟶ S)
    (hi : i ≫ g = f) (s : T ⟶ S)
    (hker : i.ker.comap (pullback.fst g s) = j.ker.comap (pullback.fst g s)) :
    ∃ e : pullback f s ≅ pullback (j ≫ g) s,
      e.hom ≫ pullback.fst (j ≫ g) s = pullback.fst f s ≫ a ∧
      e.hom ≫ pullback.snd (j ≫ g) s = pullback.snd f s := by
  obtain ⟨pX, sqX, hpX⟩ := exists_fiber_comparison i f g hi s
  obtain ⟨pZ, sqZ, hpZ⟩ := exists_fiber_comparison j (j ≫ g) g rfl s
  have ha' : a ≫ (j ≫ g) = f := by rw [← Category.assoc, ha, hi]
  obtain ⟨p, sq, hp⟩ := exists_fiber_comparison a f (j ≫ g) ha' s
  have : IsClosedImmersion pX :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
      (self := IsClosedImmersion.isStableUnderBaseChange) sqX inferInstance
  have : IsClosedImmersion pZ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
      (self := IsClosedImmersion.isStableUnderBaseChange) sqZ inferInstance
  have hpcomp : p ≫ pZ = pX := by
    apply pullback.hom_ext
    · rw [Category.assoc, ← sqZ.w, ← Category.assoc, ← sq.w, Category.assoc, ha, sqX.w]
    · rw [Category.assoc, hpZ, hp, hpX]
  have hker' : pX.ker = pZ.ker :=
    (ker_of_closed_pullback _ _ i _ sqX).trans
      (hker.trans (ker_of_closed_pullback _ _ j _ sqZ).symm)
  have : IsIso p := IsClosedImmersion.isIso_of_ker_eq pX pZ p hpcomp hker'
  exact ⟨asIso p, sq.w.symm, hp⟩

private theorem exists_finiteSubideal_with_same_pullback
    {Y Z : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (I : Y.IdealSheafData) (q : Z ⟶ Y)
    [LocallyOfFinitePresentation (pullback.snd I.subschemeι q)] :
    ∃ J : FiniteSubideal I, J.1.comap q = I.comap q := by
  obtain ⟨J, hJ⟩ := exists_isIso_baseChangeProjection I q
  have : IsIso ((finiteSubschemeBaseChangeCone I q).π.app J) := hJ
  have hker : (pullback.snd J.unop.1.subschemeι q).ker =
      (pullback.snd I.subschemeι q).ker :=
    (Scheme.Hom.ker_comp_of_isIso
      ((finiteSubschemeBaseChangeCone I q).π.app J)
      (pullback.snd J.unop.1.subschemeι q)).symm.trans
        (congrArg Scheme.Hom.ker (finiteSubschemeBaseChangeCone_projection_snd I q J))
  refine ⟨J.unop, ?_⟩
  rw [← pullbackSymmetry_hom_comp_fst J.unop.1.subschemeι q,
    Scheme.Hom.ker_comp_of_isIso, ← pullbackSymmetry_hom_comp_fst I.subschemeι q,
    Scheme.Hom.ker_comp_of_isIso] at hker
  exact hker

/-- An arbitrary proper family has a proper finitely presented closed
thickening whose fibers at two supplied field-valued points are the actual
original fibers. Both isomorphisms commute with the original projections. -/
theorem exists_proper_finitePresentation_model_with_two_fiberIsos
    {R kₛ kₜ : Type u} [CommRing R] [Field kₛ] [Field kₜ] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (s : Spec (CommRingCat.of kₛ) ⟶ Spec (CommRingCat.of R))
    (t : Spec (CommRingCat.of kₜ) ⟶ Spec (CommRingCat.of R)) :
    ∃ (Y : Scheme.{u}) (i : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of R)),
      IsClosedImmersion i ∧ IsProper g ∧ LocallyOfFinitePresentation g ∧ i ≫ g = f ∧
      ∃ (eₛ : pullback f s ≅ pullback g s) (eₜ : pullback f t ≅ pullback g t),
        eₛ.hom ≫ pullback.fst g s = pullback.fst f s ≫ i ∧
        eₛ.hom ≫ pullback.snd g s = pullback.snd f s ∧
        eₜ.hom ≫ pullback.fst g t = pullback.fst f t ≫ i ∧
        eₜ.hom ≫ pullback.snd g t = pullback.snd f t := by
  obtain ⟨Y, i, g, hi, hg, hgfp, hig⟩ := exists_proper_finitePresentation_ambient f
  have : IsClosedImmersion i := hi
  have : IsProper g := hg
  have : LocallyOfFinitePresentation g := hgfp
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated g
  let I := i.ker
  have hfinite {k : Type u} [Field k]
      (v : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
      ∃ J : FiniteSubideal I,
        J.1.comap (pullback.fst g v) = I.comap (pullback.fst g v) := by
    have : CompactSpace (pullback g v : Scheme.{u}) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd g v)
    have : QuasiSeparatedSpace (pullback g v : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.snd g v)
    have : IsLocallyNoetherian (pullback g v) := inferInstance
    have : IsClosedImmersion (pullback.snd I.subschemeι (pullback.fst g v)) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
        (self := IsClosedImmersion.isStableUnderBaseChange)
        (IsPullback.of_hasPullback I.subschemeι (pullback.fst g v)) inferInstance
    exact exists_finiteSubideal_with_same_pullback I (pullback.fst g v)
  obtain ⟨Jₛ, hJₛ⟩ := hfinite s
  obtain ⟨Jₜ, hJₜ⟩ := hfinite t
  obtain ⟨L, hₛL, hₜL⟩ := exists_ge_ge Jₛ Jₜ
  have hLₛ : L.1.comap (pullback.fst g s) = I.comap (pullback.fst g s) := by
    apply le_antisymm (comap_mono _ L.2.1)
    exact hJₛ.ge.trans (comap_mono _ hₛL)
  have hLₜ : L.1.comap (pullback.fst g t) = I.comap (pullback.fst g t) := by
    apply le_antisymm (comap_mono _ L.2.1)
    exact hJₜ.ge.trans (comap_mono _ hₜL)
  let a : X ⟶ L.1.subscheme := i.toImage ≫ inclusion L.2.1
  have ha : a ≫ L.1.subschemeι = i := by
    change (i.toImage ≫ inclusion L.2.1) ≫ L.1.subschemeι = i
    rw [Category.assoc, inclusion_subschemeι, Scheme.Hom.toImage_imageι]
  have : IsClosedImmersion a := inferInstance
  have : LocallyOfFinitePresentation L.1.subschemeι :=
    locallyOfFinitePresentation_subschemeι_of_fg L.1 L.2.2
  have hks : i.ker.comap (pullback.fst g s) =
      L.1.subschemeι.ker.comap (pullback.fst g s) := by
    rw [ker_subschemeι]
    exact hLₛ.symm
  have hkt : i.ker.comap (pullback.fst g t) =
      L.1.subschemeι.ker.comap (pullback.fst g t) := by
    rw [ker_subschemeι]
    exact hLₜ.symm
  obtain ⟨eₛ, heₛfst, heₛsnd⟩ :=
    exists_fiberIso_of_equal_ambient_ideals i L.1.subschemeι a ha f g hig s hks
  obtain ⟨eₜ, heₜfst, heₜsnd⟩ :=
    exists_fiberIso_of_equal_ambient_ideals i L.1.subschemeι a ha f g hig t hkt
  refine ⟨L.1.subscheme, a, L.1.subschemeι ≫ g, inferInstance, inferInstance,
    inferInstance, ?_, eₛ, eₜ, heₛfst, heₛsnd, heₜfst, heₜsnd⟩
  rw [← Category.assoc, ha, hig]

end AlgebraicGeometry
