/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.FinitePresentationChowOpenCompactification
public import Nyll.SchemeTheory.Descent.ClosedImmersionFinitePresentationBaseChange
public import Nyll.SchemeTheory.Descent.FiniteClosedThickeningInOpen
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper finite-presentation closed thickenings

A proper closed subscheme of a separated finitely presented scheme over an
affine base has a proper finite-presentation closed thickening. The existing
Chow open compactification and the actual finite-subideal inverse limit
supply the thickening. Properness descends through the actual proper
surjective Chow cover.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.IdealSheafData

/-- Inside a separated finitely presented ambient scheme, an actual proper
closed subscheme has a proper finite-presentation closed thickening. -/
theorem exists_proper_finiteSubideal_of_finitePresentation
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {A : Type u} [CommRing A] [Algebra R A]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of A))
    [IsSeparated f] [QuasiCompact f] [LocallyOfFinitePresentation f]
    (I : Y.IdealSheafData) [IsProper (I.subschemeι ≫ f)] :
    ∃ J : FiniteSubideal I, IsProper (J.1.subschemeι ≫ f) := by
  obtain ⟨Y', P, π, u, q, hπ, hπsurj, hu, hq, hqfp, hw⟩ :=
    exists_proper_surjective_open_compactification_of_finitePresentation R f
  have : IsProper π := hπ
  have : Surjective π := hπsurj
  have : IsOpenImmersion u := hu
  have : IsProper q := hq
  have : LocallyOfFinitePresentation q := hqfp
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace Y' := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace Y' := quasiSeparatedSpace_of_quasiSeparated π
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated q
  let h : pullback I.subschemeι π ⟶ P := pullback.snd I.subschemeι π ≫ u
  have hhq : h ≫ q = pullback.fst I.subschemeι π ≫ (I.subschemeι ≫ f) := by
    change (pullback.snd I.subschemeι π ≫ u) ≫ q =
      pullback.fst I.subschemeι π ≫ (I.subschemeι ≫ f)
    rw [Category.assoc, hw, ← Category.assoc, ← pullback.condition, Category.assoc]
  have : IsProper (h ≫ q) := hhq.symm ▸ inferInstance
  have : IsProper h := IsProper.of_comp h q
  have : IsClosedImmersion h :=
    IsClosedImmersion.of_isPreimmersion h h.isClosedMap.isClosed_range
  have hrange : Set.range h.ker.subschemeι ⊆ Set.range u := by
    rw [h.ker.range_subschemeι, Scheme.Hom.support_ker,
      h.isClosedMap.isClosed_range.closure_eq]
    rintro _ ⟨x, rfl⟩
    exact ⟨pullback.snd I.subschemeι π x, rfl⟩
  have hU : h.ker.subschemeι ⁻¹ᵁ u.opensRange = ⊤ := by
    apply top_unique
    intro x _
    exact hrange ⟨x, rfl⟩
  obtain ⟨K, hK⟩ := exists_finiteSubideal_preimage_eq_top h.ker u.opensRange hU
  have hKrange : Set.range K.1.subschemeι ⊆ Set.range u := by
    rintro _ ⟨x, rfl⟩
    exact hK.ge (Set.mem_univ x)
  let k : K.1.subscheme ⟶ Y' := IsOpenImmersion.lift u K.1.subschemeι hKrange
  have hku : k ≫ u = K.1.subschemeι := IsOpenImmersion.lift_fac u _ hKrange
  have : IsClosedImmersion (k ≫ u) := hku.symm ▸ inferInstance
  have : IsClosedImmersion k := IsClosedImmersion.of_comp k u
  have : LocallyOfFinitePresentation K.1.subschemeι :=
    locallyOfFinitePresentation_subschemeι_of_fg K.1 K.2.2
  have : LocallyOfFinitePresentation k :=
    MorphismProperty.of_isPullback
      (IsOpenImmersion.isPullback_lift_id K.1.subschemeι u hKrange).flip
      (inferInstanceAs (LocallyOfFinitePresentation K.1.subschemeι))
  let a : pullback I.subschemeι π ⟶ K.1.subscheme :=
    h.toImage ≫ inclusion K.2.1
  have hak : a ≫ k = pullback.snd I.subschemeι π := by
    apply (cancel_mono u).mp
    rw [Category.assoc, hku]
    change (h.toImage ≫ inclusion K.2.1) ≫ K.1.subschemeι = h
    rw [Category.assoc, inclusion_subschemeι, Scheme.Hom.toImage_imageι]
  let D := finiteSubschemeBaseChangeDiagram I π
  let c := finiteSubschemeBaseChangeCone I π
  let t := finiteSubschemeBaseChangeMap I π
  have hcompat : c.π ≫ t = (Functor.const _).map (a ≫ k) := by
    ext J
    change c.π.app J ≫ pullback.snd J.unop.1.subschemeι π = a ≫ k
    rw [hak]
    exact finiteSubschemeBaseChangeCone_projection_snd I π J
  obtain ⟨J, b, -, hbk⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      D t k c (finiteSubschemeBaseChangeConeIsLimit I π) a hcompat
  change b ≫ k = pullback.snd J.unop.1.subschemeι π at hbk
  have hsnd : IsClosedImmersion (pullback.snd J.unop.1.subschemeι π) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion.{u})
      (self := IsClosedImmersion.isStableUnderBaseChange)
      (IsPullback.of_hasPullback J.unop.1.subschemeι π) inferInstance
  have : IsClosedImmersion (b ≫ k) := hbk.symm ▸ hsnd
  have : IsClosedImmersion b := IsClosedImmersion.of_comp b k
  have hkq : k ≫ (π ≫ f) = K.1.subschemeι ≫ q := by
    rw [← hw, ← Category.assoc, hku]
  have heq : pullback.snd J.unop.1.subschemeι π ≫ (π ≫ f) =
      b ≫ (K.1.subschemeι ≫ q) :=
    (congrArg (fun z : D.obj J ⟶ Y' => z ≫ (π ≫ f)) hbk.symm).trans
      ((Category.assoc b k (π ≫ f)).trans
        (congrArg (fun z : K.1.subscheme ⟶ Spec (CommRingCat.of A) => b ≫ z) hkq))
  have hproper : IsProper (pullback.snd J.unop.1.subschemeι π ≫ (π ≫ f)) :=
    heq.symm ▸ (inferInstanceAs (IsProper (b ≫ (K.1.subschemeι ≫ q))))
  have : IsProper (pullback.fst J.unop.1.subschemeι π ≫
      (J.unop.1.subschemeι ≫ f)) := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
    exact hproper
  have : UniversallyClosed (J.unop.1.subschemeι ≫ f) :=
    UniversallyClosed.of_comp_surjective (pullback.fst J.unop.1.subschemeι π)
      (J.unop.1.subschemeι ≫ f)
  exact ⟨J.unop, {}⟩

end AlgebraicGeometry
