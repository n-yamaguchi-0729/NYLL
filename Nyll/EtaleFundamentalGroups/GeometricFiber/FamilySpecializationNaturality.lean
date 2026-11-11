/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.FamilySpecializationDiagram
public import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
public import Nyll.EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition
public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.EtaleFundamentalGroups.Pi1.FiniteEtale.GaloisCategory
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkSpecializationLift
public import Nyll.EtaleFundamentalGroups.StrictHenselian.LocalGeometricStalkNaturality
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Whiskering

/-!
# Naturality of the actual family-specialization diagram

A commutative square of families induces maps on the original geometric
fibers and on the families over their actual strict local models.
Compatibility of the chosen generic lifts makes the resulting geometric
square commute. Evaluation gives the analogous closed-fiber square.

The square induces a comparison of the actual finite étale pullback
functors. After taking the fiber at any point of the source generic fiber,
this comparison agrees with the two canonical geometric-fiber comparisons.
The proof reuses the existing pullback pentagon and canonical pointed
composition; no proper closed-fiber equivalence is assumed.

This is the geometric and functorial diagram of Stacks Project,
Lemma 58.16.1, https://stacks.math.columbia.edu/tag/0BUP.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace EtaleFundamentalGroups.StrictHenselian

universe u

attribute [local instance] FiniteEtale.finiteEtaleOverCategoryCoherence
  FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

variable {X Y S T : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ T) (a : Y ⟶ X) (b : T ⟶ S)
  (hab : g ≫ b = a ≫ f)

/-- The actual map on geometric fibers induced by a square of families and
the specified square of field-valued points. -/
def familyGeometricFiberMap
    {Ωt Ωs : Type u} [Field Ωt] [Field Ωs]
    (t : Spec (.of Ωt) ⟶ T) (s : Spec (.of Ωs) ⟶ S)
    (ι : Ωs →+* Ωt) (hs : t ≫ b = Spec.map (CommRingCat.ofHom ι) ≫ s) :
    pullback t g ⟶ pullback s f :=
  pullback.map t g s f (Spec.map (CommRingCat.ofHom ι)) a b hs hab

@[reassoc (attr := simp)]
theorem familyGeometricFiberMap_fst
    {Ωt Ωs : Type u} [Field Ωt] [Field Ωs]
    (t : Spec (.of Ωt) ⟶ T) (s : Spec (.of Ωs) ⟶ S)
    (ι : Ωs →+* Ωt) (hs : t ≫ b = Spec.map (CommRingCat.ofHom ι) ≫ s) :
    familyGeometricFiberMap f g a b hab t s ι hs ≫ pullback.fst s f =
      pullback.fst t g ≫ Spec.map (CommRingCat.ofHom ι) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem familyGeometricFiberMap_snd
    {Ωt Ωs : Type u} [Field Ωt] [Field Ωs]
    (t : Spec (.of Ωt) ⟶ T) (s : Spec (.of Ωs) ⟶ S)
    (ι : Ωs →+* Ωt) (hs : t ≫ b = Spec.map (CommRingCat.ofHom ι) ≫ s) :
    familyGeometricFiberMap f g a b hab t s ι hs ≫ pullback.snd s f =
      pullback.snd t g ≫ a :=
  pullback.lift_snd _ _ _

variable {Ωst Ωss : Type u} [Field Ωst] [Field Ωss]
  (st : Spec (.of Ωst) ⟶ T) (ss : Spec (.of Ωss) ⟶ S)
  (ι : Ωss →+* Ωst) (hs : st ≫ b = Spec.map (CommRingCat.ofHom ι) ≫ ss)

/-- The original family square and its canonical strict-local map induce
the actual map between the two strict-local families. -/
def familyStrictLocalMap :
    pullback (localGeometricStalkToScheme st) g ⟶
      pullback (localGeometricStalkToScheme ss) f :=
  pullback.map (localGeometricStalkToScheme st) g
    (localGeometricStalkToScheme ss) f
    (Spec.map (localGeometricStalkMap b st ss ι hs)) a b
    (localGeometricStalkMap_toScheme b st ss ι hs).symm hab

@[reassoc (attr := simp)]
theorem familyStrictLocalMap_fst :
    familyStrictLocalMap f g a b hab st ss ι hs ≫
        pullback.fst (localGeometricStalkToScheme ss) f =
      pullback.fst (localGeometricStalkToScheme st) g ≫
        Spec.map (localGeometricStalkMap b st ss ι hs) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem familyStrictLocalMap_snd :
    familyStrictLocalMap f g a b hab st ss ι hs ≫
        pullback.snd (localGeometricStalkToScheme ss) f =
      pullback.snd (localGeometricStalkToScheme st) g ≫ a :=
  pullback.lift_snd _ _ _

section Generic

variable {Ωtt Ωts : Type u} [Field Ωtt] [Field Ωts]
  (tt : Spec (.of Ωtt) ⟶ T) (ts : Spec (.of Ωts) ⟶ S)
  (κ : Ωts →+* Ωtt) (ht : tt ≫ b = Spec.map (CommRingCat.ofHom κ) ≫ ts)
  (ψt : geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo st).hom)) →+* Ωtt)
  (ψs : geometricStalk
    (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo ss).hom)) →+* Ωts)
  (hψt : Spec.map (CommRingCat.ofHom ψt) ≫ localGeometricStalkToScheme st = tt)
  (hψs : Spec.map (CommRingCat.ofHom ψs) ≫ localGeometricStalkToScheme ss = ts)
  (hlifts : ψt.comp (localGeometricStalkMap b st ss ι hs).hom = κ.comp ψs)

include hlifts in
/-- Compatible original lifts give the commuting square between the actual
generic-fiber maps and the map of strict-local families. -/
theorem familySpecializationGenericMap_naturality :
    familySpecializationGenericMap g st tt ψt hψt ≫
        familyStrictLocalMap f g a b hab st ss ι hs =
      familyGeometricFiberMap f g a b hab tt ts κ ht ≫
        familySpecializationGenericMap f ss ts ψs hψs := by
  have hlift :
      Spec.map (CommRingCat.ofHom ψt) ≫
          Spec.map (localGeometricStalkMap b st ss ι hs) =
        Spec.map (CommRingCat.ofHom κ) ≫ Spec.map (CommRingCat.ofHom ψs) := by
    calc
      _ = Spec.map (localGeometricStalkMap b st ss ι hs ≫ CommRingCat.ofHom ψt) :=
        (Spec.map_comp _ _).symm
      _ = Spec.map (CommRingCat.ofHom ψs ≫ CommRingCat.ofHom κ) :=
        congrArg Spec.map (congrArg CommRingCat.ofHom hlifts)
      _ = _ := Spec.map_comp _ _
  apply pullback.hom_ext
  · simp only [Category.assoc, familyStrictLocalMap_fst,
      familySpecializationGenericMap_fst_assoc, familySpecializationGenericMap_fst,
      familyGeometricFiberMap_fst_assoc]
    exact congrArg (fun q => pullback.fst tt g ≫ q) hlift
  · simp only [Category.assoc, familyStrictLocalMap_snd,
      familySpecializationGenericMap_snd_assoc, familySpecializationGenericMap_snd,
      familyGeometricFiberMap_snd]

/-- The actual generic square identifies the two finite étale pullback
functors from the target strict-local family to the source generic fiber. -/
def familySpecializationPullbackSquare :
    FiniteEtale.pullback (familyStrictLocalMap f g a b hab st ss ι hs) ⋙
        FiniteEtale.pullback (familySpecializationGenericMap g st tt ψt hψt) ≅
      FiniteEtale.pullback (familySpecializationGenericMap f ss ts ψs hψs) ⋙
        FiniteEtale.pullback (familyGeometricFiberMap f g a b hab tt ts κ ht) :=
  (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      (familySpecializationGenericMap g st tt ψt hψt)
      (familyStrictLocalMap f g a b hab st ss ι hs)).symm ≪≫
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      (familyGeometricFiberMap f g a b hab tt ts κ ht)
      (familySpecializationGenericMap f ss ts ψs hψs)
      (familySpecializationGenericMap g st tt ψt hψt ≫
        familyStrictLocalMap f g a b hab st ss ι hs)
      (familySpecializationGenericMap_naturality
        f g a b hab st ss ι hs tt ts κ ht ψt ψs hψt hψs hlifts)

/-- Taking the fiber at an original generic-fiber point commutes with the
actual family-square comparison. The two paths use exactly the original
canonical pullback-fiber comparisons. -/
theorem familySpecializationPullbackSquare_fiber
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ pullback tt g) :
    let u := familySpecializationGenericMap g st tt ψt hψt
    let v := familyStrictLocalMap f g a b hab st ss ι hs
    let p := familyGeometricFiberMap f g a b hab tt ts κ ht
    let q := familySpecializationGenericMap f ss ts ψs hψs
    let hsq : u ≫ v = p ≫ q := familySpecializationGenericMap_naturality
      f g a b hab st ss ι hs tt ts κ ht ψt ψs hψt hψs hlifts
    Functor.isoWhiskerRight
        (familySpecializationPullbackSquare
          f g a b hab st ss ι hs tt ts κ ht ψt ψs hψt hψs hlifts)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.associator (FiniteEtale.pullback q) (FiniteEtale.pullback p)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback q) (FiniteEtale.pullbackFiberIso p ξ) ≪≫
      FiniteEtale.pullbackFiberIso q (ξ ≫ p) ≪≫
      eqToIso (congrArg FiniteEtale.fiber
        ((Category.assoc ξ p q).trans (congrArg (fun z => ξ ≫ z) hsq.symm))) =
    Functor.associator (FiniteEtale.pullback v) (FiniteEtale.pullback u)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback v) (FiniteEtale.pullbackFiberIso u ξ) ≪≫
      FiniteEtale.pullbackFiberIso v (ξ ≫ u) ≪≫
      eqToIso (congrArg FiniteEtale.fiber (Category.assoc ξ u v)) := by
  intro u v p q
  have hsq : u ≫ v = p ≫ q := familySpecializationGenericMap_naturality
    f g a b hab st ss ι hs tt ts κ ht ψt ψs hψt hψs hlifts
  have hpoint : (ξ ≫ p) ≫ q = ξ ≫ (u ≫ v) :=
    (Category.assoc ξ p q).trans (congrArg (fun z => ξ ≫ z) hsq.symm)
  have h₁ := FiniteEtale.pullbackCompositeFiberIsoOfEq_eq_pullbackFiberIso
    u v (u ≫ v) rfl ξ (Category.assoc ξ u v)
  have h₂ := FiniteEtale.pullbackCompositeFiberIsoOfEq_eq_pullbackFiberIso
    p q (u ≫ v) hsq ξ hpoint
  let pc₁ := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) u v
  let pc₂ := MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) p q (u ≫ v) hsq
  let e₁ := Functor.isoWhiskerRight pc₁ (FiniteEtale.fiber ξ)
  let e₂ := Functor.isoWhiskerRight pc₂ (FiniteEtale.fiber ξ)
  let d₁ :=
    Functor.associator (FiniteEtale.pullback v) (FiniteEtale.pullback u)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback v) (FiniteEtale.pullbackFiberIso u ξ) ≪≫
      FiniteEtale.pullbackFiberIso v (ξ ≫ u) ≪≫
      eqToIso (congrArg FiniteEtale.fiber (Category.assoc ξ u v))
  let d₂ :=
    Functor.associator (FiniteEtale.pullback q) (FiniteEtale.pullback p)
        (FiniteEtale.fiber ξ) ≪≫
      Functor.isoWhiskerLeft (FiniteEtale.pullback q) (FiniteEtale.pullbackFiberIso p ξ) ≪≫
      FiniteEtale.pullbackFiberIso q (ξ ≫ p) ≪≫
      eqToIso (congrArg FiniteEtale.fiber hpoint)
  have heq : e₂ ≪≫ d₂ = e₁ ≪≫ d₁ := h₂.trans h₁.symm
  have hwhisk : Functor.isoWhiskerRight (pc₁.symm ≪≫ pc₂) (FiniteEtale.fiber ξ) =
      e₁.symm ≪≫ e₂ :=
    (Functor.isoWhiskerRight_trans pc₁.symm pc₂ (FiniteEtale.fiber ξ)).trans
      (congrArg (fun e => e ≪≫ e₂)
        (Functor.isoWhiskerRight_symm pc₁ (FiniteEtale.fiber ξ)).symm)
  change Functor.isoWhiskerRight (pc₁.symm ≪≫ pc₂) (FiniteEtale.fiber ξ) ≪≫ d₂ = d₁
  exact (congrArg (fun e => e ≪≫ d₂) hwhisk).trans
    ((Iso.trans_assoc e₁.symm e₂ d₂).trans
      ((congrArg (fun e => e₁.symm ≪≫ e) heq).trans (Iso.symm_self_id_assoc e₁ d₁)))

end Generic

/-- Evaluation makes the actual closed-fiber square commute, with the
specified original special pointing-field homomorphism. -/
theorem familySpecializationClosedMap_naturality :
    familySpecializationClosedMap g st ≫
        familyStrictLocalMap f g a b hab st ss ι hs =
      familyGeometricFiberMap f g a b hab st ss ι hs ≫
        familySpecializationClosedMap f ss := by
  have hlifts :
      (geometricStalkEvaluation
        (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo st).hom))).hom.comp
          (localGeometricStalkMap b st ss ι hs).hom =
        ι.comp (geometricStalkEvaluation
          (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo ss).hom))).hom :=
    congrArg CommRingCat.Hom.hom (localGeometricStalkMap_evaluation b st ss ι hs)
  exact familySpecializationGenericMap_naturality
    f g a b hab st ss ι hs st ss ι hs
    (geometricStalkEvaluation
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo st).hom))).hom
    (geometricStalkEvaluation
      (Spec.map (CommRingCat.ofHom (Scheme.stalkClosedPointTo ss).hom))).hom
    (localGeometricStalkToScheme_evaluation st)
    (localGeometricStalkToScheme_evaluation ss) hlifts

end EtaleFundamentalGroups.StrictHenselian
