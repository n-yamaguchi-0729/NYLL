/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Descent.FiniteLocallyConstantHenselianHom
public import Nyll.EtaleCohomology.Constructible.FiniteLocallyConstantSet
public import Nyll.EtaleCohomology.Sites.GeometricStalkEvaluationSections
public import Nyll.EtaleCohomology.Sites.ProperClosedFieldSections
public import Nyll.EtaleCohomology.Sites.PushforwardGlobalSections
public import Nyll.EtaleCohomology.Sites.SetSheafFunctors
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperHenselianFullyFaithful
public import Nyll.EtaleFundamentalGroups.FiniteEtale.ProperSeparablyClosedExtension
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
public import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
public import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Sites.Limits

/-!
# Finite locally constant set sections at the actual geometric closed fibre

The actual inverse-image unit, followed by restriction through the existing
identity base-change isomorphism, defines the map on global set sections.
Finite étale full faithfulness makes this map bijective on finite locally
constant coefficients by the existing representable Hom and unit comparison.

For a closed field point of a strictly local proper family, the existing
residue-factorization theorem reduces full faithfulness to the proper
henselian comparison and separably closed field extension. Applied to the
existing geometric-stalk evaluation square, this gives the original map on
sections over the native strict-local base change. The geometric-stalk ring
is the one constructed directly from the original affine coefficient map.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleFundamentalGroups.StrictHenselian

universe u

namespace EtaleCohomology

attribute [local instance] AlgebraicGeometry.FiniteEtale.finiteEtaleOverCategoryCoherence
  AlgebraicGeometry.FiniteEtale.finiteEtaleHasPullbacksAlongCoherence
  AlgebraicGeometry.FiniteEtale.finiteEtaleStableUnderBaseChangeAlongCoherence

/-- The actual inverse-image map on global set sections, using the
existing identity base-change isomorphism and the original adjunction unit. -/
def etaleSetPullbackGlobalSectionsMap
    {X Y : Scheme.{u}} (q : Y ⟶ X) (F : Sheaf X.smallEtaleTopology (Type u)) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      ((etaleSetPullback q).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y))) :=
  ((etaleSetPullbackPushforwardAdjunction q).unit.app F).hom.app
      (op (Scheme.Etale.mk (𝟙 X))) ≫
    ((etaleSetPullback q).obj F).obj.map (baseChangeIdentityIso q).hom.op

/-- The actual finite étale unit comparison identifies the original
global section map whenever finite étale inverse image is fully faithful. -/
theorem etaleSetPullbackGlobalSectionsMap_bijective_of_finiteEtaleFullyFaithful
    {X Y : Scheme.{u}} (q : Y ⟶ X)
    (hFE : (FiniteEtale.pullback q).FullyFaithful)
    {F : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsEtaleFiniteLocallyConstantSet F) :
    Function.Bijective (etaleSetPullbackGlobalSectionsMap q F) := by
  have hu : Function.Bijective
      (((etaleSetPullbackPushforwardAdjunction q).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 X)))) :=
    etaleSetPullback_unit_finiteEtale_bijective_of_finiteEtaleFullyFaithful q hFE hF
      (MorphismProperty.Over.mk (⊤ : MorphismProperty Scheme.{u}) (𝟙 X)
        (show IsFiniteEtale (𝟙 X) from ⟨⟩))
  let E := ((etaleSetPullback q).obj F).obj.mapIso (baseChangeIdentityIso q).op
  exact (ConcreteCategory.bijective_of_isIso E.hom).comp hu

private def closedFieldPullbackFullyFaithful
    (H : Type u) [CommRing H] [HenselianLocalRing H]
    [IsSepClosed (IsLocalRing.ResidueField H)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ε : H →+* Ω) [IsLocalHom ε]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of H)) [IsProper f]
    (q : Z ⟶ X) (p : Z ⟶ Spec (CommRingCat.of Ω))
    (h : IsPullback q p f (Spec.map (CommRingCat.ofHom ε))) :
    (FiniteEtale.pullback q).FullyFaithful := by
  let κ := IsLocalRing.ResidueField H
  let r := Spec.map (CommRingCat.ofHom (IsLocalRing.residue H))
  let i := pullback.fst f r
  let g := pullback.snd f r
  let factorization := exists_residueFieldFactor_of_isPullback H ε f q p h
  let l : Z ⟶ pullback f r := Classical.choose factorization
  have hli : l ≫ i = q := (Classical.choose_spec factorization).1
  have hlpb : IsPullback l p g
      (Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.lift ε))) :=
    (Classical.choose_spec factorization).2
  have : IsProper g := inferInstanceAs (IsProper (pullback.snd f r))
  have hfield : (FiniteEtale.pullback l).IsEquivalence :=
    FiniteEtale.pullback_isEquivalence_of_isProper_of_isSepClosed_field_square
      κ Ω (IsLocalRing.ResidueField.lift ε) g l p hlpb
  let hclosed : (FiniteEtale.pullback i).FullyFaithful :=
    FiniteEtale.pullbackFullyFaithful_closedFiber_of_isProper_of_henselianLocalRing f
  let c : FiniteEtale.pullback q ≅ FiniteEtale.pullback i ⋙ FiniteEtale.pullback l :=
    MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤)
      l i q hli.symm
  exact (hclosed.comp (Functor.FullyFaithful.ofFullyFaithful
    (FiniteEtale.pullback l))).ofIso c.symm

/-- For finite locally constant set coefficients, restriction to any
separably closed field-valued closed point is the actual bijective H⁰ map. -/
theorem etaleSetClosedField_globalSections_bijective_of_isPullback
    (H : Type u) [CommRing H] [HenselianLocalRing H]
    [IsSepClosed (IsLocalRing.ResidueField H)]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ε : H →+* Ω) [IsLocalHom ε]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of H)) [IsProper f]
    (q : Z ⟶ X) (p : Z ⟶ Spec (CommRingCat.of Ω))
    (h : IsPullback q p f (Spec.map (CommRingCat.ofHom ε)))
    {F : Sheaf X.smallEtaleTopology (Type u)}
    (hF : IsEtaleFiniteLocallyConstantSet F) :
    Function.Bijective (etaleSetPullbackGlobalSectionsMap q F) :=
  etaleSetPullbackGlobalSectionsMap_bijective_of_finiteEtaleFullyFaithful q
    (closedFieldPullbackFullyFaithful H ε f q p h) hF

/-- Evaluation of the original affine geometric-stalk ring induces a
bijection on the actual global sections of every finite locally constant
set sheaf on the proper strict-local base change. -/
theorem etaleSetGeometricStalkEvaluationGlobalSections_bijective
    {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
    (φ : R →+* Ω) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    {G : Sheaf
      (pullback (Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))) f).smallEtaleTopology
      (Type u)}
    (hG : IsEtaleFiniteLocallyConstantSet G) :
    Function.Bijective
      (etaleSetPullbackGlobalSectionsMap (geometricStalkEvaluationBaseChangeMap φ f) G) := by
  let H : Type u := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let ε : H →+* Ω := (geometricStalkEvaluation (Spec.map (CommRingCat.ofHom φ))).hom
  have : HenselianLocalRing H :=
    geometricStalk_henselianLocalRing (Spec.map (CommRingCat.ofHom φ))
  have : IsSepClosed (IsLocalRing.ResidueField H) :=
    geometricStalk_residueField_isSepClosed (Spec.map (CommRingCat.ofHom φ))
  have : IsLocalHom ε := geometricStalkEvaluation_isLocalHom (Spec.map (CommRingCat.ofHom φ))
  let h := Spec.map (CommRingCat.ofHom (geometricStalkStructureMap φ))
  let t := Spec.map (CommRingCat.ofHom φ)
  let fH : pullback h f ⟶ Spec (CommRingCat.of H) := pullback.fst h f
  have : IsProper fH := inferInstanceAs (IsProper (pullback.fst h f))
  exact etaleSetClosedField_globalSections_bijective_of_isPullback H ε fH
    (geometricStalkEvaluationBaseChangeMap φ f) (pullback.fst t f)
    (geometricStalkEvaluationBaseChangeMap_isPullback φ f) hG

/-- The original global section map is a natural transformation. Its
naturality is supplied by the existing unit and evaluation functors. -/
def etaleSetPullbackGlobalSectionsNatTrans
    {X Y : Scheme.{u}} (q : Y ⟶ X) :
    (sheafSections X.smallEtaleTopology (Type u)).obj (op (Scheme.Etale.mk (𝟙 X))) ⟶
      etaleSetPullback q ⋙
        (sheafSections Y.smallEtaleTopology (Type u)).obj
          (op (Scheme.Etale.mk (𝟙 Y))) where
  app F := etaleSetPullbackGlobalSectionsMap q F
  naturality F G a := by
    let ΓX := (sheafSections X.smallEtaleTopology (Type u)).obj
      (op (Scheme.Etale.mk (𝟙 X)))
    let ΓY := (sheafSections Y.smallEtaleTopology (Type u)).obj
      (op (Scheme.Etale.mk (𝟙 Y)))
    let ΓB := (sheafSections Y.smallEtaleTopology (Type u)).obj
      (op ((etaleBaseChange q).obj (Scheme.Etale.mk (𝟙 X))))
    let η : ΓX ⟶ etaleSetPullback q ⋙ ΓB :=
      Functor.whiskerRight (etaleSetPullbackPushforwardAdjunction q).unit ΓX
    let ρ : etaleSetPullback q ⋙ ΓB ⟶ etaleSetPullback q ⋙ ΓY :=
      Functor.whiskerLeft (etaleSetPullback q)
        ((sheafSections Y.smallEtaleTopology (Type u)).map
          (baseChangeIdentityIso q).hom.op)
    exact (η ≫ ρ).naturality a

end EtaleCohomology
