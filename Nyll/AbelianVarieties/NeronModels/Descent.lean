/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Topology.Sober
public import Nyll.AbelianVarieties.Geometry.Extensions
public import Nyll.AbelianVarieties.Geometry.Quotients.Neighborhoods
public import Nyll.AbelianVarieties.NeronModels.DenseOpens
public import Nyll.AbelianVarieties.NeronModels.EtaleNeighborhoods
public import Nyll.AbelianVarieties.NeronModels.GenericFibre
public import Nyll.AbelianVarieties.NeronModels.Multiplication
public import Nyll.AbelianVarieties.NeronModels.OpenExtensions
public import Nyll.SchemeTheory.Descent.FlatMorphisms
public import Nyll.SchemeTheory.Morphisms.SeparatedQuasiCompactDescent
public import Nyll.AlgebraicCurves.Geometry.Schemes.Smooth.SmoothDescendsAlongSurjectiveInfFlatInfQuasiCompact
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.AlgebraicCurves.Geometry.Descent.DescentAction
public import Nyll.AlgebraicCurves.Geometry.Descent.DescentActionEffectiveFiniteEtale
public import Nyll.AlgebraicCurves.Geometry.Descent.RepresentableMatching
public import Nyll.SchemeTheory.RingTheory.Henselian.ModuleFinite
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Étale descent of relative group models

Construct a descent action after a finite étale base change, descend the group
law and its open chart, and retain the comparison with the generic fibre.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_effective_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.EffectiveGroupDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace DescentPoints

variable (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']

/-- The affine base-change morphism induced by the algebra map. -/
noncomputable abbrev sMap : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R'))

theorem covering_props [Module.FaithfullyFlat R R'] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (sMap R R') := by
  have hff : (CommRingCat.ofHom (algebraMap R R')).hom.FaithfullyFlat := by
    change (algebraMap R R').FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  obtain ⟨hfl, hsurj⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).2
    hff
  exact ⟨⟨hsurj, hfl⟩, inferInstance⟩

scoped instance surjective_sMap [Module.FaithfullyFlat R R'] : Surjective (sMap R R') :=
  (covering_props R R').1.1

scoped instance flat_sMap [Module.FaithfullyFlat R R'] : Flat (sMap R R') :=
  (covering_props R R').1.2

theorem props_descend [Module.FaithfullyFlat R R']
    {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R))
    {B' : Scheme.{u}} (g' : B' ⟶ Spec (CommRingCat.of R'))
    [Smooth g'] [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R')) :
    Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g := by
  have hQ := covering_props R R'
  have hsnd : pullback.snd g (sMap R R') = e.hom ≫ g' := he.symm
  have hSm : Smooth (pullback.snd g (sMap R R')) := by rw [hsnd]; infer_instance
  have hSep : IsSeparated (pullback.snd g (sMap R R')) := by rw [hsnd]; infer_instance
  have hQc : QuasiCompact (pullback.snd g (sMap R R')) := by rw [hsnd]; infer_instance
  have : MorphismProperty.DescendsAlong (@Smooth : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    Smooth.descendsAlong_surjective_inf_flat_inf_quasiCompact
  have hSmg : Smooth g :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hQ hSm
  have : MorphismProperty.DescendsAlong (@IsSeparated : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := IsSeparated.descendsAlong_fpqc
  have hSepg : IsSeparated g :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @IsSeparated)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hQ hSep
  have : Surjective (sMap R R') := hQ.1.1
  have : QuasiCompact (sMap R R') := hQ.2
  exact ⟨hSmg, hSepg, inferInstance, QuasiCompact.of_pullback_snd g (sMap R R')⟩

variable {R R'}

/-- Base change of a relative point. -/
noncomputable def pointBC {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    SchemeHomOver (pullback.snd t (sMap R R')) (pullback.snd g (sMap R R')) :=
  ⟨pullback.map t (sMap R R') g (sMap R R') x.1 (𝟙 _) (𝟙 _) (by rw [x.2, Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp]),
    by rw [pullback.lift_snd, Category.comp_id]⟩

@[scoped simp]
theorem pointBC_coe_fst {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    (pointBC g x).1 ≫ pullback.fst g (sMap R R') = pullback.fst t (sMap R R') ≫ x.1 :=
  pullback.lift_fst _ _ _

@[scoped simp]
theorem pointBC_coe_snd {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R)) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    (pointBC g x).1 ≫ pullback.snd g (sMap R R') = pullback.snd t (sMap R R') := by
  rw [(pointBC g x).2]

theorem pointBC_natural {B : Scheme.{u}} (g : B ⟶ Spec (CommRingCat.of R)) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    pointBC g (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      GoodReductionJacobian.schemeHomOverComp
        (pullback.map t' (sMap R R') t (sMap R R') ψ (𝟙 _) (𝟙 _) (by rw [hψ, Category.comp_id])
          (by rw [Category.comp_id, Category.id_comp]))
        (by rw [pullback.lift_snd, Category.comp_id]) (pointBC g x) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, pointBC_coe_fst,
      pullback.lift_fst_assoc]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc, pointBC_coe_snd,
      pullback.lift_snd, Category.comp_id]

theorem pointBC_injective [Module.FaithfullyFlat R R'] {B : Scheme.{u}} (g : B ⟶ Spec
    (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Injective (pointBC (R' := R') g (t := t)) := by
  intro x y hxy
  have h := congrArg (fun z => z.1 ≫ pullback.fst g (sMap R R')) hxy
  simp only [pointBC_coe_fst] at h
  have : QuasiCompact (pullback.fst t (sMap R R')) := inferInstance
  have : Epi (pullback.fst t (sMap R R')) := inferInstance
  exact Subtype.ext ((cancel_epi (pullback.fst t (sMap R R'))).1 h)

section Invariant

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  (A : DescentAction (sMap R R') g')

/-- The induced map on the descent relation. -/
noncomputable def yRel {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶ pullback (g' ≫ sMap R R') (sMap
      R R') :=
  pullback.map _ _ _ _ y.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, y.2])
    (by rw [Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
theorem yRel_fst {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    yRel y ≫ pullback.fst _ _ = pullback.fst _ _ ≫ y.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem yRel_snd {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    yRel y ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- A relative point satisfying the descent relation. -/
def Invariant {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') : Prop :=
  DescentAction.flipMap (sMap R R') t ≫ y.1 = yRel y ≫ A.act

variable {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))

/-- Base change of a point through the chosen descent isomorphism. -/
noncomputable def pointBC' {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t
    g) :
    SchemeHomOver (pullback.snd t (sMap R R')) g' :=
  NeronModelInfra.schemeHomOverComp (pointBC g x) ⟨e.hom, he⟩

@[scoped simp]
theorem pointBC'_coe {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    (pointBC' e he x).1 = (pointBC g x).1 ≫ e.hom :=
  rfl

theorem pointBC'_injective [Module.FaithfullyFlat R R'] {T : Scheme.{u}} (t : T ⟶ Spec
    (CommRingCat.of R)) :
    Function.Injective (pointBC' e he (t := t)) := by
  intro x₁ x₂ h
  have h' : (pointBC g x₁).1 ≫ e.hom = (pointBC g x₂).1 ≫ e.hom := congrArg Subtype.val h
  exact pointBC_injective g t (Subtype.ext ((cancel_mono e.hom).1 h'))

theorem invariant_pointBC'
    (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap
      R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t g) :
    Invariant A (pointBC' e he x) := by
  let xSS : pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶
      pullback (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') :=
    pullback.map _ _ _ _ (pointBC g x).1 (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ← Category.assoc, (pointBC g x).2]) (by rw [Category.comp_id,
        Category.id_comp])
  have hxSS₁ : xSS ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (pointBC g x).1 := pullback.lift_fst _ _
    _
  have hxSS₂ : xSS ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans
    (Category.comp_id _)
  have hrel : yRel (pointBC' e he x) =
      xSS ≫ pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap
        R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) := by
    apply pullback.hom_ext
    · rw [yRel_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hxSS₁, Category.assoc]
      rfl
    · rw [yRel_snd, Category.assoc, pullback.lift_snd, Category.comp_id, hxSS₂]
  have hflip : DescentAction.flipMap (sMap R R') t ≫ (pointBC g x).1 =
      xSS ≫ DescentAction.flipMap (sMap R R') g := by
    apply pullback.hom_ext
    · rw [Category.assoc, pointBC_coe_fst, DescentAction.flipMap_fst_assoc, Category.assoc,
        DescentAction.flipMap_fst, ← Category.assoc xSS, hxSS₁, Category.assoc, pointBC_coe_fst]
    · rw [Category.assoc, pointBC_coe_snd, DescentAction.flipMap_snd, Category.assoc,
        DescentAction.flipMap_snd,
        hxSS₂]
  change DescentAction.flipMap (sMap R R') t ≫ (pointBC g x).1 ≫ e.hom = yRel (pointBC' e he x) ≫
    A.act
  rw [← Category.assoc, hflip, hrel, Category.assoc, Category.assoc, hact]
  rfl

theorem exists_pointBC'_eq_of_invariant [Module.FaithfullyFlat R R']
    (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap
      R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (pullback.snd t (sMap R R')) g') (hy : Invariant A y) :
    ∃ x : SchemeHomOver t g, pointBC' e he x = y := by
  have heinv : e.inv ≫ pullback.snd g (sMap R R') = g' := by rw [← he, Iso.inv_hom_id_assoc]
  let N : pullback t (sMap R R') ⟶ pullback g (sMap R R') := y.1 ≫ e.inv
  have hN₂ : N ≫ pullback.snd g (sMap R R') = pullback.snd t (sMap R R') := by
    change (y.1 ≫ e.inv) ≫ _ = _
    rw [Category.assoc, heinv, y.2]
  let NS : pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶
      pullback (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') :=
    pullback.map _ _ _ _ N (𝟙 _) (𝟙 _) (by rw [Category.comp_id, reassoc_of% hN₂])
      (by rw [Category.comp_id, Category.id_comp])
  have hNS₁ : NS ≫ pullback.fst _ _ = pullback.fst _ _ ≫ N := pullback.lift_fst _ _ _
  have hNS₂ : NS ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans
    (Category.comp_id _)
  have hrel : yRel y = NS ≫ pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R')
      (g' ≫ sMap R R') (sMap R R') e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc,
        he])
      (by rw [Category.comp_id, Category.id_comp]) := by
    apply pullback.hom_ext
    · rw [yRel_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, hNS₁, Category.assoc]
      change _ = pullback.fst _ _ ≫ (y.1 ≫ e.inv) ≫ e.hom
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [yRel_snd, Category.assoc, pullback.lift_snd, Category.comp_id, hNS₂]
  let a : pullback t (sMap R R') ⟶ B := N ≫ pullback.fst g (sMap R R')
  have hcond : ∀ {W : Scheme.{u}} (g₁ g₂ : W ⟶ pullback t (sMap R R')),
      g₁ ≫ pullback.fst t (sMap R R') = g₂ ≫ pullback.fst t (sMap R R') → g₁ ≫ a = g₂ ≫ a := by
    intro W g₁ g₂ hg
    have w : g₁ ≫ pullback.snd t (sMap R R') ≫ sMap R R' = (g₂ ≫ pullback.snd t (sMap R R')) ≫ sMap
      R R' := by
      rw [Category.assoc, ← pullback.condition, reassoc_of% hg]
    let ρ : W ⟶ pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') :=
      pullback.lift g₁ (g₂ ≫ pullback.snd t (sMap R R')) w
    have hρ₁ : g₁ = ρ ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    have hρ₂ : g₂ = ρ ≫ DescentAction.flipMap (sMap R R') t := by
      apply pullback.hom_ext
      · rw [Category.assoc, DescentAction.flipMap_fst, pullback.lift_fst_assoc]
        exact hg.symm
      · rw [Category.assoc, DescentAction.flipMap_snd]
        exact (pullback.lift_snd _ _ _).symm
    rw [hρ₁, hρ₂, Category.assoc, Category.assoc]
    congr 1
    change pullback.fst _ _ ≫ (y.1 ≫ e.inv) ≫ pullback.fst g (sMap R R') =
      DescentAction.flipMap (sMap R R') t ≫ (y.1 ≫ e.inv) ≫ pullback.fst g (sMap R R')
    have hy' : DescentAction.flipMap (sMap R R') t ≫ y.1 = yRel y ≫ A.act := hy
    simp only [Category.assoc]
    rw [reassoc_of% hy', hrel, Category.assoc, reassoc_of% hact]
    change _ = NS ≫ DescentAction.flipMap (sMap R R') g ≫ e.hom ≫ e.inv ≫ pullback.fst g (sMap R R')
    rw [Iso.hom_inv_id_assoc, DescentAction.flipMap_fst, reassoc_of% hNS₁]
    simp only [N, Category.assoc]
  let xl : T ⟶ B := EffectiveEpi.desc (pullback.fst t (sMap R R')) a (fun g₁ g₂ hg => hcond g₁ g₂
    hg)
  have hxl : pullback.fst t (sMap R R') ≫ xl = a := EffectiveEpi.fac _ _ _
  have hxg : xl ≫ g = t := by
    apply (cancel_epi (pullback.fst t (sMap R R'))).1
    rw [← Category.assoc, hxl]
    change (N ≫ pullback.fst g (sMap R R')) ≫ g = _
    rw [Category.assoc, pullback.condition, reassoc_of% hN₂, pullback.condition]
  refine ⟨⟨xl, hxg⟩, ?_⟩
  apply Subtype.ext
  change (pointBC g ⟨xl, hxg⟩).1 ≫ e.hom = y.1
  have hlift : (pointBC g ⟨xl, hxg⟩).1 = N := by
    apply pullback.hom_ext
    · rw [pointBC_coe_fst, hxl]
    · rw [pointBC_coe_snd, hN₂]
  rw [hlift]
  change (y.1 ≫ e.inv) ≫ e.hom = y.1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem pointBC'_bijective_invariant [Module.FaithfullyFlat R R']
    (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap
      R R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Function.Bijective (fun x : SchemeHomOver t g =>
      (⟨pointBC' e he x, invariant_pointBC' A e he hact x⟩ :
        {y : SchemeHomOver (pullback.snd t (sMap R R')) g' // Invariant A y})) := by
  refine ⟨fun x₁ x₂ h => pointBC'_injective e he t (congrArg Subtype.val h), fun y => ?_⟩
  obtain ⟨x, hx⟩ := exists_pointBC'_eq_of_invariant A e he hact y.1 y.2
  exact ⟨x, Subtype.ext hx⟩

end Invariant

section GroupLaw

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  (A : DescentAction (sMap R R') g') (LB' : RelativeGroupLaw R' g')

variable {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}

/-- The second structural map of the repeated base change. -/
noncomputable abbrev τ₃ (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶ Spec (CommRingCat.of R') :=
  pullback.snd _ _

/-- The first structural map of the repeated base change. -/
noncomputable abbrev t'₃ (t : T ⟶ Spec (CommRingCat.of R)) :
    pullback (pullback.snd t (sMap R R') ≫ sMap R R') (sMap R R') ⟶ Spec (CommRingCat.of R') :=
  pullback.fst _ _ ≫ pullback.snd t (sMap R R')

theorem hτ₃ (t : T ⟶ Spec (CommRingCat.of R)) : t'₃ t ≫ sMap R R' = τ₃ t ≫ sMap R R' := by
  rw [Category.assoc]; exact pullback.condition

/-- Pull a relative point back along the first projection. -/
noncomputable def yfst (y : SchemeHomOver (pullback.snd t (sMap R R')) g') : SchemeHomOver (t'₃ t)
    g' :=
  GoodReductionJacobian.schemeHomOverComp (pullback.fst _ _) rfl y

/-- Pull a relative point back along the descent interchange map. -/
noncomputable def yflip (y : SchemeHomOver (pullback.snd t (sMap R R')) g') : SchemeHomOver (τ₃ t)
    g' :=
  GoodReductionJacobian.schemeHomOverComp (DescentAction.flipMap (sMap R R') t)
    (DescentAction.flipMap_snd _ _) y

/-- Apply the descent action to a relative point. -/
noncomputable def actP (z : SchemeHomOver (t'₃ t) g') : SchemeHomOver (τ₃ t) g' :=
  NeronModelInfra.schemeHomOverComp
    (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
      (⟨z.1, by rw [reassoc_of% z.2]; exact pullback.condition⟩ :
        SchemeHomOver (τ₃ t ≫ sMap R R') (g' ≫ sMap R R')))
    (⟨A.act, A.act_comp⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g')

theorem actP_coe (z : SchemeHomOver (t'₃ t) g') :
    (actP A z).1 = pullback.lift z.1 (τ₃ t) (by rw [reassoc_of% z.2]; exact pullback.condition) ≫
      A.act :=
  rfl

theorem invariant_iff (y : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    Invariant A y ↔ actP A (yfst y) = yflip y := by
  have hlift : pullback.lift (yfst y).1 (τ₃ t) (by rw [reassoc_of% (yfst y).2]; exact
    pullback.condition) =
      yRel y := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, yRel_fst]; rfl
    · rw [pullback.lift_snd, yRel_snd]
  constructor
  · intro h
    apply Subtype.ext
    rw [actP_coe, hlift]
    exact h.symm
  · intro h
    have h' := congrArg Subtype.val h
    rw [actP_coe, hlift] at h'
    exact h'.symm

/-- Compatibility of the descent action with multiplication. -/
def MulCompatible : Prop :=
  ∀ {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R'))
    (hτ : t' ≫ sMap R R' = τ ≫ sMap R R') (x y : SchemeHomOver t' g'),
    NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
          (⟨(LB'.mul t' x y).1, by rw [reassoc_of% (LB'.mul t' x y).2, hτ]⟩ :
            SchemeHomOver (τ ≫ sMap R R') (g' ≫ sMap R R')))
        (⟨A.act, A.act_comp⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g') =
      LB'.mul τ
        (NeronModelInfra.schemeHomOverComp
          (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
            (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ : SchemeHomOver (τ ≫ sMap R R') (g' ≫ sMap R R')))
          (⟨A.act, A.act_comp⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g'))
        (NeronModelInfra.schemeHomOverComp
          (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
            (⟨y.1, by rw [reassoc_of% y.2, hτ]⟩ : SchemeHomOver (τ ≫ sMap R R') (g' ≫ sMap R R')))
          (⟨A.act, A.act_comp⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g'))

variable {A LB'}

theorem actP_mul (hA₂ : MulCompatible A LB') (x y : SchemeHomOver (t'₃ t) g') :
    actP A (LB'.mul (t'₃ t) x y) = LB'.mul (τ₃ t) (actP A x) (actP A y) :=
  hA₂ (τ₃ t) (t'₃ t) (hτ₃ t) x y

theorem actP_one (hA₂ : MulCompatible A LB') :
    actP A (LB'.one (t'₃ (R := R) (R' := R') t)) = LB'.one (τ₃ t) := by
  let : Group (SchemeHomOver (τ₃ (R := R) (R' := R') t) g') := LB'.pointGroup _
  have h := actP_mul (t := t) hA₂ (LB'.one _) (LB'.one _)
  rw [LB'.one_mul] at h
  have h' : actP A (LB'.one (t'₃ (R := R) (R' := R') t)) * actP A (LB'.one (t'₃ (R := R) (R' := R')
    t)) =
      actP A (LB'.one (t'₃ (R := R) (R' := R') t)) * 1 := by
    rw [mul_one]; exact h.symm
  exact mul_left_cancel h'

theorem actP_inv (hA₂ : MulCompatible A LB') (x : SchemeHomOver (t'₃ t) g') :
    actP A (LB'.inv (t'₃ t) x) = LB'.inv (τ₃ t) (actP A x) := by
  let : Group (SchemeHomOver (τ₃ (R := R) (R' := R') t) g') := LB'.pointGroup _
  have h := actP_mul (t := t) hA₂ (LB'.inv _ x) x
  rw [LB'.inv_mul_cancel, actP_one hA₂] at h
  have h' : actP A (LB'.inv (t'₃ t) x) * actP A x = 1 := h.symm
  exact eq_inv_of_mul_eq_one_left h'

theorem yfst_mul (y₁ y₂ : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    yfst (LB'.mul _ y₁ y₂) = LB'.mul (t'₃ t) (yfst y₁) (yfst y₂) :=
  LB'.mul_natural _ _ _ _ _ _

theorem yflip_mul (y₁ y₂ : SchemeHomOver (pullback.snd t (sMap R R')) g') :
    yflip (LB'.mul _ y₁ y₂) = LB'.mul (τ₃ t) (yflip y₁) (yflip y₂) :=
  LB'.mul_natural _ _ _ _ _ _

theorem invariant_mul (hA₂ : MulCompatible A LB') {y₁ y₂ : SchemeHomOver (pullback.snd t (sMap R
    R')) g'}
    (h₁ : Invariant A y₁) (h₂ : Invariant A y₂) : Invariant A (LB'.mul _ y₁ y₂) := by
  rw [invariant_iff] at h₁ h₂ ⊢
  rw [yfst_mul, actP_mul hA₂, h₁, h₂, yflip_mul]

theorem invariant_one (hA₂ : MulCompatible A LB') :
    Invariant A (LB'.one (pullback.snd t (sMap R R'))) := by
  rw [invariant_iff]
  change actP A (GoodReductionJacobian.schemeHomOverComp _ rfl (LB'.one _)) =
    GoodReductionJacobian.schemeHomOverComp _ _ (LB'.one _)
  rw [LB'.one_natural, LB'.one_natural, actP_one hA₂]

theorem invariant_inv (hA₂ : MulCompatible A LB') {y : SchemeHomOver (pullback.snd t (sMap R R'))
    g'}
    (h : Invariant A y) : Invariant A (LB'.inv _ y) := by
  rw [invariant_iff] at h ⊢
  change actP A (GoodReductionJacobian.schemeHomOverComp _ rfl (LB'.inv _ y)) =
    GoodReductionJacobian.schemeHomOverComp _ _ (LB'.inv _ y)
  rw [LB'.inv_natural, LB'.inv_natural, actP_inv hA₂]
  exact congrArg _ h

end GroupLaw

section Descended

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  {A : DescentAction (sMap R R') g'} {LB' : RelativeGroupLaw R' g'}
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))

variable [Module.FaithfullyFlat R R']
  (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R
    R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
  (hA₂ : MulCompatible A LB')

/-- Relative points identified with invariant points after base change. -/
noncomputable def Φ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t g ≃ {y : SchemeHomOver (pullback.snd t (sMap R R')) g' // Invariant A y} :=
  Equiv.ofBijective _ (pointBC'_bijective_invariant A e he hact t)

@[scoped simp] theorem Φ_apply_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x :
    SchemeHomOver t g) :
    ((Φ (T := T) e he hact t) x).1 = pointBC' e he x := rfl

/-- The group law transported from invariant relative points. -/
noncomputable def descendedLaw : RelativeGroupLaw R g where
  mul t x y := (Φ e he hact t).symm ⟨LB'.mul _ (pointBC' e he x) (pointBC' e he y),
    invariant_mul hA₂ ((Φ e he hact t) x).2 ((Φ e he hact t) y).2⟩
  one t := (Φ e he hact t).symm ⟨LB'.one _, invariant_one hA₂⟩
  inv t x := (Φ e he hact t).symm ⟨LB'.inv _ (pointBC' e he x), invariant_inv hA₂ ((Φ e he hact t)
    x).2⟩
  mul_assoc t x y z := by
    apply (Φ e he hact t).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    have hx : pointBC' e he ((Φ e he hact t).symm ⟨LB'.mul _ (pointBC' e he x) (pointBC' e he y),
        invariant_mul hA₂ ((Φ e he hact t) x).2 ((Φ e he hact t) y).2⟩) = LB'.mul _ (pointBC' e he
          x) (pointBC' e he y) :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    have hy : pointBC' e he ((Φ e he hact t).symm ⟨LB'.mul _ (pointBC' e he y) (pointBC' e he z),
        invariant_mul hA₂ ((Φ e he hact t) y).2 ((Φ e he hact t) z).2⟩) = LB'.mul _ (pointBC' e he
          y) (pointBC' e he z) :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [hx, hy, LB'.mul_assoc]
  one_mul t x := by
    apply (Φ e he hact t).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    have h1 : pointBC' e he ((Φ e he hact t).symm ⟨LB'.one _, invariant_one hA₂⟩) = LB'.one _ :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [h1, LB'.one_mul, Φ_apply_coe]
  mul_one t x := by
    apply (Φ e he hact t).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    have h1 : pointBC' e he ((Φ e he hact t).symm ⟨LB'.one _, invariant_one hA₂⟩) = LB'.one _ :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [h1, LB'.mul_one, Φ_apply_coe]
  inv_mul_cancel t x := by
    apply (Φ e he hact t).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    have h1 : pointBC' e he ((Φ e he hact t).symm ⟨LB'.inv _ (pointBC' e he x), invariant_inv hA₂
      ((Φ e he hact t) x).2⟩) =
        LB'.inv _ (pointBC' e he x) :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [h1, LB'.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply (Φ e he hact t').injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply, Φ_apply_coe]
    have hnat : ∀ z : SchemeHomOver t g, pointBC' e he (GoodReductionJacobian.schemeHomOverComp ψ hψ
      z) =
        GoodReductionJacobian.schemeHomOverComp
          (pullback.map t' (sMap R R') t (sMap R R') ψ (𝟙 _) (𝟙 _) (by rw [hψ, Category.comp_id])
            (by rw [Category.comp_id, Category.id_comp]))
          (by rw [pullback.lift_snd, Category.comp_id]) (pointBC' e he z) := by
      intro z
      apply Subtype.ext
      change (pointBC g (GoodReductionJacobian.schemeHomOverComp ψ hψ z)).1 ≫ e.hom = _
      rw [pointBC_natural]
      rfl
    have hmul : pointBC' e he ((Φ e he hact t).symm ⟨LB'.mul _ (pointBC' e he x) (pointBC' e he y),
        invariant_mul hA₂ ((Φ e he hact t) x).2 ((Φ e he hact t) y).2⟩) = LB'.mul _ (pointBC' e he
          x) (pointBC' e he y) :=
      congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)
    rw [hnat, hmul, LB'.mul_natural, ← hnat, ← hnat]

theorem pointBC'_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g) :
    pointBC' e he ((descendedLaw e he hact hA₂).mul t x y) = LB'.mul _ (pointBC' e he x) (pointBC' e
      he y) :=
  congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)

theorem pointBC'_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    pointBC' e he ((descendedLaw e he hact hA₂).one t) = LB'.one _ :=
  congrArg Subtype.val ((Φ e he hact t).apply_symm_apply _)

end Descended

section Embedding

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  (A : DescentAction (sMap R R') g')
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (X' : X.Opens)
  (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (sMap R R')) g')
  (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R
    R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
  (hA₁ : pullback.map (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R')
    (sMap R R')
        jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') (X'.ι ≫ f)).act ≫ jY'.1)

include hA₁ in
theorem invariant_jY' : Invariant A jY' := hA₁.symm

theorem isPullback_pointBC (jY : SchemeHomOver (X'.ι ≫ f) g) :
    IsPullback (pointBC g jY).1 (pullback.fst (X'.ι ≫ f) (sMap R R')) (pullback.fst g (sMap R R'))
      jY.1 := by
  refine IsPullback.of_right ?_ (pointBC_coe_fst g jY) (IsPullback.of_hasPullback g (sMap R
    R')).flip
  convert (IsPullback.of_hasPullback (X'.ι ≫ f) (sMap R R')).flip using 1
  · exact pointBC_coe_snd g jY
  · exact jY.2

theorem pointBC'_comp (jY : SchemeHomOver (X'.ι ≫ f) g) (hjY : pointBC' e he jY = jY')
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a : SchemeHomOver t (X'.ι ≫ f)) :
    pointBC' e he (NeronModelInfra.schemeHomOverComp a jY) =
      NeronModelInfra.schemeHomOverComp (pointBC (X'.ι ≫ f) a) jY' := by
  rw [← hjY]
  apply Subtype.ext
  change (pointBC g (NeronModelInfra.schemeHomOverComp a jY)).1 ≫ e.hom =
    (pointBC (X'.ι ≫ f) a).1 ≫ (pointBC g jY).1 ≫ e.hom
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [pointBC_coe_fst, Category.assoc, pointBC_coe_fst, ← Category.assoc, pointBC_coe_fst,
      Category.assoc]
    rfl
  · rw [pointBC_coe_snd, Category.assoc, pointBC_coe_snd, pointBC_coe_snd]

variable [Module.FaithfullyFlat R R']

include hact hA₁ in
theorem exists_jY : ∃ jY : SchemeHomOver (X'.ι ≫ f) g, pointBC' e he jY = jY' :=
  exists_pointBC'_eq_of_invariant A e he hact jY' (invariant_jY' A f X' jY' hA₁)

theorem isOpenImmersion_jY [IsOpenImmersion jY'.1] (jY : SchemeHomOver (X'.ι ≫ f) g)
    (hjY : pointBC' e he jY = jY') : IsOpenImmersion jY.1 := by
  have h1 : IsOpenImmersion ((pointBC g jY).1 ≫ e.hom) := by
    have : (pointBC' e he jY).1 = jY'.1 := by rw [hjY]
    rw [pointBC'_coe] at this
    rw [this]; infer_instance
  have h2 : IsOpenImmersion (pointBC g jY).1 :=
    (MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _ e.hom).mp h1
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) (pullback.fst g
    (sMap R R')) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (isPullback_pointBC f X' jY) hQ h2

end Embedding

section Restrict

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  {A : DescentAction (sMap R R') g'} {LB' : RelativeGroupLaw R' g'}
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
  (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
  (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (sMap R R')) g')
  (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
      (w : SchemeHomOver (t' ≫ sMap R R') (U.ι ≫ pullback.fst f f ≫ f))
      (a b c : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)),
    a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
    c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
    NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') c) jY' =
      LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R
        R') a) jY')
        (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') b)
          jY'))

variable [Module.FaithfullyFlat R R']
  (hact : pullback.map (pullback.snd g (sMap R R') ≫ sMap R R') (sMap R R') (g' ≫ sMap R R') (sMap R
    R')
        e.hom (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, he])
        (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
      (DescentAction.canonical (sMap R R') g).act ≫ e.hom)
  (hA₂ : MulCompatible A LB')

omit [Module.FaithfullyFlat R R'] in
theorem pointBC_eq_baseChangePointOfBase {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)}
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (a : SchemeHomOver t y) :
    pointBC y a = RelativeGroupLaw.baseChangePointOfBase (sMap R R')
      (⟨pullback.fst t (sMap R R') ≫ a.1, by rw [Category.assoc, a.2, pullback.condition]⟩ :
        SchemeHomOver (pullback.snd t (sMap R R') ≫ sMap R R') y) := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [pointBC_coe_fst, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  · rw [pointBC_coe_snd, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]

include hres' in
theorem descended_restricts (jY : SchemeHomOver (X'.ι ≫ f) g) (hjY : pointBC' e he jY = jY')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f))
    (ha : a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f) (hb : b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f
      f)
    (hc : c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1) :
    NeronModelInfra.schemeHomOverComp c jY =
      (descendedLaw e he hact hA₂).mul t (NeronModelInfra.schemeHomOverComp a jY)
        (NeronModelInfra.schemeHomOverComp b jY) := by
  apply pointBC'_injective e he t
  rw [pointBC'_mul, pointBC'_comp e he f X' jY' jY hjY, pointBC'_comp e he f X' jY' jY hjY,
    pointBC'_comp e he f X' jY' jY hjY, pointBC_eq_baseChangePointOfBase,
      pointBC_eq_baseChangePointOfBase,
    pointBC_eq_baseChangePointOfBase]
  let π := pullback.fst t (sMap R R')
  refine hres' (pullback.snd t (sMap R R'))
    ⟨π ≫ w.1, by rw [Category.assoc, w.2, pullback.condition]⟩ _ _ _ ?_ ?_ ?_
  · change (π ≫ a.1) ≫ X'.ι = (π ≫ w.1) ≫ U.ι ≫ pullback.fst f f
    rw [Category.assoc, ha, Category.assoc]
  · change (π ≫ b.1) ≫ X'.ι = (π ≫ w.1) ≫ U.ι ≫ pullback.snd f f
    rw [Category.assoc, hb, Category.assoc]
  · change (π ≫ c.1) ≫ X'.ι = (π ≫ w.1) ≫ (pullback f f).homOfLE hUW ≫ m.1
    rw [Category.assoc, hc, Category.assoc]

end Restrict

theorem exists_maximal_specializes {Y : Type u} [TopologicalSpace Y] [QuasiSober Y] [T0Space Y]
    {F : Set Y} (hF : IsClosed F) {b : Y} (hb : b ∈ F) :
    ∃ η ∈ F, η ⤳ b ∧ ∀ y ∈ F, y ⤳ η → y = η := by
  have : QuasiSober F := hF.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨η, hη, hmax⟩ :=
    NeronModelInfra.DenseSliceLocus.exists_maximal_specializes (⟨b, hb⟩ : F)
  refine ⟨η.1, η.2, hη.map continuous_subtype_val, fun y hy hyη => ?_⟩
  exact congrArg Subtype.val (hmax ⟨y, hy⟩ ((subtype_specializes_iff _ _).2 hyη))

section ClosedPoint

variable (R R')
variable [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R']

theorem sMap_base_eq_closedPoint_iff (p : ↥(Spec (CommRingCat.of R'))) :
    (sMap R R').base p = IsLocalRing.closedPoint R ↔ p = IsLocalRing.closedPoint R' := by
  have aux (q : PrimeSpectrum R') :
      PrimeSpectrum.comap (algebraMap R R') q = IsLocalRing.closedPoint R ↔
        q = IsLocalRing.closedPoint R' := by
    constructor
    · intro h
      have h1 : (q.asIdeal.under R).IsMaximal := by
        change (PrimeSpectrum.comap (algebraMap R R') q).asIdeal.IsMaximal
        rw [h]
        exact IsLocalRing.maximalIdeal.isMaximal R
      have h2 : q.asIdeal.IsMaximal :=
        Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) q.asIdeal h1
      apply PrimeSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal h2
    · intro h
      subst q
      apply PrimeSpectrum.ext
      have : (IsLocalRing.closedPoint R').asIdeal.IsMaximal :=
        IsLocalRing.maximalIdeal.isMaximal R'
      exact IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R)
          (IsLocalRing.closedPoint R').asIdeal)
  exact aux p

end ClosedPoint

section Density

variable {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (e : pullback g (sMap R R') ≅ B') (he : e.hom ≫ g' = pullback.snd g (sMap R R'))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (X' : X.Opens)
  (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (sMap R R')) g')
  (jY : SchemeHomOver (X'.ι ≫ f) g) (hjY : pointBC' e he jY = jY')

include hjY in
theorem fst_mem_range_of_mem_range {b₁ : ↥(pullback g (sMap R R'))}
    (h : e.hom.base b₁ ∈ Set.range jY'.1.base) : (pullback.fst g (sMap R R')).base b₁ ∈ Set.range
      jY.1.base := by
  obtain ⟨y, hy⟩ := h
  have hval : jY'.1 = (pointBC g jY).1 ≫ e.hom := by rw [← hjY]; rfl
  rw [hval, Scheme.Hom.comp_apply] at hy
  have hinj : Function.Injective e.hom.base := e.hom.homeomorph.injective
  have hy' : (pointBC g jY).1.base y = b₁ := hinj hy
  refine ⟨(pullback.fst (X'.ι ≫ f) (sMap R R')).base y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← pointBC_coe_fst g jY, Scheme.Hom.comp_apply, hy']

variable [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R'] [Module.FaithfullyFlat R R']

omit [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R'] [Module.FaithfullyFlat R R'] in
include he in
theorem g_fst_eq (b₁ : ↥(pullback g (sMap R R'))) :
    g.base ((pullback.fst g (sMap R R')).base b₁) = (sMap R R').base (g'.base (e.hom.base b₁)) := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply
    e.hom g', he]

include he hjY in
theorem mem_range_jY_of_ne (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range
    jY'.1.base)
    (b : B) (hb : g.base b ≠ IsLocalRing.closedPoint R) : b ∈ Set.range jY.1.base := by
  obtain ⟨b₁, rfl⟩ := (inferInstance : Surjective (pullback.fst g (sMap R R'))).surj b
  apply fst_mem_range_of_mem_range e he f X' jY' jY hjY
  apply hjY'₁
  intro hc
  apply hb
  rw [g_fst_eq e he, hc]
  exact (sMap_base_eq_closedPoint_iff R R' _).2 rfl

include he hjY in
theorem mem_range_jY_of_maximal
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (b : B) (hb : g.base b = IsLocalRing.closedPoint R)
    (hmax : ∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) : b ∈ Set.range jY.1.base
      := by
  obtain ⟨b₁, rfl⟩ := (inferInstance : Surjective (pullback.fst g (sMap R R'))).surj b
  let F : Set ↥B' := g'.base ⁻¹' {IsLocalRing.closedPoint R'}
  have hF : IsClosed F := (IsLocalRing.isClosed_singleton_closedPoint R').preimage
    g'.base.hom.continuous
  have hb' : e.hom.base b₁ ∈ F := by
    change g'.base (e.hom.base b₁) = IsLocalRing.closedPoint R'
    rw [← sMap_base_eq_closedPoint_iff R R', ← g_fst_eq e he]
    exact hb
  obtain ⟨η, hηF, hηb, hηmax⟩ := exists_maximal_specializes hF hb'
  have hη : η ∈ Set.range jY'.1.base := hjY'₂ η hηF (fun y hy hyF => hηmax y hyF hy)
  let η₁ : ↥(pullback g (sMap R R')) := e.inv.base η
  have hη₁ : e.hom.base η₁ = η := by
    change (e.inv ≫ e.hom).base η = η
    rw [Iso.inv_hom_id]; rfl
  have hspec : (pullback.fst g (sMap R R')).base η₁ ⤳ (pullback.fst g (sMap R R')).base b₁ := by
    have h1 : η₁ ⤳ e.inv.base (e.hom.base b₁) := hηb.map e.inv.base.hom.continuous
    have h2 : e.inv.base (e.hom.base b₁) = b₁ := by
      change (e.hom ≫ e.inv).base b₁ = b₁
      rw [Iso.hom_inv_id]; rfl
    rw [h2] at h1
    exact h1.map (pullback.fst g (sMap R R')).base.hom.continuous
  have hclosed : g.base ((pullback.fst g (sMap R R')).base η₁) = IsLocalRing.closedPoint R := by
    rw [g_fst_eq e he, hη₁, sMap_base_eq_closedPoint_iff R R']
    exact hηF
  have heq : (pullback.fst g (sMap R R')).base η₁ = (pullback.fst g (sMap R R')).base b₁ := hmax _
    hspec hclosed
  rw [← heq]
  apply fst_mem_range_of_mem_range e he f X' jY' jY hjY
  rw [hη₁]
  exact hη

end Density

section GenericFibre

variable {S₀ : Scheme.{u}} (ι : S₀ ⟶ Spec (CommRingCat.of R))
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (X' : X.Opens)

theorem isPullback_map (jY : SchemeHomOver (X'.ι ≫ f) g) :
    IsPullback
      (pullback.map (X'.ι ≫ f) ι g ι jY.1 (𝟙 _) (𝟙 _) (by rw [jY.2, Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp]))
      (pullback.fst (X'.ι ≫ f) ι) (pullback.fst g ι) jY.1 := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback g ι).flip
  convert (IsPullback.of_hasPullback (X'.ι ≫ f) ι).flip using 1
  · exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  · exact jY.2

theorem isIso_map_of_forall_mem_range (jY : SchemeHomOver (X'.ι ≫ f) g) [IsOpenImmersion jY.1]
    (hdense : ∀ b : B, g.base b ∈ Set.range ι.base → b ∈ Set.range jY.1.base) :
    IsIso (pullback.map (X'.ι ≫ f) ι g ι jY.1 (𝟙 _) (𝟙 _) (by rw [jY.2, Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp])) := by
  have hP := isPullback_map ι f X' jY
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip inferInstance, ⟨fun q =>
    ?_⟩⟩
  have hq : (pullback.fst g ι).base q ∈ Set.range jY.1.base := by
    apply hdense
    refine ⟨(pullback.snd g ι).base q, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  have hrange : Set.range (hP.isoPullback.hom ≫ pullback.fst (pullback.fst g ι) jY.1).base =
      Set.range (pullback.map (X'.ι ≫ f) ι g ι jY.1 (𝟙 _) (𝟙 _) (by rw [jY.2, Category.comp_id])
        (by rw [Category.comp_id, Category.id_comp])).base := by
    rw [hP.isoPullback_hom_fst]
  have hq' : q ∈ Set.range (pullback.fst (pullback.fst g ι) jY.1).base := by
    rw [Scheme.Pullback.range_fst]
    exact hq
  obtain ⟨z, hz⟩ := hq'
  refine ⟨hP.isoPullback.inv.base z, ?_⟩
  have : (hP.isoPullback.inv ≫ pullback.map (X'.ι ≫ f) ι g ι jY.1 (𝟙 _) (𝟙 _) (by rw [jY.2,
    Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp])) = pullback.fst (pullback.fst g ι) jY.1 := by
    rw [Iso.inv_comp_eq, hP.isoPullback_hom_fst]
  rw [← Scheme.Hom.comp_apply, this]
  exact hz

end GenericFibre

section GenericIso

variable [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem specGenericFibreInclusion_ne_closedPoint (p : ↥(Spec (CommRingCat.of K))) :
    (specGenericFibreInclusion R K).base p ≠ IsLocalRing.closedPoint R := by
  intro h
  have h1 : ((specGenericFibreInclusion R K).base p).asIdeal = ⊥ := by
    change (p.asIdeal.comap (algebraMap R K)) = ⊥
    have hp : p.asIdeal = ⊥ := by
      have : p.asIdeal.IsPrime := p.isPrime
      exact (Ideal.eq_bot_of_prime p.asIdeal)
    rw [hp]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
  rw [h] at h1
  exact IsDiscreteValuationRing.not_a_field R h1

variable {K}
variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
  (X' : X.Opens) (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
  (jY : SchemeHomOver (X'.ι ≫ f) g)
  (hjY₁ : ∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base)

include hjY₁ in
theorem isIso_genericFibreRestrict_jY [IsOpenImmersion jY.1] : IsIso (genericFibreRestrict R K g
    (X'.ι ≫ f) jY).1 := by
  rw [genericFibreRestrict_coe_eq_pullbackMap g (X'.ι ≫ f) jY (by rw [jY.2, Category.comp_id])
    (by rw [Category.comp_id, Category.id_comp])]
  apply isIso_map_of_forall_mem_range
  rintro b ⟨p, hp⟩
  apply hjY₁
  rw [← hp]
  exact specGenericFibreInclusion_ne_closedPoint K p

include hX'₁ in
theorem isIso_genericFibreRestrict_incl :
    IsIso (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩).1 := by
  rw [genericFibreRestrict_coe_eq_pullbackMap f (X'.ι ≫ f) ⟨X'.ι, rfl⟩ (Category.comp_id _)
    (by rw [Category.comp_id, Category.id_comp])]
  have : IsOpenImmersion (⟨X'.ι, rfl⟩ : SchemeHomOver (X'.ι ≫ f) f).1 := by
    change IsOpenImmersion X'.ι; infer_instance
  apply isIso_map_of_forall_mem_range
  rintro b ⟨p, hp⟩
  have hb : b ∈ X' := hX'₁ b (by rw [← hp]; exact specGenericFibreInclusion_ne_closedPoint K p)
  change b ∈ Set.range X'.ι.base
  rw [Scheme.Opens.range_ι]
  exact hb

/-- The generic-fibre comparison transported through the descended open chart. -/
noncomputable def ePrime (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1) :
    SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK :=
  ⟨inv (genericFibreRestrict R K g (X'.ι ≫ f) jY).1 ≫ (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι,
    rfl⟩).1 ≫ e.1,
    by
      rw [Category.assoc, Category.assoc, e.2, (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι,
        rfl⟩).2,
        IsIso.inv_comp_eq, (genericFibreRestrict R K g (X'.ι ≫ f) jY).2]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem ePrime_coe (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1) :
    (ePrime f e X' jY hiso).1 = inv (genericFibreRestrict R K g (X'.ι ≫ f) jY).1 ≫
      (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩).1 ≫ e.1 :=
  rfl

include hX'₁ in
theorem isIso_ePrime [IsIso e.1] (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1) :
    IsIso (ePrime f e X' jY hiso).1 := by
  have : IsIso (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩).1 :=
    isIso_genericFibreRestrict_incl (K := K) f X' hX'₁
  rw [ePrime_coe]
  infer_instance

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem ePrime_compat (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1) :
    NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g (X'.ι ≫ f) jY) (ePrime f e X' jY
      hiso) =
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e := by
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, ePrime_coe,
    IsIso.hom_inv_id_assoc]

end GenericIso

section Hhom

variable [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem bcOfBase_comp {A₁ B₁ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {g₁ : B₁ ⟶ Spec
    (CommRingCat.of R)}
    (φ : SchemeHomOver g₁ f₁) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)}
    (y : SchemeHomOver (t ≫ specGenericFibreInclusion R K) g₁) :
    RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K)
      (NeronModelInfra.schemeHomOverComp y φ) =
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase
        (specGenericFibreInclusion R K) y)
        (genericFibreRestrict R K f₁ g₁ φ) := by
  rw [← RelativeGroupLaw.baseChangePointOfBase_toBase (specGenericFibreInclusion R K)
      (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase
        (specGenericFibreInclusion R K) y)
        (genericFibreRestrict R K f₁ g₁ φ)),
    RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict,
      RelativeGroupLaw.baseChangePointToBase_ofBase]

variable {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
  (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
  (hmK : (NeronModelInfra.schemeHomOverComp
      (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
    pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
        (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
      (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (pullback.fst f f ≫ f)
            ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
  (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
  (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
  (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f
    f).base q ∈ X' ∧
    m.1.base ⟨q, hUW hq⟩ ∈ X')
  {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
  (jY : SchemeHomOver (X'.ι ≫ f) g)
  (hres : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
    a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
    c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
    NeronModelInfra.schemeHomOverComp c jY =
      LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b jY))
  (hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1)

include hmK hU₁ hU₂ hres in
theorem ePrime_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))) :
    NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) (ePrime f e X' jY hiso) =
      LXK.mul t (NeronModelInfra.schemeHomOverComp x (ePrime f e X' jY hiso))
        (NeronModelInfra.schemeHomOverComp y (ePrime f e X' jY hiso)) := by
  set jYK := genericFibreRestrict R K g (X'.ι ≫ f) jY with hjYK
  set iXK := genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩ with hiXK
  set e' := ePrime f e X' jY hiso with he'
  have : IsIso jYK.1 := hiso
  have hcompat : NeronModelInfra.schemeHomOverComp jYK e' = NeronModelInfra.schemeHomOverComp iXK e
    :=
    ePrime_compat f e X' jY hiso
  let invJ : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) (pullback.snd (X'.ι ≫ f)
    (specGenericFibreInclusion R K)) :=
    ⟨inv jYK.1, by rw [IsIso.inv_comp_eq, jYK.2]⟩
  have hinvJ : ∀ z : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K)),
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z invJ) jYK = z := by
    intro z
    apply Subtype.ext
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, invJ]
  let αK := NeronModelInfra.schemeHomOverComp x invJ
  let βK := NeronModelInfra.schemeHomOverComp y invJ
  let α : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (X'.ι ≫ f) :=
    RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) αK
  let β : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (X'.ι ≫ f) :=
    RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) βK
  have hE1x : RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) x =
    NeronModelInfra.schemeHomOverComp α jY := by
    rw [← hinvJ x]
    exact RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K jY αK
  have hE1y : RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) y =
    NeronModelInfra.schemeHomOverComp β jY := by
    rw [← hinvJ y]
    exact RelativeGroupLaw.baseChangePointToBase_comp_genericFibreRestrict K jY βK
  have hαf : (α.1 ≫ X'.ι) ≫ f = t ≫ (specGenericFibreInclusion R K) := by rw [Category.assoc]; exact
    α.2
  have hβf : (β.1 ≫ X'.ι) ≫ f = t ≫ (specGenericFibreInclusion R K) := by rw [Category.assoc]; exact
    β.2
  let pair : T ⟶ pullback f f := pullback.lift (α.1 ≫ X'.ι) (β.1 ≫ X'.ι) (hαf.trans hβf.symm)
  have hpair : pair ≫ pullback.fst f f ≫ f = t ≫ (specGenericFibreInclusion R K) := by rw
    [pullback.lift_fst_assoc, hαf]
  have hrange : Set.range pair.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hU₁
    intro hc
    have h1 : (pullback.fst f f ≫ f).base (pair.base z) = (specGenericFibreInclusion R K).base
      (t.base z) := by
      rw [← Scheme.Hom.comp_apply, hpair, Scheme.Hom.comp_apply]
    rw [h1] at hc
    exact specGenericFibreInclusion_ne_closedPoint K _ hc
  let wl : T ⟶ U := IsOpenImmersion.lift U.ι pair hrange
  have hwl : wl ≫ U.ι = pair := IsOpenImmersion.lift_fac _ _ _
  let w : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (U.ι ≫ pullback.fst f f ≫ f) := ⟨wl,
    by rw [reassoc_of% hwl, hpair]⟩
  have ha : α.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f := by
    change _ = wl ≫ _
    rw [reassoc_of% hwl, pullback.lift_fst]
  have hb : β.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f := by
    change _ = wl ≫ _
    rw [reassoc_of% hwl, pullback.lift_snd]
  let cm : T ⟶ X := w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1
  have hrangec : Set.range cm.base ⊆ Set.range X'.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : (U.ι.base (wl.base z)) ∈ U := (show U from wl z).property
    have h3 := (hU₂ _ hq).2.2
    have hpt : ((pullback f f).homOfLE hUW).base (wl.base z) =
        ⟨U.ι.base (wl.base z), hUW hq⟩ :=
      Scheme.homOfLE_apply' hUW (show U from wl z).val (show U from wl z).property
    change m.1.base (((pullback f f).homOfLE hUW).base (wl.base z)) ∈ X'
    rw [hpt]
    exact h3
  let cl : T ⟶ X' := IsOpenImmersion.lift X'.ι cm hrangec
  have hcl : cl ≫ X'.ι = cm := IsOpenImmersion.lift_fac _ _ _
  have hwW : (w.1 ≫ (pullback f f).homOfLE hUW) ≫ W.ι ≫ pullback.fst f f ≫ f = t ≫
    (specGenericFibreInclusion R K) := by
    rw [Category.assoc, Scheme.homOfLE_ι_assoc]
    exact w.2
  let c : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (X'.ι ≫ f) := ⟨cl, by
    rw [reassoc_of% hcl]
    change (w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1) ≫ f = t ≫ (specGenericFibreInclusion R K)
    rw [Category.assoc, Category.assoc, m.2, ← Category.assoc]
    exact hwW⟩
  have hc : c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 := hcl
  have hE3 : NeronModelInfra.schemeHomOverComp c jY =
      LB.mul (t ≫ (specGenericFibreInclusion R K)) (NeronModelInfra.schemeHomOverComp α jY)
        (NeronModelInfra.schemeHomOverComp β jY) :=
    hres (t ≫ (specGenericFibreInclusion R K)) w α β c ha hb hc
  have hE4 : (LB.genericFibre K).mul t x y =
      RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K)
        (NeronModelInfra.schemeHomOverComp c jY) := by
    rw [RelativeGroupLaw.baseChange_mul, hE1x, hE1y, ← hE3]
  let wW : SchemeHomOver (t ≫ (specGenericFibreInclusion R K)) (W.ι ≫ pullback.fst f f ≫ f) := ⟨w.1
    ≫ (pullback f f).homOfLE hUW, hwW⟩
  have hcm : NeronModelInfra.schemeHomOverComp c (⟨X'.ι, rfl⟩ : SchemeHomOver (X'.ι ≫ f) f) =
      NeronModelInfra.schemeHomOverComp wW m := by
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, hc,
      Category.assoc]
  have hL : NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase
        (specGenericFibreInclusion R K) wW)
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f)
          m) e) := by
    rw [hE4, bcOfBase_comp, NeronModelInfra.schemeHomOverComp_assoc, ← hjYK, hcompat, hiXK,
      ← NeronModelInfra.schemeHomOverComp_assoc, ← bcOfBase_comp, hcm, bcOfBase_comp,
      NeronModelInfra.schemeHomOverComp_assoc]
  set wK := RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion R K) wW with hwK
  let s₀ := pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
  let prW : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) (pullback.fst f f ≫ f) := ⟨W.ι, rfl⟩
  let pK : SchemeHomOver t s₀ := NeronModelInfra.schemeHomOverComp wK (genericFibreRestrict R K _ _
    prW)
  have hprW : (genericFibreRestrict R K (pullback.fst f f ≫ f) (W.ι ≫ pullback.fst f f ≫ f) prW).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
        (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) :=
    genericFibreRestrict_coe_eq_pullbackMap _ _ prW _ _
  let P := NeronModelInfra.schemeHomOverComp
    (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e
  let Q := NeronModelInfra.schemeHomOverComp
    (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.snd f f, pullback.condition.symm⟩)
      e
  have hL2 : NeronModelInfra.schemeHomOverComp wK
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m)
        e) =
      LXK.mul t (GoodReductionJacobian.schemeHomOverComp pK.1 pK.2 P)
        (GoodReductionJacobian.schemeHomOverComp pK.1 pK.2 Q) := by
    rw [← LXK.mul_natural]
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe, hmK, GoodReductionJacobian.schemeHomOverComp_coe,
      NeronModelInfra.schemeHomOverComp_coe, hprW, Category.assoc]
  rw [hL, hL2]
  have hPQ : ∀ (pr : SchemeHomOver (pullback.fst f f ≫ f) f) (γ : SchemeHomOver (t ≫
    (specGenericFibreInclusion R K)) (X'.ι ≫ f))
      (γK : SchemeHomOver t (pullback.snd (X'.ι ≫ f) (specGenericFibreInclusion R K)))
      (hγK : RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion R K) γK = γ)
      (hγ : γ.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pr.1),
      GoodReductionJacobian.schemeHomOverComp pK.1 pK.2
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) pr) e)
          =
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp γK jYK) e' := by
    intro pr γ γK hγK hγ
    have h1 : GoodReductionJacobian.schemeHomOverComp pK.1 pK.2
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (pullback.fst f f ≫ f) pr) e)
          =
        NeronModelInfra.schemeHomOverComp
          (NeronModelInfra.schemeHomOverComp pK (genericFibreRestrict R K f (pullback.fst f f ≫ f)
            pr)) e := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
        Category.assoc]
    have h2 : NeronModelInfra.schemeHomOverComp pK (genericFibreRestrict R K f (pullback.fst f f ≫
      f) pr) =
        NeronModelInfra.schemeHomOverComp γK iXK := by
      change NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp wK
        (genericFibreRestrict R K _ _ prW)) _ = _
      rw [hwK, ← bcOfBase_comp, ← bcOfBase_comp, hiXK, ←
        RelativeGroupLaw.baseChangePointOfBase_toBase (specGenericFibreInclusion R K) γK,
        hγK, ← bcOfBase_comp]
      congr 1
      apply Subtype.ext
      simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
      change (w.1 ≫ (pullback f f).homOfLE hUW) ≫ W.ι ≫ pr.1 = γ.1 ≫ X'.ι
      rw [hγ, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [h1, h2, NeronModelInfra.schemeHomOverComp_assoc, ← hcompat, ←
      NeronModelInfra.schemeHomOverComp_assoc]
  rw [hPQ ⟨pullback.fst f f, rfl⟩ α αK rfl ha, hPQ ⟨pullback.snd f f, pullback.condition.symm⟩ β βK
    rfl hb,
    hinvJ x, hinvJ y]

end Hhom

end DescentPoints

end AbelianVarieties.NOSProofs.EffectiveGroupDescent

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian
open AbelianVarieties.NOSProofs.EffectiveGroupDescent

universe u

theorem exists_groupLaw_of_effective_descent
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f
      f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {B' : Scheme.{u}} (g' : B' ⟶ Spec (CommRingCat.of R')) (LB' : RelativeGroupLaw R' g')
    [Smooth g'] [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      g') [IsOpenImmersion jY'.1]
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
          pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map
        (CommRingCat.ofHom (algebraMap R R'))) c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase
          (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) b) jY'))
    (A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g')
    (hA₁ :
      pullback.map (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))
          jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (X'.ι ≫ f)).act ≫
          jY'.1)
    (hA₂ : ∀ {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R'))
          (hτ : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = τ ≫ Spec.map
            (CommRingCat.ofHom (algebraMap R R')))
          (x y : SchemeHomOver t' g'),
        NeronModelInfra.schemeHomOverComp
            (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
              (⟨(LB'.mul t' x y).1, by rw [reassoc_of% (LB'.mul t' x y).2, hτ]⟩ :
                SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (⟨A.act, A.act_comp⟩ : SchemeHomOver
              (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') =
          LB'.mul τ
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R
                R')))
                (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R
                R')))
                (⟨y.1, by rw [reassoc_of% y.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g')))
    (hA : A.Effective) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (jY : SchemeHomOver (X'.ι ≫ f) g) (e' : SchemeHomOver (pullback.snd g
        (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsOpenImmersion jY.1 ∧
      (∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base) ∧
      (∀ b : B, g.base b = IsLocalRing.closedPoint R →
        (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range jY.1.base) ∧
      IsIso e'.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y
            e')) ∧
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g (X'.ι ≫ f) jY) e' =
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        NeronModelInfra.schemeHomOverComp c jY =
          LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b
            jY)) := by
  obtain ⟨B, g, eB, heB, hact⟩ := hA
  have hA₂' : DescentPoints.MulCompatible A LB' := fun τ t' hτ x y => hA₂ τ t' hτ x y
  let LB : RelativeGroupLaw R g := DescentPoints.descendedLaw eB heB hact hA₂'
  obtain ⟨jY, hjY⟩ := DescentPoints.exists_jY A eB heB f X' jY' hact hA₁
  have hprops := DescentPoints.props_descend R R' g g' eB heB
  have hopen : IsOpenImmersion jY.1 := DescentPoints.isOpenImmersion_jY eB heB f X' jY' jY hjY
  have hres : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp c jY =
        LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b jY)
          :=
    fun t w a b c ha hb hc =>
      DescentPoints.descended_restricts eB heB f W m X' U hUW jY' hres' hact hA₂' jY hjY t w a b c
        ha hb hc
  have hd₁ : ∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base :=
    DescentPoints.mem_range_jY_of_ne eB heB f X' jY' jY hjY hjY'₁
  have hd₂ : ∀ b : B, g.base b = IsLocalRing.closedPoint R →
      (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range jY.1.base :=
    DescentPoints.mem_range_jY_of_maximal eB heB f X' jY' jY hjY hjY'₂
  have hiso : IsIso (genericFibreRestrict R K g (X'.ι ≫ f) jY).1 :=
    DescentPoints.isIso_genericFibreRestrict_jY f X' jY hd₁
  refine ⟨B, g, LB, jY, DescentPoints.ePrime f e X' jY hiso, hprops.1, hprops.2.1, hprops.2.2.1,
    hprops.2.2.2,
    hopen, hd₁, hd₂, DescentPoints.isIso_ePrime f e X' hX'₁ jY hiso, ?_, DescentPoints.ePrime_compat
      f e X' jY hiso,
    hres⟩
  intro T t x y
  exact DescentPoints.ePrime_hom LXK f e W m hmK X' U hUW hU₁ hU₂ LB jY hres hiso t x y

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_descentAction_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.EtaleDescentAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Action

open AbelianVarieties.NOSProofs.EffectiveGroupDescent.DescentPoints
  (sMap sMap_base_eq_closedPoint_iff specGenericFibreInclusion_ne_closedPoint)
open scoped AbelianVarieties.NOSProofs.EffectiveGroupDescent.DescentPoints

section WeilExtension

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]

theorem pullbackMap_eq_genericFibreRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R)) (φ : Y ⟶ X) (hφ : φ ≫ f = g)
    (h₁ : g ≫ 𝟙 (Spec (CommRingCat.of R)) = φ ≫ f)
    (h₂ : specGenericFibreInclusion R K ≫ 𝟙 (Spec (CommRingCat.of R)) =
      𝟙 (Spec (CommRingCat.of K)) ≫ specGenericFibreInclusion R K) :
    pullback.map g (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) φ
        (𝟙 (Spec (CommRingCat.of K))) (𝟙 (Spec (CommRingCat.of R))) h₁ h₂ =
      (genericFibreRestrict R K f g ⟨φ, hφ⟩).1 :=
  (genericFibreRestrict_coe_eq_pullbackMap f g ⟨φ, hφ⟩ h₁ h₂).symm

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem base_ne_closedPoint {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of K)) (p : S) :
    (s ≫ specGenericFibreInclusion R K).base p ≠ IsLocalRing.closedPoint R := by
  exact specGenericFibreInclusion_ne_closedPoint K (s p)

variable {B₁ B₂ Y : Scheme.{u}} {g₁ : B₁ ⟶ Spec (CommRingCat.of R)} {g₂ : B₂ ⟶ Spec (CommRingCat.of
    R)}

theorem exists_extension [Smooth g₁] [QuasiCompact g₁] [Smooth g₂] [IsSeparated g₂]
    (L₂ : RelativeGroupLaw R g₂)
    {y : Y ⟶ Spec (CommRingCat.of R)} (σ₁ : SchemeHomOver y g₁) (σ₂ : SchemeHomOver y g₂)
    [IsOpenImmersion σ₁.1]
    (hσ₁ : ∀ b : B₁, g₁.base b = IsLocalRing.closedPoint R →
      (∀ b' : B₁, b' ⤳ b → g₁.base b' = IsLocalRing.closedPoint R → b' = b) → b ∈ Set.range
        σ₁.1.base)
    (φK : SchemeHomOver (pullback.snd g₁ (specGenericFibreInclusion R K))
      (pullback.snd g₂ (specGenericFibreInclusion R K)))
    (hcompat : NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g₁ y σ₁) φK =
      genericFibreRestrict R K g₂ y σ₂) :
    ∃ φ : SchemeHomOver g₁ g₂, genericFibreRestrict R K g₂ g₁ φ = φK := by
  let ι := specGenericFibreInclusion R K
  have hloc : ∀ η : B₁, g₁.base η = IsLocalRing.closedPoint R →
      (∀ b' : B₁, b' ⤳ η → g₁.base b' = IsLocalRing.closedPoint R → b' = η) →
      ∃ (U : B₁.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ g₁) g₂),
        (genericFibreRestrict R K g₂ (U.ι ≫ g₁) g).1 =
          pullback.map (U.ι ≫ g₁) ι g₁ ι U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ φK.1 := by
    intro η hη hmax
    obtain ⟨y₀, hy₀⟩ := hσ₁ η hη hmax
    let U : B₁.Opens := σ₁.1.opensRange
    have hηU : η ∈ U := ⟨y₀, hy₀⟩
    let l : (U : Scheme.{u}) ⟶ Y := IsOpenImmersion.lift σ₁.1 U.ι (by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨x, rfl⟩; exact ⟨x, rfl⟩)
    have hl : l ≫ σ₁.1 = U.ι := IsOpenImmersion.lift_fac _ _ _
    have hly : l ≫ y = U.ι ≫ g₁ := by rw [← σ₁.2, ← Category.assoc, hl]
    let l' : SchemeHomOver (U.ι ≫ g₁) y := ⟨l, hly⟩
    have hU : (⟨U.ι, rfl⟩ : SchemeHomOver (U.ι ≫ g₁) g₁) = NeronModelInfra.schemeHomOverComp l' σ₁
      :=
      Subtype.ext hl.symm
    refine ⟨U, hηU, NeronModelInfra.schemeHomOverComp l' σ₂, ?_⟩
    rw [genericFibreRestrict_schemeHomOverComp, ← hcompat, pullbackMap_eq_genericFibreRestrict K g₁
      _ U.ι rfl,
      hU, genericFibreRestrict_schemeHomOverComp]
    rfl
  obtain ⟨V, v, hVη, hVs, hvK⟩ :=
    NeronModelInfra.exists_opens_extension_of_forall_nhds_extension R K g₂ g₁ φK hloc
  obtain ⟨W, d, hd⟩ :=
    RelativeGroupLaw.exists_opens_diagonal_difference_extension R L₂ g₁ V hVη hVs v
  obtain ⟨Φ, hΦ⟩ :=
    RelativeGroupLaw.exists_extension_of_diagonal_difference_extension R L₂ g₁ V hVη
      hVs v W d hd
  have hgen : ∀ q : ↑(pullback g₁ ι), (pullback.fst g₁ ι).base q ∈ V := fun q =>
    hVη _ (by
      change (pullback.fst g₁ ι ≫ g₁).base q ≠ _
      rw [pullback.condition]; exact base_ne_closedPoint K _ q)
  let ℓ : pullback g₁ ι ⟶ ↑V :=
    IsOpenImmersion.lift V.ι (pullback.fst g₁ ι) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hgen q)
  have hℓ : ℓ ≫ V.ι = pullback.fst g₁ ι := IsOpenImmersion.lift_fac _ _ _
  let κ : pullback g₁ ι ⟶ pullback (V.ι ≫ g₁) ι :=
    pullback.lift ℓ (pullback.snd g₁ ι) (by rw [← Category.assoc, hℓ, pullback.condition])
  have hκ1 : κ ≫ pullback.fst (V.ι ≫ g₁) ι = ℓ := pullback.lift_fst _ _ _
  have hκ2 : κ ≫ pullback.snd (V.ι ≫ g₁) ι = pullback.snd g₁ ι := pullback.lift_snd _ _ _
  have hκ : κ ≫ pullback.map (V.ι ≫ g₁) ι g₁ ι V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.map, pullback.lift_fst, ← Category.assoc, hκ1, hℓ,
        Category.id_comp]
    · rw [Category.assoc, pullback.map, pullback.lift_snd, ← Category.assoc, hκ2, Category.id_comp,
        Category.comp_id]
  refine ⟨Φ, ?_⟩
  have h1 : κ ≫ (genericFibreRestrict R K g₂ (V.ι ≫ g₁) v).1 = (genericFibreRestrict R K g₂ g₁ Φ).1
    := by
    apply pullback.hom_ext
    · rw [Category.assoc, genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst,
        ← Category.assoc, hκ1, ← hΦ, ← Category.assoc, hℓ]
    · rw [Category.assoc, genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd, hκ2]
  apply Subtype.ext
  rw [← h1, hvK, ← Category.assoc, hκ, Category.id_comp]

end WeilExtension

section Base

variable (R : Type u) [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']

scoped instance etale_sMap [Algebra.Etale R R'] : Etale (sMap R R') := by
  refine HasRingHomProperty.Spec_iff.mpr ?_
  change RingHom.Etale (algebraMap R R')
  rw [RingHom.etale_algebraMap]
  infer_instance

variable {R R'}

theorem ne_closedPoint_of_comp_eq [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R']
    {T : Scheme.{u}} {τ t' : T ⟶ Spec (CommRingCat.of R')}
    (hτ : t' ≫ sMap R R' = τ ≫ sMap R R') (p : T) (h : τ.base p ≠ IsLocalRing.closedPoint R') :
    t'.base p ≠ IsLocalRing.closedPoint R' := by
  intro hc
  apply h
  rw [← sMap_base_eq_closedPoint_iff R R'] at hc ⊢
  rw [← Scheme.Hom.comp_apply, ← hτ, Scheme.Hom.comp_apply]
  exact hc

end Base

section Main

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (X' : X.Opens)
  {B' : Scheme.{u}} {g' : B' ⟶ Spec (CommRingCat.of R')}
  (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (sMap R R')) g')

/-- The first base change of the open chart. -/
noncomputable def sigma1 :
    SchemeHomOver (pullback.snd (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R'))
      (pullback.snd (g' ≫ sMap R R') (sMap R R')) :=
  ⟨pullback.map _ _ _ _ jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
      (by rw [Category.comp_id, Category.id_comp]),
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)⟩

/-- The conjugate open chart under the base-change interchange. -/
noncomputable def sigma2 :
    SchemeHomOver (pullback.snd (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R')) g' :=
  ⟨(DescentAction.canonical (sMap R R') (X'.ι ≫ f)).act ≫ jY'.1, by
    rw [Category.assoc, jY'.2]
    exact (DescentAction.canonical (sMap R R') (X'.ι ≫ f)).act_comp⟩

@[reassoc]
theorem sigma1_fst : (sigma1 f X' jY').1 ≫ pullback.fst _ _ = pullback.fst _ _ ≫ jY'.1 :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem sigma1_snd : (sigma1 f X' jY').1 ≫ pullback.snd _ _ = pullback.snd _ _ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

theorem sigma2_coe : (sigma2 f X' jY').1 = DescentAction.flipMap (sMap R R') (X'.ι ≫ f) ≫ jY'.1 :=
    rfl

theorem isPullback_sigma1 :
    IsPullback (sigma1 f X' jY').1 (pullback.fst _ _) (pullback.fst (g' ≫ sMap R R') (sMap R R'))
      jY'.1 := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback (g' ≫ sMap R R') (sMap R R')).flip
  convert (IsPullback.of_hasPullback (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R
    R')).flip
    using 1
  · exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  · rw [← Category.assoc, jY'.2]

scoped instance isOpenImmersion_sigma1 [IsOpenImmersion jY'.1] : IsOpenImmersion (sigma1 f X' jY').1
    :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_sigma1 f X' jY').flip
    inferInstance

theorem mem_range_sigma1_iff (q : ↑(pullback (g' ≫ sMap R R') (sMap R R'))) :
    q ∈ Set.range (sigma1 f X' jY').1.base ↔
      (pullback.fst (g' ≫ sMap R R') (sMap R R')).base q ∈ Set.range jY'.1.base := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(pullback.fst (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R')).base z, ?_⟩
    have e : ((sigma1 f X' jY').1 ≫ pullback.fst (g' ≫ sMap R R') (sMap R R')).base z =
        (pullback.fst (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R') ≫ jY'.1).base z
          := by
      rw [sigma1_fst]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
    exact e.symm
  · intro hq
    have hq' : q ∈ Set.range (pullback.fst (pullback.fst (g' ≫ sMap R R') (sMap R R')) jY'.1).base
      := by
      rw [Scheme.Pullback.range_fst]
      exact hq
    obtain ⟨z, hz⟩ := hq'
    refine ⟨(isPullback_sigma1 f X' jY').isoPullback.inv.base z, ?_⟩
    rw [← Scheme.Hom.comp_apply, (Iso.inv_comp_eq _).2 ((isPullback_sigma1 f X'
      jY').isoPullback_hom_fst).symm]
    exact hz

section Density

variable [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R']

theorem mem_range_sigma1_of_ne
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (q : ↑(pullback (g' ≫ sMap R R') (sMap R R')))
    (hq : (pullback.snd (g' ≫ sMap R R') (sMap R R')).base q ≠ IsLocalRing.closedPoint R') :
    q ∈ Set.range (sigma1 f X' jY').1.base := by
  rw [mem_range_sigma1_iff]
  apply hjY'₁
  intro hc
  apply hq
  have e : (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g' ≫ sMap R R').base q =
      (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R').base q := by
    rw [pullback.condition]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
  rw [← sMap_base_eq_closedPoint_iff R R' (g'.base _)] at hc
  rw [← sMap_base_eq_closedPoint_iff R R' ((pullback.snd (g' ≫ sMap R R') (sMap R R')).base q), ← e]
  exact hc

theorem mem_range_sigma1_of_maximal [Flat (sMap R R')]
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (b : ↑(pullback (g' ≫ sMap R R') (sMap R R')))
    (hb : (pullback.snd (g' ≫ sMap R R') (sMap R R')).base b = IsLocalRing.closedPoint R')
    (hmax : ∀ b' : ↑(pullback (g' ≫ sMap R R') (sMap R R')), b' ⤳ b →
      (pullback.snd (g' ≫ sMap R R') (sMap R R')).base b' = IsLocalRing.closedPoint R' → b' = b) :
    b ∈ Set.range (sigma1 f X' jY').1.base := by
  rw [mem_range_sigma1_iff]
  have hcl : ∀ q : ↑(pullback (g' ≫ sMap R R') (sMap R R')),
      g'.base ((pullback.fst (g' ≫ sMap R R') (sMap R R')).base q) = IsLocalRing.closedPoint R' ↔
        (pullback.snd (g' ≫ sMap R R') (sMap R R')).base q = IsLocalRing.closedPoint R' := by
    intro q
    have e : (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g' ≫ sMap R R').base q =
        (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R').base q := by
      rw [pullback.condition]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e
    rw [← sMap_base_eq_closedPoint_iff R R' (g'.base _),
      ← sMap_base_eq_closedPoint_iff R R' ((pullback.snd (g' ≫ sMap R R') (sMap R R')).base q), e]
  apply hjY'₂ _ ((hcl b).2 hb)
  intro y hy hyc
  obtain ⟨b', hb'b, hb'y⟩ := Flat.generalizingMap (pullback.fst (g' ≫ sMap R R') (sMap R R')) hy
  have hb'c : (pullback.snd (g' ≫ sMap R R') (sMap R R')).base b' = IsLocalRing.closedPoint R' := by
    rw [← hcl b', hb'y]
    exact hyc
  have := hmax b' hb'b hb'c
  subst this
  exact hb'y.symm

end Density

/-- Apply the descent action to a relative point. -/
noncomputable def actP (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (x : SchemeHomOver t' g') : SchemeHomOver τ g' :=
  NeronModelInfra.schemeHomOverComp
    (RelativeGroupLaw.baseChangePointOfBase (sMap R R')
      (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ : SchemeHomOver (τ ≫ sMap R R') (g' ≫ sMap R R')))
    (⟨act, hact⟩ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g')

theorem actP_coe (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (x : SchemeHomOver t' g') :
    (actP act hact τ t' hτ x).1 = pullback.lift x.1 τ (by rw [reassoc_of% x.2, hτ]) ≫ act :=
  rfl

theorem comp_actP (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    {T T₁ : Scheme.{u}} (ψ : T₁ ⟶ T) (τ t' : T ⟶ Spec (CommRingCat.of R'))
    (hτ : t' ≫ sMap R R' = τ ≫ sMap R R') (τ₁ t'₁ : T₁ ⟶ Spec (CommRingCat.of R'))
    (hψτ : ψ ≫ τ = τ₁) (hψt : ψ ≫ t' = t'₁) (hτ₁ : t'₁ ≫ sMap R R' = τ₁ ≫ sMap R R')
    (x : SchemeHomOver t' g') :
    GoodReductionJacobian.schemeHomOverComp ψ hψτ (actP act hact τ t' hτ x) =
      actP act hact τ₁ t'₁ hτ₁ (GoodReductionJacobian.schemeHomOverComp ψ hψt x) := by
  apply Subtype.ext
  rw [GoodReductionJacobian.schemeHomOverComp_coe, actP_coe, actP_coe, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst,
      GoodReductionJacobian.schemeHomOverComp_coe]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hψτ]

/-- The point supplied by the base-changed open chart. -/
noncomputable def xa {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (a : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)) : SchemeHomOver t' g' :=
  NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') a) jY'

theorem xa_coe {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
    (a : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)) :
    (xa f X' jY' t' a).1 = pullback.lift a.1 t' a.2 ≫ jY'.1 :=
  rfl

/-- A relative point with its structural map rewritten. -/
def rebase {Z : Scheme.{u}} {z : Z ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {τ t' : T ⟶ Spec (CommRingCat.of R')} (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (a : SchemeHomOver (t' ≫ sMap R R') z) : SchemeHomOver (τ ≫ sMap R R') z :=
  ⟨a.1, a.2.trans hτ⟩

theorem act_xa (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1)
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (a : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)) :
    actP act hact τ t' hτ (xa f X' jY' t' a) = xa f X' jY' τ (rebase hτ a) := by
  apply Subtype.ext
  let z : T ⟶ pullback (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R') :=
    pullback.lift (pullback.lift a.1 t' a.2) τ (by rw [pullback.lift_snd_assoc, hτ])
  have h1 : z ≫ (sigma1 f X' jY').1 =
      pullback.lift (xa f X' jY' t' a).1 τ (by rw [reassoc_of% (xa f X' jY' t' a).2, hτ]) := by
    apply pullback.hom_ext
    · rw [Category.assoc, sigma1_fst, pullback.lift_fst_assoc, pullback.lift_fst, xa_coe]
    · rw [Category.assoc, sigma1_snd, pullback.lift_snd, pullback.lift_snd]
  have h2 : z ≫ (sigma2 f X' jY').1 = (xa f X' jY' τ (rebase hτ a)).1 := by
    rw [sigma2_coe, xa_coe, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, DescentAction.flipMap_fst, pullback.lift_fst_assoc, pullback.lift_fst,
        pullback.lift_fst]
      rfl
    · rw [Category.assoc, DescentAction.flipMap_snd, pullback.lift_snd, pullback.lift_snd]
  rw [actP_coe, ← h1, Category.assoc, hP1, h2]

section Lift

variable [IsLocalRing R] [IsLocalRing R'] [Module.Finite R R'] [IsOpenImmersion jY'.1]

omit [IsLocalRing R] [Module.Finite R R'] in
theorem exists_eq_xa
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (x : SchemeHomOver t' g')
    (hgen : ∀ p : T, t'.base p ≠ IsLocalRing.closedPoint R') :
    ∃ a : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f), x = xa f X' jY' t' a := by
  have hrange : Set.range x.1.base ⊆ Set.range jY'.1.base := by
    rintro _ ⟨p, rfl⟩
    apply hjY'₁
    rw [← Scheme.Hom.comp_apply, x.2]
    exact hgen p
  let ℓ := IsOpenImmersion.lift jY'.1 x.1 hrange
  have hℓ : ℓ ≫ jY'.1 = x.1 := IsOpenImmersion.lift_fac _ _ _
  have hℓ₂ : ℓ ≫ pullback.snd (X'.ι ≫ f) (sMap R R') = t' := by
    rw [← x.2, ← hℓ, Category.assoc, jY'.2]
  refine ⟨⟨ℓ ≫ pullback.fst (X'.ι ≫ f) (sMap R R'), by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hℓ₂]⟩, ?_⟩
  apply Subtype.ext
  rw [xa_coe, ← hℓ]
  congr 1
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
  · rw [pullback.lift_snd, hℓ₂]

end Lift

section Pair

variable (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
  (U : (pullback f f).Opens) (hUW : U ≤ W)

theorem exists_pair_prod [IsLocalRing R]
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
      (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (hgen : ∀ p : T, t.base p ≠
      IsLocalRing.closedPoint R)
    (a b : SchemeHomOver t (X'.ι ≫ f)) :
    ∃ (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (c : SchemeHomOver t (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f ∧ b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f ∧
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 := by
  have hαf : (a.1 ≫ X'.ι) ≫ f = t := by rw [Category.assoc]; exact a.2
  have hβf : (b.1 ≫ X'.ι) ≫ f = t := by rw [Category.assoc]; exact b.2
  let pair : T ⟶ pullback f f := pullback.lift (a.1 ≫ X'.ι) (b.1 ≫ X'.ι) (hαf.trans hβf.symm)
  have hpair : pair ≫ pullback.fst f f ≫ f = t := by rw [pullback.lift_fst_assoc, hαf]
  have hrange : Set.range pair.base ⊆ Set.range U.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hU₁
    rw [← Scheme.Hom.comp_apply, hpair]
    exact hgen z
  let wl : T ⟶ U := IsOpenImmersion.lift U.ι pair hrange
  have hwl : wl ≫ U.ι = pair := IsOpenImmersion.lift_fac _ _ _
  let w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f) := ⟨wl, by rw [reassoc_of% hwl, hpair]⟩
  have ha : a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f := by
    change _ = wl ≫ _
    rw [reassoc_of% hwl, pullback.lift_fst]
  have hb : b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f := by
    change _ = wl ≫ _
    rw [reassoc_of% hwl, pullback.lift_snd]
  let cm : T ⟶ X := w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1
  have hrangec : Set.range cm.base ⊆ Set.range X'.ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : (U.ι.base (wl.base z)) ∈ U := (show U from wl z).property
    have h3 := (hU₂ _ hq).2.2
    have hpt : ((pullback f f).homOfLE hUW).base (wl.base z) =
        ⟨U.ι.base (wl.base z), hUW hq⟩ :=
      Scheme.homOfLE_apply' hUW (show U from wl z).val (show U from wl z).property
    change m.1.base (((pullback f f).homOfLE hUW).base (wl.base z)) ∈ X'
    rw [hpt]
    exact h3
  let cl : T ⟶ X' := IsOpenImmersion.lift X'.ι cm hrangec
  have hcl : cl ≫ X'.ι = cm := IsOpenImmersion.lift_fac _ _ _
  have hwW : (w.1 ≫ (pullback f f).homOfLE hUW) ≫ W.ι ≫ pullback.fst f f ≫ f = t := by
    rw [Category.assoc, Scheme.homOfLE_ι_assoc]
    exact w.2
  let c : SchemeHomOver t (X'.ι ≫ f) := ⟨cl, by
    rw [reassoc_of% hcl]
    change (w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1) ≫ f = t
    rw [Category.assoc, Category.assoc, m.2, ← Category.assoc]
    exact hwW⟩
  exact ⟨w, c, ha, hb, hcl⟩

end Pair

section DVR

variable [IsDomain R] [IsDiscreteValuationRing R] [IsDomain R'] [IsDiscreteValuationRing R']
  [Module.Finite R R'] [Algebra.Etale R R']
  (K' : Type u) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
  [Smooth f] [Smooth g'] [IsSeparated g'] [QuasiCompact g'] [IsOpenImmersion jY'.1]
  (LB' : RelativeGroupLaw R' g')

omit [Algebra.Etale R R'] [Smooth f] [Smooth g'] [IsSeparated g']
  [QuasiCompact g'] [IsOpenImmersion jY'.1] in
theorem fst_mem_range_sigma1
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (p : ↑(pullback (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K')))
      :
    (pullback.fst (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R'
      K')).base p ∈
      Set.range (sigma1 f X' jY').1.base :=
  mem_range_sigma1_of_ne f X' jY' hjY'₁ _ (by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact specGenericFibreInclusion_ne_closedPoint (R := R') K' _)

omit [Algebra.Etale R R'] [Smooth f] [Smooth g'] [IsSeparated g'] [QuasiCompact g'] in
theorem exists_phiK
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base) :
    ∃ φK : SchemeHomOver (pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R'))
      (specGenericFibreInclusion R' K'))
        (pullback.snd g' (specGenericFibreInclusion R' K')),
      NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R' K' (pullback.snd (g' ≫ sMap R R') (sMap R R')) _ (sigma1 f X'
            jY')) φK =
        genericFibreRestrict R' K' g' _ (sigma2 f X' jY') := by
  let ℓ : pullback (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K') ⟶
      pullback (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R') :=
    IsOpenImmersion.lift (sigma1 f X' jY').1
      (pullback.fst (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K'))
        (by
      rintro _ ⟨p, rfl⟩
      exact fst_mem_range_sigma1 f X' jY' K' hjY'₁ p)
  have hℓ : ℓ ≫ (sigma1 f X' jY').1 =
      pullback.fst (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K') :=
    IsOpenImmersion.lift_fac _ _ _
  have hcond : (ℓ ≫ (sigma2 f X' jY').1) ≫ g' =
      pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K') ≫
        specGenericFibreInclusion R' K' := by
    calc (ℓ ≫ (sigma2 f X' jY').1) ≫ g'
        = ℓ ≫ (sigma1 f X' jY').1 ≫ pullback.snd (g' ≫ sMap R R') (sMap R R') := by
          rw [Category.assoc, (sigma2 f X' jY').2, (sigma1 f X' jY').2]
      _ = pullback.fst (pullback.snd (g' ≫ sMap R R') (sMap R R')) (specGenericFibreInclusion R' K')
        ≫
            pullback.snd (g' ≫ sMap R R') (sMap R R') := by rw [← Category.assoc, hℓ]
      _ = _ := pullback.condition
  refine ⟨⟨pullback.lift (ℓ ≫ (sigma2 f X' jY').1) (pullback.snd _ _) hcond, pullback.lift_snd _ _
    _⟩, ?_⟩
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, pullback.lift_fst,
      genericFibreRestrict_coe_comp_fst, ← Category.assoc]
    congr 1
    rw [← cancel_mono (sigma1 f X' jY').1, Category.assoc, hℓ, genericFibreRestrict_coe_comp_fst]
  · rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, pullback.lift_snd,
      genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]

include K' LB' in
theorem exists_act
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
        :
    ∃ Φ : SchemeHomOver (pullback.snd (g' ≫ sMap R R') (sMap R R')) g',
      (sigma1 f X' jY').1 ≫ Φ.1 = (sigma2 f X' jY').1 := by
  obtain ⟨φK, hcompat⟩ := exists_phiK f X' jY' K' hjY'₁
  obtain ⟨Φ, hΦ⟩ := exists_extension K' LB' (sigma1 f X' jY') (sigma2 f X' jY')
    (fun b hb hmax => mem_range_sigma1_of_maximal f X' jY' hjY'₂ b hb hmax) φK hcompat
  refine ⟨Φ, ?_⟩
  have h : NeronModelInfra.schemeHomOverComp (sigma1 f X' jY') Φ = sigma2 f X' jY' := by
    apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R' K' g'
      (pullback.snd (pullback.snd (X'.ι ≫ f) (sMap R R') ≫ sMap R R') (sMap R R'))
    rw [genericFibreRestrict_schemeHomOverComp, hΦ, hcompat]
  exact congrArg Subtype.val h

include K' in
omit [Algebra.Etale R R'] [Smooth f] [QuasiCompact g'] in
omit [IsDomain R] [IsDiscreteValuationRing R] [Module.Finite R R'] in
theorem unit_act
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1) :
    DescentAction.unitMap (sMap R R') g' ≫ act = 𝟙 B' := by
  let U₁ : SchemeHomOver g' g' :=
    ⟨DescentAction.unitMap (sMap R R') g' ≫ act, by rw [Category.assoc, hact,
      DescentAction.unitMap_snd]⟩
  suffices h : U₁ = schemeHomOverId g' from congrArg Subtype.val h
  apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R' K' g' g'
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst, schemeHomOverId_coe,
      Category.comp_id]
    let u := pullback.fst g' (specGenericFibreInclusion R' K')
    have hgen : ∀ p, (u ≫ g').base p ≠ IsLocalRing.closedPoint R' := fun p => by
      rw [pullback.condition, Scheme.Hom.comp_apply]
      exact specGenericFibreInclusion_ne_closedPoint (R := R') K' _
    obtain ⟨a, ha⟩ := exists_eq_xa f X' jY' hjY'₁ (u ≫ g') ⟨u, rfl⟩ hgen
    have hav : u = (xa f X' jY' (u ≫ g') a).1 := congrArg Subtype.val ha
    have key : actP act hact (u ≫ g') (u ≫ g') rfl ⟨u, rfl⟩ = xa f X' jY' (u ≫ g') (rebase rfl a)
      := by
      rw [ha]; exact act_xa f X' jY' act hact hP1 _ _ rfl a
    have hk : pullback.lift u (u ≫ g') (Category.assoc _ _ _).symm ≫ act = (xa f X' jY' (u ≫ g')
      a).1 :=
      congrArg Subtype.val key
    have hu : u ≫ DescentAction.unitMap (sMap R R') g' = pullback.lift u (u ≫ g') (Category.assoc _
      _ _).symm := by
      apply pullback.hom_ext
      · rw [Category.assoc, DescentAction.unitMap_fst, Category.comp_id, pullback.lift_fst]
      · rw [Category.assoc, DescentAction.unitMap_snd, pullback.lift_snd]
    change u ≫ DescentAction.unitMap (sMap R R') g' ≫ act = u
    rw [← Category.assoc, hu, hk]
    exact hav.symm
  · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]

omit [Algebra.Etale R R'] [Smooth f] [Smooth g'] [IsSeparated g'] [QuasiCompact g'] in
theorem comp_actMap_act
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1)
    {T : Scheme.{u}}
    (u : T ⟶ pullback (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R'))
    (hu : ∀ p : T, (u ≫ pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R
      R')).base p ≠
      IsLocalRing.closedPoint R') :
    u ≫ DescentAction.actMap act hact ≫ act = u ≫ DescentAction.proj₁₃ (sMap R R') g' ≫ act := by
  have hστ : (u ≫ pullback.fst _ _ ≫ pullback.snd (g' ≫ sMap R R') (sMap R R')) ≫ sMap R R' =
      (u ≫ pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R')) ≫ sMap
        R R' := by
    simp only [Category.assoc]
    rw [pullback.condition]
  have htσ : (u ≫ pullback.fst _ _ ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') ≫ sMap R R' =
      (u ≫ pullback.fst _ _ ≫ pullback.snd (g' ≫ sMap R R') (sMap R R')) ≫ sMap R R' := by
    simp only [Category.assoc]
    rw [pullback.condition]
  have hσg : ∀ p, (u ≫ pullback.fst _ _ ≫ pullback.snd (g' ≫ sMap R R') (sMap R R')).base p ≠
      IsLocalRing.closedPoint R' := fun p => ne_closedPoint_of_comp_eq hστ p (hu p)
  have htg : ∀ p, (u ≫ pullback.fst _ _ ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g').base p ≠
      IsLocalRing.closedPoint R' := fun p => ne_closedPoint_of_comp_eq htσ p (hσg p)
  let x₀ : SchemeHomOver (u ≫ pullback.fst _ _ ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g'
    :=
    ⟨u ≫ pullback.fst _ _ ≫ pullback.fst (g' ≫ sMap R R') (sMap R R'), by simp only
      [Category.assoc]⟩
  obtain ⟨a, ha⟩ := exists_eq_xa f X' jY' hjY'₁ _ x₀ htg
  have eA : ∀ h, pullback.lift x₀.1 (u ≫ pullback.fst _ _ ≫ pullback.snd (g' ≫ sMap R R') (sMap R
    R')) h =
      u ≫ pullback.fst _ _ := fun h => by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc]
    · rw [pullback.lift_snd, Category.assoc]
  have hA : (actP act hact _ _ htσ x₀).1 = u ≫ pullback.fst _ _ ≫ act := by
    rw [actP_coe, eA, Category.assoc]
  have eB : ∀ h, pullback.lift (actP act hact _ _ htσ x₀).1
      (u ≫ pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R')) h =
      u ≫ DescentAction.actMap act hact := fun h => by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hA, Category.assoc, DescentAction.actMap_fst]
    · rw [pullback.lift_snd, Category.assoc, DescentAction.actMap_snd]
  have hB : (actP act hact _ _ hστ (actP act hact _ _ htσ x₀)).1 = u ≫ DescentAction.actMap act hact
    ≫ act := by
    rw [actP_coe, eB, Category.assoc]
  have eC : ∀ h, pullback.lift x₀.1
      (u ≫ pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R')) h =
      u ≫ DescentAction.proj₁₃ (sMap R R') g' := fun h => by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, DescentAction.proj₁₃_fst]
    · rw [pullback.lift_snd, Category.assoc, DescentAction.proj₁₃_snd]
  have hC : (actP act hact _ _ (htσ.trans hστ) x₀).1 = u ≫ DescentAction.proj₁₃ (sMap R R') g' ≫ act
    := by
    rw [actP_coe, eC, Category.assoc]
  have hD : actP act hact _ _ hστ (actP act hact _ _ htσ x₀) = actP act hact _ _ (htσ.trans hστ) x₀
    := by
    rw [ha, act_xa f X' jY' act hact hP1, act_xa f X' jY' act hact hP1, act_xa f X' jY' act hact
      hP1]
    rfl
  rw [← hB, ← hC, hD]

include K' in
omit [Smooth f] [QuasiCompact g'] in
theorem trans_act
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1) :
    DescentAction.actMap act hact ≫ act = DescentAction.proj₁₃ (sMap R R') g' ≫ act := by
  let T₁ : SchemeHomOver (pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap
    R R')) g' :=
    ⟨DescentAction.actMap act hact ≫ act, by rw [Category.assoc, hact, DescentAction.actMap_snd]⟩
  let T₂ : SchemeHomOver (pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap
    R R')) g' :=
    ⟨DescentAction.proj₁₃ (sMap R R') g' ≫ act, by rw [Category.assoc, hact,
      DescentAction.proj₁₃_snd]⟩
  suffices h : T₁ = T₂ from congrArg Subtype.val h
  apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R' K' g'
    (pullback.snd (pullback.snd (g' ≫ sMap R R') (sMap R R') ≫ sMap R R') (sMap R R'))
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst]
    change pullback.fst _ _ ≫ (DescentAction.actMap act hact ≫ act) =
      pullback.fst _ _ ≫ (DescentAction.proj₁₃ (sMap R R') g' ≫ act)
    apply comp_actMap_act f X' jY' hjY'₁ act hact hP1
    intro p
    rw [pullback.condition, Scheme.Hom.comp_apply]
    exact specGenericFibreInclusion_ne_closedPoint (R := R') K' _
  · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]

section Mul

variable (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
  (U : (pullback f f).Opens) (hUW : U ≤ W)

omit [Algebra.Etale R R'] [Smooth f] [Smooth g'] [IsSeparated g'] [QuasiCompact g'] in
theorem mul_actP_of_generic
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
      (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ sMap R R') (U.ι ≫ pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap
          R R') a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') b)
            jY'))
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1)
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (x y : SchemeHomOver t' g') (hgen : ∀ p : T, τ.base p ≠ IsLocalRing.closedPoint R') :
    actP act hact τ t' hτ (LB'.mul t' x y) = LB'.mul τ (actP act hact τ t' hτ x) (actP act hact τ t'
      hτ y) := by
  have hgen' : ∀ p : T, t'.base p ≠ IsLocalRing.closedPoint R' := fun p => ne_closedPoint_of_comp_eq
    hτ p (hgen p)
  have hgenR : ∀ p : T, (t' ≫ sMap R R').base p ≠ IsLocalRing.closedPoint R := fun p hp =>
    hgen' p ((sMap_base_eq_closedPoint_iff R R' _).1 (by rw [← Scheme.Hom.comp_apply]; exact hp))
  obtain ⟨a, rfl⟩ := exists_eq_xa f X' jY' hjY'₁ t' x hgen'
  obtain ⟨b, rfl⟩ := exists_eq_xa f X' jY' hjY'₁ t' y hgen'
  obtain ⟨w, c, ha, hb, hc⟩ := exists_pair_prod f X' W m U hUW hU₁ hU₂ (t' ≫ sMap R R') hgenR a b
  have H1 : xa f X' jY' t' c = LB'.mul t' (xa f X' jY' t' a) (xa f X' jY' t' b) := hres' t' w a b c
    ha hb hc
  have H2 : xa f X' jY' τ (rebase hτ c) = LB'.mul τ (xa f X' jY' τ (rebase hτ a)) (xa f X' jY' τ
    (rebase hτ b)) :=
    hres' τ (rebase hτ w) (rebase hτ a) (rebase hτ b) (rebase hτ c) ha hb hc
  rw [← H1, act_xa f X' jY' act hact hP1, act_xa f X' jY' act hact hP1, act_xa f X' jY' act hact
    hP1]
  exact H2

include K' in
omit [Smooth f] [QuasiCompact g'] in
theorem mul_actP
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧
      (pullback.snd f f).base q ∈ X' ∧ m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ sMap R R') (U.ι ≫ pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ sMap R R') (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap
          R R') a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (sMap R R') b)
            jY'))
    (act : pullback (g' ≫ sMap R R') (sMap R R') ⟶ B')
    (hact : act ≫ g' = pullback.snd (g' ≫ sMap R R') (sMap R R'))
    (hP1 : (sigma1 f X' jY').1 ≫ act = (sigma2 f X' jY').1)
    {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R')) (hτ : t' ≫ sMap R R' = τ ≫ sMap R R')
    (x y : SchemeHomOver t' g') :
    actP act hact τ t' hτ (LB'.mul t' x y) = LB'.mul τ (actP act hact τ t' hτ x) (actP act hact τ t'
      hτ y) := by
  let qP := pullback.fst (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g'
  let τ₀ : pullback (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g' ⟶ Spec (CommRingCat.of R')
    :=
    qP ≫ pullback.snd (g' ≫ sMap R R') (sMap R R')
  let t₀ : pullback (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g' ⟶ Spec (CommRingCat.of R')
    :=
    qP ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g'
  have hτ₀ : t₀ ≫ sMap R R' = τ₀ ≫ sMap R R' := by
    simp only [t₀, τ₀, Category.assoc]
    rw [pullback.condition]
  let x₀ : SchemeHomOver t₀ g' := ⟨qP ≫ pullback.fst (g' ≫ sMap R R') (sMap R R'), Category.assoc _
    _ _⟩
  let y₀ : SchemeHomOver t₀ g' :=
    ⟨pullback.snd (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g', pullback.condition.symm⟩
  have : Flat τ₀ := inferInstanceAs
    (Flat (pullback.fst (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g' ≫
      pullback.snd (g' ≫ sMap R R') (sMap R R')))
  have huniv : actP act hact τ₀ t₀ hτ₀ (LB'.mul t₀ x₀ y₀) =
      LB'.mul τ₀ (actP act hact τ₀ t₀ hτ₀ x₀) (actP act hact τ₀ t₀ hτ₀ y₀) := by
    apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R' K' g' τ₀
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst]
      have hg : ∀ p, (pullback.fst τ₀ (specGenericFibreInclusion R' K') ≫ τ₀).base p ≠
          IsLocalRing.closedPoint R' := fun p => by
        rw [pullback.condition, Scheme.Hom.comp_apply]
        exact specGenericFibreInclusion_ne_closedPoint (R := R') K' _
      have key := mul_actP_of_generic f X' jY' LB' W m U hUW hU₁ hU₂ hjY'₁ hres' act hact hP1
        (pullback.fst τ₀ (specGenericFibreInclusion R' K') ≫ τ₀)
        (pullback.fst τ₀ (specGenericFibreInclusion R' K') ≫ t₀)
        (by simp only [Category.assoc, hτ₀])
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst τ₀ (specGenericFibreInclusion R' K'))
          rfl x₀)
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst τ₀ (specGenericFibreInclusion R' K'))
          rfl y₀) hg
      rw [← LB'.mul_natural,
        ← comp_actP act hact (pullback.fst τ₀ (specGenericFibreInclusion R' K')) τ₀ t₀ hτ₀ _ _ rfl
          rfl,
        ← comp_actP act hact (pullback.fst τ₀ (specGenericFibreInclusion R' K')) τ₀ t₀ hτ₀ _ _ rfl
          rfl,
        ← comp_actP act hact (pullback.fst τ₀ (specGenericFibreInclusion R' K')) τ₀ t₀ hτ₀ _ _ rfl
          rfl,
        ← LB'.mul_natural] at key
      exact congrArg Subtype.val key
    · rw [genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]
  let qx : T ⟶ pullback (g' ≫ sMap R R') (sMap R R') := pullback.lift x.1 τ (by rw [reassoc_of% x.2,
    hτ])
  have hqx : qx ≫ pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g' = y.1 ≫ g' := by
    simp only [qx]
    rw [pullback.lift_fst_assoc, x.2, y.2]
  let q : T ⟶ pullback (pullback.fst (g' ≫ sMap R R') (sMap R R') ≫ g') g' := pullback.lift qx y.1
    hqx
  have hqτ : q ≫ τ₀ = τ := by
    simp only [τ₀, qP, q, qx]
    rw [pullback.lift_fst_assoc, pullback.lift_snd]
  have hqt : q ≫ t₀ = t' := by
    simp only [t₀, qP, q, qx]
    rw [pullback.lift_fst_assoc, pullback.lift_fst_assoc, x.2]
  have hx : GoodReductionJacobian.schemeHomOverComp q hqt x₀ = x := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe]
    simp only [x₀, q, qP, qx]
    rw [pullback.lift_fst_assoc, pullback.lift_fst]
  have hy : GoodReductionJacobian.schemeHomOverComp q hqt y₀ = y := by
    apply Subtype.ext
    rw [GoodReductionJacobian.schemeHomOverComp_coe]
    simp only [y₀, q]
    rw [pullback.lift_snd]
  have h1 := congrArg (GoodReductionJacobian.schemeHomOverComp q hqτ) huniv
  rw [comp_actP act hact q τ₀ t₀ hτ₀ τ t' hqτ hqt hτ, LB'.mul_natural, LB'.mul_natural,
    comp_actP act hact q τ₀ t₀ hτ₀ τ t' hqτ hqt hτ, comp_actP act hact q τ₀ t₀ hτ₀ τ t' hqτ hqt hτ,
      hx, hy] at h1
  exact h1

end Mul

end DVR

end Main

end Action

end AbelianVarieties.NOSProofs.EtaleDescentAction

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian
open AbelianVarieties.NOSProofs.EtaleDescentAction

universe u

theorem exists_descentAction_of_etale_groupLaw
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f
      f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {B' : Scheme.{u}} (g' : B' ⟶ Spec (CommRingCat.of R')) (LB' : RelativeGroupLaw R' g')
    [Smooth g'] [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      g') [IsOpenImmersion jY'.1]
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
          pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map
        (CommRingCat.ofHom (algebraMap R R'))) c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase
          (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) b) jY')) :
    ∃ A : DescentAction (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g',
      pullback.map (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (Spec.map (CommRingCat.ofHom (algebraMap R R')))
          (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))
          jY'.1 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, ← Category.assoc, jY'.2])
          (by rw [Category.comp_id, Category.id_comp]) ≫ A.act =
        (DescentAction.canonical (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (X'.ι ≫ f)).act ≫
          jY'.1 ∧
      (∀ {T : Scheme.{u}} (τ t' : T ⟶ Spec (CommRingCat.of R'))
          (hτ : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = τ ≫ Spec.map
            (CommRingCat.ofHom (algebraMap R R')))
          (x y : SchemeHomOver t' g'),
        NeronModelInfra.schemeHomOverComp
            (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R')))
              (⟨(LB'.mul t' x y).1, by rw [reassoc_of% (LB'.mul t' x y).2, hτ]⟩ :
                SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
            (⟨A.act, A.act_comp⟩ : SchemeHomOver
              (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g') =
          LB'.mul τ
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R
                R')))
                (⟨x.1, by rw [reassoc_of% x.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))
            (NeronModelInfra.schemeHomOverComp
              (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R
                R')))
                (⟨y.1, by rw [reassoc_of% y.2, hτ]⟩ :
                  SchemeHomOver (τ ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                    (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))))
              (⟨A.act, A.act_comp⟩ : SchemeHomOver
                (pullback.snd (g' ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')))
                  (Spec.map (CommRingCat.ofHom (algebraMap R R')))) g'))) := by
  obtain ⟨Φ, hP1⟩ := Action.exists_act f X' jY' (FractionRing R') LB' hjY'₁ hjY'₂
  refine ⟨⟨Φ.1, Φ.2, Action.unit_act f X' jY' (FractionRing R') hjY'₁ Φ.1 Φ.2 hP1,
    Action.trans_act f X' jY' (FractionRing R') hjY'₁ Φ.1 Φ.2 hP1⟩, hP1, ?_⟩
  intro T τ t' hτ x y
  exact Action.mul_actP f X' jY' (FractionRing R') LB' W m U hUW hU₁ hU₂ hjY'₁ hres' Φ.1 Φ.2 hP1 τ
    t' hτ x y

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_finite_etale_relativeGroupLaw_isOpenImmersion_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem exists_groupLaw_of_etale_groupLaw
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hXk : ∃ x : X, f.base x = IsLocalRing.closedPoint R)
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (_hW₁ : ∀ p : ↑(pullback f f),
      (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (_hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (_hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (_hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (_hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (_hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
    (_hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X')
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f
      f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (_hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))
              ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈
              U})))
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [Module.Finite R R'] [Algebra.Etale R R'] [Module.FaithfullyFlat R R']
    {B' : Scheme.{u}} (g' : B' ⟶ Spec (CommRingCat.of R')) (LB' : RelativeGroupLaw R' g')
    [Smooth g'] [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
      g') [IsOpenImmersion jY'.1]
    (hjY'₁ : ∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base)
    (hjY'₂ : ∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
      (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range jY'.1.base)
    (hres' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
        (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
          pullback.fst f f ≫ f))
        (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫ f)),
      a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
      c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
      NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map
        (CommRingCat.ofHom (algebraMap R R'))) c) jY' =
        LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase
          (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a) jY')
          (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map
            (CommRingCat.ofHom (algebraMap R R'))) b) jY')) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (jY : SchemeHomOver (X'.ι ≫ f) g) (e' : SchemeHomOver (pullback.snd g
        (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsOpenImmersion jY.1 ∧
      (∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base) ∧
      (∀ b : B, g.base b = IsLocalRing.closedPoint R →
        (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range jY.1.base) ∧
      IsIso e'.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y
            e')) ∧
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g (X'.ι ≫ f) jY) e' =
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        NeronModelInfra.schemeHomOverComp c jY =
          LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b
            jY)) := by
  obtain ⟨A, hA₁, hA₂⟩ :=
    exists_descentAction_of_etale_groupLaw
      f W m X' U hUW hU₁ hU₂ R' g' LB' jY' hjY'₁ hjY'₂ hres'
  have : HenselianLocalRing R' := HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := R)
  have haff : ∀ S : Finset ↥B', ∃ V : B'.Opens, IsAffineOpen V ∧ ∀ x ∈ S, x ∈ V := fun S =>
    RelativeGroupLaw.exists_isAffineOpen_forall_mem_of_smooth_of_henselianLocalRing LB' S
  have hA : A.Effective := AlgebraicGeometry.DescentAction.effective_of_finiteEtale R R' A haff
  exact
    exists_groupLaw_of_effective_descent
      K LXK f e W m hmK X' U hUW hX'₁ hU₁ hU₂ R' g' LB' jY' hjY'₁ hjY'₂ hres' A hA₁ hA₂ hA

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_finite_etale_relativeGroupLaw_isOpenImmersion_of_forall_dense_preimage_fibre_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem exists_etale_groupLaw_of_dense_fibres
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hXk : ∃ x : X, f.base x = IsLocalRing.closedPoint R)
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
    (hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X')
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f
      f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))
              ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈
              U}))) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ :
      Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (B' : Scheme.{u}) (g' : B' ⟶ Spec (CommRingCat.of R')) (LB' : RelativeGroupLaw R' g')
      (jY' : SchemeHomOver (pullback.snd (X'.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R
        R')))) g'),
      Smooth g' ∧ IsSeparated g' ∧ LocallyOfFiniteType g' ∧ QuasiCompact g' ∧
      IsOpenImmersion jY'.1 ∧
      (∀ b : B', g'.base b ≠ IsLocalRing.closedPoint R' → b ∈ Set.range jY'.1.base) ∧
      (∀ b : B', g'.base b = IsLocalRing.closedPoint R' →
        (∀ y : B', y ⤳ b → g'.base y = IsLocalRing.closedPoint R' → y = b) → b ∈ Set.range
          jY'.1.base) ∧
      (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R'))
          (w : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (U.ι ≫
            pullback.fst f f ≫ f))
          (a b c : SchemeHomOver (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap R R')))) (X'.ι ≫
            f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map
          (CommRingCat.ofHom (algebraMap R R'))) c) jY' =
          LB'.mul t' (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase
            (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a) jY')
            (NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointOfBase (Spec.map
              (CommRingCat.ofHom (algebraMap R R'))) b) jY')) := by
  classical
  obtain ⟨R', instCR, instDom, instDVR, instAlg, instFin, instEt, instFF, Y', y', ι, U', m',
      hsm, hsep, hloft, hqc, hιo, hgen, hmax, hU'₁, hU'₂, hΦ', hΦ'₁, hΦ'₂, hΨ', hΨ'₁, hΨ'₂, hassoc',
      hext, ⟨a', ha'⟩, hsq⟩ :=
    NeronModelInfra.exists_etale_translation_cover
      K LXK f hXk e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂ X' U hUW hX'₁ hX'₂ hU₁ hU₂ hU₃
  have : Smooth y' := hsm
  have : IsSeparated y' := hsep
  have : LocallyOfFiniteType y' := hloft
  have : QuasiCompact y' := hqc
  have : IsOpenImmersion ι.1 := hιo
  obtain ⟨L, hL⟩ :=
    exists_relativeGroupLaw_mul_eq_of_forall_dense_preimage_fibre_of_forall_mem_opens_of_section
      y' U' m' hU'₁ hU'₂ hΦ' hΦ'₁ hΦ'₂ hΨ' hΨ'₁ hΨ'₂ (fun t u v p q => hassoc' t u v p q) a' ha'
      (Scheme.Hom.opensRange ι.1)
      (fun p hp => (Scheme.Hom.mem_opensRange).2 (hmax p hp))
      (fun q h₁ h₂ => hsq q ((Scheme.Hom.mem_opensRange).1 h₁) ((Scheme.Hom.mem_opensRange).1 h₂))
  refine ⟨R', instCR, instDom, instDVR, instAlg, instFin, instEt, instFF, Y', y', L, ι,
    hsm, hsep, hloft, hqc, hιo, hgen, ?_, ?_⟩
  · intro b hb hbmax
    exact hmax b (fun p' hp' hy => hbmax p' hp' (hy.trans hb))
  · intro T t' w a b c ha hb hc
    obtain ⟨w', h₁, h₂, h₃⟩ := hext t' w a b c ha hb hc
    have key := hL t' w'
      (NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) a)
          ι)
      (NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) b)
          ι)
      (NeronModelInfra.schemeHomOverComp
        (RelativeGroupLaw.baseChangePointOfBase (Spec.map (CommRingCat.ofHom (algebraMap R R'))) c)
          ι)
      (by rw [NeronModelInfra.schemeHomOverComp_coe, h₁])
      (by rw [NeronModelInfra.schemeHomOverComp_coe, h₂])
      (by rw [NeronModelInfra.schemeHomOverComp_coe, h₃])
    exact key.symm

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_relativeGroupLaw_isOpenImmersion_opens_of_forall_dense_preimage_fibre_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry hiding DescentAction
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

theorem exists_groupLaw_of_dense_fibres
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hXk : ∃ x : X, f.base x = IsLocalRing.closedPoint R)
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (W : (pullback f f).Opens) (m : SchemeHomOver (W.ι ≫ pullback.fst f f ≫ f) f)
    (hW₁ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p ≠ IsLocalRing.closedPoint R → p ∈ W)
    (hW₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ W)
    (hmK : (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (W.ι ≫ pullback.fst f f ≫ f) m) e).1 =
      pullback.map (W.ι ≫ pullback.fst f f ≫ f) (specGenericFibreInclusion R K)
          (pullback.fst f f ≫ f) (specGenericFibreInclusion R K) W.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        (LXK.mul (pullback.snd (pullback.fst f f ≫ f) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f) ⟨pullback.fst f f, rfl⟩) e)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst f f ≫ f)
              ⟨pullback.snd f f, pullback.condition.symm⟩) e)).1)
    (hΦ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)))
    (hΦ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
        ((Category.assoc _ _ _).trans m.2.symm)).base)
    (hΨ : IsOpenImmersion
      (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))))
    (hΨ₂ : ∀ p : ↑(pullback f f), (pullback.fst f f ≫ f).base p = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback f f), y ⤳ p → (pullback.fst f f ≫ f).base y = IsLocalRing.closedPoint R → y
        = p) →
      p ∈ Set.range (pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
        (m.2.trans (by rw [Category.assoc, pullback.condition]))).base)
    (X' : X.Opens) (U : (pullback f f).Opens) (hUW : U ≤ W)
    (hX'₁ : ∀ x : X, f.base x ≠ IsLocalRing.closedPoint R → x ∈ X')
    (hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X')
    (hU₁ : ∀ q : ↑(pullback f f), (pullback.fst f f ≫ f).base q ≠ IsLocalRing.closedPoint R → q ∈ U)
    (hU₂ : ∀ (q : ↑(pullback f f)) (hq : q ∈ U), (pullback.fst f f).base q ∈ X' ∧ (pullback.snd f
      f).base q ∈ X' ∧
      m.1.base ⟨q, hUW hq⟩ ∈ X')
    (hU₃ : ∀ x : X, x ∈ X' →
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            (U : Set ↑(pullback f f))) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) (W.ι ≫ pullback.fst f f) m.1
            ((Category.assoc _ _ _).trans m.2.symm)).base '' {w | W.ι.base w ∈ U})) ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.fst f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈ U}))
              ∧
        Dense ((Subtype.val : {q : ↑(pullback f f) // (pullback.snd f f).base q = x} → ↑(pullback f
          f)) ⁻¹'
            ((pullback.lift (f := f) (g := f) m.1 (W.ι ≫ pullback.snd f f)
            (m.2.trans (by rw [Category.assoc, pullback.condition]))).base '' {w | W.ι.base w ∈
              U}))) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (jY : SchemeHomOver (X'.ι ≫ f) g) (e' : SchemeHomOver (pullback.snd g
        (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsOpenImmersion jY.1 ∧
      (∀ b : B, g.base b ≠ IsLocalRing.closedPoint R → b ∈ Set.range jY.1.base) ∧
      (∀ b : B, g.base b = IsLocalRing.closedPoint R →
        (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range jY.1.base) ∧
      IsIso e'.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y
            e')) ∧
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g (X'.ι ≫ f) jY) e' =
        NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
          (w : SchemeHomOver t (U.ι ≫ pullback.fst f f ≫ f)) (a b c : SchemeHomOver t (X'.ι ≫ f)),
        a.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.fst f f → b.1 ≫ X'.ι = w.1 ≫ U.ι ≫ pullback.snd f f →
        c.1 ≫ X'.ι = w.1 ≫ (pullback f f).homOfLE hUW ≫ m.1 →
        NeronModelInfra.schemeHomOverComp c jY =
          LB.mul t (NeronModelInfra.schemeHomOverComp a jY) (NeronModelInfra.schemeHomOverComp b
            jY)) := by
  obtain ⟨R', _, _, _, _, _, _, _, B', g', LB', jY', hg'₁, hg'₂, hg'₃, hg'₄, hjY', hjY'₁, hjY'₂,
    hres'⟩ :=
    exists_etale_groupLaw_of_dense_fibres
      K LXK f hXk e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂ X' U hUW hX'₁ hX'₂ hU₁ hU₂ hU₃
  have : Smooth g' := hg'₁
  have : IsSeparated g' := hg'₂
  have : LocallyOfFiniteType g' := hg'₃
  have : QuasiCompact g' := hg'₄
  have : IsOpenImmersion jY'.1 := hjY'
  exact
    exists_groupLaw_of_etale_groupLaw
      K LXK f hXk e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂ X' U hUW hX'₁ hX'₂ hU₁ hU₂ hU₃ R' g' LB' jY' hjY'₁
        hjY'₂ hres'

end NeronModelInfra
end
