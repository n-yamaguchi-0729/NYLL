/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.Choose
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.AbelianVarieties.NeronModels.GenericFibre
public import Nyll.AbelianVarieties.NeronModels.GroupLaw
public import Nyll.AbelianVarieties.NeronModels.MappingProperty
public import Nyll.AbelianVarieties.NeronModels.ModelFamilies
public import Nyll.AbelianVarieties.NeronModels.Smoothening.Iteration
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.AbelianVarieties.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.AbelianVarieties.Geometry.AbelianSchemeGeometricallyIntegral
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-! # Existence of the Néron model of an abelian variety -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.Existence


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace SmoothModelFamilies

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)}

/-- The induced map on the generic fibres of a model and its refinement. -/
noncomputable abbrev gfMap {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    pullback (u ≫ f) (specGenericFibreInclusion R K) ⟶ pullback f (specGenericFibreInclusion R
      K) :=
  pullback.map (u ≫ f) (specGenericFibreInclusion R K) f (specGenericFibreInclusion R K) u
    (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc]
theorem gfMap_snd {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    gfMap K f u ≫ pullback.snd f (specGenericFibreInclusion R K) =
      pullback.snd (u ≫ f) (specGenericFibreInclusion R K) := by
  rw [pullback.lift_snd, Category.comp_id]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
@[reassoc]
theorem gfMap_fst {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (u : X' ⟶ X) :
    gfMap K f u ≫ pullback.fst f (specGenericFibreInclusion R K) =
      pullback.fst (u ≫ f) (specGenericFibreInclusion R K) ≫ u :=
  pullback.lift_fst _ _ _

theorem exists_smooth_modelFamily [Smooth gK]
    (M₀ : ModelFamily R K gK) (hfin : Finite M₀.ι)
    (hM₀ : ∀ i, IsSeparated (M₀.str i) ∧ LocallyOfFiniteType (M₀.str i) ∧ QuasiCompact (M₀.str i))
    (hpts : M₀.CatchesIndexOnePoints) :
    ∃ M : ModelFamily R K gK, Finite M.ι ∧
      (∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
        QuasiCompact (M.str i)) ∧
      M.CatchesIndexOnePoints := by
  classical
  have hK : ∀ i, Smooth (pullback.snd (M₀.str i) (specGenericFibreInclusion R K)) := fun i => by
    rw [← (M₀.chart i).2]
    infer_instance
  have H : ∀ i, ∃ (X' : Scheme.{u}) (u : X' ⟶ M₀.X i),
      Smooth (u ≫ M₀.str i) ∧ QuasiCompact (u ≫ M₀.str i) ∧ IsSeparated u ∧
      IsIso (gfMap K (M₀.str i) u) ∧
      ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
        [IsLocalHom (algebraMap R R')], IsIndexOneExtension R R' →
        ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (M₀.str i),
          ∃ x' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (u ≫ M₀.str i),
            x'.1 ≫ u = x.1 := fun i => by
    have : LocallyOfFiniteType (M₀.str i) := (hM₀ i).2.1
    have : QuasiCompact (M₀.str i) := (hM₀ i).2.2
    exact NeronModelInfra.exists_smooth_hom_isIso_genericFibre_lift_of_isIndexOneExtension K
      (M₀.str i) (hK i)
  choose X' u hsm hqc hsep hiso hlift using H
  let M : ModelFamily R K gK :=
    { ι := M₀.ι
      X := X'
      str := fun i => u i ≫ M₀.str i
      chart := fun i => NeronModelInfra.schemeHomOverComp ⟨gfMap K (M₀.str i) (u i), gfMap_snd K
        (M₀.str i) (u i)⟩ (M₀.chart i)
      isOpenImmersion_chart := fun i => by
        have : IsIso (gfMap K (M₀.str i) (u i)) := hiso i
        change IsOpenImmersion (gfMap K (M₀.str i) (u i) ≫ (M₀.chart i).1)
        infer_instance }
  refine ⟨M, hfin, fun i => ?_, ?_⟩
  · have : Smooth (u i ≫ M₀.str i) := hsm i
    have : QuasiCompact (u i ≫ M₀.str i) := hqc i
    have : IsSeparated (u i) := hsep i
    have : IsSeparated (M₀.str i) := (hM₀ i).1
    refine ⟨hsm i, ?_, ?_, hqc i⟩
    · change IsSeparated (u i ≫ M₀.str i); infer_instance
    · change LocallyOfFiniteType (u i ≫ M₀.str i); infer_instance
  · intro R' _ _ _ _ _ K' _ _ _ _ _ _ _ hidx a
    obtain ⟨i, x, hx⟩ := hpts R' K' hidx a
    obtain ⟨x', hx'⟩ := hlift i R' hidx x
    refine ⟨i, x', ?_⟩
    rw [← hx]
    apply Subtype.ext
    change (pointGenericFibre (K := K) (K' := K') x').1 ≫ gfMap K (M₀.str i) (u i) ≫ (M₀.chart
      i).1 =
      (pointGenericFibre (K := K) (K' := K') x).1 ≫ (M₀.chart i).1
    rw [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, gfMap_fst, ← Category.assoc, pointGenericFibre_coe_comp_fst,
      Category.assoc, hx',
        pointGenericFibre_coe_comp_fst]
    · rw [Category.assoc, gfMap_snd, pointGenericFibre_coe_comp_snd,
      pointGenericFibre_coe_comp_snd]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem isCommutative_genericFibre
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g) (LAK :
      RelativeGroupLaw K gK)
    (hc : LAK.IsCommutative)
    (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (hemul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
      NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
        LAK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y
          e)) :
    (LB.genericFibre K).IsCommutative := by
  intro T t x y
  have h := hemul t x y
  rw [hc, ← hemul t y x] at h
  apply Subtype.ext
  rw [← cancel_mono e.1]
  exact congrArg (fun s => s.1) h

end SmoothModelFamilies

end NeronModelInfra.Existence

namespace GoodReductionJacobian.RelativeGroupLaw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra
open GoodReductionJacobian

universe u

open NeronModelInfra.Existence.SmoothModelFamilies in
theorem exists_neronModel_of_abelian_variety
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} (LAK : RelativeGroupLaw K gK)
    (hAK : AbelianSchemePropertyBundle K gK) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      NeronModelPropertyBundle R K g ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
        LB.mul t x y = LB.mul t y x) ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
          LAK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y
            e)) := by
  have : IsProper gK := hAK.proper
  have : Smooth gK := hAK.smooth
  have : GeometricallyIntegral gK := hAK.geometricallyIntegral
  have hc : LAK.IsCommutative :=
    GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isProper_of_geometricallyIntegral LAK
  obtain ⟨M₀, hfin₀, hM₀, hpts₀⟩ :=
    NeronModelInfra.exists_modelFamily_finite_catchesIndexOnePoints_of_isProper (R := R) K gK
  obtain ⟨M, hfin, hM, hpts⟩ := exists_smooth_modelFamily K M₀ hfin₀
    (fun i => ⟨(hM₀ i).2.1, (hM₀ i).2.2.2.1, (hM₀ i).2.2.2.2⟩) hpts₀
  obtain ⟨B, g, LB, e, hsm, hsep, hloft, hqc, he, hemul, htw⟩ :=
    NeronModelInfra.exists_groupLaw_with_translation_extensions
      (R := R) K LAK hc M hfin hM hpts
  have : Smooth g := hsm
  have : IsSeparated g := hsep
  have : LocallyOfFiniteType g := hloft
  have : QuasiCompact g := hqc
  have : IsIso e.1 := he
  refine ⟨B, g, LB, e, ?_, ?_, he, hemul⟩
  · exact NeronModelInfra.neronModelPropertyBundle_of_forall_nhds_twist_extension K LB htw
  · have hgen : (LB.genericFibre K).IsCommutative := isCommutative_genericFibre K LB LAK hc e hemul
    have hLB : LB.IsCommutative :=
      GoodReductionJacobian.RelativeGroupLaw.isCommutative_of_isCommutative_genericFibre K LB hgen
    intro T t x y
    exact hLB t x y

end GoodReductionJacobian.RelativeGroupLaw
end
