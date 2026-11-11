/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Tactic.Choose
public import Nyll.AbelianVarieties.Geometry.AbelianSchemePullback
public import Nyll.AbelianVarieties.Geometry.Extensions
public import Nyll.AbelianVarieties.NeronModels.AbelianExtensions
public import Nyll.AbelianVarieties.NeronModels.Basic
public import Nyll.AbelianVarieties.NeronModels.GenericFibre
public import Nyll.AbelianVarieties.NeronModels.OpenExtensions
public import Nyll.AbelianVarieties.NeronModels.Uniqueness
public import Nyll.AbelianVarieties.Basic
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-! # The Néron mapping property from local extensions -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_neronUniqueExtension_of_forall_quasiCompact.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.MappingProperty.QuasiCompactTests


universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra

namespace Gluing
open _root_.NeronModelInfra

variable (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K]

/-- The generic-fibre map induced by a morphism over the base. -/
noncomputable def fibreShift {Y Y' : Scheme.{u}} (r : Y ⟶ Y')
    {tY' : Y' ⟶ Spec (CommRingCat.of R)} {tY : Y ⟶ Spec (CommRingCat.of R)} (hr : r ≫ tY' = tY) :
    pullback tY (specGenericFibreInclusion R K) ⟶ pullback tY' (specGenericFibreInclusion R K) :=
  pullback.lift (pullback.fst tY (specGenericFibreInclusion R K) ≫ r)
    (pullback.snd tY (specGenericFibreInclusion R K)) (by rw [Category.assoc, hr,
      pullback.condition])

@[reassoc (attr := simp)]
theorem fibreShift_fst {Y Y' : Scheme.{u}} (r : Y ⟶ Y')
    {tY' : Y' ⟶ Spec (CommRingCat.of R)} {tY : Y ⟶ Spec (CommRingCat.of R)} (hr : r ≫ tY' = tY) :
    fibreShift R K r hr ≫ pullback.fst tY' (specGenericFibreInclusion R K) =
      pullback.fst tY (specGenericFibreInclusion R K) ≫ r :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fibreShift_snd {Y Y' : Scheme.{u}} (r : Y ⟶ Y')
    {tY' : Y' ⟶ Spec (CommRingCat.of R)} {tY : Y ⟶ Spec (CommRingCat.of R)} (hr : r ≫ tY' = tY) :
    fibreShift R K r hr ≫ pullback.snd tY' (specGenericFibreInclusion R K) =
      pullback.snd tY (specGenericFibreInclusion R K) :=
  pullback.lift_snd _ _ _

theorem fibreShift_comp {Y Y' Y'' : Scheme.{u}} (r : Y ⟶ Y') (r' : Y' ⟶ Y'')
    {tY'' : Y'' ⟶ Spec (CommRingCat.of R)} {tY' : Y' ⟶ Spec (CommRingCat.of R)}
    {tY : Y ⟶ Spec (CommRingCat.of R)} (hr : r ≫ tY' = tY) (hr' : r' ≫ tY'' = tY') :
    fibreShift R K r hr ≫ fibreShift R K r' hr' =
      fibreShift R K (r ≫ r') (by rw [Category.assoc, hr', hr]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fibreShift_fst, fibreShift_fst_assoc]
  · simp only [Category.assoc, fibreShift_snd]

theorem fibreShift_congr {Y Y' : Scheme.{u}} {r r' : Y ⟶ Y'}
    {tY' : Y' ⟶ Spec (CommRingCat.of R)} {tY : Y ⟶ Spec (CommRingCat.of R)}
    (hrr : r = r') (hr : r ≫ tY' = tY) :
    fibreShift R K r hr = fibreShift R K r' (hrr ▸ hr) := by
  subst hrr; rfl

/-- Restriction of a model morphism to a chart over the base. -/
def chartRestrict {X T T' : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {s : T' ⟶ Spec (CommRingCat.of R)}
    (w : T' ⟶ T) (hs : w ≫ t = s) (φ : SchemeHomOver t fX) : SchemeHomOver s fX :=
  ⟨w ≫ φ.1, by rw [Category.assoc, φ.2, hs]⟩

@[scoped simp]
theorem chartRestrict_coe {X T T' : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {s : T' ⟶ Spec (CommRingCat.of R)} (w : T' ⟶ T) (hs : w ≫
      t = s)
    (φ : SchemeHomOver t fX) : (chartRestrict R fX w hs φ).1 = w ≫ φ.1 :=
  rfl

theorem genericFibreRestrict_chartRestrict {X T T' : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {s : T' ⟶ Spec (CommRingCat.of R)} (w : T' ⟶ T) (hs : w ≫
      t = s)
    (φ : SchemeHomOver t fX) :
    (genericFibreRestrict R K fX s (chartRestrict R fX w hs φ)).1 =
      fibreShift R K w hs ≫ (genericFibreRestrict R K fX t φ).1 := by
  apply pullback.hom_ext
  · simp only [genericFibreRestrict_coe_comp_fst, chartRestrict_coe, Category.assoc,
    fibreShift_fst_assoc]
  · simp only [genericFibreRestrict_coe_comp_snd, Category.assoc, fibreShift_snd]

theorem chartSolution_restrict_eq {X T Y Z : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} (w : Y ⟶ T)
    (ψ : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd fX (specGenericFibreInclusion R K)))
    (φw : SchemeHomOver (w ≫ t) fX)
    (hφw : (genericFibreRestrict R K fX (w ≫ t) φw).1 = fibreShift R K w rfl ≫ ψ.1)
    (r : Z ⟶ Y) (n : Z ⟶ T) (hn : r ≫ w = n) :
    (genericFibreRestrict R K fX (n ≫ t) (chartRestrict R fX r (by rw [← Category.assoc, hn])
      φw)).1 =
      fibreShift R K n rfl ≫ ψ.1 := by
  rw [genericFibreRestrict_chartRestrict, hφw, ← Category.assoc, fibreShift_comp,
    fibreShift_congr R K hn]

theorem exists_pulledChart_compare {T Y : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (w : Y ⟶
  T) :
    ∃ h : pullback (pullback.fst t (specGenericFibreInclusion R K)) w ⟶
        pullback (w ≫ t) (specGenericFibreInclusion R K),
      h ≫ pullback.fst (w ≫ t) (specGenericFibreInclusion R K) =
        pullback.snd (pullback.fst t (specGenericFibreInclusion R K)) w ∧
      h ≫ pullback.snd (w ≫ t) (specGenericFibreInclusion R K) =
        pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
          pullback.snd t (specGenericFibreInclusion R K) := by
  have hcond : pullback.snd (pullback.fst t (specGenericFibreInclusion R K)) w ≫ (w ≫ t) =
      (pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
        pullback.snd t (specGenericFibreInclusion R K)) ≫ specGenericFibreInclusion R K := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, pullback.condition, Category.assoc]
  exact ⟨pullback.lift _ _ hcond, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem pulledChart_fst_glue_eq {X T Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) (w : Y ⟶ T)
    (ψ : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd fX (specGenericFibreInclusion R K)))
    (φw : SchemeHomOver (w ≫ t) fX)
    (hφw : (genericFibreRestrict R K fX (w ≫ t) φw).1 = fibreShift R K w rfl ≫ ψ.1)
    (glue : T ⟶ X) (hglue : w ≫ glue = φw.1) :
    pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
        (pullback.fst t (specGenericFibreInclusion R K) ≫ glue) =
      pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
        (ψ.1 ≫ pullback.fst fX (specGenericFibreInclusion R K)) := by
  obtain ⟨h, hh1, hh2⟩ := exists_pulledChart_compare R K t w
  have hshift : h ≫ fibreShift R K w rfl = pullback.fst (pullback.fst t
    (specGenericFibreInclusion R K)) w := by
    apply pullback.hom_ext
    · rw [Category.assoc, fibreShift_fst, ← Category.assoc, hh1, ← pullback.condition]
    · rw [Category.assoc, fibreShift_snd, hh2]
  calc pullback.fst (pullback.fst t (specGenericFibreInclusion R K)) w ≫
        (pullback.fst t (specGenericFibreInclusion R K) ≫ glue)
      = (pullback.snd (pullback.fst t (specGenericFibreInclusion R K)) w ≫ w) ≫ glue := by
        rw [← Category.assoc, pullback.condition]
    _ = pullback.snd (pullback.fst t (specGenericFibreInclusion R K)) w ≫ φw.1 := by
        rw [Category.assoc, hglue]
    _ = h ≫ ((genericFibreRestrict R K fX (w ≫ t) φw).1 ≫
          pullback.fst fX (specGenericFibreInclusion R K)) := by
        rw [genericFibreRestrict_coe_comp_fst, ← Category.assoc, hh1]
    _ = (h ≫ fibreShift R K w rfl) ≫ (ψ.1 ≫ pullback.fst fX (specGenericFibreInclusion R K)) := by
        rw [hφw]; simp only [Category.assoc]
    _ = _ := by rw [hshift]

end Gluing

open Gluing in
theorem _root_.NeronModelInfra.neronUniqueExtension_of_forall_quasiCompact
    (R : Type u) [CommRing R] (K : Type u) [Field K] [Algebra R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : ∀ (T : Scheme.{u}) (t : T ⟶ Spec (CommRingCat.of R)), Smooth t → QuasiCompact t →
      Function.Bijective (genericFibreRestrict R K f t)) :
    NeronUniqueExtension R K f := by
  have hinj (Y : Scheme.{u}) (s : Y ⟶ Spec (CommRingCat.of R)) (hs : Smooth s) :
      Function.Injective (genericFibreRestrict R K f s) := by
    have : Smooth s := hs
    intro a b hab
    apply Subtype.ext
    apply Scheme.Cover.hom_ext Y.affineCover
    intro i
    have hsm : Smooth (Y.affineCover.f i ≫ s) := inferInstance
    have hqc : QuasiCompact (Y.affineCover.f i ≫ s) := inferInstance
    have hlocal :
        genericFibreRestrict R K f (Y.affineCover.f i ≫ s)
            (chartRestrict R f (Y.affineCover.f i) rfl a) =
          genericFibreRestrict R K f (Y.affineCover.f i ≫ s)
            (chartRestrict R f (Y.affineCover.f i) rfl b) := by
      apply Subtype.ext
      rw [genericFibreRestrict_chartRestrict, genericFibreRestrict_chartRestrict, hab]
    exact congrArg Subtype.val ((h _ (Y.affineCover.f i ≫ s) hsm hqc).injective hlocal)
  intro T t ht
  have : Smooth t := ht
  have hsm : ∀ i : T.affineCover.I₀, Smooth (T.affineCover.f i ≫ t) := fun i => inferInstance
  have hqc : ∀ i : T.affineCover.I₀, QuasiCompact (T.affineCover.f i ≫ t) := fun i => by
    infer_instance
  constructor
  · exact hinj T t ht
  · intro ψ
    choose φ hφ using fun i : T.affineCover.I₀ =>
      (h _ (T.affineCover.f i ≫ t) (hsm i) (hqc i)).surjective
        ⟨fibreShift R K (T.affineCover.f i) rfl ≫ ψ.1, by rw [Category.assoc, ψ.2, fibreShift_snd]⟩
    have hcompat : ∀ i j : T.affineCover.I₀,
        pullback.fst (T.affineCover.f i) (T.affineCover.f j) ≫ (φ i).1 =
          pullback.snd (T.affineCover.f i) (T.affineCover.f j) ≫ (φ j).1 := by
      intro i j
      let n : pullback (T.affineCover.f i) (T.affineCover.f j) ⟶ T := pullback.fst _ _ ≫
        T.affineCover.f i
      have : Smooth (n ≫ t) := inferInstance
      have e₁ := chartSolution_restrict_eq R K f (T.affineCover.f i) ψ (φ i) (congrArg
        Subtype.val (hφ i))
        (pullback.fst _ _) n rfl
      have hn₂ : pullback.snd (T.affineCover.f i) (T.affineCover.f j) ≫ T.affineCover.f j = n :=
        pullback.condition.symm
      have e₂ := chartSolution_restrict_eq R K f (T.affineCover.f j) ψ (φ j) (congrArg
        Subtype.val (hφ j))
        (pullback.snd _ _) n hn₂
      have key := hinj _ (n ≫ t) inferInstance (Subtype.ext (e₁.trans e₂.symm))
      simpa only [chartRestrict_coe] using congrArg Subtype.val key
    have hover : Scheme.Cover.glueMorphisms T.affineCover (fun i => (φ i).1) hcompat ≫ f = t := by
      apply Scheme.Cover.hom_ext T.affineCover
      intro i
      simp only [Scheme.Cover.ι_glueMorphisms_assoc]
      exact (φ i).2
    refine ⟨⟨Scheme.Cover.glueMorphisms T.affineCover (fun i => (φ i).1) hcompat, hover⟩, ?_⟩
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst]
      apply Scheme.Cover.hom_ext (Precoverage.ZeroHypercover.pullback₁
        (pullback.fst t (specGenericFibreInclusion R K)) T.affineCover)
      intro i
      exact pulledChart_fst_glue_eq R K f t (T.affineCover.f i) ψ (φ i) (congrArg Subtype.val
        (hφ i)) _
        (Scheme.Cover.ι_glueMorphisms _ _ hcompat i)
    · rw [genericFibreRestrict_coe_comp_snd, ψ.2]

end NeronModelInfra.MappingProperty.QuasiCompactTests
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_neronModelPropertyBundle_of_forall_nhds_twist_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.MappingProperty.TwistExtensions


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace Twists

open GoodReductionJacobian.AbelianSchemePropertyBundle.NGlue

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

variable {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem genericFibreRestrict_one (LB : RelativeGroupLaw R g) {Z : Scheme.{u}}
    (z : Z ⟶ Spec (CommRingCat.of R)) :
    genericFibreRestrict R K g z (LB.one z) =
      (LB.genericFibre K).one (pullback.snd z (specGenericFibreInclusion R K)) := by
  rw [RelativeGroupLaw.baseChange_one,
    ← LB.one_natural z _ (pullback.fst z (specGenericFibreInclusion R K)) pullback.condition]
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [genericFibreRestrict_coe_comp_fst, RelativeGroupLaw.baseChangePointOfBase_coe,
    pullback.lift_fst,
      GoodReductionJacobian.schemeHomOverComp_coe]
  · rw [genericFibreRestrict_coe_comp_snd, RelativeGroupLaw.baseChangePointOfBase_coe,
    pullback.lift_snd]

variable [Smooth g] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

omit [LocallyOfFiniteType g] in
theorem exists_extension (LB : RelativeGroupLaw R g)
    (htw : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
      (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
        (pullback.snd g (specGenericFibreInclusion R K)))
      (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R
        → y = η) →
      ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
        (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
          pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
              (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z)
              (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
              (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                ⟨pullback.snd z g, pullback.condition.symm⟩)).1)
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
      (pullback.snd g (specGenericFibreInclusion R K))) :
    ∃ u : SchemeHomOver z g, genericFibreRestrict R K g z u = uK := by
  let ι := specGenericFibreInclusion R K
  let T' := pullback z g
  let t' : T' ⟶ Spec (CommRingCat.of R) := pullback.fst z g ≫ z
  have : Smooth t' := inferInstance
  have : QuasiCompact t' := inferInstance
  let p₁ : SchemeHomOver t' z := ⟨pullback.fst z g, rfl⟩
  let p₂ : SchemeHomOver t' g := ⟨pullback.snd z g, pullback.condition.symm⟩
  let twistK : SchemeHomOver (pullback.snd t' ι) (pullback.snd g ι) :=
    (LB.genericFibre K).mul (pullback.snd t' ι)
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K z t' p₁) uK)
      (genericFibreRestrict R K g t' p₂)
  obtain ⟨V, v, hVη, hVs, hvK⟩ :=
    NeronModelInfra.exists_opens_extension_of_forall_nhds_extension R K g t' twistK (htw Z z uK)
  obtain ⟨W, d, hd⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension R LB t' V
      hVη hVs v
  obtain ⟨Φ, hΦ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension R
      LB t' V hVη
      hVs v W d hd
  have hgen : ∀ q : ↑(pullback t' ι), (pullback.fst t' ι).base q ∈ V := fun q =>
    hVη _ (by
      change (pullback.fst t' ι ≫ t').base q ≠ _
      rw [pullback.condition]
      exact specGenericFibreInclusion_base_ne_closedPoint R K ((pullback.snd t' ι) q))
  let ℓ : pullback t' ι ⟶ ↑V :=
    IsOpenImmersion.lift V.ι (pullback.fst t' ι) (by
      rintro _ ⟨q, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hgen q)
  have hℓ : ℓ ≫ V.ι = pullback.fst t' ι := IsOpenImmersion.lift_fac _ _ _
  let κ : pullback t' ι ⟶ pullback (V.ι ≫ t') ι :=
    pullback.lift ℓ (pullback.snd t' ι) (by rw [← Category.assoc, hℓ, pullback.condition])
  have hκ1 : κ ≫ pullback.fst (V.ι ≫ t') ι = ℓ := pullback.lift_fst _ _ _
  have hκ2 : κ ≫ pullback.snd (V.ι ≫ t') ι = pullback.snd t' ι := pullback.lift_snd _ _ _
  have hκ : κ ≫ pullback.map (V.ι ≫ t') ι t' ι V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.map, pullback.lift_fst, ← Category.assoc, hκ1, hℓ,
      Category.id_comp]
    · rw [Category.assoc, pullback.map, pullback.lift_snd, ← Category.assoc, hκ2, Category.id_comp,
        Category.comp_id]
  have hΦK : genericFibreRestrict R K g t' Φ = twistK := by
    have h1 : κ ≫ (genericFibreRestrict R K g (V.ι ≫ t') v).1 = (genericFibreRestrict R K g t'
      Φ).1 := by
      apply pullback.hom_ext
      · rw [Category.assoc, genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst,
          ← Category.assoc, hκ1, ← hΦ, ← Category.assoc, hℓ]
      · rw [Category.assoc, genericFibreRestrict_coe_comp_snd,
        genericFibreRestrict_coe_comp_snd, hκ2]
    apply Subtype.ext
    rw [← h1, hvK, ← Category.assoc, hκ, Category.id_comp]
  let sec : Z ⟶ T' := pullback.lift (𝟙 Z) (LB.one z).1 (by rw [Category.id_comp, (LB.one z).2])
  have hsec1 : sec ≫ pullback.fst z g = 𝟙 Z := pullback.lift_fst _ _ _
  have hsec2 : sec ≫ pullback.snd z g = (LB.one z).1 := pullback.lift_snd _ _ _
  have hsec : sec ≫ t' = z := by
    change sec ≫ pullback.fst z g ≫ z = z
    rw [← Category.assoc, hsec1, Category.id_comp]
  let s : SchemeHomOver z t' := ⟨sec, hsec⟩
  refine ⟨NeronModelInfra.schemeHomOverComp s Φ, ?_⟩
  rw [genericFibreRestrict_schemeHomOverComp, hΦK]
  let sK := genericFibreRestrict R K t' z s
  have hs1 : NeronModelInfra.schemeHomOverComp s p₁ = schemeHomOverId z := Subtype.ext hsec1
  have hs2 : NeronModelInfra.schemeHomOverComp s p₂ = LB.one z := Subtype.ext hsec2
  have hnat : NeronModelInfra.schemeHomOverComp sK twistK =
      GoodReductionJacobian.schemeHomOverComp sK.1 sK.2 twistK := Subtype.ext rfl
  rw [hnat]
  change GoodReductionJacobian.schemeHomOverComp sK.1 sK.2
      ((LB.genericFibre K).mul (pullback.snd t' ι)
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K z t' p₁) uK)
        (genericFibreRestrict R K g t' p₂)) = uK
  rw [(LB.genericFibre K).mul_natural]
  have e1 : GoodReductionJacobian.schemeHomOverComp sK.1 sK.2
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K z t' p₁) uK) = uK := by
    have : NeronModelInfra.schemeHomOverComp sK (genericFibreRestrict R K z t' p₁) =
        schemeHomOverId (pullback.snd z ι) := by
      rw [← genericFibreRestrict_schemeHomOverComp, hs1, genericFibreRestrict_schemeHomOverId]
    apply Subtype.ext
    change sK.1 ≫ (genericFibreRestrict R K z t' p₁).1 ≫ uK.1 = uK.1
    have h2 := congrArg Subtype.val this
    rw [NeronModelInfra.schemeHomOverComp_coe, schemeHomOverId_coe] at h2
    rw [← Category.assoc, h2, Category.id_comp]
  have e2 : GoodReductionJacobian.schemeHomOverComp sK.1 sK.2 (genericFibreRestrict R K g t' p₂) =
      (LB.genericFibre K).one (pullback.snd z ι) := by
    have : NeronModelInfra.schemeHomOverComp sK (genericFibreRestrict R K g t' p₂) =
        genericFibreRestrict R K g z (LB.one z) := by
      rw [← genericFibreRestrict_schemeHomOverComp, hs2]
    rw [genericFibreRestrict_one K LB z] at this
    rw [← this]
    exact Subtype.ext rfl
  rw [e1, e2, (LB.genericFibre K).mul_one]

theorem main (LB : RelativeGroupLaw R g)
    (htw : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
      (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
        (pullback.snd g (specGenericFibreInclusion R K)))
      (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R
        → y = η) →
      ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
        (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
          pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
              (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z)
              (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
              (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                ⟨pullback.snd z g, pullback.condition.symm⟩)).1) :
    NeronModelPropertyBundle R K g where
  smooth := inferInstance
  separated := inferInstance
  locallyOfFiniteType := inferInstance
  quasiCompact := inferInstance
  neronMapping := by
    apply NeronModelInfra.neronUniqueExtension_of_forall_quasiCompact R K g
    intro T t ht hqc
    have : Smooth t := ht
    have : QuasiCompact t := hqc
    refine ⟨NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K g t, fun
      uK => ?_⟩
    exact exists_extension K LB htw t uK

end Twists

theorem _root_.NeronModelInfra.neronModelPropertyBundle_of_forall_nhds_twist_extension
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)}
    [Smooth g] [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (LB : RelativeGroupLaw R g)
    (htw : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
      (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
        (pullback.snd g (specGenericFibreInclusion R K)))
      (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R
        → y = η) →
      ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
        (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
          pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
              (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z)
              (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
              (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                ⟨pullback.snd z g, pullback.condition.symm⟩)).1) :
    NeronModelPropertyBundle R K g :=
  Twists.main K LB htw

end NeronModelInfra.MappingProperty.TwistExtensions
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.MappingProperty.AbelianModels


universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem _root_.NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f) :
    NeronModelInfra.NeronModelPropertyBundle R K f := by
  have : IsProper f := hA.proper
  have hsep : IsSeparated f := inferInstance
  refine ⟨hA.smooth, hsep, inferInstance, inferInstance, ?_⟩
  refine neronUniqueExtension_of_forall_quasiCompact R K f fun T t ht hqc => ?_
  have : Smooth t := ht
  have : QuasiCompact t := hqc
  have : Flat t := inferInstance
  exact ⟨genericFibreRestrict_injective_of_flat_of_isSeparated R K f t,
    hA.genericFibreRestrict_surjective_of_quasiCompact R K t⟩

end NeronModelInfra.MappingProperty.AbelianModels
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_NeronModelPropertyBundle_isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra.MappingProperty.OpenAbelianModels


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace OpenModels



section GenericFibre

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
  {B U : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {gU : U ⟶ Spec (CommRingCat.of R)}

theorem isOpenImmersion_genericFibreRestrict (u : SchemeHomOver gU g) [IsOpenImmersion u.1] :
    IsOpenImmersion (genericFibreRestrict R K g gU u).1 := by
  rw [genericFibreRestrict_coe_eq_pullbackMap g gU u (by rw [Category.comp_id, u.2])
    (by rw [Category.comp_id, Category.id_comp])]
  infer_instance

theorem isClosed_range_genericFibreRestrict (u : SchemeHomOver gU g) [IsProper gU]
    [IsSeparated g] :
    IsClosed (Set.range (genericFibreRestrict R K g gU u).1.base) := by
  have : IsProper ((genericFibreRestrict R K g gU u).1 ≫
      pullback.snd g (specGenericFibreInclusion R K)) := by
    rw [(genericFibreRestrict R K g gU u).2]; infer_instance
  have : IsProper (genericFibreRestrict R K g gU u).1 :=
    IsProper.of_comp _ (pullback.snd g (specGenericFibreInclusion R K))
  exact (genericFibreRestrict R K g gU u).1.isClosedMap.isClosed_range

theorem nonempty_genericFibre (L : RelativeGroupLaw R gU) :
    Nonempty ↥(pullback gU (specGenericFibreInclusion R K)) := by
  let e := L.one (specGenericFibreInclusion R K)
  let pt : Spec (CommRingCat.of K) ⟶ pullback gU (specGenericFibreInclusion R K) :=
    pullback.lift e.1 (𝟙 _) (by rw [e.2, Category.id_comp])
  exact ⟨pt.base (IsLocalRing.closedPoint K)⟩

end GenericFibre

section Main

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {B U : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {gU : U ⟶ Spec (CommRingCat.of R)}

theorem isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
    (hN : NeronModelPropertyBundle R K g)
    [PreconnectedSpace ↥(pullback g (specGenericFibreInclusion R K))]
    (i : U ⟶ B) [IsOpenImmersion i] (hi : i ≫ g = gU)
    (hU : AbelianSchemePropertyBundle R gU) :
    IsIso i ∧ AbelianSchemePropertyBundle R g := by
  have hNU : NeronModelPropertyBundle R K gU :=
    NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle R K hU
  have : IsProper gU := hU.proper
  have : IsSeparated g := hN.separated
  obtain ⟨LU⟩ := hU.hasGroupLaw
  let u : SchemeHomOver gU g := ⟨i, hi⟩
  have : IsOpenImmersion u.1 := ‹IsOpenImmersion i›
  let uK := genericFibreRestrict R K g gU u
  have hopen : IsOpenImmersion uK.1 := isOpenImmersion_genericFibreRestrict K u
  have hclopen : IsClopen (Set.range uK.1.base) :=
    ⟨isClosed_range_genericFibreRestrict K u, uK.1.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range uK.1.base).Nonempty := by
    obtain ⟨p⟩ := nonempty_genericFibre K LU
    exact ⟨uK.1.base p, p, rfl⟩
  have hrange : Set.range uK.1.base = Set.univ := by
    rcases isClopen_iff.mp hclopen with h | h
    · exact absurd h hne.ne_empty
    · exact h
  have : Epi uK.1.base := by
    rw [TopCat.epi_iff_surjective, ← Set.range_eq_univ]
    exact hrange
  have hisoK : IsIso uK.1 := IsOpenImmersion.isIso uK.1
  let vK : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K))
      (pullback.snd gU (specGenericFibreInclusion R K)) :=
    ⟨inv uK.1, by rw [IsIso.inv_comp_eq, uK.2]⟩
  have hiso : IsIso u.1 :=
    neronTwoModels_isoExtension_isIso (K := K) hNU.neronMapping hN.neronMapping hU.smooth
      hN.smooth vK (IsIso.hom_inv_id uK.1) (IsIso.inv_hom_id uK.1) (u := u) rfl
  have : IsIso i := hiso
  have hsq : IsPullback (inv i) g gU (𝟙 (Spec (CommRingCat.of R))) := by
    apply IsPullback.of_horiz_isIso
    constructor
    rw [Category.comp_id, IsIso.inv_comp_eq, hi]
  exact ⟨hiso, hU.of_isPullback hsq⟩

end Main

end OpenModels

end NeronModelInfra.MappingProperty.OpenAbelianModels

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open NeronModelInfra.MappingProperty.OpenAbelianModels

namespace NeronModelInfra.NeronModelPropertyBundle

universe u

theorem isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B U : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {gU : U ⟶ Spec (CommRingCat.of R)}
    (hN : NeronModelPropertyBundle R K g)
    [PreconnectedSpace ↥(pullback g (specGenericFibreInclusion R K))]
    (i : U ⟶ B) [IsOpenImmersion i] (hi : i ≫ g = gU)
    (hU : AbelianSchemePropertyBundle R gU) :
    IsIso i ∧ AbelianSchemePropertyBundle R g :=
  OpenModels.isIso_and_abelianSchemePropertyBundle_of_isOpenImmersion K hN i hi hU

end NeronModelInfra.NeronModelPropertyBundle
end
