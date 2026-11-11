/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Sober
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.AbelianVarieties.NeronModels.StalkExtensions
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.Gluing.OpenSubschemes
public import Nyll.SchemeTheory.Morphisms.SectionRigidity
public import Nyll.SchemeTheory.LocalGeometry.OpenIrreducibleComponents
public import Nyll.SchemeTheory.LocalGeometry.SmoothNormalStalk
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-! # Neighborhood extensions from models catching index-one points -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_nhds_extension_chart_of_catchesIndexOnePoints.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace LocalExtensionCharts

theorem isDominant_of_genericPoint_mem {X Y : Scheme.{u}} [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : genericPoint Y ∈ Set.range f.base) : IsDominant f := by
  refine ⟨?_⟩
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  have hc : closure ({genericPoint Y} : Set Y) = (⊤ : Set Y) := genericPoint_spec Y
  rw [Set.top_eq_univ] at hc
  rw [← hc]
  exact closure_mono (Set.singleton_subset_iff.mpr h)

end LocalExtensionCharts

theorem exists_nhds_extension_chart_of_catchesIndexOnePoints
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {AK : Scheme.{u}} {gK : AK ⟶ Spec (CommRingCat.of K)} [IsSeparated gK]
    (M : ModelFamily R K gK) (hM : ∀ i, LocallyOfFiniteType (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (ζ : Z) (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hmax : ∀ y : Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ) :
    ∃ (i : M.ι) (U : Z.Opens) (_ : ζ ∈ U) (u : SchemeHomOver (U.ι ≫ z) (M.str i)),
      (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K (M.str i) (U.ι ≫ z) u)
        (M.chart i)).1 =
        pullback.map (U.ι ≫ z) (specGenericFibreInclusion R K) z (specGenericFibreInclusion R K)
          U.ι (𝟙 _)
          (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            uK.1 := by
  classical
  let g : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤ (z.base
      ζ) trivial
  let φc : CommRingCat.of R ⟶ Z.presheaf.stalk ζ := g ≫ z.stalkMap ζ
  let algRO : Algebra R (Z.presheaf.stalk ζ) := φc.hom.toAlgebra
  have hfac : Z.fromSpecStalk ζ ≫ z = Spec.map φc := by
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk z, Spec.fromSpecStalk_eq]
  have halg : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R
    (Z.presheaf.stalk ζ))) := by
    rw [hfac]; rfl
  obtain ⟨hdom, hdvr, hloc, hidx⟩ :=
    NeronModelInfra.isIndexOneExtension_stalk_of_smooth_of_forall_specializes z ζ hζ hmax halg
  have : IsDomain (Z.presheaf.stalk ζ) := hdom
  have : IsDiscreteValuationRing (Z.presheaf.stalk ζ) := hdvr
  have : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ)) := hloc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have hne0 : algebraMap R (Z.presheaf.stalk ζ) ϖ ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field (Z.presheaf.stalk ζ)
    rw [← hidx.map_maximalIdeal, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.map_span,
      Set.image_singleton, h0, Ideal.span_singleton_eq_bot]
  have hinj : Function.Injective (algebraMap R (Z.presheaf.stalk ζ)) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    have : (RingHom.ker (algebraMap R (Z.presheaf.stalk ζ))).IsPrime := RingHom.ker_isPrime _
    have hmax' := Ring.DimensionLEOne.maximalOfPrime hker this
    have : ϖ ∈ RingHom.ker (algebraMap R (Z.presheaf.stalk ζ)) := by
      rw [IsLocalRing.eq_maximalIdeal hmax']; exact hϖm
    exact hne0 this
  have hinjK : Function.Injective (algebraMap R (FractionRing (Z.presheaf.stalk ζ))) := by
    rw [IsScalarTower.algebraMap_eq R (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ))]
    exact (IsFractionRing.injective (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk
      ζ))).comp hinj
  let algKK : Algebra K (FractionRing (Z.presheaf.stalk ζ)) := (IsFractionRing.lift
    hinjK).toAlgebra
  have : IsScalarTower R K (FractionRing (Z.presheaf.stalk ζ)) :=
    IsScalarTower.of_algebraMap_eq fun r => (IsFractionRing.lift_algebraMap hinjK r).symm
  let xZ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ)))) z :=
    ⟨Z.fromSpecStalk ζ, halg⟩
  obtain ⟨i, x, hx⟩ := hpts (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ)) hidx
    (schemeHomOverComp (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) xZ)
      uK)
  have : LocallyOfFiniteType (M.str i) := hM i
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  obtain ⟨U, hζU, v, hv, hvx⟩ :=
    AlgebraicGeometry.Scheme.exists_opens_extension_of_fromSpecStalk z (M.str i) ζ x.1
      (x.2.trans halg.symm)
  have hstalk : ∀ y : Z, IsDomain (Z.presheaf.stalk y) := fun y =>
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      z y).1
  have : IsReduced Z := by
    have : ∀ y : Z, _root_.IsReduced (Z.presheaf.stalk y) := fun y =>
      have : IsDomain (Z.presheaf.stalk y) := hstalk y
      inferInstance
    exact isReduced_of_isReduced_stalk Z
  obtain ⟨hCopen, -⟩ := AlgebraicGeometry.isOpen_irreducibleComponent_of_isDomain_stalk hstalk ζ
  let C : Z.Opens := ⟨irreducibleComponent ζ, hCopen⟩
  let U' : Z.Opens := U ⊓ C
  have hζU' : ζ ∈ U' := ⟨hζU, mem_irreducibleComponent⟩
  have hqs : QuasiSober (U' : Set Z) := U'.isOpen.isOpenEmbedding_subtypeVal.quasiSober
  have hirr : IrreducibleSpace (U' : Set Z) := by
    refine Subtype.irreducibleSpace ⟨⟨ζ, hζU'⟩, ?_⟩
    exact isIrreducible_irreducibleComponent.isPreirreducible.open_subset U'.isOpen (fun y hy =>
      hy.2)
  have hqs' : QuasiSober (U' : Scheme.{u}) := hqs
  have hirr' : IrreducibleSpace (U' : Scheme.{u}) := hirr
  let v' : (U' : Scheme.{u}) ⟶ M.X i := Z.homOfLE inf_le_left ≫ v
  have hv' : v' ≫ M.str i = U'.ι ≫ z := by
    rw [Category.assoc, hv, ← Category.assoc, Scheme.homOfLE_ι]
  have hvx' : U'.fromSpecStalkOfMem ζ hζU' ≫ v' = x.1 := by
    rw [← hvx, ← Category.assoc]
    congr 1
    rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  refine ⟨i, U', hζU', ⟨v', hv'⟩, ?_⟩
  have : IsOpenImmersion (specGenericFibreInclusion R K) := inferInstance
  have : IsReduced (U' : Scheme.{u}) := isReduced_of_isOpenImmersion U'.ι
  have : IsReduced (pullback (U'.ι ≫ z) (specGenericFibreInclusion R K)) :=
    isReduced_of_isOpenImmersion (pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K))
  let xU : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ))))
    (U'.ι ≫ z) :=
    ⟨U'.fromSpecStalkOfMem ζ hζU', by
      rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
      exact halg⟩
  let ιK := (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) xU).1
  have hdomO : IsDominant (U'.fromSpecStalkOfMem ζ hζU') := by
    apply LocalExtensionCharts.isDominant_of_genericPoint_mem
    have hsp : (U'.ι).base (genericPoint (U' : Scheme.{u})) ⤳ ζ :=
      (genericPoint_specializes (⟨ζ, hζU'⟩ : (U' : Scheme.{u}))).map U'.ι.base.hom.continuous
    have hmem : (U'.ι).base (genericPoint (U' : Scheme.{u})) ∈ Set.range (Z.fromSpecStalk
      ζ).base := by
      rw [Scheme.range_fromSpecStalk]; exact hsp
    obtain ⟨q, hq⟩ := hmem
    refine ⟨q, ?_⟩
    apply U'.ι.isOpenEmbedding.injective
    rw [← hq, ← Scheme.Hom.comp_apply, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hdomK : IsDominant (Spec.map (CommRingCat.ofHom
      (algebraMap (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ))))) := by
    apply LocalExtensionCharts.isDominant_of_genericPoint_mem
    refine ⟨IsLocalRing.closedPoint _, ?_⟩
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap (Z.presheaf.stalk ζ) (FractionRing (Z.presheaf.stalk ζ)))
      (IsLocalRing.maximalIdeal (FractionRing (Z.presheaf.stalk ζ))) = ⊥
    have hm : IsLocalRing.maximalIdeal (FractionRing (Z.presheaf.stalk ζ)) = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    rw [hm, ← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective (Z.presheaf.stalk ζ) _)]
  have : IsDominant ιK := by
    have hcomp : ιK ≫ pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K) =
        Spec.map (CommRingCat.ofHom (algebraMap (Z.presheaf.stalk ζ) (FractionRing
          (Z.presheaf.stalk ζ)))) ≫
          U'.fromSpecStalkOfMem ζ hζU' :=
      pointGenericFibre_coe_comp_fst xU
    have : IsDominant (ιK ≫ pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K)) := by
      rw [hcomp]; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion ιK (pullback.fst (U'.ι ≫ z)
      (specGenericFibreInclusion R K))
  have hxval : (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) x).1 ≫
    (M.chart i).1 =
      (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) xZ).1 ≫ uK.1 :=
    congrArg Subtype.val hx
  have hleft : ιK ≫ (genericFibreRestrict R K (M.str i) (U'.ι ≫ z) ⟨v', hv'⟩).1 =
      (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) x).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc]
      simp only [genericFibreRestrict, pullback.lift_fst]
      rw [← Category.assoc, show ιK ≫ pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K) =
        _ from
        pointGenericFibre_coe_comp_fst xU, pointGenericFibre_coe_comp_fst x, Category.assoc, hvx']
    · rw [Category.assoc]
      simp only [genericFibreRestrict, pullback.lift_snd]
      rw [show ιK ≫ pullback.snd (U'.ι ≫ z) (specGenericFibreInclusion R K) = _ from
        pointGenericFibre_coe_comp_snd xU, pointGenericFibre_coe_comp_snd x]
  have hright : ιK ≫ pullback.map (U'.ι ≫ z) (specGenericFibreInclusion R K) z
    (specGenericFibreInclusion R K) U'.ι
      (𝟙 _) (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
      (pointGenericFibre (K := K) (K' := FractionRing (Z.presheaf.stalk ζ)) xZ).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        show ιK ≫ pullback.fst (U'.ι ≫ z) (specGenericFibreInclusion R K) = _ from
          pointGenericFibre_coe_comp_fst xU,
        pointGenericFibre_coe_comp_fst xZ, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
        show ιK ≫ pullback.snd (U'.ι ≫ z) (specGenericFibreInclusion R K) = _ from
          pointGenericFibre_coe_comp_snd xU,
        pointGenericFibre_coe_comp_snd xZ, Category.comp_id]
  apply ext_of_isDominant_of_isSeparated gK ?_ ιK ?_
  · rw [(schemeHomOverComp (genericFibreRestrict R K (M.str i) (U'.ι ≫ z) ⟨v', hv'⟩) (M.chart
    i)).2,
      Category.assoc, uK.2, pullback.lift_snd, Category.comp_id]
  · rw [schemeHomOverComp_coe, ← Category.assoc, hleft, hxval, ← Category.assoc, hright]

end NeronModelInfra
end
