/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Set
public import Nyll.AbelianVarieties.Geometry.GroupLaw
public import Nyll.AbelianVarieties.NeronModels.Density
public import Nyll.AbelianVarieties.NeronModels.Differentials.ComponentData
public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.SchemeTheory.LocalGeometry.Normality
public import Nyll.SchemeTheory.BaseChange.PullbackIsomorphisms
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.LocalGeometry.SmoothDVRStalk
public import Nyll.SchemeTheory.LocalGeometry.SmoothNormalStalk
public import Nyll.SchemeTheory.LocalGeometry.SmoothStalks
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Functoriality.AffinePullbackSections
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Local extension comparisons at model stalks

Specializations in a fiber product, generic-fiber images, and smooth codimension-one
stalks provide the local comparisons used to extend translations between models.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.SpecializationSlices

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

universe u

namespace SpecializationSlice

theorem flat_SpecMap_of_field {k L : Type u} [Field k] [Field L]
    (φ : CommRingCat.of k ⟶ CommRingCat.of L) :
    Flat (Spec.map φ) := by
  rw [Flat.SpecMap_iff]
  let : Algebra k L := φ.hom.toAlgebra
  change Module.Flat k L
  infer_instance

theorem main
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (θ : ↑(pullback f f)) (hθ : f.base ((pullback.fst f f).base θ) = IsLocalRing.closedPoint R)
    (y : X) (hy : y ⤳ (pullback.snd f f).base θ) (hys : f.base y = IsLocalRing.closedPoint R) :
    ∃ θ' : ↑(pullback f f), θ' ⤳ θ ∧ (pullback.fst f f).base θ' = (pullback.fst f f).base θ ∧
      (pullback.snd f f).base θ' = y := by
  set a : X := (pullback.fst f f).base θ with ha
  set s : ↑(Spec (CommRingCat.of R)) := f.base a with hs
  let ιa : Spec (X.residueField a) ⟶ X := X.fromSpecResidueField a
  let ιs : Spec ((Spec (CommRingCat.of R)).residueField s) ⟶ Spec (CommRingCat.of R) :=
    (Spec (CommRingCat.of R)).fromSpecResidueField s
  let r := f.residueFieldMap a
  have hr : Spec.map r ≫ ιs = ιa ≫ f := f.SpecMap_residueFieldMap_fromSpecResidueField a
  have : Flat (Spec.map r) := flat_SpecMap_of_field r
  let jXs : pullback ιs f ⟶ X := pullback.snd ιs f
  let E := pullback (Spec.map r) (pullback.fst ιs f)
  let g₂ : E ⟶ pullback ιs f := pullback.snd (Spec.map r) (pullback.fst ιs f)
  have : Flat g₂ := inferInstance
  let iso : E ≅ pullback (Spec.map r ≫ ιs) f := pullbackRightPullbackFstIso ιs f (Spec.map r)
  let ψ₀ : pullback (Spec.map r ≫ ιs) f ⟶ pullback f f :=
    pullback.map (Spec.map r ≫ ιs) f f f ιa (𝟙 X) (𝟙 _) (by rw [hr, Category.comp_id])
      (by rw [Category.comp_id, Category.id_comp])
  let ψ : E ⟶ pullback f f := iso.hom ≫ ψ₀
  have hψsnd : ψ ≫ pullback.snd f f = g₂ ≫ jXs := by
    simp only [ψ, ψ₀, Category.assoc, pullback.lift_snd, Category.comp_id]
    exact pullbackRightPullbackFstIso_hom_snd ιs f (Spec.map r)
  have hψfst : ψ ≫ pullback.fst f f = (iso.hom ≫ pullback.fst _ _) ≫ ιa := by
    simp only [ψ, ψ₀, Category.assoc, pullback.lift_fst]
  have hrangeψ₀ : Set.range ψ₀.base = {q | (pullback.fst f f).base q = a} := by
    have h := Scheme.Pullback.range_map (Spec.map r ≫ ιs) f f f ιa (𝟙 X) (𝟙 _)
      (by rw [hr, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
    rw [h]
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, ιa,
        Scheme.range_fromSpecResidueField,
      Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · intro hq; exact ⟨hq, ⟨(pullback.snd f f).base q, rfl⟩⟩
  have hrangeψ : Set.range ψ.base = {q | (pullback.fst f f).base q = a} := by
    rw [← hrangeψ₀]
    change Set.range ((iso.hom ≫ ψ₀).base) = _
    have : Set.range ((iso.hom ≫ ψ₀).base) = ψ₀.base '' Set.range iso.hom.base := by
      rw [← Set.range_comp]; rfl
    rw [this, (show Function.Surjective iso.hom.base from
        (Scheme.homeoOfIso iso).surjective).range_eq,
      Set.image_univ]
  obtain ⟨θ₁, hθ₁⟩ : θ ∈ Set.range ψ.base := by rw [hrangeψ]; exact ha.symm
  have hrange_jXs : Set.range jXs.base = {x | f.base x = s} := by
    change Set.range (pullback.snd ιs f).base = _
    rw [Scheme.Pullback.range_snd]
    ext x
    simp only [ιs, Set.mem_preimage, Scheme.range_fromSpecResidueField, Set.mem_singleton_iff,
        Set.mem_ofPred_eq]
  have hys' : f.base y = s := by rw [hys]; exact hθ.symm
  obtain ⟨y₁, rfl⟩ : y ∈ Set.range jXs.base := by rw [hrange_jXs]; exact hys'
  have hsndθ : (pullback.snd f f).base θ = jXs.base (g₂.base θ₁) := by
    rw [← hθ₁, ← Scheme.Hom.comp_apply, hψsnd, Scheme.Hom.comp_apply]
  have hy₁ : y₁ ⤳ g₂.base θ₁ := by
    rw [← jXs.isEmbedding.isInducing.specializes_iff, ← hsndθ]
    exact hy
  obtain ⟨ε, hεθ₁, hεy⟩ := Flat.generalizingMap g₂ hy₁
  refine ⟨ψ.base ε, ?_, ?_, ?_⟩
  · rw [← hθ₁]; exact hεθ₁.map ψ.continuous
  · have h1 : ψ.base ε ∈ Set.range ψ.base := ⟨ε, rfl⟩
    rw [hrangeψ] at h1
    exact h1
  · rw [← Scheme.Hom.comp_apply, hψsnd, Scheme.Hom.comp_apply, hεy]

end SpecializationSlice

end
end AbelianVarieties.NOSProofs.SpecializationSlices

namespace NeronModelInfra

noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)
open AbelianVarieties.NOSProofs.SpecializationSlices

theorem exists_specializes_fst_eq_snd_eq_of_specializes_snd
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (θ : ↑(pullback f f)) (hθ : f.base ((pullback.fst f f).base θ) = IsLocalRing.closedPoint R)
    (y : X) (hy : y ⤳ (pullback.snd f f).base θ) (hys : f.base y = IsLocalRing.closedPoint R) :
    ∃ θ' : ↑(pullback f f), θ' ⤳ θ ∧ (pullback.fst f f).base θ' = (pullback.fst f f).base θ ∧
      (pullback.snd f f).base θ' = y :=
  SpecializationSlice.main f θ hθ y hy hys

end
end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_isIso_stalkMap_imageInc_fst_of_fst_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)

theorem isIso_stalkMap_imageInc_fst_of_fst_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK)
        (_he₁ : IsOpenImmersion e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    [IsIntegral Y₁]
    (ξ₁ : ↥Y₁) (hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (hξ₁gen : ∀ y : ↥Y₁, f₁.base y = IsLocalRing.closedPoint R → ξ₁ ⤳ y)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁
        (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂
        (specGenericFibreInclusion R K))
    (η : ↥δ.image) (hη₁ : (pullback.fst f₁ f₂).base (δ.imageι.base η) = ξ₁) :
    IsIso ((δ.imageι ≫ pullback.fst f₁ f₂).stalkMap η) := by
  obtain ⟨hsm₁, hsep₁, hlft₁, hqc₁⟩ := hf₁
  obtain ⟨hsm₂, hsep₂, hlft₂, hqc₂⟩ := hf₂
  let p₁ := pullback.fst f₁ (specGenericFibreInclusion R K)
  let π := δ.imageι ≫ pullback.fst f₁ f₂
  have hgenpt : f₁.base (genericPoint Y₁) ≠ IsLocalRing.closedPoint R := by
    intro h
    obtain ⟨θ, hθξ, hθ⟩ := Flat.generalizingMap f₁
      (show (⟨⊥, Ideal.isPrime_bot⟩ : ↥(Spec (CommRingCat.of R))) ⤳ f₁.base ξ₁ from by
        rw [hξ₁, ← PrimeSpectrum.le_iff_specializes]; exact bot_le)
    have h1 : f₁.base (genericPoint Y₁) ⤳ f₁.base θ :=
        (genericPoint_specializes θ).map f₁.continuous
    rw [h, hθ] at h1
    have h2 := ((IsLocalRing.isClosed_singleton_closedPoint (R := R)).closure_eq ▸
      (specializes_iff_mem_closure.mp h1) : (⟨⊥, Ideal.isPrime_bot⟩ : ↥(Spec (CommRingCat.of R))) ∈
        ({IsLocalRing.closedPoint R} : Set _))
    have h3 := congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp h2)
    exact IsDiscreteValuationRing.not_a_field R h3.symm
  have : Nonempty ↥(pullback f₁ (specGenericFibreInclusion R K)) := by
    have : genericPoint Y₁ ∈ Set.range p₁.base := by
      rw [Scheme.Pullback.range_fst]
      rw [range_specGenericFibreInclusion R K]
      exact hgenpt
    obtain ⟨z, -⟩ := this
    exact ⟨z⟩
  have : IsIntegral (pullback f₁ (specGenericFibreInclusion R K)) :=
      isIntegral_of_isOpenImmersion p₁
  have : Nonempty ↥(pullback e₁.1 e₂.1) :=
    ⟨(inv (pullback.fst e₁.1 e₂.1)).base (Classical.arbitrary _)⟩
  have hEint : IsIntegral (pullback e₁.1 e₂.1) :=
      isIntegral_of_isOpenImmersion (pullback.fst e₁.1 e₂.1)
  have : IsLocallyNoetherian (pullback f₁ (specGenericFibreInclusion R K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f₁ (specGenericFibreInclusion R K))
  have : CompactSpace ↥(pullback f₁ (specGenericFibreInclusion R K)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f₁ (specGenericFibreInclusion R K))
  have : IsLocallyNoetherian (pullback e₁.1 e₂.1) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst e₁.1 e₂.1)
  have : CompactSpace ↥(pullback e₁.1 e₂.1) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst e₁.1 e₂.1)
  have : IsNoetherian (pullback e₁.1 e₂.1) := {}
  have : IsLocallyNoetherian (pullback f₁ f₂) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f₁ f₂ ≫ f₁)
  have : QuasiCompact δ := inferInstance
  have hcond : pullback.fst e₁.1 e₂.1 ≫ (p₁ ≫ f₁) =
      (pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K)) ≫ f₂ := by
    rw [← Category.assoc, ← hδ₁, ← hδ₂, Category.assoc, Category.assoc, pullback.condition]
  let δK : pullback e₁.1 e₂.1 ⟶ pullback (p₁ ≫ f₁) f₂ :=
    pullback.lift (pullback.fst e₁.1 e₂.1) (pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ _) hcond
  let u : pullback (p₁ ≫ f₁) f₂ ⟶ pullback f₁ f₂ :=
    pullback.map _ _ _ _ p₁ (𝟙 _) (𝟙 _) (Category.comp_id _)
        (by rw [Category.comp_id, Category.id_comp])
  have hδKu : δK ≫ u = δ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hδ₁]
      change δK ≫ pullback.map _ _ _ _ p₁ (𝟙 _) (𝟙 _) _ _ ≫ pullback.fst f₁ f₂ = _
      rw [pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, hδ₂]
      change δK ≫ pullback.map _ _ _ _ p₁ (𝟙 _) (𝟙 _) _ _ ≫ pullback.snd f₁ f₂ = _
      rw [pullback.lift_snd, ← Category.assoc, pullback.lift_snd, Category.comp_id]
  have : IsClosedImmersion δK := by
    have : IsClosedImmersion (δK ≫ pullback.fst (p₁ ≫ f₁) f₂) := by
      rw [pullback.lift_fst]; infer_instance
    exact IsClosedImmersion.of_comp δK (pullback.fst (p₁ ≫ f₁) f₂)
  have : IsOpenImmersion u := by dsimp only [u]; infer_instance
  have : IsImmersion δ := by rw [← hδKu]; infer_instance
  obtain ⟨hDint, hτgen, hτiso⟩ :=
    AlgebraicGeometry.Scheme.Hom.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint δ
  have hj : δ.toImage ≫ π = pullback.fst e₁.1 e₂.1 ≫ p₁ := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hδ₁]
  have hjo : IsOpenImmersion (δ.toImage ≫ π) := by rw [hj]; infer_instance
  have hgen : π.base (genericPoint δ.image) = genericPoint Y₁ := by
    rw [← hτgen, ← Scheme.Hom.comp_apply]
    have himg := (genericPoint_spec ↥(pullback e₁.1 e₂.1)).image (δ.toImage ≫ π).continuous
    rw [Set.image_univ] at himg
    have hdense : closure (Set.range (δ.toImage ≫ π).base) = Set.univ :=
      ((δ.toImage ≫ π).isOpenEmbedding.isOpen_range.dense
        (Set.range_nonempty _)).closure_eq
    rw [hdense] at himg
    exact himg.eq (genericPoint_spec Y₁)
  have hbir : IsIso (π.stalkMap (genericPoint δ.image)) := by
    rw [← hτgen]
    have hso : IsIso ((δ.toImage ≫ π).stalkMap (genericPoint ↥(pullback e₁.1 e₂.1))) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp hjo).2 (genericPoint ↥(pullback e₁.1 e₂.1))
    have hc := Scheme.Hom.stalkMap_comp δ.toImage π (genericPoint ↥(pullback e₁.1 e₂.1))
    have : IsIso (π.stalkMap (δ.toImage.base (genericPoint ↥(pullback e₁.1 e₂.1))) ≫
        δ.toImage.stalkMap (genericPoint ↥(pullback e₁.1 e₂.1))) := by
      rw [← hc]; exact hso
    exact IsIso.of_isIso_comp_right (π.stalkMap (δ.toImage.base
        (genericPoint ↥(pullback e₁.1 e₂.1))))
      (δ.toImage.stalkMap (genericPoint ↥(pullback e₁.1 e₂.1)))
  have hηne : η ≠ genericPoint δ.image := by
    intro h
    apply hgenpt
    rw [← hgen, ← h]
    change f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base η)) = _
    rw [hη₁, hξ₁]
  have hπη : π.base η = ξ₁ := by
    change (pullback.fst f₁ f₂).base (δ.imageι.base η) = ξ₁; exact hη₁
  obtain ⟨_, hdvr⟩ :=
    AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R f₁ (π.base η)
    (by rw [hπη]; exact hξ₁)
    (by
      intro y hy hyk
      rw [hπη] at hy ⊢
      exact (hy.antisymm (hξ₁gen y hyk)).eq)
  exact AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_isIso_stalkMap_genericPoint π hgen hbir η

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)

theorem isOpenImmersion_toImage_and_range_toImage_and_range_imageInc_of_genericFibre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK)
        (_he₁ : IsOpenImmersion e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (he₂ : IsIso e₂.1)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁
        (specGenericFibreInclusion R K))
    (_hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂
        (specGenericFibreInclusion R K)) :
    IsOpenImmersion δ.toImage ∧
      Set.range δ.toImage.base =
        {d | f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base d)) ≠ IsLocalRing.closedPoint R} ∧
      Set.range δ.imageι.base = closure (Set.range δ.base) := by
  classical
  obtain ⟨_, hsep₁, _, hqc₁⟩ := hf₁
  obtain ⟨_, hsep₂, _, hqc₂⟩ := hf₂
  have hc : pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K) =
      δ ≫ pullback.fst f₁ f₂ := hδ₁.symm
  let c : pullback e₁.1 e₂.1 ⟶ pullback (pullback.fst f₁ (specGenericFibreInclusion R K))
      (pullback.fst f₁ f₂) :=
    pullback.lift (pullback.fst e₁.1 e₂.1) δ hc
  have hc₁ : c ≫ pullback.fst _ _ = pullback.fst e₁.1 e₂.1 := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd _ _ = δ := pullback.lift_snd _ _ _
  have : IsClosedImmersion (c ≫ pullback.fst (pullback.fst f₁ (specGenericFibreInclusion R K))
      (pullback.fst f₁ f₂)) := by rw [hc₁]; infer_instance
  have hcci : IsClosedImmersion c := IsClosedImmersion.of_comp c (pullback.fst _ _)
  have hδimm : IsImmersion δ := by rw [← hc₂]; infer_instance
  have hδqc : QuasiCompact δ := by rw [← hc₂]; infer_instance
  refine ⟨inferInstance, ?_, ?_⟩
  swap
  · change Set.range δ.ker.subschemeι = closure (Set.range δ)
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  · have hgen : ∀ q : PrimeSpectrum R, q ≠ IsLocalRing.closedPoint R ↔
        q ∈ Set.range (specGenericFibreInclusion R K).base := by
      intro q
      rw [range_specGenericFibreInclusion R K]
      rfl
    apply Set.Subset.antisymm
    · rintro _ ⟨x, rfl⟩
      change f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base (δ.toImage.base x))) ≠ _
      have e1 : δ.imageι.base (δ.toImage.base x) = δ.base x := by
        rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
      have hm : δ ≫ pullback.fst f₁ f₂ ≫ f₁ = pullback.fst e₁.1 e₂.1 ≫
          pullback.snd f₁ (specGenericFibreInclusion R K) ≫ specGenericFibreInclusion R K := by
        rw [← Category.assoc, hδ₁, Category.assoc, pullback.condition]
      have e2 : f₁.base ((pullback.fst f₁ f₂).base (δ.base x)) =
          (specGenericFibreInclusion R K).base ((pullback.snd f₁
              (specGenericFibreInclusion R K)).base
            ((pullback.fst e₁.1 e₂.1).base x)) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hm, Scheme.Hom.comp_apply,
          Scheme.Hom.comp_apply]
      rw [e1, e2]
      exact (hgen _).mpr ⟨_, rfl⟩
    · intro d hd
      change f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base d)) ≠ _ at hd
      have h1 : (pullback.fst f₁ f₂).base (δ.imageι.base d) ∈
          Set.range (pullback.fst f₁ (specGenericFibreInclusion R K)).base := by
        rw [Scheme.Pullback.range_fst]
        exact (hgen _).mp hd
      have h2 : δ.imageι.base d ∈ Set.range (pullback.snd (pullback.fst f₁
          (specGenericFibreInclusion R K))
          (pullback.fst f₁ f₂)).base := by
        rw [Scheme.Pullback.range_snd]
        exact h1
      have h3 : δ.imageι.base d ∈ closure (Set.range δ.base) := by
        rw [← Scheme.Hom.support_ker, ← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨d, rfl⟩
      have h4 : δ.imageι.base d ∈ Set.range δ.base := by
        obtain ⟨u, hu⟩ := h2
        have hq₂ := (pullback.snd (pullback.fst f₁ (specGenericFibreInclusion R K))
          (pullback.fst f₁ f₂)).isOpenEmbedding
        have hcl : IsClosed (Set.range c.base) := c.isClosedEmbedding.isClosed_range
        have : Set.range δ.base = (pullback.snd (pullback.fst f₁ (specGenericFibreInclusion R K))
            (pullback.fst f₁ f₂)).base '' Set.range c.base := by
          rw [← Set.range_comp, ← hc₂]
          rfl
        rw [this] at h3 ⊢
        have hu' : u ∈ closure (Set.range c.base) := by
          rw [hq₂.isEmbedding.closure_eq_preimage_closure_image, Set.mem_preimage, hu]
          exact h3
        rw [hcl.closure_eq] at hu'
        exact ⟨u, hu', hu⟩
      obtain ⟨x, hx⟩ := h4
      refine ⟨x, δ.imageι.isClosedEmbedding.injective ?_⟩
      rw [← hx, ← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.LocalPointCoordinates

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra TensorProduct

universe u

namespace AffineCoordinates

theorem ΓSpecIso_inv_hom_apply (R : Type u) [CommRing R] (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso
        (CommRingCat.of R)).inv.hom r) = r := by
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Scheme.ΓSpecIso
      (CommRingCat.of R)).hom).hom r = r
  rw [Iso.inv_hom_id]; rfl

theorem ΓSpecIso_nat_apply {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (r : Γ(Spec
    (CommRingCat.of R), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((Spec.map (CommRingCat.ofHom g)).appTop.hom r) =
      g ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r) := by
  have := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)
  have h := congrArg (fun k : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of S => k.hom r) this
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h

open _root_.AlgebraicCurves.Geometry.Schemes.Proofs.AffineOpenBaseChange in
open AlgebraicGeometry.Scheme.TwoAffineOpenCover.AffineBaseChange in
theorem topIso_inv_map {X : Scheme.{u}} (U : X.Opens) (s : Γ(X, ⊤)) :
    U.topIso.inv.hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) = U.ι.appTop.hom s := by
  have hmap := opens_ι_appTop_topIso_hom U
  have hcomp : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ U.topIso.inv =
      U.ι.appTop := by
    rw [← hmap, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg (fun k : Γ(X, ⊤) ⟶ Γ(U, ⊤) => k.hom s) hcomp

end AffineCoordinates

open AffineCoordinates

end AbelianVarieties.NOSProofs.LocalPointCoordinates

namespace NeronModelInfra

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)
open AbelianVarieties.NOSProofs.LocalPointCoordinates.AffineCoordinates

theorem exists_algHom_comap_maximalIdeal_eq_primeIdealOf_of_apply_closedPoint_mem
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R']
    (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) f)
    (U : X.Opens) (hU : IsAffineOpen U) (hxU : x.1 (IsLocalRing.closedPoint R') ∈ U) :
    let _alg : Algebra R Γ(X, U) :=
      ((X.presheaf.map (homOfLE le_top).op).hom.comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)).toAlgebra
    ∃ c : Γ(X, U) →ₐ[R] R',
      (IsLocalRing.maximalIdeal R').comap c = (hU.primeIdealOf ⟨x.1
          (IsLocalRing.closedPoint R'), hxU⟩).asIdeal := by
  intro _alg
  have hpre : x.1 ⁻¹ᵁ U = ⊤ := (IsLocalRing.closedPoint_mem_iff _).mp hxU
  have hrange : Set.range x.1.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have : p ∈ x.1 ⁻¹ᵁ U := by rw [hpre]; trivial
    exact this
  let φU : Spec (CommRingCat.of R') ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι x.1 hrange
  have hφU : φU ≫ U.ι = x.1 := IsOpenImmersion.lift_fac U.ι x.1 hrange
  let c₀ : Γ(X, U) →+* R' :=
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom.comp (φU.appTop.hom.comp U.topIso.inv.hom)
  have hc₀ : ∀ r : R, c₀ (algebraMap R Γ(X, U) r) = algebraMap R R' r := by
    intro r
    change (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom (φU.appTop.hom (U.topIso.inv.hom
      ((X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom ((Scheme.ΓSpecIso
          (CommRingCat.of R)).inv.hom r))))) = _
    rw [topIso_inv_map]
    have h1 : ∀ t, φU.appTop.hom (U.ι.appTop.hom (f.appTop.hom t)) = ((φU ≫ U.ι) ≫
        f).appTop.hom t := fun t => by
      simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [h1, hφU, x.2, ΓSpecIso_nat_apply, ΓSpecIso_inv_hom_apply]
  let c : Γ(X, U) →ₐ[R] R' := AlgHom.mk c₀ hc₀
  refine ⟨c, ?_⟩
  have hSpec : Spec.map (CommRingCat.ofHom c₀) = φU ≫ U.toSpecΓ := by
    change Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom.comp
        (φU.appTop.hom.comp U.topIso.inv.hom))) = _
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom,
        CommRingCat.ofHom_hom, CommRingCat.ofHom_hom,
      Spec.map_comp, Spec.map_comp, SpecMap_ΓSpecIso_hom, Scheme.Opens.toSpecΓ,
          ← Category.assoc, ← Category.assoc,
      ← Scheme.toSpecΓ_naturality]
  have hpt : φU.base (IsLocalRing.closedPoint R') = ⟨x.1.base (IsLocalRing.closedPoint R'),
      hxU⟩ := by
    apply Subtype.ext
    change (φU ≫ U.ι).base (IsLocalRing.closedPoint R') = _
    rw [hφU]
  change Ideal.comap c₀ (IsLocalRing.maximalIdeal R') = (hU.isoSpec.hom.base ⟨x.1.base
      (IsLocalRing.closedPoint R'), hxU⟩).asIdeal
  rw [IsAffineOpen.isoSpec_hom, ← hpt]
  change _ = ((φU ≫ U.toSpecΓ).base (IsLocalRing.closedPoint R')).asIdeal
  rw [← hSpec]
  rfl

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_isIndexOneExtension_stalk_of_smooth_of_forall_specializes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.RamificationOneStalks

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

namespace MinimalStalks

open IsLocalRing

section Field

variable {k : Type u} [Field k] {B : Type u} [CommRing B] [Algebra k B]

theorem isRegularLocalRing_localization_of_smooth [Algebra.Smooth k B] (q : Ideal B)
    [hq : q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  have h := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk
    (f := Spec.map (CommRingCat.ofHom (algebraMap k B))) (⟨q, hq⟩ : PrimeSpectrum B)
  exact @IsRegularLocalRing.of_ringEquiv _ _ h _ _
    (AlgebraicGeometry.StructureSheaf.stalkIso B (⟨q, hq⟩ : PrimeSpectrum B)).toRingEquiv.symm

theorem isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero (S : Type u) [CommRing S]
    [IsRegularLocalRing S] (h : ringKrullDim S = 0) : IsField S := by
  have hsp : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) = ringKrullDim S :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  rw [h] at hsp
  have h0 : (maximalIdeal S).spanFinrank = 0 := by exact_mod_cast hsp
  have hbot : maximalIdeal S = ⊥ :=
    (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0
  exact IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot

theorem isField_localization_of_smooth_of_minimal [Algebra.Smooth k B] (q : Ideal B)
    [hq : q.IsPrime]
    (hmin : q ∈ minimalPrimes B) : IsField (Localization.AtPrime q) := by
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    isRegularLocalRing_localization_of_smooth (k := k) q
  apply isField_of_isRegularLocalRing_of_ringKrullDim_eq_zero
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
    Ideal.height_eq_zero_iff.mpr hmin]
  rfl

end Field

end MinimalStalks

end AbelianVarieties.NOSProofs.RamificationOneStalks

namespace NeronModelInfra

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)
open AbelianVarieties.NOSProofs.RamificationOneStalks

theorem isIndexOneExtension_stalk_of_smooth_of_forall_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (ζ : Z) (hζ : z.base ζ = IsLocalRing.closedPoint R)
    (hgen : ∀ y : Z, y ⤳ ζ → z.base y = IsLocalRing.closedPoint R → y = ζ)
    [Algebra R (Z.presheaf.stalk ζ)]
    (halg : Z.fromSpecStalk ζ ≫ z = Spec.map (CommRingCat.ofHom (algebraMap R
        (Z.presheaf.stalk ζ)))) :
    ∃ (_ : IsDomain (Z.presheaf.stalk ζ)) (_ : IsDiscreteValuationRing (Z.presheaf.stalk ζ))
      (_ : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ))),
      IsIndexOneExtension R (Z.presheaf.stalk ζ) := by
  classical
  obtain ⟨hdom, hdvr⟩ :=
    AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R z ζ hζ hgen
  have : IsDomain (Z.presheaf.stalk ζ) := hdom
  have : IsDiscreteValuationRing (Z.presheaf.stalk ζ) := hdvr
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian z
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let g : CommRingCat.of R ⟶ (Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.germ ⊤
        (z.base ζ) trivial
  let φ : CommRingCat.of R ⟶ Z.presheaf.stalk ζ := g ≫ z.stalkMap ζ
  have hfac : Z.fromSpecStalk ζ ≫ z = Spec.map φ := by
    rw [Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk z, Spec.fromSpecStalk_eq]
  have hφ : algebraMap R (Z.presheaf.stalk ζ) = φ.hom := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ζ))) = Spec.map φ :=
      halg.symm.trans hfac
    have h2 := Spec.map_injective h1
    exact congrArg (fun f => f.hom) h2
  have hbase : ∀ 𝔮 : PrimeSpectrum (Z.presheaf.stalk ζ),
      z.base ((Z.fromSpecStalk ζ).base 𝔮) = (Spec.map φ).base 𝔮 := fun 𝔮 => by
    rw [← hfac]; rfl
  have hcomapq : ∀ 𝔮 : PrimeSpectrum (Z.presheaf.stalk ζ),
      ((Spec.map φ).base 𝔮).asIdeal = 𝔮.asIdeal.comap φ.hom := fun _ => rfl
  have hcomap : (IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ)).comap (algebraMap R
      (Z.presheaf.stalk ζ)) =
      IsLocalRing.maximalIdeal R := by
    rw [hφ]
    change (IsLocalRing.closedPoint (Z.presheaf.stalk ζ)).asIdeal.comap φ.hom = _
    rw [← hcomapq, ← hbase, Scheme.fromSpecStalk_closedPoint, hζ]
    rfl
  have hlh : IsLocalHom (algebraMap R (Z.presheaf.stalk ζ)) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem : a ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr hna
    rw [← hcomap, Ideal.mem_comap] at hmem
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) ha
  have hϖm : algebraMap R (Z.presheaf.stalk ζ) ϖ ∈ IsLocalRing.maximalIdeal
      (Z.presheaf.stalk ζ) := by
    rw [← Ideal.mem_comap, hcomap]
    exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have hgreg : IsSMulRegular ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ)) (g.hom ϖ) := by
    let : Algebra Γ(Spec (CommRingCat.of R), ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk
        (z.base ζ)) :=
      ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (z.base ζ) trivial).hom.toAlgebra
    have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ))
        ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf
          ⟨z.base ζ, trivial⟩).asIdeal :=
      (isAffineOpen_top (Spec (CommRingCat.of R))).isLocalization_stalk ⟨z.base ζ, trivial⟩
    have : IsDomain Γ(Spec (CommRingCat.of R), ⊤) :=
      Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
        (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.injective
    have hle := ((isAffineOpen_top (Spec (CommRingCat.of R))).primeIdealOf
      ⟨z.base ζ, trivial⟩).asIdeal.primeCompl_le_nonZeroDivisors
    have : IsDomain ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ)) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
    have hne : g.hom ϖ ≠ 0 := by
      intro h0
      have hinj := IsLocalization.injective ((Spec (CommRingCat.of R)).presheaf.stalk
          (z.base ζ)) hle
      have h0' : algebraMap Γ(Spec (CommRingCat.of R),
          ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ))
            ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)
          = algebraMap Γ(Spec (CommRingCat.of R),
              ⊤) ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ)) 0 := by
        rw [map_zero]; exact h0
      have := hinj h0'
      exact hϖ.ne_zero ((Scheme.ΓSpecIso
          (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
        (by rw [map_zero]; exact this))
    exact (IsRegular.of_ne_zero hne).left.isSMulRegular
  have hflat : (z.stalkMap ζ).hom.Flat := Flat.stalkMap z ζ
  have hreg : IsSMulRegular (Z.presheaf.stalk ζ) (φ.hom ϖ) := by
    let : Algebra ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ))
        (Z.presheaf.stalk ζ) := (z.stalkMap ζ).hom.toAlgebra
    have : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (z.base ζ))
        (Z.presheaf.stalk ζ) := hflat
    exact hgreg.of_flat
  have hne0 : algebraMap R (Z.presheaf.stalk ζ) ϖ ≠ 0 := by
    rw [hφ]
    intro h0
    have h1 : φ.hom ϖ * 1 = φ.hom ϖ * 0 := by rw [h0, zero_mul, zero_mul]
    exact one_ne_zero (hreg h1)
  obtain ⟨_, ⟨V, hV, rfl⟩, hζV, -⟩ :=
    Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ ζ) isOpen_univ
  have hVU : (V : Z.Opens) ≤ z ⁻¹ᵁ ⊤ := le_top
  have hU : IsAffineOpen (⊤ : (Spec (CommRingCat.of R)).Opens) := isAffineOpen_top _
  have hψ : (z.appLE ⊤ V hVU).hom.Smooth := z.smooth_appLE hU hV hVU
  have hιR : Function.Bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.bijective
  let algRA : Algebra R Γ(Z, V) := ((z.appLE ⊤ V hVU).hom.comp (Scheme.ΓSpecIso
      (CommRingCat.of R)).inv.hom).toAlgebra
  have hsmA : Algebra.Smooth R Γ(Z, V) := RingHom.Smooth.comp (RingHom.Smooth.of_bijective hιR) hψ
  let algAO : Algebra Γ(Z, V) (Z.presheaf.stalk ζ) := Z.presheaf.algebra_section_stalk ⟨ζ, hζV⟩
  have : IsLocalization.AtPrime (Z.presheaf.stalk ζ) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨ζ, hζV⟩
  have halgRA : ∀ r : R, algebraMap R Γ(Z, V) r = (z.appLE ⊤ V hVU).hom ((Scheme.ΓSpecIso
      (CommRingCat.of R)).inv.hom r) :=
    fun r => rfl
  have halgAO : ∀ a : Γ(Z, V), algebraMap Γ(Z,
      V) (Z.presheaf.stalk ζ) a = (Z.presheaf.germ V ζ hζV).hom a :=
    fun a => rfl
  have htower : IsScalarTower R Γ(Z, V) (Z.presheaf.stalk ζ) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [halgAO, halgRA, hφ]
    change (z.stalkMap ζ).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (z.base ζ) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
    have hres := Z.presheaf.germ_res (homOfLE hVU) ζ hζV
    have hst := Scheme.Hom.germ_stalkMap z ⊤ ζ trivial
    exact (congrArg (fun α : Γ(Spec (CommRingCat.of R), ⊤) ⟶ Z.presheaf.stalk ζ =>
      α.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) hst).trans
      (congrArg (fun α : Γ(Z, z ⁻¹ᵁ ⊤) ⟶ Z.presheaf.stalk ζ =>
        α.hom ((z.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) hres).symm
  have hϖmR : ϖ ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have h𝔭 : (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal = (IsLocalRing.maximalIdeal
      (Z.presheaf.stalk ζ)).comap (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ)) :=
    (IsLocalization.AtPrime.under_maximalIdeal (Z.presheaf.stalk ζ) (hV.primeIdealOf ⟨ζ,
        hζV⟩).asIdeal).symm
  have h𝔭R : (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal.comap (algebraMap R Γ(Z,
      V)) = IsLocalRing.maximalIdeal R := by
    rw [h𝔭, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hcomap]
  have h𝔞𝔭 : ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))) ≤ (hV.primeIdealOf ⟨ζ,
      hζV⟩).asIdeal := by
    rw [Ideal.map_le_iff_le_comap, h𝔭R]
  let kfield : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have : Algebra.FormallySmooth R Γ(Z, V) := hsmA.formallySmooth
  have : Algebra.FinitePresentation R Γ(Z, V) := hsmA.finitePresentation
  have hsmB : Algebra.Smooth (R ⧸ IsLocalRing.maximalIdeal R) (Γ(Z,
      V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) :=
    ⟨Algebra.FormallySmooth.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Γ(Z,
        V) (IsLocalRing.maximalIdeal R)).symm,
     Algebra.FinitePresentation.equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Γ(Z,
         V) (IsLocalRing.maximalIdeal R)).symm⟩
  have hq' : (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
      V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact h𝔞𝔭)
  have hcQQ : (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
      V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal).comap (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) = (hV.primeIdealOf ⟨ζ,
      hζV⟩).asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    have : Ideal.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
        V)))) ⊥ = ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))) := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rw [this]
    exact sup_eq_left.mpr h𝔞𝔭
  have hmin : (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
      V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal) ∈ minimalPrimes (Γ(Z,
      V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) := by
    rw [minimalPrimes_eq_minimals]
    refine ⟨hq', fun Q' hQ' hle => ?_⟩
    have hQp : (Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
        V))))).IsPrime := Ideal.comap_isPrime _ _
    have hQle : Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
        V)))) ≤ (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal := by
      rw [← hcQQ]; exact Ideal.comap_mono hle
    have hdisj : Disjoint (((hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal.primeCompl : Submonoid Γ(Z,
        V)) : Set Γ(Z, V)) ↑(Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
        (algebraMap R Γ(Z, V))))) := by
      rw [Set.disjoint_left]
      intro x hx hxQ
      exact hx (hQle hxQ)
    have hQO : ((Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
        (algebraMap R Γ(Z, V))))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (hV.primeIdealOf ⟨ζ,
          hζV⟩).asIdeal.primeCompl (Z.presheaf.stalk ζ) _ hQp hdisj
    have hQO_ne : (Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
        (algebraMap R Γ(Z, V))))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ)) ≠ ⊥ := by
      intro h0
      have hmem : algebraMap R (Z.presheaf.stalk ζ) ϖ ∈ (Q'.comap (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))).map (algebraMap Γ(Z,
          V) (Z.presheaf.stalk ζ)) := by
        rw [IsScalarTower.algebraMap_apply R Γ(Z, V) (Z.presheaf.stalk ζ)]
        apply Ideal.mem_map_of_mem
        have h1 : algebraMap R Γ(Z, V) ϖ ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
            V))) := Ideal.mem_map_of_mem _ hϖmR
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr h1]
        exact Q'.zero_mem
      rw [h0] at hmem
      exact hne0 (Ideal.mem_bot.mp hmem)
    have hQO_max : (Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
        (algebraMap R Γ(Z, V))))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ)) =
        IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ) :=
      IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hQO_ne hQO)
    have hQeq : Q'.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
        V)))) = (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal := by
      have h1 := IsLocalization.under_map_of_isPrime_disjoint (hV.primeIdealOf ⟨ζ,
          hζV⟩).asIdeal.primeCompl (Z.presheaf.stalk ζ) hQp hdisj
      rw [hQO_max, Ideal.under_def] at h1
      rw [← h1, h𝔭]
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
        (algebraMap R Γ(Z, V)))) Ideal.Quotient.mk_surjective Q', hQeq]
  have hfield : IsField (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
      hζV⟩).asIdeal)) :=
    MinimalStalks.isField_localization_of_smooth_of_minimal (k :=
        (R ⧸ IsLocalRing.maximalIdeal R)) (Ideal.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
        hζV⟩).asIdeal) hmin
  have hsub : Algebra.algebraMapSubmonoid (Γ(Z,
      V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
      hζV⟩).asIdeal.primeCompl = (Ideal.map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
      hζV⟩).asIdeal).primeCompl := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hx
      intro hmem
      apply ha
      change a ∈ (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal
      rw [← hcQQ, Ideal.mem_comap]
      exact hmem
    · intro hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      refine Submonoid.mem_map.mpr ⟨a, ?_, rfl⟩
      intro ha
      exact hx (Ideal.mem_map_of_mem _ ha)
  have hlocOB : IsLocalization.AtPrime ((Z.presheaf.stalk ζ) ⧸
      (((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z,
      V) (Z.presheaf.stalk ζ))) (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
      (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal) := by
    have h : IsLocalization (Algebra.algebraMapSubmonoid (Γ(Z,
        V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
        hζV⟩).asIdeal.primeCompl) ((Z.presheaf.stalk ζ) ⧸ (((IsLocalRing.maximalIdeal R).map
        (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))) := inferInstance
    rwa [hsub] at h
  let eO : ((Z.presheaf.stalk ζ) ⧸ (((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
      V)))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))) ≃ₐ[(Γ(Z,
      V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
      V))))] Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
      hζV⟩).asIdeal) :=
    IsLocalization.algEquiv (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
        (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
        hζV⟩).asIdeal).primeCompl ((Z.presheaf.stalk ζ) ⧸ (((IsLocalRing.maximalIdeal R).map
        (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z,
        V) (Z.presheaf.stalk ζ))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
        hζV⟩).asIdeal))
  have hOBfield : IsField ((Z.presheaf.stalk ζ) ⧸ (((IsLocalRing.maximalIdeal R).map
      (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z, V) (Z.presheaf.stalk ζ))) :=
      MulEquiv.isField hfield eO.toMulEquiv
  have h𝔞O : (((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))).map (algebraMap Γ(Z,
      V) (Z.presheaf.stalk ζ)) = (IsLocalRing.maximalIdeal R).map (algebraMap R
      (Z.presheaf.stalk ζ)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hmap : (IsLocalRing.maximalIdeal R).map (algebraMap R (Z.presheaf.stalk ζ)) =
      IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ) := by
    rw [← h𝔞O]
    exact IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _ hOBfield)
  have : Algebra.FormallySmooth (R ⧸ IsLocalRing.maximalIdeal R) (Γ(Z,
      V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) := hsmB.formallySmooth
  have : Algebra.FormallySmooth (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
      V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
      hζV⟩).asIdeal)) :=
    Algebra.FormallySmooth.of_isLocalization (Ideal.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
        hζV⟩).asIdeal).primeCompl
  have hfsX : Algebra.FormallySmooth (R ⧸ IsLocalRing.maximalIdeal R) (Localization.AtPrime
      (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
      V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) :=
    Algebra.FormallySmooth.comp (R ⧸ IsLocalRing.maximalIdeal R) (Γ(Z,
        V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
        V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
        hζV⟩).asIdeal))
  let algkX : Algebra (IsLocalRing.ResidueField R)
      (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))
        (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) :=
    (inferInstance : Algebra (R ⧸ IsLocalRing.maximalIdeal R)
      (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V))))
        (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)))
  have hfsX' : Algebra.FormallySmooth (IsLocalRing.ResidueField R) (Localization.AtPrime
      (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
      V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) := hfsX
  let eR : Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
      (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
      hζV⟩).asIdeal) ≃+* IsLocalRing.ResidueField (Z.presheaf.stalk ζ) :=
    eO.symm.toRingEquiv.trans (Ideal.quotEquivOfEq (h𝔞O.trans hmap))
  have hcomm : ∀ x : IsLocalRing.ResidueField R,
      eR (algebraMap (IsLocalRing.ResidueField R) (Localization.AtPrime (Ideal.map
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
          V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) x) =
        algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField
            (Z.presheaf.stalk ζ)) x := by
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    have h1 : algebraMap (IsLocalRing.ResidueField R) (Localization.AtPrime (Ideal.map
        (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
        V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) (IsLocalRing.residue R r) =
        algebraMap (Γ(Z, V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
            V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
            ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
            hζV⟩).asIdeal)) (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
            (algebraMap R Γ(Z, V))) (algebraMap R Γ(Z, V) r)) := by
      change algebraMap (R ⧸ IsLocalRing.maximalIdeal R) (Localization.AtPrime (Ideal.map
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
          V)))) (hV.primeIdealOf ⟨ζ, hζV⟩).asIdeal)) (Ideal.Quotient.mk _ r) = _
      rw [IsScalarTower.algebraMap_apply (R ⧸ IsLocalRing.maximalIdeal R) (Γ(Z,
          V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
          V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
          ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
          hζV⟩).asIdeal))]
      rfl
    rw [h1]
    change Ideal.quotEquivOfEq (h𝔞O.trans hmap) (eO.symm (algebraMap (Γ(Z,
        V) ⧸ ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z,
        V)))) (Localization.AtPrime (Ideal.map (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal R).map (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
        hζV⟩).asIdeal)) _)) = _
    rw [AlgEquiv.commutes]
    change Ideal.quotEquivOfEq (h𝔞O.trans hmap) (Ideal.Quotient.mk _ (algebraMap Γ(Z,
        V) (Z.presheaf.stalk ζ) (algebraMap R Γ(Z, V) r))) = _
    rw [Ideal.quotEquivOfEq_mk, ← IsScalarTower.algebraMap_apply]
    rfl
  let eA : Localization.AtPrime (Ideal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal R).map
      (algebraMap R Γ(Z, V)))) (hV.primeIdealOf ⟨ζ,
      hζV⟩).asIdeal) ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField (Z.presheaf.stalk ζ) :=
    AlgEquiv.ofRingEquiv (f := eR) hcomm
  have hfs : Algebra.FormallySmooth (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField
      (Z.presheaf.stalk ζ)) :=
    Algebra.FormallySmooth.of_equiv eA
  exact ⟨hdom, hdvr, hlh, ⟨hmap, hfs⟩⟩

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.TranslationStalks

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

universe u

namespace TranslationCharts

theorem isOpenImmersion_opensRange_ι_comp_translate
    {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
    [IsOpenImmersion (specGenericFibreInclusion R K)]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) [IsIso e.1]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (Y : Scheme.{u}) (fY : Y ⟶ Spec (CommRingCat.of R))
    (eY : SchemeHomOver (pullback.snd fY (specGenericFibreInclusion R K)) gK) [IsOpenImmersion eY.1]
    (U₀ : (pullback z f).Opens) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z) fY)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K fY (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) eY).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z fY) (hv₁ : v ≫ pullback.fst z fY = U₀.ι ≫ pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z fY = τ₀.1) :
    IsOpenImmersion
      ((pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z)
          (specGenericFibreInclusion R K)).opensRange.ι ≫ v) := by
  have hq : v ≫ (pullback.fst z fY ≫ z) = (U₀.ι ≫ pullback.fst z f ≫ z) := by
    simp only [← Category.assoc, hv₁]
  let mapU : pullback (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ⟶ pullback
      (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) :=
    pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
        (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  let w : pullback (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ⟶ pullback
      (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) :=
    pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
        (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) v (𝟙 _) (𝟙 _)
        (by rw [Category.comp_id, hq])
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hmapU : IsOpenImmersion mapU :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstance : IsOpenImmersion U₀.ι)
      (inferInstance : IsOpenImmersion (𝟙 _)) rfl (Category.id_comp _).symm
  let β : pullback (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ⟶ pullback
      (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd f
      (specGenericFibreInclusion R K)) :=
    pullback.lift
      (pullback.lift (pullback.fst (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ≫
          pullback.fst z f) (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.lift (pullback.fst (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ≫
          pullback.snd z f) (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
        (by rw [Category.assoc, ← pullback.condition (f := z) (g := f)]; exact pullback.condition))
      (by rw [pullback.lift_snd, pullback.lift_snd])
  have hβ : IsIso β := AlgebraicGeometry.isIso_lift_baseChange_fst_baseChange_snd z f
      (specGenericFibreInclusion R K)
  let βY : pullback (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) ⟶ pullback
      (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd fY
      (specGenericFibreInclusion R K)) :=
    pullback.lift
      (pullback.lift (pullback.fst (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) ≫
          pullback.fst z fY) (pullback.snd (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K))
        (by rw [Category.assoc]; exact pullback.condition))
      (pullback.lift (pullback.fst (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) ≫
          pullback.snd z fY) (pullback.snd (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K))
        (by rw [Category.assoc, ← pullback.condition (f := z) (g := fY)]; exact pullback.condition))
      (by rw [pullback.lift_snd, pullback.lift_snd])
  have hβY : IsIso βY := AlgebraicGeometry.isIso_lift_baseChange_fst_baseChange_snd z fY
      (specGenericFibreInclusion R K)
  let mapE : pullback (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd f
      (specGenericFibreInclusion R K)) ⟶ pullback (pullback.snd z
      (specGenericFibreInclusion R K)) gK :=
    pullback.map (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd f
        (specGenericFibreInclusion R K)) (pullback.snd z (specGenericFibreInclusion R K)) gK
        (𝟙 _) e.1 (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans e.2.symm)
  let mapEY : pullback (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd fY
      (specGenericFibreInclusion R K)) ⟶ pullback (pullback.snd z
      (specGenericFibreInclusion R K)) gK :=
    pullback.map (pullback.snd z (specGenericFibreInclusion R K)) (pullback.snd fY
        (specGenericFibreInclusion R K)) (pullback.snd z (specGenericFibreInclusion R K)) gK
        (𝟙 _) eY.1 (𝟙 _)
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans eY.2.symm)
  have hmapEY : IsOpenImmersion mapEY :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (inferInstance : IsOpenImmersion (𝟙 _))
      (inferInstance : IsOpenImmersion eY.1) (Category.id_comp _).symm eY.2.symm
  obtain ⟨σ, hσ₁, hσ₂⟩ := LXK.exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul (pullback.snd z
      (specGenericFibreInclusion R K)) uK
  have key : w ≫ βY ≫ mapEY = mapU ≫ β ≫ mapE ≫ σ.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hσ₁]
      simp only [mapEY, mapE, pullback.lift_fst, Category.comp_id, βY, β]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, w, mapU]
        simp only [← Category.assoc, pullback.lift_fst]
        simp only [Category.assoc, hv₁]
      · simp only [Category.assoc, pullback.lift_snd, w, mapU]
    · have hψ : (β ≫ mapE) ≫ pullback.fst (pullback.snd z (specGenericFibreInclusion R K)) gK ≫
        (pullback.snd z (specGenericFibreInclusion R K)) = pullback.snd (pullback.fst z f ≫ z)
        (specGenericFibreInclusion R K) := by
        simp only [Category.assoc, mapE, β, pullback.lift_fst_assoc, Category.id_comp,
            pullback.lift_snd]
      have nat := congrArg Subtype.val
        (LXK.mul_natural (pullback.fst (pullback.snd z (specGenericFibreInclusion R K)) gK ≫
            (pullback.snd z (specGenericFibreInclusion R K))) (pullback.snd (pullback.fst z f ≫
            z) (specGenericFibreInclusion R K)) (β ≫ mapE) hψ
          ⟨pullback.fst (pullback.snd z (specGenericFibreInclusion R K)) gK ≫ uK.1,
              by rw [Category.assoc, uK.2]⟩
          ⟨pullback.snd (pullback.snd z (specGenericFibreInclusion R K)) gK,
              pullback.condition.symm⟩)
      simp only [GoodReductionJacobian.schemeHomOverComp_coe] at nat
      have hA : GoodReductionJacobian.schemeHomOverComp (β ≫ mapE) hψ
            ⟨pullback.fst (pullback.snd z (specGenericFibreInclusion R K)) gK ≫ uK.1,
                by rw [Category.assoc, uK.2]⟩ =
          NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK := by
        apply Subtype.ext
        simp only [GoodReductionJacobian.schemeHomOverComp_coe,
            NeronModelInfra.schemeHomOverComp_coe,
          genericFibreRestrict, Category.assoc, mapE, β, pullback.lift_fst_assoc, Category.id_comp]
      have hB : GoodReductionJacobian.schemeHomOverComp (β ≫ mapE) hψ
            ⟨pullback.snd (pullback.snd z (specGenericFibreInclusion R K)) gK,
                pullback.condition.symm⟩ =
          NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f,
                pullback.condition.symm⟩) e := by
        apply Subtype.ext
        simp only [GoodReductionJacobian.schemeHomOverComp_coe,
            NeronModelInfra.schemeHomOverComp_coe,
          genericFibreRestrict, Category.assoc, mapE, β, pullback.lift_snd_assoc, pullback.lift_snd]
      rw [hA, hB] at nat
      have eL : (w ≫ βY ≫ mapEY) ≫ pullback.snd (pullback.snd z
          (specGenericFibreInclusion R K)) gK =
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K fY (U₀.ι ≫
              pullback.fst z f ≫ z) τ₀) eY).1 := by
        simp only [NeronModelInfra.schemeHomOverComp_coe, genericFibreRestrict, Category.assoc,
          mapEY, pullback.lift_snd]
        simp only [← Category.assoc]
        congr 1
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_snd,
            pullback.lift_fst_assoc, βY, w, hv₂]
        · simp only [Category.assoc, pullback.map, pullback.lift_snd, βY, w,
            Category.comp_id]
      rw [eL, hτ₀]
      simp only [Category.assoc, hσ₂]
      rw [← nat]
      simp only [Category.assoc, mapU]
  have : IsOpenImmersion (mapU ≫ β ≫ mapE ≫ σ.hom) := inferInstance
  have hwc : IsOpenImmersion (w ≫ βY ≫ mapEY) := by rw [key]; infer_instance
  have : IsOpenImmersion (βY ≫ mapEY) := inferInstance
  have hw : IsOpenImmersion w := IsOpenImmersion.of_comp w (βY ≫ mapEY)
  have h4 : pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ≫ v = w ≫
      pullback.fst (pullback.fst z fY ≫ z) (specGenericFibreInclusion R K) := by
    simp only [w, pullback.lift_fst]
  have h5 : IsOpenImmersion (pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z)
      (specGenericFibreInclusion R K) ≫ v) := by rw [h4]; infer_instance
  have h6 : (pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z)
      (specGenericFibreInclusion R K)).opensRange.ι ≫ v =
      (pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z)
          (specGenericFibreInclusion R K)).isoOpensRange.inv ≫ pullback.fst (U₀.ι ≫
          pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ≫ v := by
    rw [Scheme.Hom.isoOpensRange_inv_comp_assoc]
  rw [h6]
  infer_instance

end TranslationCharts

namespace TranslationCharts

theorem exists_mem_opensRange_fst_specializes
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {S : Scheme.{u}} (s : S ⟶ Spec (CommRingCat.of R)) [Flat s] (x : S) :
    ∃ x' : S, x' ∈ (pullback.fst s (specGenericFibreInclusion R K)).opensRange ∧ x' ⤳ x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let ξ : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ : (ξ : Spec (CommRingCat.of R)) ⤳ s.base x :=
    (PrimeSpectrum.le_iff_specializes ξ (s.base x)).mp bot_le
  obtain ⟨x', hx', hx'ξ⟩ := Flat.generalizingMap s hξ
  refine ⟨x', ?_, hx'⟩
  rw [AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst]
  change s.base x' ∈ Set.range (specGenericFibreInclusion R K).base
  rw [range_specGenericFibreInclusion_eq_basicOpen R K hϖ, hx'ξ]
  change ξ ∈ PrimeSpectrum.basicOpen ϖ
  rw [PrimeSpectrum.mem_basicOpen]
  change ϖ ∉ (⊥ : Ideal R)
  rw [Ideal.mem_bot]
  exact hϖ.ne_zero

end TranslationCharts

end AbelianVarieties.NOSProofs.TranslationStalks

namespace NeronModelInfra

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)
open GoodReductionJacobian
open AbelianVarieties.NOSProofs.TranslationStalks
open TranslationCharts

theorem isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f))
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫
        z) T.f)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫
        pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1) :
    ∃ (_ : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
      (_ : IsDomain ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩))),
      let _alg : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η,
          hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η,
            hηU⟩) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η,
            hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z T.f).presheaf.stalk (v.base ⟨η,
          hηU⟩)) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) := by
  have hTs : Smooth T.f := T.smooth
  have hTe : IsOpenImmersion T.e.1 := T.isOpenImmersion
  have hD1 : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) :=
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (U₀.ι ≫ pullback.fst z f ≫ z) ⟨η, hηU⟩).1
  have hD2 : IsDomain ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) :=
    (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (pullback.fst z T.f ≫ z) (v.base ⟨η, hηU⟩)).1
  refine ⟨hD1, hD2, ?_⟩
  intro _alg
  obtain ⟨x', hx'U, hx'η⟩ :=
    exists_mem_opensRange_fst_specializes K (U₀.ι ≫ pullback.fst z f ≫ z) ⟨η, hηU⟩
  have : IsOpenImmersion
      ((pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z)
        (specGenericFibreInclusion R K)).opensRange.ι ≫ v) :=
    isOpenImmersion_opensRange_ι_comp_translate K LXK X f e Z z uK T.Y T.f T.e U₀ τ₀ hτ₀ v hv₁ hv₂
  exact AlgebraicGeometry.isFractionRing_stalk_fractionRing_stalk_of_isOpenImmersion_restrict
    v ⟨η, hηU⟩
    (pullback.fst (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)).opensRange ⟨x',
        hx'U, hx'η⟩

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)
open GoodReductionJacobian

theorem mul_pointGenericFibre_eq_pointGenericFibre_comp_chart_of_genericFibreRestrict_comp_eq_mul
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f))
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫
        z) T.f)
    (hτ₀ : (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
            pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫
        pullback.fst z f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    [Algebra R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))]
    (halgZ : Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)) ≫ z =
      Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk ((pullback.fst z T.f).base
          (v.base ⟨η, hηU⟩))))))
    [Algebra R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)]
    (halgO : (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ (U₀.ι ≫ pullback.fst z f ≫ z) =
      Spec.map (CommRingCat.ofHom (algebraMap R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))))
    [Algebra R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))]
    (halg₁ : T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η,
        hηU⟩)) ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk
        ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))))))
    (K' F : Type u) [Field K'] [Algebra (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η,
        hηU⟩))) K'] [IsFractionRing (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η,
        hηU⟩))) K'] [Algebra R K'] [Algebra K K']
    [IsScalarTower R (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η,
        hηU⟩))) K'] [IsScalarTower R K K']
    [Field F] [Algebra ((U₀ : Scheme.{u}).presheaf.stalk ⟨η,
        hηU⟩) F] [Algebra R F] [Algebra K F] [Algebra K' F] [Algebra (Z.presheaf.stalk
        ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F]
    [IsScalarTower R ((U₀ : Scheme.{u}).presheaf.stalk ⟨η,
        hηU⟩) F] [IsScalarTower R K F] [IsScalarTower K K' F] [IsScalarTower (Z.presheaf.stalk
        ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) K' F]
    (hRO : (algebraMap (Z.presheaf.stalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F) =
      (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F).comp ((v.stalkMap ⟨η,
          hηU⟩).hom.comp
        ((pullback.fst z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom))
    [Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η,
        hηU⟩))) F] [IsScalarTower R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η,
        hηU⟩))) F]
    (hτF : (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F) =
      (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F).comp ((v.stalkMap ⟨η,
          hηU⟩).hom.comp
        ((pullback.snd z T.f).stalkMap (v.base ⟨η, hηU⟩)).hom)) :
    (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
        ⟨Spec.map (CommRingCat.ofHom (algebraMap K' F)) ≫
            (NeronModelInfra.schemeHomOverComp
              (pointGenericFibre (K := K) (K' := K')
                (⟨Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)), halgZ⟩ :
                  SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk
                      ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))))) z)) uK).1, by
          rw [Category.assoc, (NeronModelInfra.schemeHomOverComp _ uK).2, ← Spec.map_comp,
              ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq]⟩
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨(U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩, halgO⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R
                  ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) (U₀.ι ≫ pullback.fst z f ≫ z)))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U₀.ι ≫ pullback.fst z f ≫ z)
              ⟨U₀.ι ≫ pullback.snd z f, by rw [Category.assoc, ← pullback.condition]⟩) e))).1 =
      (NeronModelInfra.schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)), halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk
                ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))))) T.f))
        T.e).1 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : (U₀ : Scheme.{u}), x₀ = ⟨η, hηU⟩ := ⟨_, rfl⟩
  subst hx₀
  let Pη : Spec (CommRingCat.of F) ⟶ pullback (U₀.ι ≫ pullback.fst z f ≫ z)
      (specGenericFibreInclusion R K) :=
    (pointGenericFibre (K := K) (K' := F)
      (⟨(U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩, halgO⟩ :
        SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R
            ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))))
          (U₀.ι ≫ pullback.fst z f ≫ z))).1
  have hPη₁ : Pη ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F)) ≫
        (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ := pointGenericFibre_coe_comp_fst _
  have hPη₂ : Pη ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap K F)) :=
    pointGenericFibre_coe_comp_snd _
  have hPη₁' : ∀ {W : Scheme.{u}} (h : (U₀ : Scheme.{u}) ⟶ W), Pη ≫ pullback.fst _ _ ≫ h =
      Spec.map (CommRingCat.ofHom (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F)) ≫
        (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ h := fun h => by
    rw [← Category.assoc, hPη₁, Category.assoc]
  let mapU : pullback (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K) ⟶
      pullback (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) :=
    pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
      (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hO₁ : Spec.map (CommRingCat.ofHom (algebraMap (T.Y.presheaf.stalk
      ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) F)) ≫
      T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)) =
      Spec.map (CommRingCat.ofHom (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F)) ≫
        (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ τ₀.1 := by
    rw [hτF, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
        CommRingCat.ofHom_hom,
      CommRingCat.ofHom_hom, Category.assoc, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk_assoc v
        (x := (⟨η, hηU⟩ : (U₀ : Scheme.{u}))), hv₂]
  have hOZ : Spec.map (CommRingCat.ofHom (algebraMap (Z.presheaf.stalk
      ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩))) F)) ≫
      Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)) =
      Spec.map (CommRingCat.ofHom (algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) F)) ≫
        (U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩ ≫ U₀.ι ≫ pullback.fst z f := by
    rw [hRO, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
        CommRingCat.ofHom_hom,
      CommRingCat.ofHom_hom, Category.assoc, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.SpecMap_stalkMap_fromSpecStalk_assoc v
        (x := (⟨η, hηU⟩ : (U₀ : Scheme.{u}))), hv₁]
  have h1 : Pη ≫ (NeronModelInfra.schemeHomOverComp
      (genericFibreRestrict R K T.f (U₀.ι ≫ pullback.fst z f ≫ z) τ₀) T.e).1 =
      (NeronModelInfra.schemeHomOverComp
        (pointGenericFibre (K := K) (K' := F)
          (⟨T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)), halg₁⟩ :
            SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk
                ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))))) T.f))
        T.e).1 := by
    simp only [NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [pointGenericFibre_coe_comp_fst, Category.assoc]
      simp only [genericFibreRestrict, pullback.lift_fst]
      rw [← Category.assoc, hPη₁, hO₁, Category.assoc]
    · rw [pointGenericFibre_coe_comp_snd, Category.assoc]
      simp only [genericFibreRestrict, pullback.lift_snd]
      exact hPη₂
  have hψ : (Pη ≫ mapU) ≫ pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) =
      Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    simp only [Category.assoc, mapU, pullback.lift_snd, Category.comp_id, hPη₂]
  have nat := congrArg Subtype.val
    (LXK.mul_natural (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
      (Spec.map (CommRingCat.ofHom (algebraMap K F))) (Pη ≫ mapU) hψ
      (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
      (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f,
            pullback.condition.symm⟩) e))
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at nat
  have hA : GoodReductionJacobian.schemeHomOverComp (Pη ≫ mapU) hψ
      (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK) =
      ⟨Spec.map (CommRingCat.ofHom (algebraMap K' F)) ≫
            (NeronModelInfra.schemeHomOverComp
              (pointGenericFibre (K := K) (K' := K')
                (⟨Z.fromSpecStalk ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)), halgZ⟩ :
                  SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Z.presheaf.stalk
                      ((pullback.fst z T.f).base (v.base ⟨η, hηU⟩)))))) z)) uK).1, by
          rw [Category.assoc, (NeronModelInfra.schemeHomOverComp _ uK).2, ← Spec.map_comp,
              ← CommRingCat.ofHom_comp,
            ← IsScalarTower.algebraMap_eq]⟩ := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe,
        NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, genericFibreRestrict, pullback.lift_fst,
        pointGenericFibre_coe_comp_fst]
      conv_rhs => rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq]
      rw [hOZ]
      simp only [mapU, pullback.lift_fst_assoc, Category.assoc, hPη₁']
    · simp only [Category.assoc, genericFibreRestrict, pullback.lift_snd,
        pointGenericFibre_coe_comp_snd]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
      simp only [mapU, pullback.lift_snd, Category.comp_id, hPη₂]
  have hB : GoodReductionJacobian.schemeHomOverComp (Pη ≫ mapU) hψ
      (NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f,
            pullback.condition.symm⟩) e) =
      NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := F)
            (⟨(U₀ : Scheme.{u}).fromSpecStalk ⟨η, hηU⟩, halgO⟩ :
              SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R
                  ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) (U₀.ι ≫ pullback.fst z f ≫ z)))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U₀.ι ≫ pullback.fst z f ≫ z)
              ⟨U₀.ι ≫ pullback.snd z f, by rw [Category.assoc, ← pullback.condition]⟩) e) := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe,
        NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
    change Pη ≫ _ = Pη ≫ _
    congr 1
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, genericFibreRestrict, pullback.lift_fst, mapU,
        pullback.lift_fst_assoc]
    · simp only [Category.assoc, genericFibreRestrict, pullback.lift_snd, mapU,
        Category.comp_id]
  rw [hA, hB] at nat
  rw [← nat, Category.assoc, ← hτ₀, h1]

end NeronModelInfra
end
