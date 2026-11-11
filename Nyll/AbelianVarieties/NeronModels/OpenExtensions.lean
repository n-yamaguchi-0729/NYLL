/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.Topology.Sober
public import Nyll.AbelianVarieties.NeronModels.Basic
public import Nyll.AbelianVarieties.NeronModels.Density
public import Nyll.AbelianVarieties.NeronModels.Endomorphisms
public import Nyll.AbelianVarieties.NeronModels.GenericFibre
public import Nyll.SchemeTheory.Morphisms.OpenImmersionCriteria
public import Nyll.AlgebraicCurves.Geometry.Schemes.FunctionFields.PartialMapMemDomainToRationalMap
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.SchemeTheory.LocalGeometry.SmoothDVRStalk
public import Nyll.SchemeTheory.Morphisms.SmoothReducedReduced

/-!
# Extending generic-fiber morphisms over open neighborhoods

Properness gives extensions around generic points of the special fiber. Separatedness
then glues compatible local extensions while retaining the full generic fiber.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)

theorem exists_nhds_extension_of_isProper_of_smooth
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
      (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
        pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t
            (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by
  classical
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace t
  have : IsNoetherian T := {}
  have : IsReduced T := Smooth.isReduced_of_isReduced_of_isLocallyNoetherian t
  obtain ⟨hdom, hdvr⟩ :=
    AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R t η hηs hgen
  let ξ : T := (T.fromSpecStalk η).base ⟨⊥, Ideal.isPrime_bot⟩
  have hξη : ξ ⤳ η := by
    have : ξ ∈ Set.range (T.fromSpecStalk η).base := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  have hξne : ξ ≠ η := by
    intro h
    have h2 : (T.fromSpecStalk η).base (IsLocalRing.closedPoint (T.presheaf.stalk η)) = η :=
      Scheme.fromSpecStalk_closedPoint
    have h3 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (T.presheaf.stalk η)) =
        IsLocalRing.closedPoint (T.presheaf.stalk η) :=
      (T.fromSpecStalk η).isEmbedding.injective (h.trans h2.symm)
    exact IsDiscreteValuationRing.not_a_field (T.presheaf.stalk η)
      (congrArg PrimeSpectrum.asIdeal h3).symm
  have hξt : t.base ξ ≠ IsLocalRing.closedPoint R := fun h => hξne (hgen ξ hξη h)
  have hcomp : ∀ Z ∈ irreducibleComponents T, η ∈ Z → Z = closure {ξ} := by
    intro Z hZ hηZ
    have hZirr : IsIrreducible Z := hZ.1
    have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hz : IsGenericPoint hZirr.genericPoint Z := hZirr.isGenericPoint_genericPoint hZcl
    have hzmem : hZirr.genericPoint ∈ Set.range (T.fromSpecStalk η).base := by
      rw [Scheme.range_fromSpecStalk]; exact hz.specializes hηZ
    obtain ⟨q, hq⟩ := hzmem
    have hξz : ξ ⤳ hZirr.genericPoint := by
      rw [← hq]
      refine Specializes.map ?_ (T.fromSpecStalk η).base.hom.continuous
      exact (PrimeSpectrum.le_iff_specializes _ q).mp (show (⊥ : Ideal
          (T.presheaf.stalk η)) ≤ q.asIdeal from bot_le)
    have h1 : Z ⊆ closure {ξ} := by
      rw [← hz.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξz))
        isClosed_closure
    exact h1.antisymm (hZ.2 isIrreducible_singleton.closure h1)
  have hZ₀ : irreducibleComponent η ∈ irreducibleComponents T :=
    irreducibleComponent_mem_irreducibleComponents η
  have hZ₀eq : irreducibleComponent η = closure {ξ} := hcomp _ hZ₀ mem_irreducibleComponent
  let U₀ : T.Opens := T.irreducibleComponentOpen (irreducibleComponent η)
  have hηU₀ : η ∈ U₀ := by
    change η ∈ (⋃₀ (irreducibleComponents T \ {irreducibleComponent η}))ᶜ
    rintro ⟨Z, ⟨hZ, hZne⟩, hηZ⟩
    exact hZne ((hcomp Z hZ hηZ).trans hZ₀eq.symm)
  have hξU₀ : ξ ∈ U₀ := hξη.mem_open U₀.2 hηU₀
  have hU₀Z₀ : (U₀ : Set T) ⊆ irreducibleComponent η := by
    rw [← closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (irreducibleComponent η) hZ₀]
    exact subset_closure
  have hU₀irr : IsIrreducible (U₀ : Set T) :=
    ⟨⟨η, hηU₀⟩, hZ₀.1.2.open_subset U₀.2 hU₀Z₀⟩
  have : IrreducibleSpace U₀.toScheme := Subtype.irreducibleSpace hU₀irr
  have : IsIntegral U₀.toScheme :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨‹_›, inferInstance⟩
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  have hY : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let Ugen : T.Opens := (pullback.fst t (specGenericFibreInclusion R K)).opensRange
  have hmemUgen : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ Ugen := by
    intro x hx
    change x ∈ (pullback.fst t (specGenericFibreInclusion R K)).opensRange
    rw [Scheme.Hom.opensRange_pullbackFst]
    change t.base x ∈ (specGenericFibreInclusion R K).opensRange
    change t.base x ∈ Set.range (specGenericFibreInclusion R K).base
    rw [range_specGenericFibreInclusion R K]
    exact hx
  let D : U₀.toScheme.Opens := U₀.ι ⁻¹ᵁ Ugen
  have hξD : (⟨ξ, hξU₀⟩ : U₀.toScheme) ∈ D := by
    change ξ ∈ Ugen
    exact hmemUgen ξ hξt
  have hDdense : Dense (D : Set U₀.toScheme) := D.2.dense ⟨⟨ξ, hξU₀⟩, hξD⟩
  have hDrange : Set.range (D.ι ≫ U₀.ι).base ⊆
      Set.range (pullback.fst t (specGenericFibreInclusion R K)).base := by
    rintro _ ⟨z, rfl⟩
    rw [← Scheme.Hom.coe_opensRange]
    exact z.2
  let f₀ : U₀.toScheme.PartialMap X :=
    { domain := D
      dense_domain := hDdense
      hom := IsOpenImmersion.lift (pullback.fst t (specGenericFibreInclusion R K)) (D.ι ≫
          U₀.ι) hDrange ≫
        uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K) }
  have hf₀ : f₀.hom ≫ f = f₀.domain.ι ≫ (U₀.ι ≫ t) := by
    change (IsOpenImmersion.lift (pullback.fst t (specGenericFibreInclusion R K)) (D.ι ≫
        U₀.ι) hDrange ≫
        uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) ≫ f = D.ι ≫ U₀.ι ≫ t
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% uK.2, ← pullback.condition, IsOpenImmersion.lift_fac_assoc,
      Category.assoc]
  let η' : U₀.toScheme := ⟨η, hηU₀⟩
  have hιη : U₀.ι.base η' = η := rfl
  have : Smooth (U₀.ι ≫ t) := inferInstance
  have hη's : (U₀.ι ≫ t).base η' = IsLocalRing.closedPoint R := by
    change t.base (U₀.ι η') = _
    rw [hιη, hηs]
  have hgen' : ∀ y : U₀.toScheme, y ⤳ η' → (U₀.ι ≫ t).base y = IsLocalRing.closedPoint R →
      y = η' := by
    intro y hy hys
    apply U₀.ι.isOpenEmbedding.injective
    rw [hιη]
    apply hgen
    · rw [← hιη]; exact hy.map U₀.ι.base.hom.continuous
    · exact hys
  obtain ⟨hd', hdvr'⟩ := Smooth.isDiscreteValuationRing_stalk_of_forall_specializes
    R (U₀.ι ≫ t) η' hη's hgen'
  have hx : ValuationRing (U₀.toScheme.presheaf.stalk η') := inferInstance
  have hmem : η' ∈ f₀.toRationalMap.domain :=
    AlgebraicGeometry.Scheme.PartialMap.mem_domain_toRationalMap_of_valuationRing_stalk
      (U₀.ι ≫ t) f hY f₀ hf₀ η' hx
  let g₀ : U₀.toScheme.PartialMap X := f₀.toRationalMap.toPartialMap
  have hle : D ≤ g₀.domain := f₀.le_domain_toRationalMap
  have hres : U₀.toScheme.homOfLE hle ≫ g₀.hom = f₀.hom := by
    exact f₀.toPartialMap_toRationalMap_restrict
  have : IsDominant (U₀.toScheme.homOfLE hle) :=
      AlgebraicGeometry.Opens.isDominant_homOfLE hDdense hle
  have hg₀ : g₀.hom ≫ f = g₀.domain.ι ≫ U₀.ι ≫ t := by
    apply ext_of_isDominant (U₀.toScheme.homOfLE hle)
    rw [reassoc_of% hres, hf₀, Scheme.homOfLE_ι_assoc]
  let U : T.Opens := U₀.ι ''ᵁ g₀.domain
  have hηU : η ∈ U := ⟨η', hmem, rfl⟩
  have hgU : ((U₀.ι.isoImage g₀.domain).inv ≫ g₀.hom) ≫ f = U.ι ≫ t := by
    rw [Category.assoc, hg₀, Scheme.Hom.isoImage_inv_ι_assoc]
  refine ⟨U, hηU, ⟨(U₀.ι.isoImage g₀.domain).inv ≫ g₀.hom, hgU⟩, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, genericFibreRestrict_coe_comp_fst]
    have hθrange : Set.range (pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K) ≫ U.ι).base ⊆
        Set.range (D.ι ≫ U₀.ι).base := by
      rintro _ ⟨z, rfl⟩
      have hz : (pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K)).base z ∈
          (pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K)).opensRange := ⟨z, rfl⟩
      rw [Scheme.Hom.opensRange_pullbackFst] at hz
      obtain ⟨x, hx, hxe⟩ := ((pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K)).base z).2
      have hxD : x ∈ D := by
        change U₀.ι.base x ∈ (pullback.fst t (specGenericFibreInclusion R K)).opensRange
        rw [Scheme.Hom.opensRange_pullbackFst]
        exact (congrArg (fun y : T => y ∈ t ⁻¹ᵁ
            (specGenericFibreInclusion R K).opensRange) hxe).mpr hz
      exact ⟨⟨x, hxD⟩, hxe⟩
    obtain ⟨θ, hθ⟩ : ∃ θ : pullback (U.ι ≫ t) (specGenericFibreInclusion R K) ⟶ D.toScheme,
        θ ≫ D.ι ≫ U₀.ι = pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K) ≫ U.ι :=
      ⟨IsOpenImmersion.lift (D.ι ≫ U₀.ι) _ hθrange, IsOpenImmersion.lift_fac _ _ _⟩
    have hA : pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K) ≫
        (U₀.ι.isoImage g₀.domain).inv =
        θ ≫ U₀.toScheme.homOfLE hle := by
      rw [← cancel_mono (g₀.domain.ι ≫ U₀.ι), Category.assoc, Scheme.Hom.isoImage_inv_ι,
        Category.assoc, Scheme.homOfLE_ι_assoc, hθ]
    rw [reassoc_of% hA, hres]
    change θ ≫ (IsOpenImmersion.lift (pullback.fst t (specGenericFibreInclusion R K)) (D.ι ≫
        U₀.ι) hDrange ≫
        uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) =
      pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t
          (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)
    rw [← Category.assoc θ]
    congr 1
    rw [← cancel_mono (pullback.fst t (specGenericFibreInclusion R K)), Category.assoc,
      IsOpenImmersion.lift_fac, hθ]
    simp only [pullback.map, pullback.lift_fst]
  · simp only [Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.map]
    rw [uK.2, pullback.lift_snd, Category.comp_id]

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_nhds_extension_of_isIso_stalkMap_imageInc_fst.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)

universe u

theorem exists_nhds_extension_of_isIso_stalkMap_imageInc_fst
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K))
    [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    {Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ Spec (CommRingCat.of R)) (f₂ : Y₂ ⟶ Spec (CommRingCat.of R))
    (hf₁ : Smooth f₁ ∧ IsSeparated f₁ ∧ LocallyOfFiniteType f₁ ∧ QuasiCompact f₁)
    (hf₂ : Smooth f₂ ∧ IsSeparated f₂ ∧ LocallyOfFiniteType f₂ ∧ QuasiCompact f₂)
    (e₁ : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K)) gK)
        (_he₁ : IsOpenImmersion e₁.1)
    (e₂ : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K)) gK) (_he₂ : IsIso e₂.1)
    (ξ₁ : ↥Y₁) (_hξ₁ : f₁.base ξ₁ = IsLocalRing.closedPoint R)
    (δ : pullback e₁.1 e₂.1 ⟶ pullback f₁ f₂)
    (hδ₁ : δ ≫ pullback.fst f₁ f₂ = pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁
        (specGenericFibreInclusion R K))
    (hδ₂ : δ ≫ pullback.snd f₁ f₂ = pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂
        (specGenericFibreInclusion R K))
    (hopen : IsOpenImmersion δ.toImage)
    (hlocus : Set.range δ.toImage.base =
      {d | f₁.base ((pullback.fst f₁ f₂).base (δ.imageι.base d)) ≠ IsLocalRing.closedPoint R})
    (η : ↥δ.image) (hη₁ : (pullback.fst f₁ f₂).base (δ.imageι.base η) = ξ₁)
    (hiso : IsIso ((δ.imageι ≫ pullback.fst f₁ f₂).stalkMap η)) :
    ∃ (U : Y₁.Opens) (_ : ξ₁ ∈ U) (u : SchemeHomOver (U.ι ≫ f₁) f₂),
      (genericFibreRestrict R K f₂ (U.ι ≫ f₁) u).1 ≫ e₂.1 =
        (genericFibreRestrict R K f₁ (U.ι ≫ f₁) ⟨U.ι, rfl⟩).1 ≫ e₁.1 := by
  obtain ⟨_, _, hlft₁, _⟩ := hf₁
  obtain ⟨_, _, hlft₂, _⟩ := hf₂
  set p₁ := pullback.fst f₁ f₂ with hp₁
  set p₂ := pullback.snd f₁ f₂ with hp₂
  set F := δ.imageι ≫ p₁ with hF
  have : IsLocallyNoetherian Y₁ := LocallyOfFiniteType.isLocallyNoetherian f₁
  have : LocallyOfFiniteType F := by rw [hF]; infer_instance
  obtain ⟨W, hηW, hWimm⟩ :=
    AlgebraicGeometry.exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType F η
  set j := W.ι ≫ F with hj
  have hover : (j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₂) ≫ f₂ = j.opensRange.ι ≫ f₁ := by
    rw [Category.assoc, Category.assoc, Category.assoc, hp₂, ← pullback.condition, ← hp₁,
      ← Category.assoc δ.imageι, ← hF, ← Category.assoc W.ι, ← hj, ← Category.assoc,
      Scheme.Hom.isoOpensRange_inv_comp]
  have hover' : j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₂ ≫ f₂ = j.opensRange.ι ≫ f₁ := by
    simpa only [Category.assoc] using hover
  have hjU : j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₁ = j.opensRange.ι := by
    rw [← hF, ← hj, Scheme.Hom.isoOpensRange_inv_comp]
  refine ⟨j.opensRange, ⟨⟨η, hηW⟩, ?_⟩, ⟨j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₂, hover⟩, ?_⟩
  · change (W.ι ≫ δ.imageι ≫ p₁).base ⟨η, hηW⟩ = ξ₁
    exact hη₁
  set θ : pullback (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ⟶ δ.image :=
    pullback.fst (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ≫ j.isoOpensRange.inv ≫
        W.ι with hθ
  have hθF : θ ≫ δ.imageι ≫ p₁ = pullback.fst (j.opensRange.ι ≫ f₁)
      (specGenericFibreInclusion R K) ≫ j.opensRange.ι := by
    rw [hθ]; simp only [Category.assoc]; rw [hjU]
  have hθrange : Set.range θ.base ⊆ Set.range δ.toImage.base := by
    rintro _ ⟨q, rfl⟩
    rw [hlocus]
    change f₁.base (p₁.base (δ.imageι.base (θ.base q))) ≠ IsLocalRing.closedPoint R
    have hq : f₁.base (p₁.base (δ.imageι.base (θ.base q))) =
        (specGenericFibreInclusion R K).base ((pullback.snd (j.opensRange.ι ≫ f₁)
            (specGenericFibreInclusion R K)).base q) := by
      change (θ ≫ δ.imageι ≫ p₁ ≫ f₁).base q = (pullback.snd (j.opensRange.ι ≫ f₁)
          (specGenericFibreInclusion R K) ≫ (specGenericFibreInclusion R K)).base q
      rw [reassoc_of% hθF, pullback.condition]
    rw [hq]
    exact (range_specGenericFibreInclusion R K).subset ⟨_, rfl⟩
  set θ' := IsOpenImmersion.lift δ.toImage θ hθrange with hθ'
  have hθ'τ : θ' ≫ δ.toImage = θ := IsOpenImmersion.lift_fac _ _ _
  have hθ'δ : θ' ≫ δ = θ ≫ δ.imageι := by
    rw [← hθ'τ, Category.assoc, Scheme.Hom.toImage_imageι]
  have hA : θ' ≫ pullback.fst e₁.1 e₂.1 ≫ pullback.fst f₁ (specGenericFibreInclusion R K) =
      pullback.fst (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ≫ j.opensRange.ι := by
    rw [← hδ₁, ← Category.assoc, hθ'δ, Category.assoc, hθF]
  have hB : θ' ≫ pullback.snd e₁.1 e₂.1 ≫ pullback.fst f₂ (specGenericFibreInclusion R K) =
      pullback.fst (j.opensRange.ι ≫ f₁) (specGenericFibreInclusion R K) ≫ (j.isoOpensRange.inv ≫
          W.ι ≫ δ.imageι ≫ p₂) := by
    rw [← hδ₂, ← Category.assoc, hθ'δ, hθ]; simp only [Category.assoc]
  have E1 : (genericFibreRestrict R K f₁ (j.opensRange.ι ≫ f₁) ⟨j.opensRange.ι, rfl⟩).1 =
      θ' ≫ pullback.fst e₁.1 e₂.1 := by
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, Category.assoc, hA]
    · rw [genericFibreRestrict_coe_comp_snd, ← cancel_mono (specGenericFibreInclusion R K)]
      simp only [Category.assoc]
      rw [← pullback.condition, ← pullback.condition, reassoc_of% hA]
  have E2 : (genericFibreRestrict R K f₂ (j.opensRange.ι ≫ f₁)
      ⟨j.isoOpensRange.inv ≫ W.ι ≫ δ.imageι ≫ p₂, hover⟩).1 = θ' ≫ pullback.snd e₁.1 e₂.1 := by
    apply pullback.hom_ext
    · rw [genericFibreRestrict_coe_comp_fst, Category.assoc, hB]
    · rw [genericFibreRestrict_coe_comp_snd, ← cancel_mono (specGenericFibreInclusion R K)]
      simp only [Category.assoc]
      rw [← pullback.condition, ← pullback.condition, reassoc_of% hB, hover']
  rw [E1, E2, Category.assoc, Category.assoc, pullback.condition]

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_extension_of_forall_nhds_extension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)

theorem exists_opens_extension_of_forall_nhds_extension
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K)))
    (hloc : ∀ η : T, t.base η = IsLocalRing.closedPoint R →
      (∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) f),
        (genericFibreRestrict R K f (U.ι ≫ t) g).1 =
          pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t
              (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1) :
    ∃ (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f),
      (∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      (∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z,
          x.1 ∈ V) ∧
      (genericFibreRestrict R K f (V.ι ≫ t) v).1 =
        pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t
            (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by
  classical
  let Ts := {x : T // t.base x = IsLocalRing.closedPoint R}
  have hS : IsClosed {y : T | t.base y = IsLocalRing.closedPoint R} :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
      (IsLocalRing.maximalIdeal.isMaximal R)).preimage t.base.hom.continuous
  have : QuasiSober Ts := hS.isClosedEmbedding_subtypeVal.quasiSober
  let ι := Option (irreducibleComponents Ts)
  have hZirr : ∀ Z : irreducibleComponents Ts, IsIrreducible (Z.1 : Set Ts) := fun Z => Z.2.1
  have hZcl : ∀ Z : irreducibleComponents Ts, IsClosed (Z.1 : Set Ts) := fun Z =>
    isClosed_of_mem_irreducibleComponents _ Z.2
  let ηZ : irreducibleComponents Ts → Ts := fun Z => (hZirr Z).genericPoint
  have hηZ : ∀ Z, IsGenericPoint (ηZ Z) (Z.1 : Set Ts) := fun Z =>
    (hZirr Z).isGenericPoint_genericPoint (hZcl Z)
  have hgenZ : ∀ Z : irreducibleComponents Ts, ∀ y : T, y ⤳ (ηZ Z).1 →
      t.base y = IsLocalRing.closedPoint R → y = (ηZ Z).1 := by
    intro Z y hy hys
    let y' : Ts := ⟨y, hys⟩
    have hy' : y' ⤳ ηZ Z := Topology.IsInducing.subtypeVal.specializes_iff.mp hy
    have h1 : (Z.1 : Set Ts) ⊆ closure {y'} := by
      rw [← (hηZ Z).def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hy'))
        isClosed_closure
    have h2 : closure {y'} ⊆ (Z.1 : Set Ts) := Z.2.2 isIrreducible_singleton.closure h1
    have h3 : IsGenericPoint y' (Z.1 : Set Ts) := isGenericPoint_def.mpr (h2.antisymm h1)
    exact congrArg Subtype.val (h3.eq (hηZ Z))
  choose U_ hηU g_ hg_ using fun Z : irreducibleComponents Ts =>
    hloc (ηZ Z).1 (ηZ Z).2 (hgenZ Z)
  let Ugen : T.Opens := (pullback.fst t (specGenericFibreInclusion R K)).opensRange
  let ggen : SchemeHomOver (Ugen.ι ≫ t) f :=
    ⟨(Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv ≫ uK.1 ≫
        pullback.fst f (specGenericFibreInclusion R K), by
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% uK.2, ← pullback.condition,
        Scheme.Hom.isoOpensRange_inv_comp_assoc]⟩
  let U : ι → T.Opens := fun i => i.elim Ugen U_
  let g : ∀ i : ι, SchemeHomOver ((U i).ι ≫ t) f := fun i =>
    match i with
    | none => ggen
    | some Z => g_ Z
  let V : T.Opens := ⨆ i, U i
  have hgU : ∀ i, pullback.fst ((U i).ι ≫ t) (specGenericFibreInclusion R K) ≫ (g i).1 =
      pullback.map ((U i).ι ≫ t) (specGenericFibreInclusion R K) t
          (specGenericFibreInclusion R K) (U i).ι (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 ≫ pullback.fst f
            (specGenericFibreInclusion R K) := by
    intro i
    cases i with
    | none =>
      have hnone : pullback.fst (Ugen.ι ≫ t) (specGenericFibreInclusion R K) ≫
          (Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv =
          pullback.map (Ugen.ι ≫ t) (specGenericFibreInclusion R K) t
              (specGenericFibreInclusion R K) Ugen.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
            ((Category.comp_id _).trans (Category.id_comp _).symm) := by
        rw [← cancel_mono (pullback.fst t (specGenericFibreInclusion R K))]
        simp only [Category.assoc, pullback.map, pullback.lift_fst]
        rw [Scheme.Hom.isoOpensRange_inv_comp]
      change pullback.fst (Ugen.ι ≫ t) (specGenericFibreInclusion R K) ≫
          ((Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv ≫
              uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K)) = _
      rw [reassoc_of% hnone]
      rfl
    | some Z =>
      change pullback.fst ((U_ Z).ι ≫ t) (specGenericFibreInclusion R K) ≫ (g_ Z).1 =
        pullback.map ((U_ Z).ι ≫ t) (specGenericFibreInclusion R K) t
            (specGenericFibreInclusion R K) (U_ Z).ι (𝟙 _) (𝟙 _) (Category.comp_id _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 ≫ pullback.fst f
              (specGenericFibreInclusion R K)
      rw [← genericFibreRestrict_coe_comp_fst (R := R) (K := K) f ((U_ Z).ι ≫ t) (g_ Z), hg_ Z,
        Category.assoc]
  let 𝒰 : V.toScheme.OpenCover := Scheme.Opens.iSupOpenCover U
  let jU (i : ι) : (U i).toScheme ⟶ V.toScheme := T.homOfLE (le_iSup U i)
  have (i : ι) : IsOpenImmersion (jU i) :=
    inferInstanceAs (IsOpenImmersion (T.homOfLE (le_iSup U i)))
  have hUι : ∀ k : ι, jU k ≫ (⨆ i, U i).ι = (U k).ι := fun k => Scheme.homOfLE_ι T (le_iSup U k)
  have hcompat : ∀ i j : ι, pullback.fst (jU i) (jU j) ≫ (g i).1 =
      pullback.snd (jU i) (jU j) ≫ (g j).1 := by
    intro i j
    let p : pullback (jU i) (jU j) ⟶ Spec (CommRingCat.of R) :=
      pullback.fst (jU i) (jU j) ≫ (U i).ι ≫ t
    have h12 : pullback.fst (jU i) (jU j) ≫ (U i).ι = pullback.snd (jU i) (jU j) ≫ (U j).ι := by
      rw [← hUι i, ← hUι j, pullback.condition_assoc]
    have hp₂ : pullback.snd (jU i) (jU j) ≫ (U j).ι ≫ t = p := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ t) h12.symm).trans (Category.assoc _ _ _))
    have : Smooth p := inferInstance
    let a : SchemeHomOver p f := ⟨pullback.fst _ _ ≫ (g i).1, by
      rw [Category.assoc]; exact congrArg (fun h => pullback.fst (jU i) (jU j) ≫ h) (g i).2⟩
    let b : SchemeHomOver p f := ⟨pullback.snd _ _ ≫ (g j).1, by
      rw [Category.assoc]; exact (congrArg (fun h => pullback.snd (jU i) (jU j) ≫ h)
          (g j).2).trans hp₂⟩
    suffices hab : a = b from congrArg Subtype.val hab
    apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K f p
    apply Subtype.ext
    apply pullback.hom_ext
    · simp only [genericFibreRestrict_coe_comp_fst]
      have key : ∀ (k : ι) (q : pullback (jU i) (jU j) ⟶ (U k).toScheme) (hq : q ≫ (U k).ι ≫
          t = p),
          pullback.fst p (specGenericFibreInclusion R K) ≫ q ≫ (g k).1 =
            pullback.lift (pullback.fst p (specGenericFibreInclusion R K) ≫ q ≫ (U k).ι)
                (pullback.snd p (specGenericFibreInclusion R K))
              (by rw [Category.assoc, Category.assoc, hq, pullback.condition]) ≫
                uK.1 ≫ pullback.fst f (specGenericFibreInclusion R K) := by
        intro k q hq
        have hm : pullback.fst p (specGenericFibreInclusion R K) ≫ q = pullback.map p
            (specGenericFibreInclusion R K) ((U k).ι ≫ t) (specGenericFibreInclusion R K) q
            (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id, hq]) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              pullback.fst ((U k).ι ≫ t) (specGenericFibreInclusion R K) := by
          simp only [pullback.map, pullback.lift_fst]
        rw [← Category.assoc (pullback.fst p (specGenericFibreInclusion R K)), hm,
            Category.assoc, hgU k]
        simp only [← Category.assoc]
        congr 2
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
        · simp only [Category.assoc, pullback.map, pullback.lift_snd,
            Category.comp_id]
      change pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.fst (jU i) (jU j) ≫
          (g i).1 =
        pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.snd (jU i) (jU j) ≫ (g j).1
      refine (key i (pullback.fst _ _) rfl).trans ?_
      refine Eq.trans ?_ (key j (pullback.snd _ _) hp₂).symm
      have h12' : pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.fst (jU i) (jU j) ≫
          (U i).ι =
          pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.snd (jU i) (jU j) ≫
              (U j).ι := by rw [h12]
      congr 2
    · simp only [genericFibreRestrict_coe_comp_snd]
  let v : V.toScheme ⟶ X := 𝒰.glueMorphisms (fun i => (g i).1) hcompat
  have hv : ∀ i : ι, jU i ≫ v = (g i).1 := fun i => 𝒰.ι_glueMorphisms _ _ i
  have hvf : v ≫ f = V.ι ≫ t := by
    apply 𝒰.hom_ext
    intro i
    change ι at i
    change jU i ≫ v ≫ f = jU i ≫ V.ι ≫ t
    rw [reassoc_of% (hv i)]
    refine ((g i).2).trans ?_
    change (U i).ι ≫ t = T.homOfLE (le_iSup U i) ≫ (⨆ i, U i).ι ≫ t
    rw [Scheme.homOfLE_ι_assoc]
  refine ⟨V, ⟨v, hvf⟩, ?_, ?_, ?_⟩
  · intro x hx
    have : x ∈ U none := by
      change x ∈ (pullback.fst t (specGenericFibreInclusion R K)).opensRange
      rw [Scheme.Hom.opensRange_pullbackFst]
      change t.base x ∈ (specGenericFibreInclusion R K).opensRange
      change t.base x ∈ Set.range (specGenericFibreInclusion R K).base
      rw [range_specGenericFibreInclusion R K]
      exact hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨none, this⟩
  · intro Z hZ
    exact ⟨ηZ ⟨Z, hZ⟩, (hηZ ⟨Z, hZ⟩).mem, TopologicalSpace.Opens.mem_iSup.mpr ⟨some ⟨Z, hZ⟩,
        hηU ⟨Z, hZ⟩⟩⟩
  · apply pullback.hom_ext
    · simp only [genericFibreRestrict_coe_comp_fst]
      have hrange : Set.range (pullback.fst (V.ι ≫ t)
          (specGenericFibreInclusion R K)).base ⊆ Set.range (jU none).base := by
        rintro _ ⟨z, rfl⟩
        have hz : (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base z ∈ Set.range
            (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base :=
          ⟨z, rfl⟩
        rw [IsOpenImmersion.range_pullbackFst] at hz
        have h1 : Set.range (jU none).base = ((V.ι ⁻¹ᵁ (U none) : V.toScheme.Opens) : Set V) := by
          change Set.range (T.homOfLE (le_iSup U none)).base = _
          rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
        rw [h1]
        change V.ι.base ((pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base z) ∈
            (pullback.fst t (specGenericFibreInclusion R K)).opensRange
        rw [Scheme.Hom.opensRange_pullbackFst]
        exact hz
      let l := IsOpenImmersion.lift (jU none) (pullback.fst (V.ι ≫ t)
          (specGenericFibreInclusion R K)) hrange
      have hl : l ≫ jU none = pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K) :=
          IsOpenImmersion.lift_fac _ _ _
      have hkey : l ≫ (Scheme.Hom.isoOpensRange (pullback.fst t
          (specGenericFibreInclusion R K))).inv =
          pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t
              (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
            ((Category.comp_id _).trans (Category.id_comp _).symm) := by
        apply (cancel_mono (pullback.fst t (specGenericFibreInclusion R K))).mp
        calc
          _ = l ≫ Ugen.ι := (Category.assoc _ _ _).trans
            (congrArg (l ≫ ·) (Scheme.Hom.isoOpensRange_inv_comp _))
          _ = (l ≫ jU none) ≫ V.ι :=
            (congrArg (l ≫ ·) (hUι none).symm).trans (Category.assoc _ _ _).symm
          _ = pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K) ≫ V.ι :=
            congrArg (· ≫ V.ι) hl
          _ = _ := (pullback.lift_fst _ _ _).symm
      rw [← hl, Category.assoc, hv none]
      change l ≫ ((Scheme.Hom.isoOpensRange (pullback.fst t
          (specGenericFibreInclusion R K))).inv ≫ uK.1 ≫ pullback.fst f
          (specGenericFibreInclusion R K)) = _
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ uK.1 ≫ pullback.fst f
          (specGenericFibreInclusion R K)) hkey).trans (Category.assoc _ _ _).symm)
    · simp only [Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.map]
      rw [uK.2, pullback.lift_snd, Category.comp_id]

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace NeronModelInfra

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AbelianVarieties.NOSProofs.AssociativityRestriction.PartialMultiplication
  (range_specGenericFibreInclusion)

theorem exists_opens_extension_of_isProper_of_smooth
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X T : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd f (specGenericFibreInclusion R K))) :
    ∃ (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f),
      (∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) ∧
      (∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z,
          x.1 ∈ V) ∧
      (genericFibreRestrict R K f (V.ι ≫ t) v).1 =
        pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t
            (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1  := by
  apply exists_opens_extension_of_forall_nhds_extension R K f t uK
  intro η hηs hgen
  exact exists_nhds_extension_of_isProper_of_smooth R K f t uK η hηs hgen

end NeronModelInfra
end
