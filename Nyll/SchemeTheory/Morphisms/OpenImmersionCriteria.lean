/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Smooth.Locus
public import Nyll.SchemeTheory.LocalGeometry.SmoothnessDefect
public import Nyll.SchemeTheory.RingTheory.Ramification.UnramifiedDVR
public import Nyll.SchemeTheory.LocalGeometry.DVRStalks
public import Nyll.SchemeTheory.LocalGeometry.SmoothDVRStalk

/-! # Open immersions from local and DVR stalk comparisons -/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (x : X) [IsIso (f.stalkMap x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hV, g, hg1, hg2⟩ := spread_out_of_isGermInjective (sX := 𝟙 Y) (sY := f) (x := f x) (y
    := x)
    rfl (inv (f.stalkMap x)) (by
      rw [IsIso.hom_inv_id, Scheme.Hom.stalkMap_id]
      change 𝟙 _ = Y.presheaf.stalkSpecializes (specializes_refl (f x)) ≫ 𝟙 _
      rw [TopCat.Presheaf.stalkSpecializes_refl, Category.comp_id])
  rw [Category.comp_id] at hg2
  let W₀ : X.Opens := f ⁻¹ᵁ V
  have hxW₀ : x ∈ W₀ := hV
  have hrange : Set.range (W₀.ι ≫ f) ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact w.2
  let fV : (W₀ : Scheme.{u}) ⟶ V := IsOpenImmersion.lift V.ι (W₀.ι ≫ f) hrange
  have hfV : fV ≫ V.ι = W₀.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  let k : (W₀ : Scheme.{u}) ⟶ X := fV ≫ g
  have hk₀ : W₀.fromSpecStalkOfMem x hxW₀ ≫ k = W₀.fromSpecStalkOfMem x hxW₀ ≫ W₀.ι := by
    have h1 : W₀.fromSpecStalkOfMem x hxW₀ ≫ fV = Spec.map (f.stalkMap x) ≫ V.fromSpecStalkOfMem
      (f x) hV := by
      rw [← cancel_mono V.ι, Category.assoc, hfV, Scheme.Opens.fromSpecStalkOfMem_ι_assoc,
        Category.assoc,
        Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkMap_fromSpecStalk]
    change W₀.fromSpecStalkOfMem x hxW₀ ≫ fV ≫ g = _
    rw [← Category.assoc, h1, Category.assoc, ← hg1, ← Category.assoc, ← Spec.map_comp,
      IsIso.inv_hom_id,
      Spec.map_id, Category.id_comp, Scheme.Opens.fromSpecStalkOfMem_ι]
  let x₀ : (W₀ : Scheme.{u}) := ⟨x, hxW₀⟩
  have : IsLocallyNoetherian (W₀ : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian W₀.ι
  have : (W₀ : Scheme.{u}).IsGermInjectiveAt x₀ := inferInstance
  have hk : (W₀ : Scheme.{u}).fromSpecStalk x₀ ≫ k =
      (W₀ : Scheme.{u}).fromSpecStalk x₀ ≫ W₀.ι := by
    have h := hk₀
    simp only [Scheme.Opens.fromSpecStalkOfMem, Category.assoc] at h
    exact (cancel_epi (Spec.map (inv (W₀.ι.stalkMap x₀)))).mp h
  obtain ⟨W, hxW, hW⟩ := spread_out_unique_of_isGermInjective' k W₀.ι hk
  let jW : (W : Scheme.{u}) ⟶ X := W.ι ≫ W₀.ι
  let U : X.Opens := jW.opensRange
  have hxU : x ∈ U := ⟨⟨⟨x, hxW₀⟩, hxW⟩, rfl⟩
  let V' : (V : Scheme.{u}).Opens := g ⁻¹ᵁ U
  have hkW : W.ι ≫ k = jW := hW
  have hα_range : Set.range (W.ι ≫ fV) ⊆ Set.range V'.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change g ((W.ι ≫ fV) w) ∈ U
    rw [← Scheme.Hom.comp_apply, Category.assoc]
    change (W.ι ≫ k) w ∈ U
    rw [hkW]
    exact ⟨w, rfl⟩
  let α : (W : Scheme.{u}) ⟶ V' := IsOpenImmersion.lift V'.ι (W.ι ≫ fV) hα_range
  have hα : α ≫ V'.ι = W.ι ≫ fV := IsOpenImmersion.lift_fac _ _ _
  have hβ_range : Set.range (V'.ι ≫ g) ⊆ Set.range jW := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  let β : (V' : Scheme.{u}) ⟶ W := IsOpenImmersion.lift jW (V'.ι ≫ g) hβ_range
  have hβ : β ≫ jW = V'.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hαβ : α ≫ β = 𝟙 _ := by
    rw [← cancel_mono jW, Category.assoc, hβ, ← Category.assoc, hα, Category.assoc,
      Category.id_comp]
    exact hkW
  have hβα : β ≫ α = 𝟙 _ := by
    rw [← cancel_mono (V'.ι ≫ V.ι), Category.assoc, ← Category.assoc α, hα, Category.assoc, hfV,
      Category.id_comp]
    rw [← Category.assoc W.ι, ← Category.assoc β, hβ, Category.assoc, hg2]
  have : IsIso α := ⟨⟨β, hαβ, hβα⟩⟩
  have hUι : U.ι = (IsOpenImmersion.isoOfRangeEq U.ι jW (by rw [Scheme.Opens.range_ι]; rfl)).hom ≫
    jW :=
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm
  refine ⟨U, hxU, ?_⟩
  have hjWf : jW ≫ f = α ≫ V'.ι ≫ V.ι := by
    rw [← Category.assoc α, hα]
    simp only [jW, Category.assoc, hfV]
  rw [hUι, Category.assoc, hjWf]
  infer_instance

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_opens_comp_eq_base_eq_of_isLocalHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem exists_opens_comp_eq_base_eq_of_isLocalHom
    {X Y Y' : Scheme.{u}} (U : X.Opens) (α : (U : Scheme.{u}) ⟶ Y) (z : X) (hzU : z ∈ U)
    [X.IsGermInjectiveAt z]
    (β : Y' ⟶ Y) [LocallyOfFiniteType β]
    {O : Type u} [CommRing O] [IsLocalRing O]
    (ℓ₀ : Spec (CommRingCat.of O) ⟶ Y) (ℓ : Spec (CommRingCat.of O) ⟶ Y') (hℓ : ℓ ≫ β = ℓ₀)
    (φ : CommRingCat.of O ⟶ X.presheaf.stalk z) [IsLocalHom φ.hom]
    (hφ : Spec.map φ ≫ ℓ₀ = U.fromSpecStalkOfMem z hzU ≫ α) :
    ∃ (U' : X.Opens) (hU' : U' ≤ U) (hzU' : z ∈ U') (α' : (U' : Scheme.{u}) ⟶ Y'),
      α' ≫ β = X.homOfLE hU' ≫ α ∧ α'.base ⟨z, hzU'⟩ = ℓ.base (IsLocalRing.closedPoint O) := by
  let zU : (U : Scheme.{u}) := ⟨z, hzU⟩
  have : (U : Scheme.{u}).IsGermInjectiveAt zU := by
    have hzz : U.ι.base zU = z := rfl
    apply (isGermInjectiveAt_iff_of_isOpenImmersion (f := U.ι)
      (x := zU)).mp
    rw [hzz]
    infer_instance
  let w : Spec ((U : Scheme.{u}).presheaf.stalk zU) ⟶ Y' := Spec.map (U.ι.stalkMap zU)
    ≫ Spec.map φ ≫ ℓ
  have hUfrom : Spec.map (U.ι.stalkMap zU) ≫ U.fromSpecStalkOfMem z hzU = (U :
    Scheme.{u}).fromSpecStalk zU := by
    change Spec.map (U.ι.stalkMap zU) ≫
      Spec.map (inv (U.ι.stalkMap zU)) ≫ _ = _
    rw [← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id, Category.id_comp]
  have hw : w ≫ β = (U : Scheme.{u}).fromSpecStalk zU ≫ α := by
    simp only [w, Category.assoc, hℓ]
    erw [hφ, ← Category.assoc, hUfrom]
  obtain ⟨W, hzW, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' α β w hw
  have hzW' : z ∈ U.ι ''ᵁ W := (Scheme.Opens.mem_ι_image_iff (x := zU)).mpr hzW
  let zW : (W : Scheme.{u}) := ⟨zU, hzW⟩
  let zV : (U.ι ''ᵁ W : X.Opens).toScheme := ⟨z, hzW'⟩
  refine ⟨U.ι ''ᵁ W, Scheme.Opens.ι_image_le U W, hzW', (U.ι.isoImage W).inv ≫ g, ?_, ?_⟩
  · rw [Category.assoc, hg₂, ← Category.assoc]
    congr 1
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.isoImage_inv_ι, Scheme.homOfLE_ι]
  · have hpt : ((U.ι.isoImage W).inv ≫ g).base zV = g.base zW := by
      rw [Scheme.Hom.comp_apply]
      congr 1
      have h1 : ((U.ι.isoImage W).inv ≫ W.ι).base zV = zU := by
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, Category.assoc, Scheme.Hom.isoImage_inv_ι]
        rfl
      apply W.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h1]
      rfl
    rw [hpt]
    let cU : Spec ((U : Scheme.{u}).presheaf.stalk zU) := IsLocalRing.closedPoint _
    have h2 : g zW = w cU := by
      rw [hg₁, Scheme.Hom.comp_apply]
      apply congrArg g
      apply W.ι.isOpenEmbedding.injective
      change zU = (W.fromSpecStalkOfMem zU hzW ≫ W.ι) cU
      rw [Scheme.Opens.fromSpecStalkOfMem_ι]
      exact Scheme.fromSpecStalk_closedPoint.symm
    rw [h2]
    change ℓ ((Spec.map φ) ((Spec.map (U.ι.stalkMap zU)) cU)) =
      ℓ (IsLocalRing.closedPoint O)
    apply congrArg ℓ
    have e1 : (Spec.map (U.ι.stalkMap zU)) cU =
        IsLocalRing.closedPoint (X.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint (U.ι.stalkMap zU).hom
    rw [e1]
    exact IsLocalRing.comap_closedPoint φ.hom

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_isIso_morphismRestrict_of_isOpenImmersion_of_range_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem isIso_morphismRestrict_of_isOpenImmersion_of_range_eq
    {P P' : Scheme.{u}} (β : P' ⟶ P) (U : P.Opens) (s : (U : Scheme.{u}) ⟶ P') [IsOpenImmersion s]
    (hsβ : s ≫ β = U.ι) (hsr : Set.range s.base = β.base ⁻¹' (U : Set P)) :
    IsIso (β ∣_ U) := by
  have hr : Set.range s.base = Set.range (β ⁻¹ᵁ U).ι.base := by
    rw [hsr, Scheme.Opens.range_ι]; rfl
  let e := IsOpenImmersion.isoOfRangeEq s (β ⁻¹ᵁ U).ι hr
  have he : e.hom ≫ (β ⁻¹ᵁ U).ι = s := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have h1 : e.hom ≫ (β ∣_ U) = 𝟙 _ := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, he, hsβ,
      Category.id_comp]
  have h2 : β ∣_ U = e.inv := by
    rw [← Category.id_comp (β ∣_ U), ← e.inv_hom_id, Category.assoc, h1, Category.comp_id]
  rw [h2]
  infer_instance

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

open CategoryTheory AlgebraicGeometry

universe u

namespace OpenImmNearDVR

theorem main
    {U W : Scheme.{u}} (v : U ⟶ W) [LocallyOfFiniteType v] [IsLocallyNoetherian W]
    (x : U) [IsDomain (U.presheaf.stalk x)] [IsDiscreteValuationRing (U.presheaf.stalk x)]
    (π : W.presheaf.stalk (v.base x)) (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime)
    (hfrac : let : Algebra (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)) :=
        ((algebraMap (U.presheaf.stalk x) (FractionRing (U.presheaf.stalk x))).comp (v.stalkMap
          x).hom).toAlgebra
      IsFractionRing (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)))
    (hfs : let : Algebra (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x) := (v.stalkMap
      x).hom.toAlgebra
      Algebra.FormallySmooth (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x)) :
    ∃ V : U.Opens, x ∈ V ∧ IsOpenImmersion (V.ι ≫ v) := by
  classical
  let O := U.presheaf.stalk x
  let O' := W.presheaf.stalk (v.base x)
  let F := FractionRing O
  let φ : O' →+* O := (v.stalkMap x).hom
  let instOO : Algebra O' O := φ.toAlgebra
  let instOF : Algebra O' F := ((algebraMap O F).comp φ).toAlgebra
  have instT : @IsScalarTower O' O F instOO.toSMul Algebra.toSMul instOF.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing O' F := hfrac
  have hφF : Function.Injective (algebraMap O' F) := IsFractionRing.injective O' F
  have hinj : Function.Injective (algebraMap O' O) := by
    intro a b hab
    apply hφF
    change algebraMap O F (φ a) = algebraMap O F (φ b)
    exact congrArg (algebraMap O F) hab
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU₀, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (v.base x)) isOpen_univ
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, hle⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ v ⁻¹ᵁ U₀ from hxU₀) (v ⁻¹ᵁ U₀).2
  have e : V₀ ≤ v ⁻¹ᵁ U₀ := hle
  let A := Γ(W, U₀)
  let B := Γ(U, V₀)
  let instAB : Algebra A B := (v.appLE U₀ V₀ e).hom.toAlgebra
  have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  have hft : (v.appLE U₀ V₀ e).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) v inferInstance ⟨U₀, hU₀⟩ ⟨V₀, hV₀⟩ e
  have : Algebra.FiniteType A B := hft
  have : Algebra.FinitePresentation A B := (Algebra.FinitePresentation.of_finiteType).mp
    inferInstance
  let 𝔓 := hV₀.primeIdealOf ⟨x, hxV₀⟩
  have hsmooth : 𝔓 ∈ Algebra.smoothLocus A B := by
    rw [← formallySmooth_stalkMap_iff U₀ hU₀ V₀ hV₀ e hxV₀]
    exact hfs
  have : Algebra.IsSmoothAt A 𝔓.asIdeal := hsmooth
  obtain ⟨s, hs𝔓, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth A 𝔓.asIdeal
  have : Algebra.Smooth A (Localization.Away s) := hsm
  let instBO : Algebra B O := TopCat.Presheaf.algebra_section_stalk U.presheaf (⟨x, hxV₀⟩ : V₀)
  have hlocO : IsLocalization.AtPrime O 𝔓.asIdeal := hV₀.isLocalization_stalk ⟨x, hxV₀⟩
  let instAO : Algebra A O := ((algebraMap B O).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let instAO' : Algebra A O' := TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨v.base x, hxU₀⟩
    : U₀)
  have hlocO' : IsLocalization.AtPrime O' (hU₀.primeIdealOf ⟨v.base x, hxU₀⟩).asIdeal :=
    hU₀.isLocalization_stalk ⟨v.base x, hxU₀⟩
  have htower : ∀ a : A, algebraMap O' O (algebraMap A O' a) = algebraMap A O a := by
    intro a
    change (v.stalkMap x).hom ((W.presheaf.germ U₀ (v.base x) hxU₀).hom a) =
      (U.presheaf.germ V₀ x hxV₀).hom ((v.appLE U₀ V₀ e).hom a)
    have hv := congrArg (fun ψ => ψ.hom a) (Scheme.Hom.germ_stalkMap v U₀ x hxU₀)
    have hr := congrArg (fun ψ => ψ.hom ((v.app U₀).hom a))
      (U.presheaf.germ_res (homOfLE e) x hxV₀)
    exact hv.trans hr.symm
  have : IsScalarTower A O' O := IsScalarTower.of_algebraMap_eq fun a => (htower a).symm
  let Bs := Localization.Away s
  let 𝔓s : Ideal Bs := Ideal.map (algebraMap B Bs) 𝔓.asIdeal
  have hdisj : Disjoint (Submonoid.powers s : Set B) ↑𝔓.asIdeal :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime s).mpr hs𝔓
  have h𝔓s : 𝔓s.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) Bs _
    inferInstance hdisj
  have hcomap : 𝔓s.comap (algebraMap B Bs) = 𝔓.asIdeal :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) Bs inferInstance hdisj
  let O₂ := Localization.AtPrime 𝔓s
  have : IsLocalization.AtPrime O₂ 𝔓.asIdeal := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers s) O₂ 𝔓s
    convert h using 2
    exact hcomap.symm
  have : Module.Flat A Bs := inferInstance
  have : Module.Flat Bs O₂ := IsLocalization.flat O₂ 𝔓s.primeCompl
  have : Module.Flat A O₂ := Module.Flat.trans A Bs O₂
  let eO : O₂ ≃ₐ[B] O := IsLocalization.algEquiv 𝔓.asIdeal.primeCompl O₂ O
  have : Module.Flat A O :=
    Module.Flat.of_linearEquiv ((eO.restrictScalars A).toLinearEquiv).symm
  have : Module.Flat O' O :=
    (Module.flat_iff_of_isLocalization O' (hU₀.primeIdealOf ⟨v.base x, hxU₀⟩).asIdeal.primeCompl
      O).mpr inferInstance
  have : IsLocalHom (algebraMap O' O) := inferInstanceAs (IsLocalHom (v.stalkMap x).hom)
  have hbij : Function.Bijective (algebraMap O' O) :=
    IsDiscreteValuationRing.bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing
      (O' := O') (O := O) (F := F) hinj π hπ0 hπ
  have : IsIso (v.stalkMap x) := by
    have : v.stalkMap x = (RingEquiv.ofBijective φ hbij).toCommRingCatIso.hom := by
      ext a; rfl
    rw [this]
    infer_instance
  exact AlgebraicGeometry.exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType v x

end OpenImmNearDVR

theorem exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
    {U W : Scheme.{u}} (v : U ⟶ W) [LocallyOfFiniteType v] [IsLocallyNoetherian W]
    (x : U) [IsDomain (U.presheaf.stalk x)] [IsDiscreteValuationRing (U.presheaf.stalk x)]
    (π : W.presheaf.stalk (v.base x)) (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime)
    (hfrac : let : Algebra (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)) :=
        ((algebraMap (U.presheaf.stalk x) (FractionRing (U.presheaf.stalk x))).comp (v.stalkMap
          x).hom).toAlgebra
      IsFractionRing (W.presheaf.stalk (v.base x)) (FractionRing (U.presheaf.stalk x)))
    (hfs : let : Algebra (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x) := (v.stalkMap
      x).hom.toAlgebra
      Algebra.FormallySmooth (W.presheaf.stalk (v.base x)) (U.presheaf.stalk x)) :
    ∃ V : U.Opens, x ∈ V ∧ IsOpenImmersion (V.ι ≫ v) :=
  OpenImmNearDVR.main v x π hπ0 hπ hfrac hfs

end AlgebraicGeometry
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Smooth_snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem Smooth.snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {Z X Y : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (g : Y ⟶ Spec (CommRingCat.of R)) [Smooth z] [Smooth f] [Smooth g] [LocallyOfFiniteType g]
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint
      R → y = η)
    (yT : ↑Y) (hyT : g.base yT = IsLocalRing.closedPoint R)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z g) (hv₁ : v ≫ pullback.fst z g = U₀.ι ≫ pullback.fst z f)
    (hgen : yT ⤳ (v ≫ pullback.snd z g).base ⟨η, hηU⟩)
    (hdom : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
    (hdom' : IsDomain ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)))
    (hfrac : let : Algebra ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ :
      Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ :
          Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ :
        Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
    (hfs : let : Algebra ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ :
      Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z g).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ :
        Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :
    (v ≫ pullback.snd z g).base ⟨η, hηU⟩ = yT ∧
      ∃ (U₁ : (pullback z f).Opens) (_ : η ∈ U₁) (h₁ : U₁ ≤ U₀),
        IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v) := by
  classical
  set x : ↥(U₀ : Scheme.{u}) := ⟨η, hηU⟩ with hx
  have hU₀ι : ∀ u : ↥(U₀ : Scheme.{u}), U₀.ι.base u = u.1 := fun u => rfl
  have hQ : v ≫ pullback.fst z g ≫ z = U₀.ι ≫ pullback.fst z f ≫ z := by rw [← Category.assoc,
    hv₁, Category.assoc]
  have hxs : (U₀.ι ≫ pullback.fst z f ≫ z).base x = IsLocalRing.closedPoint R := by
    rw [Scheme.Hom.comp_apply]; exact hη
  have hxmax : ∀ y : ↥(U₀ : Scheme.{u}), y ⤳ x → (U₀.ι ≫ pullback.fst z f ≫ z).base y =
    IsLocalRing.closedPoint R →
      y = x := by
    intro y hy hys
    apply U₀.ι.isOpenEmbedding.injective
    rw [Scheme.Hom.comp_apply] at hys
    exact hmax _ (hy.map U₀.ι.continuous) hys
  obtain ⟨_, hdvr⟩ :=
    AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R (U₀.ι ≫
      pullback.fst z f ≫ z)
      x hxs hxmax
  have : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk x) := hdom
  have : IsDiscreteValuationRing ((U₀ : Scheme.{u}).presheaf.stalk x) := hdvr
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hvxs : (pullback.fst z g ≫ z).base (v.base x) = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, hQ]; exact hxs
  let algQ : Algebra R ((pullback z g).presheaf.stalk (v.base x)) := NeronModelInfra.stalkAlgebra
    (pullback.fst z g ≫ z) (v.base x)
  obtain ⟨hπ0, hπ⟩ :=
    AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint ϖ hϖ
      (pullback.fst z g ≫ z) (v.base x) hvxs
      (NeronModelInfra.fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra (pullback.fst z g ≫
        z) (v.base x))
  have : LocallyOfFiniteType (v ≫ pullback.fst z g ≫ z) := by rw [hQ]; infer_instance
  have : LocallyOfFiniteType v := locallyOfFiniteType_of_comp v (pullback.fst z g ≫ z)
  have : IsLocallyNoetherian (pullback z g) := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.fst z g ≫ z)
  have : IsDomain ((pullback z g).presheaf.stalk (v.base x)) := hdom'
  obtain ⟨V₁, hxV₁, hV₁⟩ :=
    exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing
      v x (algebraMap R _ ϖ) hπ0 hπ hfrac hfs
  let U₁ : (pullback z f).Opens := U₀.ι ''ᵁ V₁
  have h₁ : U₁ ≤ U₀ := Scheme.Opens.ι_image_le U₀ V₁
  have hηU₁ : η ∈ U₁ := ⟨x, hxV₁, rfl⟩
  have hhom : (pullback z f).homOfLE h₁ = (U₀.ι.isoImage V₁).inv ≫ V₁.ι := by
    rw [← cancel_mono U₀.ι, Scheme.homOfLE_ι, Category.assoc, Scheme.Hom.isoImage_inv_ι]
  have hv : IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v) := by
    rw [hhom, Category.assoc]; infer_instance
  refine ⟨?_, U₁, hηU₁, h₁, hv⟩
  have hgen₁ : GeneralizingMap ((pullback z f).homOfLE h₁ ≫ v).base :=
    Topology.IsOpenEmbedding.generalizingMap ((pullback z f).homOfLE h₁ ≫ v).isOpenEmbedding
  have hgen₂ : GeneralizingMap (pullback.snd z g).base := Flat.generalizingMap _
  have hgenq := hgen₁.comp hgen₂
  set x₁ : ↥(U₁ : Scheme.{u}) := ⟨η, hηU₁⟩ with hx₁
  have hx₁x : ((pullback z f).homOfLE h₁).base x₁ = x := by
    apply U₀.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    rfl
  have hstr : U₁.ι ≫ pullback.fst z f ≫ z = ((pullback z f).homOfLE h₁ ≫ v) ≫ pullback.snd z g ≫ g
    := by
    rw [← Scheme.homOfLE_ι (pullback z f) h₁, Category.assoc, ← hQ, pullback.condition,
      Category.assoc]
  have key : ∀ y' : ↥Y, y' ⤳ (pullback.snd z g).base (v.base x) → g.base y' =
    IsLocalRing.closedPoint R →
      y' = (pullback.snd z g).base (v.base x) := by
    intro y' hy' hy's
    have hy'' : y' ⤳ ((pullback.snd z g).base ∘ ((pullback z f).homOfLE h₁ ≫ v).base) x₁ := by
      rwa [Function.comp_apply, Scheme.Hom.comp_apply, hx₁x]
    obtain ⟨x', hx'x₁, hx'y⟩ := hgenq hy''
    have hsp : U₁.ι.base x' ⤳ η := hx'x₁.map U₁.ι.continuous
    have hx's : (pullback.fst z f ≫ z).base (U₁.ι.base x') = IsLocalRing.closedPoint R := by
      rw [← Scheme.Hom.comp_apply, hstr, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ←
        Function.comp_apply
        (f := ⇑(ConcreteCategory.hom (pullback.snd z g).base)), hx'y]
      exact hy's
    have hx'η : U₁.ι.base x' = η := hmax _ hsp hx's
    have hx'eq : x' = x₁ := U₁.ι.isOpenEmbedding.injective hx'η
    rw [← hx'y, hx'eq, Function.comp_apply, Scheme.Hom.comp_apply, hx₁x]
  rw [Scheme.Hom.comp_apply] at hgen ⊢
  exact (key yT hgen hyT).symm

end AlgebraicGeometry
end
