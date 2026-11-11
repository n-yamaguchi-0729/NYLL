/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Nyll.AbelianVarieties.Geometry.RelativeDimension
public import Nyll.AbelianVarieties.Geometry.TopForms
public import Nyll.AbelianVarieties.NeronModels.Differentials.ComponentData
public import Nyll.AbelianVarieties.NeronModels.Differentials.Components
public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms
public import Nyll.AbelianVarieties.NeronModels.LocalExtensionCharts
public import Nyll.AbelianVarieties.NeronModels.MinimalComponents
public import Nyll.AbelianVarieties.NeronModels.ModelCovers
public import Nyll.AbelianVarieties.NeronModels.StalkExtensions
public import Nyll.AbelianVarieties.NeronModels.WeakModel
public import Nyll.SchemeTheory.Morphisms.OpenImmersionCriteria
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.BaseChange
public import Nyll.SchemeTheory.GroupSchemes.RelativeGroupLaw.Basic
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.LocallyFreeOfRank
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections
public import Nyll.SchemeTheory.BaseChange.SchemeHomOver
public import Nyll.SchemeTheory.CategoryTheory.SchemeHomOver

/-!
# Translation charts from minimal components

Construct local translation charts from minimal differential orders, then glue them into
smooth models with compatible left and right translation charts.
-/

@[expose] public section

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_translation_chart_of_minimal_representative.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry GoodReductionJacobian

universe u

open NeronModelInfra renaming
 exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
 → minimal_stalk_smooth

open NeronModelInfra renaming
 isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
 → translation_stalk_fractionRing

open AlgebraicGeometry.Smooth renaming
 snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
 → open_chart_of_stalk


theorem exists_translation_chart_of_minimal_representative
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (D : MinimalComponentData R K gK d ω)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f))
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z)
      T.f)
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
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z
      f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    (U₁ : (pullback z f).Opens) (hηU₁ : η ∈ U₁) (h₁ : U₁ ≤ U₀)
    (hv : IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v))
    (hyτ : τ₀.1.base ⟨η, hηU⟩ = T.y)
    (c : D.ι) (W : T.Y.Opens) (hyW : T.y ∈ W) (ε : SchemeHomOver (W.ι ≫ T.f) (D.C c).f)
    (hε : IsOpenImmersion ε.1) (hεy : ε.1.base ⟨T.y, hyW⟩ = (D.C c).y)
    (hεchart : (genericFibreRestrict R K (D.C c).f (W.ι ≫ T.f) ε).1 ≫ (D.C c).e.1 =
      (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1) :
    ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
      IsOpenImmersion
        (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
        pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
            (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1 := by
  classical
  let W₁ : T.Y.Opens := W.ι ''ᵁ (ε.1 ⁻¹ᵁ (V c))
  have hW₁W : W₁ ≤ W := by
    simpa only [Scheme.Opens.opensRange_ι] using W.ι.image_le_opensRange (ε.1 ⁻¹ᵁ (V c))
  let U : (pullback z f).Opens := U₁ ⊓ U₀.ι ''ᵁ (τ₀.1 ⁻¹ᵁ W₁)
  have hUU₁ : U ≤ U₁ := inf_le_left
  have hUU₀ : U ≤ U₀ := hUU₁.trans h₁
  have hηU' : η ∈ U := by
    refine ⟨hηU₁, ?_⟩
    change η ∈ (U₀.ι ''ᵁ (τ₀.1 ⁻¹ᵁ W₁) : Set _)
    rw [Scheme.Hom.coe_image]
    refine ⟨⟨η, hηU⟩, ?_, rfl⟩
    change τ₀.1.base ⟨η, hηU⟩ ∈ (W₁ : Set _)
    rw [hyτ, Scheme.Hom.coe_image]
    refine ⟨⟨T.y, hyW⟩, ?_, rfl⟩
    change ε.1.base ⟨T.y, hyW⟩ ∈ V c
    rw [hεy]
    exact hyV c
  let t₁ : (U : Scheme.{u}) ⟶ T.Y := (pullback z f).homOfLE hUU₀ ≫ τ₀.1
  have hι_homOfLE : ∀ u : (U : Scheme.{u}), U₀.ι.base (((pullback z f).homOfLE hUU₀).base u) = u.1
    := by
    intro u
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    rfl
  have ht₁W₁ : ∀ u : (U : Scheme.{u}), t₁.base u ∈ W₁ := by
    intro u
    obtain ⟨w, hw, hwu⟩ := (show u.1 ∈ (U₀.ι ''ᵁ (τ₀.1 ⁻¹ᵁ W₁) : Set _) from u.2.2)
    have hw' : w = ((pullback z f).homOfLE hUU₀).base u :=
      U₀.ι.isOpenEmbedding.injective (hwu.trans (hι_homOfLE u).symm)
    change τ₀.1.base (((pullback z f).homOfLE hUU₀).base u) ∈ W₁
    rw [← hw']; exact hw
  have hrange₁ : Set.range t₁.base ⊆ Set.range W.ι.base := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hW₁W (ht₁W₁ u)
  let t₂ : (U : Scheme.{u}) ⟶ (W : Scheme.{u}) := IsOpenImmersion.lift W.ι t₁ hrange₁
  have ht₂ : t₂ ≫ W.ι = t₁ := IsOpenImmersion.lift_fac _ _ _
  have ht₂V : ∀ u : (U : Scheme.{u}), (t₂ ≫ ε.1).base u ∈ V c := by
    intro u
    obtain ⟨w, hw, hwu⟩ := (show t₁.base u ∈ (W₁ : Set _) from ht₁W₁ u)
    have hw' : w = t₂.base u :=
      W.ι.isOpenEmbedding.injective (hwu.trans (by rw [← Scheme.Hom.comp_apply, ht₂]))
    rw [Scheme.Hom.comp_apply, ← hw']
    exact hw
  have hrange₂ : Set.range (t₂ ≫ ε.1).base ⊆ Set.range (V c).ι.base := by
    rintro _ ⟨u, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ht₂V u
  let t₄ : (U : Scheme.{u}) ⟶ (V c : Scheme.{u}) := IsOpenImmersion.lift (V c).ι (t₂ ≫ ε.1) hrange₂
  have ht₄ : t₄ ≫ (V c).ι = t₂ ≫ ε.1 := IsOpenImmersion.lift_fac _ _ _
  have hUover : U.ι ≫ pullback.fst z f ≫ z = (pullback z f).homOfLE hUU₀ ≫ U₀.ι ≫ pullback.fst z f
    ≫ z := by
    rw [Scheme.homOfLE_ι_assoc]
  let a : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) (U₀.ι ≫ pullback.fst z f ≫ z) :=
    ⟨(pullback z f).homOfLE hUU₀, hUover.symm⟩
  let b : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) (W.ι ≫ T.f) :=
    ⟨t₂, by rw [← Category.assoc, ht₂, Category.assoc, τ₀.2, hUover]⟩
  let dd : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) ((V c).ι ≫ (D.C c).f) :=
    ⟨t₄, by
      rw [← Category.assoc, ht₄, Category.assoc, ε.2, ← Category.assoc, ht₂,
        Category.assoc, τ₀.2, hUover]⟩
  let τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f := NeronModelInfra.schemeHomOverComp dd (j c)
  have hba : NeronModelInfra.schemeHomOverComp b ⟨W.ι, rfl⟩ = NeronModelInfra.schemeHomOverComp a
    τ₀ :=
    Subtype.ext ht₂
  have hdb : NeronModelInfra.schemeHomOverComp dd ⟨(V c).ι, rfl⟩ =
    NeronModelInfra.schemeHomOverComp b ε :=
    Subtype.ext ht₄
  refine ⟨U, hηU', τ, ?_, ?_⟩
  · have : IsOpenImmersion (j c).1 := hjopen c
    have : IsOpenImmersion ε.1 := hε
    have : IsOpenImmersion ((pullback z f).homOfLE h₁ ≫ v) := hv
    have ht₁def : t₁ = (pullback z f).homOfLE hUU₀ ≫ τ₀.1 := rfl
    obtain ⟨mW, hmW⟩ : ∃ m : pullback z (W.ι ≫ T.f) ⟶ pullback z T.f,
        m = pullback.map z (W.ι ≫ T.f) z T.f (𝟙 Z) W.ι (𝟙 _)
          (by simp only [Category.id_comp, Category.comp_id])
          (by simp only [Category.comp_id]) := ⟨_, rfl⟩
    obtain ⟨mε, hmε⟩ : ∃ m : pullback z (W.ι ≫ T.f) ⟶ pullback z (D.C c).f,
        m = pullback.map z (W.ι ≫ T.f) z (D.C c).f (𝟙 Z) ε.1 (𝟙 _)
          (by simp only [Category.id_comp, Category.comp_id])
          (by rw [Category.comp_id, ε.2]) := ⟨_, rfl⟩
    obtain ⟨mV, hmV⟩ : ∃ m : pullback z ((V c).ι ≫ (D.C c).f) ⟶ pullback z (D.C c).f,
        m = pullback.map z ((V c).ι ≫ (D.C c).f) z (D.C c).f (𝟙 Z) (V c).ι (𝟙 _)
          (by simp only [Category.id_comp, Category.comp_id])
          (by simp only [Category.comp_id]) := ⟨_, rfl⟩
    obtain ⟨mj, hmj⟩ : ∃ m : pullback z ((V c).ι ≫ (D.C c).f) ⟶ pullback z f,
        m = pullback.map z ((V c).ι ≫ (D.C c).f) z f (𝟙 Z) (j c).1 (𝟙 _)
          (by simp only [Category.id_comp, Category.comp_id])
          (by rw [Category.comp_id, (j c).2]) := ⟨_, rfl⟩
    have : IsOpenImmersion mW := by rw [hmW]; infer_instance
    have : IsOpenImmersion mε := by rw [hmε]; infer_instance
    have : IsOpenImmersion mV := by rw [hmV]; infer_instance
    have : IsOpenImmersion mj := by rw [hmj]; infer_instance
    obtain ⟨M₁, hM₁⟩ : ∃ m : (U : Scheme.{u}) ⟶ pullback z (W.ι ≫ T.f),
        m = pullback.lift (U.ι ≫ pullback.fst z f) t₂
          (by rw [Category.assoc]; exact b.2.symm) := ⟨_, rfl⟩
    have hM₁v : M₁ ≫ mW = (pullback z f).homOfLE hUU₁ ≫ ((pullback z f).homOfLE h₁ ≫ v) := by
      rw [hM₁, hmW]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, hv₁, Scheme.homOfLE_ι_assoc]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, hv₂,
        Scheme.homOfLE_homOfLE_assoc,
          ht₂, ht₁def]
    have : IsOpenImmersion (M₁ ≫ mW) := by rw [hM₁v]; infer_instance
    have : IsOpenImmersion M₁ := IsOpenImmersion.of_comp M₁ mW
    obtain ⟨M₃, hM₃⟩ : ∃ m : (U : Scheme.{u}) ⟶ pullback z ((V c).ι ≫ (D.C c).f),
        m = pullback.lift (U.ι ≫ pullback.fst z f) t₄
          (by rw [Category.assoc]; exact dd.2.symm) := ⟨_, rfl⟩
    have hM₃M₁ : M₃ ≫ mV = M₁ ≫ mε := by
      rw [hM₃, hmV, hM₁, hmε]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, ht₄]
    have : IsOpenImmersion (M₃ ≫ mV) := by rw [hM₃M₁]; infer_instance
    have : IsOpenImmersion M₃ := IsOpenImmersion.of_comp M₃ mV
    have hL : pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
        ((Category.assoc _ _ _).trans τ.2.symm) = M₃ ≫ mj := by
      rw [hM₃, hmj]
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
        rfl
    rw [hL]
    infer_instance
  · have hF := fun {A B C : Scheme.{u}} (fa : A ⟶ Spec (CommRingCat.of R)) (fb : B ⟶ Spec
    (CommRingCat.of R))
        (fc : C ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver fb fa) (ψ : SchemeHomOver fa fc) =>
      congrArg Subtype.val (NeronModelInfra.genericFibreRestrict_schemeHomOverComp R K fc fa fb φ ψ)
    simp only [NeronModelInfra.schemeHomOverComp_coe] at hF
    have S6 := hτ₀
    rw [NeronModelInfra.schemeHomOverComp_coe] at S6
    have ha1 : a.1 = (pullback z f).homOfLE hUU₀ := rfl
    have S7 : (genericFibreRestrict R K (U₀.ι ≫ pullback.fst z f ≫ z) (U.ι ≫ pullback.fst z f ≫ z)
      a).1 ≫
        pullback.map (U₀.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
          (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U₀.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
        pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
          (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) := by
      apply pullback.hom_ext
      · simp only [NeronModelInfra.genericFibreRestrict, ha1, Category.assoc, pullback.lift_fst,
          pullback.lift_fst_assoc, Scheme.homOfLE_ι]
      · simp only [NeronModelInfra.genericFibreRestrict, Category.assoc,
          pullback.lift_snd, Category.comp_id]
    rw [NeronModelInfra.schemeHomOverComp_coe]
    change (genericFibreRestrict R K f _ (NeronModelInfra.schemeHomOverComp dd (j c))).1 ≫ e.1 = _
    rw [reassoc_of% (hF _ _ _ dd (j c)), hjchart c, ← reassoc_of% (hF _ _ _ dd ⟨(V c).ι, rfl⟩), hdb,
      reassoc_of% (hF _ _ _ b ε), hεchart, ← reassoc_of% (hF _ _ _ b ⟨W.ι, rfl⟩), hba,
      reassoc_of% (hF _ _ _ a τ₀), S6, reassoc_of% S7]

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_translation_chart_of_formallySmooth_stalk.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry GoodReductionJacobian

universe u

open NeronModelInfra renaming
 exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
 → minimal_stalk_smooth

open NeronModelInfra renaming
 isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
 → translation_stalk_fractionRing

open AlgebraicGeometry.Smooth renaming
 snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
 → open_chart_of_stalk


theorem exists_translation_chart_of_formallySmooth_stalk
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤))
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η : ↑(pullback z f)) (hη : (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint
      R → y = η)
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀) (τ₀ : SchemeHomOver (U₀.ι ≫ pullback.fst z f ≫ z)
      T.f)
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
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f) (hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z
      f)
    (hv₂ : v ≫ pullback.snd z T.f = τ₀.1)
    (hgen : T.y ⤳ τ₀.1.base ⟨η, hηU⟩)
    (hn : ∃ c : D.ι, T.n = (D.C c).n)
    (hdom : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))
    (hdom' : IsDomain ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)))
    (hfrac : let : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀
      : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :=
        ((algebraMap ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) (FractionRing ((U₀ :
          Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))).comp (v.stalkMap ⟨η, hηU⟩).hom).toAlgebra
      IsFractionRing ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) (FractionRing ((U₀ :
        Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
    (hfs : let : Algebra ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ :
      Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := (v.stalkMap ⟨η, hηU⟩).hom.toAlgebra
      Algebra.FormallySmooth ((pullback z T.f).presheaf.stalk (v.base ⟨η, hηU⟩)) ((U₀ :
        Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) :
    ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
      IsOpenImmersion
        (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
        pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
            (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1 := by
  have : Smooth T.f := T.smooth
  have : LocallyOfFiniteType T.f := T.locallyOfFiniteType
  obtain ⟨hyτ, U₁, hηU₁, h₁, hv⟩ :=
    open_chart_of_stalk z f T.f η hη hmax T.y T.hy U₀ hηU v hv₁ (by rw [hv₂]; exact hgen)
      hdom hdom' hfrac hfs
  obtain ⟨c, W, hyW, ε, hε, hεy, hεchart⟩ := hD.2 T hn
  exact NeronModelInfra.exists_translation_chart_of_minimal_representative K LXK d ω D X f e V
    j hyV hjopen hjchart Z z uK η T U₀ hηU τ₀ hτ₀ v hv₁ hv₂
    U₁ hηU₁ h₁ hv (by rw [← hv₂]; exact hyτ) c W hyW ε hε hεy hεchart

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_translation_charts_of_minimal_openCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry GoodReductionJacobian

universe u

open NeronModelInfra renaming
 exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
 → minimal_stalk_smooth

open NeronModelInfra renaming
 isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
 → translation_stalk_fractionRing

open AlgebraicGeometry.Smooth renaming
 snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
 → open_chart_of_stalk


theorem translation_charts_of_minimal_openCover
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints)
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ(gK.topDifferentials d, ⊤)) (hωframe : Scheme.Modules.IsFrameOn ω ⊤)
    (hleft : (∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F]
      [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) gK)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) gK)
        (U' U'' : XK.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(XK, U') F] [Algebra Γ(XK, U'') F],
        let : Algebra K Γ(XK, U') := gK.sectionsAlgebra U'
        let : Algebra K Γ(XK, U'') := gK.sectionsAlgebra U''
        ∀ [IsScalarTower K Γ(XK, U') F] [IsScalarTower K Γ(XK, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') F)) ≫ hU''.fromSpec =
          (LXK.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(XK, U')]^d (gK.kaehlerPresheaf.obj (op U')))
          (ω'' : ⋀[Γ(XK, U'')]^d (gK.kaehlerPresheaf.obj (op U''))),
          gK.topToSections d U' ω' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          gK.topToSections d U'' ω'' = (gK.topDifferentials d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(XK, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(XK, U') F
            d ω'))
    (D : MinimalComponentData R K gK d ω) (hD : D.IsOmegaMinimal)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (V : ∀ c : D.ι, ((D.C c).Y).Opens) (j : ∀ c : D.ι, SchemeHomOver ((V c).ι ≫ (D.C c).f) f)
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [IsIso e.1]
    (hyV : ∀ c, (D.C c).y ∈ V c)
    (hVK : ∀ c (y' : ↥(D.C c).Y), (D.C c).f.base y' ≠ IsLocalRing.closedPoint R → y' ∈ V c)
    (hjopen : ∀ c, IsOpenImmersion (j c).1)
    (hjchart : ∀ c, (genericFibreRestrict R K f ((V c).ι ≫ (D.C c).f) (j c)).1 ≫ e.1 =
      (genericFibreRestrict R K (D.C c).f ((V c).ι ≫ (D.C c).f) ⟨(V c).ι, rfl⟩).1 ≫ (D.C c).e.1)
    (hcover : ∀ x : ↥X, ∃ c, x ∈ Set.range (j c).1.base) :
    (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R
          → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1) ∧
    (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R
          → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩)
                    uK)).1)  := by
  classical
  have hL : ∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R
          → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
      IsOpenImmersion
        (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
          ((Category.assoc _ _ _).trans τ.2.symm)) ∧
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
        pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
            (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1 := by
    intro Z z _ _ uK η hη hmax
    let ΦK : SchemeHomOver (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
      gK :=
      LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f,
            pullback.condition.symm⟩) e)
    obtain ⟨i, U₀, hηU, τ₀, hτ₀⟩ :=
      NeronModelInfra.exists_nhds_extension_chart_of_catchesIndexOnePoints K M (fun i => (hM
        i).2.2.1) hpts
        (pullback.fst z f ≫ z) ΦK η hη hmax
    have : Smooth (M.str i) := (hM i).1
    have : LocallyOfFiniteType (M.str i) := (hM i).2.2.1
    have : QuasiCompact (M.str i) := (hM i).2.2.2
    have hy' : (M.str i).base (τ₀.1.base ⟨η, hηU⟩) = IsLocalRing.closedPoint R := by
      exact (congrArg (fun φ : (U₀ : Scheme.{u}) ⟶ Spec (CommRingCat.of R) =>
        φ.base (⟨η, hηU⟩ : ↥(U₀ : Scheme.{u}))) τ₀.2).trans hη
    obtain ⟨-, huniq, -⟩ :=
      NeronModelInfra.finite_maximal_specialFibre_and_existsUnique_specializes_and_exists_opens
        (M.str i)
    obtain ⟨ξ, ⟨⟨hξ, hξmax⟩, hξgen⟩, -⟩ := huniq _ hy'
    obtain ⟨hdom, hdvr, alg, halg, algK, hst, b, U, hU, algU, hstU, hx, ωU, hωU, a, ha, ha0⟩ :=
      NeronModelInfra.exists_componentReading_data_of_smooth_of_forall_specializes K gK d ω hωframe
        (M.str i) (M.chart i) ξ hξ hξmax
    let T : ComponentReading R K gK d ω :=
      ⟨M.X i, M.str i, inferInstance, inferInstance, M.chart i, inferInstance, ξ, hξ, hξmax,
        hdom, hdvr, alg, halg, algK, hst, b, U, hU, algU, hstU, hx, ωU, hωU, a, ha, ha0⟩
    let v : (U₀ : Scheme.{u}) ⟶ pullback z T.f :=
      pullback.lift (U₀.ι ≫ pullback.fst z f) τ₀.1 ((Category.assoc _ _ _).trans τ₀.2.symm)
    have hv₁ : v ≫ pullback.fst z T.f = U₀.ι ≫ pullback.fst z f := pullback.lift_fst _ _ _
    have hv₂ : v ≫ pullback.snd z T.f = τ₀.1 := pullback.lift_snd _ _ _
    obtain ⟨hdomO, hdomO', hfrac⟩ :=
      translation_stalk_fractionRing K LXK d ω X f e Z z uK η T U₀ hηU τ₀ hτ₀ v hv₁ hv₂
    obtain ⟨hn, hfs⟩ :=
      minimal_stalk_smooth K LXK d ω hωframe hleft D hD X f e V j hyV hVK hjopen hjchart hcover
        Z z uK η hη hmax T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ hξgen
    exact NeronModelInfra.exists_translation_chart_of_formallySmooth_stalk K LXK d ω D hD X f e V
      j hyV hjopen hjchart
      Z z uK η hη hmax T U₀ hηU τ₀ hτ₀ v hv₁ hv₂ hξgen hn hdomO hdomO' hfrac hfs
  refine ⟨hL, ?_⟩
  intro Z z _ _ uK η hη hmax
  obtain ⟨U, hU, τ, h1, h2⟩ := hL Z z uK η hη hmax
  refine ⟨U, hU, τ, h1, ?_⟩
  rw [h2, hcomm.mul_comm]

end NeronModelInfra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_exists_model_with_translation_charts.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


namespace NeronModelInfra


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry GoodReductionJacobian

universe u

open NeronModelInfra renaming
 exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
 → minimal_stalk_smooth

open NeronModelInfra renaming
 isFractionRing_stalk_of_genericFibreRestrict_comp_eq_mul_of_pullback_lift
 → translation_stalk_fractionRing

open AlgebraicGeometry.Smooth renaming
 snd_apply_eq_and_exists_isOpenImmersion_homOfLE_comp_of_formallySmooth_stalk
 → open_chart_of_stalk


theorem exists_model_with_translation_charts
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
      (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK),
      Smooth f ∧ IsSeparated f ∧ LocallyOfFiniteType f ∧ QuasiCompact f ∧
      (∃ x : X, f.base x = IsLocalRing.closedPoint R) ∧ IsIso e.1 ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R
          → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1) ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
        (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R
          → y = η) →
        ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
          IsOpenImmersion
            (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
              ((Category.assoc _ _ _).trans τ.2.symm)) ∧
          (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
            pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                    ⟨pullback.snd z f, pullback.condition.symm⟩) e)
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩)
                    uK)).1) := by
  classical
  obtain ⟨d, hd⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth LXK
  obtain ⟨ω, hωframe, hleft⟩ :=
    RelativeGroupLaw.exists_isFrameOn_topDifferentials_forall_topFormMap_mul_eq gK LXK d
  obtain ⟨D, hD⟩ :=
    NeronModelInfra.exists_minimalComponentData_isOmegaMinimal_of_catchesIndexOnePoints K LXK M
      hfin hM hpts d ω
      hωframe
  have : Finite D.ι := D.finite
  have : Nonempty D.ι := D.nonempty
  obtain ⟨X, g, eX, V, j, hsm, hsep, hlft, hqc, hiso, hyV, hVK, hjopen, hjchart, hcover⟩ :=
    NeronModelInfra.exists_model_openCover_of_forall_ne_not_exists_extension K gK
      (fun c => (D.C c).Y) (fun c => (D.C c).f)
      (fun c => ⟨(D.C c).smooth, D.isSeparated c, (D.C c).locallyOfFiniteType, D.quasiCompact c⟩)
      (fun c => (D.C c).e) D.isIso (fun c => (D.C c).y) (fun c => (D.C c).hy) D.hgen D.inequiv
  have : Smooth g := hsm
  have : IsSeparated g := hsep
  have : LocallyOfFiniteType g := hlft
  have : QuasiCompact g := hqc
  have : IsIso eX.1 := hiso
  obtain ⟨hL, hR⟩ :=
    NeronModelInfra.translation_charts_of_minimal_openCover
      K LXK hcomm M hM hpts d ω hωframe hleft D hD X g eX V j hyV hVK hjopen hjchart hcover
  obtain ⟨c₀⟩ := D.nonempty
  refine ⟨X, g, eX, hsm, hsep, hlft, hqc, ⟨(j c₀).1.base ⟨(D.C c₀).y, hyV c₀⟩, ?_⟩, hiso, hL, hR⟩
  exact (congrArg (fun φ : (V c₀ : Scheme.{u}) ⟶ Spec (CommRingCat.of R) =>
    φ.base (⟨(D.C c₀).y, hyV c₀⟩ : ↥(V c₀ : Scheme.{u}))) (j c₀).2).trans (D.C c₀).hy

end NeronModelInfra
end
