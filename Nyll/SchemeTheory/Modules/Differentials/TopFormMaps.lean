/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms
public import Nyll.SchemeTheory.Modules.Differentials.Pullback
public import Nyll.SchemeTheory.Modules.Differentials.Sections
public import Nyll.SchemeTheory.Modules.ExteriorPower.Det
public import Nyll.SchemeTheory.Modules.ExteriorPower.PresheafExteriorPower
public import Nyll.SchemeTheory.Modules.Frames.Frames
public import Nyll.SchemeTheory.Modules.Frames.IsFrameOnPullbackLocalSection
public import Nyll.SchemeTheory.Modules.Functoriality.PullbackLocalSection
public import Nyll.SchemeTheory.Modules.KaehlerDifferentials
public import Nyll.SchemeTheory.Modules.Sections.SectionsAlgebra
public import Nyll.SchemeTheory.Modules.Tensor.TensorSections

/-! # Restriction and change of affine charts for top differential forms -/

@[expose] public section

attribute [local instance] AlgebraicGeometry.Scheme.Hom.kaehlerPresheafModule

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_map_topToSections_eq_topToSections_topFormMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.TopFormMaps

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

open AbelianVarieties.NOSProofs.AffineExteriorSections

theorem _root_.AlgebraicGeometry.Scheme.Hom.map_topToSections_eq_topToSections_topFormMap
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)
    {U W : X.Opens} (hWU : W ≤ U) :
    let _ : Algebra A Γ(X, U) := f.sectionsAlgebra U
    let _ : Algebra A Γ(X, W) := f.sectionsAlgebra W
    let : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
    ∀ [IsScalarTower A Γ(X, U) Γ(X, W)] (η : ⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U))),
      (f.topDifferentials d).presheaf.map (homOfLE hWU).op (f.topToSections d U η) =
        f.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A A Γ(X, U) Γ(X, W) d η) := by
  intro algU algW algUW tower η
  exact (ExteriorSections.resD_top f d hWU η).trans
    (congrArg (f.topToSections d W)
      (SchemeTheory.DifferentialPullback.Construction.emap_eq_topFormMap f d hWU η))

end SchemeTheory.TopFormMaps
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.TopFormMaps

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace AffineCharts

theorem exists_ringHom_of_mem {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {F : Type u} [Field F] (φ : Spec (CommRingCat.of F) ⟶ X) (hφ : φ.base (IsLocalRing.closedPoint
      F) ∈ U) :
    ∃ ψ : Γ(X, U) →+* F, Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec = φ := by
  have hr : Set.range φ.base ⊆ Set.range hU.fromSpec.base := by
    rw [IsAffineOpen.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint F)]
    exact hφ
  let θ := IsOpenImmersion.lift hU.fromSpec φ hr
  refine ⟨(Spec.preimage θ).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem ringHom_eq_of_specMap_comp_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {F : Type u} [CommRing F] (ψ₁ ψ₂ : Γ(X, U) →+* F)
    (h : Spec.map (CommRingCat.ofHom ψ₁) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom ψ₂) ≫
      hU.fromSpec) :
    ψ₁ = ψ₂ := by
  have h1 : Spec.map (CommRingCat.ofHom ψ₁) = Spec.map (CommRingCat.ofHom ψ₂) := (cancel_mono
    _).mp h
  exact congrArg (fun f => f.hom) (Spec.map_injective h1)

end AffineCharts

theorem _root_.AlgebraicGeometry.Scheme.Hom.topFormMap_eq_topFormMap_of_specMap_comp_fromSpec_eq
    {K : Type u} [CommRing K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (ω : Γ(g.topDifferentials d, ⊤))
    (F : Type u) [Field F] [Algebra K F]
    (U₁ : X.Opens) (hU₁ : IsAffineOpen U₁) [Algebra Γ(X, U₁) F]
    (hKU₁ : let _ : Algebra K Γ(X, U₁) := g.sectionsAlgebra U₁; IsScalarTower K Γ(X, U₁) F)
    (U₂ : X.Opens) (hU₂ : IsAffineOpen U₂) [Algebra Γ(X, U₂) F]
    (hKU₂ : let _ : Algebra K Γ(X, U₂) := g.sectionsAlgebra U₂; IsScalarTower K Γ(X, U₂) F)
    (hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) F)) ≫ hU₁.fromSpec =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₂) F)) ≫ hU₂.fromSpec)
    (ω₁ : ⋀[Γ(X, U₁)]^d (g.kaehlerPresheaf.obj (op U₁)))
    (hω₁ : g.topToSections d U₁ ω₁ = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω)
    (ω₂ : ⋀[Γ(X, U₂)]^d (g.kaehlerPresheaf.obj (op U₂)))
    (hω₂ : g.topToSections d U₂ ω₂ = (g.topDifferentials d).presheaf.map (homOfLE le_top).op ω) :
    let _ : Algebra K Γ(X, U₁) := g.sectionsAlgebra U₁
    let _ : Algebra K Γ(X, U₂) := g.sectionsAlgebra U₂
    NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₁) F d ω₁ =
      NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₂) F d ω₂ := by
  intro i₁ i₂
  have : IsScalarTower K Γ(X, U₁) F := hKU₁
  have : IsScalarTower K Γ(X, U₂) F := hKU₂
  set x : Spec (CommRingCat.of F) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) F)) ≫
    hU₁.fromSpec
    with hxdef
  have hp₁ : x.base (IsLocalRing.closedPoint F) ∈ U₁ := by
    have : x.base (IsLocalRing.closedPoint F) ∈ Set.range hU₁.fromSpec.base :=
      ⟨(Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₁) F))).base (IsLocalRing.closedPoint F), by
        rw [hxdef]; rfl⟩
    rwa [IsAffineOpen.range_fromSpec] at this
  have hp₂ : x.base (IsLocalRing.closedPoint F) ∈ U₂ := by
    have : x.base (IsLocalRing.closedPoint F) ∈ Set.range hU₂.fromSpec.base :=
      ⟨(Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U₂) F))).base (IsLocalRing.closedPoint F), by
        rw [hx]; rfl⟩
    rwa [IsAffineOpen.range_fromSpec] at this
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x.base (IsLocalRing.closedPoint F) ∈ (U₁
      ⊓ U₂ : X.Opens)
      from ⟨hp₁, hp₂⟩) (U₁ ⊓ U₂).2
  have hW₁ : W ≤ U₁ := fun y hy => (hWle hy).1
  have hW₂ : W ≤ U₂ := fun y hy => (hWle hy).2
  obtain ⟨ψ, hψ⟩ := AffineCharts.exists_ringHom_of_mem hW x hpW
  have hfac₁ : algebraMap Γ(X, U₁) F = ψ.comp (X.presheaf.map (homOfLE hW₁).op).hom := by
    apply AffineCharts.ringHom_eq_of_specMap_comp_fromSpec hU₁
    rw [← hxdef, ← hψ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
      hU₁.map_fromSpec hW]
  have hfac₂ : algebraMap Γ(X, U₂) F = ψ.comp (X.presheaf.map (homOfLE hW₂).op).hom := by
    apply AffineCharts.ringHom_eq_of_specMap_comp_fromSpec hU₂
    rw [← hx, ← hψ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
      hU₂.map_fromSpec hW]
  let iW : Algebra K Γ(X, W) := g.sectionsAlgebra W
  let a₁ : Algebra Γ(X, U₁) Γ(X, W) := (X.presheaf.map (homOfLE hW₁).op).hom.toAlgebra
  let a₂ : Algebra Γ(X, U₂) Γ(X, W) := (X.presheaf.map (homOfLE hW₂).op).hom.toAlgebra
  let aF : Algebra Γ(X, W) F := ψ.toAlgebra
  have t₁ : IsScalarTower K Γ(X, U₁) Γ(X, W) :=
    SchemeTheory.DifferentialPullback.Construction.tower_sections g hW₁
  have t₂ : IsScalarTower K Γ(X, U₂) Γ(X, W) :=
    SchemeTheory.DifferentialPullback.Construction.tower_sections g hW₂
  have s₁ : IsScalarTower Γ(X, U₁) Γ(X, W) F := IsScalarTower.of_algebraMap_eq' hfac₁
  have s₂ : IsScalarTower Γ(X, U₂) Γ(X, W) F := IsScalarTower.of_algebraMap_eq' hfac₂
  have sK : IsScalarTower K Γ(X, W) F := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq K Γ(X, U₁) F, IsScalarTower.algebraMap_eq Γ(X, U₁) Γ(X, W) F,
      IsScalarTower.algebraMap_eq K Γ(X, U₁) Γ(X, W), RingHom.comp_assoc])
  have hT := Scheme.Hom.topToSections_bijective_of_isAffineOpen g d hW
  have key : NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₁) Γ(X, W) d ω₁ =
      NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, U₂) Γ(X, W) d ω₂ := by
    apply hT.1
    rw [← Scheme.Hom.map_topToSections_eq_topToSections_topFormMap g d hW₁ ω₁,
      ← Scheme.Hom.map_topToSections_eq_topToSections_topFormMap g d hW₂ ω₂, hω₁, hω₂,
      ← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp, ←
        Functor.map_comp]
    rfl
  have e := congrArg (fun s => NeronModelInfra.TopFormOrder.topFormMap K K Γ(X, W) F d s) key
  have h₁ := @NeronModelInfra.TopFormOrder.topFormMap_topFormMap
    K K K Γ(X, U₁) Γ(X, W) F _ _ _ _ _ _ _ _ _ _
    i₁ iW _ a₁ aF _ s₁ iW t₁ _ _ sK _ _ hKU₁ _ d ω₁
  have h₂ := @NeronModelInfra.TopFormOrder.topFormMap_topFormMap
    K K K Γ(X, U₂) Γ(X, W) F _ _ _ _ _ _ _ _ _ _
    i₂ iW _ a₂ aF _ s₂ iW t₂ _ _ sK _ _ hKU₂ _ d ω₂
  exact h₁.symm.trans (e.trans h₂)

end SchemeTheory.TopFormMaps
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_bijective_smul_topFormMap_of_isFrameOn_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.TopFormMaps

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom
open AbelianVarieties.NOSProofs.AffineExteriorSections

universe u

theorem _root_.AlgebraicGeometry.Scheme.Hom.bijective_smul_topFormMap_of_isFrameOn_of_isPullback
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B)))) (d : ℕ)
    [SmoothOfRelativeDimension d gY]
    (U : Y.Opens) (hU : IsAffineOpen U) (s : Γ(gY.topDifferentials d, U)) (hs :
      Scheme.Modules.IsFrameOn s U)
    (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U)))
    (hη : gY.topToSections d U η = s)
    (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U) :
    let _ : Algebra A Γ(Y, U) := gY.sectionsAlgebra U
    let _ : Algebra B Γ(X, W) := gX.sectionsAlgebra W
    let : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
    ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)],
      Function.Bijective fun c : Γ(X, W) =>
        c • NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η := by
  intro algU algW algUW iA iT₁ iT₂
  subst hη
  obtain ⟨θ, hθ⟩ :=
    Scheme.Hom.exists_hom_pullback_topDifferentials_map_pullbackLocalSection_topToSections_eq gY
      gX φ hφ.w d
  have : IsIso θ :=
    isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
      gY gX φ hφ d θ hθ
  have hfr : Scheme.Modules.IsFrameOn
      ((asIso θ).hom.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U
        η))) (φ ⁻¹ᵁ U) :=
    (Scheme.Modules.IsFrameOn.pullbackLocalSection φ hs).map_iso (asIso θ)
  have hb := hfr.bijective hWU hWU
  have hchart := hθ U hU W hW hWU η
  rw [asIso_hom, hchart] at hb
  have hT := Scheme.Hom.topToSections_bijective_of_isAffineOpen gX d hW
  have hlin (c : Γ(X, W)) (x : ⋀[Γ(X, W)]^d (Ω[Γ(X, W)⁄B])) :
      gX.topToSections d W (c • x) = c • gX.topToSections d W x := by
    refine (ExteriorSections.topToSections_eq gX d W (c • x)).trans ?_
    refine (congrArg (ExteriorSections.unitD gX d W)
      ((exteriorPower.map d (gX.kaehlerToSectionsₗ W)).map_smul c x)).trans ?_
    exact (ExteriorSections.unitD_smul gX d W c _).trans
      (congrArg (c • ·) (ExteriorSections.topToSections_eq gX d W x).symm)
  refine ⟨fun c₁ c₂ h => hb.1 ?_, fun x => ?_⟩
  · dsimp only at h ⊢
    rw [← hlin, ← hlin, h]
  · obtain ⟨c, hc⟩ := hb.2 (gX.topToSections d W x)
    refine ⟨c, hT.1 ?_⟩
    dsimp only at hc ⊢
    rw [hlin]
    exact hc

end SchemeTheory.TopFormMaps
end
