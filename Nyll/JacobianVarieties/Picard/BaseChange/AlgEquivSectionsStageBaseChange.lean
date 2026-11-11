/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_algEquiv_sections_stage_baseChange_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Scheme
public import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
public import Nyll.SchemeTheory.Modules.Functoriality.AffinePullbackSections
public import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.StageHom
public import Nyll.AlgebraicCurves.Geometry.Picard.BaseChange.IsPullbackBaseChangeSnd

public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Designation
public import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation
/-!
# Algebra equivalences for affine sections after a change of stage
-/

@[expose] public section

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.StageSectionsBaseChange

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.TensorProduct
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover
open _root_.AlgebraicGeometry.RelPicard.LFP

noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Spec.map_comp
  Scheme.Hom.map_appLE
  Scheme.Opens.topIso_inv
  pullbackSpecIso_inv_snd
  Scheme.Hom
  Scheme.Hom.appLE_comp_appLE
  Scheme.Γ
  IsAffineOpen.fromSpec_top
  IsAffineOpen.SpecMap_appLE_fromSpec
  Spec
  Spec.map
  Scheme.ΓSpecIso_inv_naturality
  Scheme
  pullbackSpecIso
  Scheme.isoSpec_Spec_inv
  IsAffineOpen.isoSpec_hom_appTop
  pullbackRestrictIsoRestrict_inv_fst_assoc
  Scheme.Opens.topIso_hom
  Scheme.Hom.comp_appTop
  IsAffineOpen.isoSpec
  pullbackSpecIso_inv_fst
  isAffineOpen_top
  IsAffineOpen
  pullbackRestrictIsoRestrict
  Scheme.Opens
  Scheme.Hom.appLE_map
  Scheme.Hom.app_eq_appLE
  Scheme.Hom.comp_preimage
  Scheme.Opens.ι_appTop
  Scheme.Hom.appLE
  morphismRestrict_appLE
  Scheme.ΓSpecIso
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom
  RelPicard.baseChangeSnd
  RelPicard.LFP.stageHom
  RelPicard.isPullback_baseChangeSnd)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd LFP.stageHom isPullback_baseChangeSnd)

namespace LFP

export _root_.AlgebraicGeometry.RelPicard.LFP (stageHom)

namespace StageTransport

open _root_.AlgebraicGeometry.RelPicard.LFP
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

/-- Equal scheme maps induce equal maps on restricted sections. -/
theorem appLE_congrHom {X Z : Scheme.{u}} {f g : X ⟶ Z} (e : f = g) (U : Z.Opens) (V : X.Opens)
    (h₁ : V ≤ f ⁻¹ᵁ U) (h₂ : V ≤ g ⁻¹ᵁ U) : f.appLE U V h₁ = g.appLE U V h₂ := by
  subst e; rfl

variable {Y Y' : Scheme.{u}} (φ : Y' ⟶ Y) [IsIso φ] {W : Y.Opens} {W' : Y'.Opens} (hW : φ ⁻¹ᵁ W =
  W')

/-- Transport of sections along an isomorphism and its identified inverse image open. -/
def transportIso : Γ(Y, W) ≅ Γ(Y', W') :=
  asIso (φ.app W) ≪≫ Y'.presheaf.mapIso (eqToIso hW.symm).op

/-- The transport isomorphism is the restricted map on sections. -/
theorem transportIso_hom : (transportIso φ hW).hom = φ.appLE W W' hW.ge := by
  change φ.app W ≫ Y'.presheaf.map (eqToHom hW.symm).op = φ.app W ≫ Y'.presheaf.map (homOfLE
    hW.ge).op
  exact congrArg (fun k : W' ⟶ φ ⁻¹ᵁ W => φ.app W ≫ Y'.presheaf.map k.op) (Subsingleton.elim _ _)

/-- Evaluation of the transport isomorphism agrees with the restricted section map. -/
theorem transportIso_hom_apply (t : Γ(Y, W)) :
    (transportIso φ hW).hom.hom t = (φ.appLE W W' hW.ge).hom t := by
  rw [transportIso_hom]

variable {S : Type u} [CommRing S] (p : Y ⟶ Spec (.of S)) (p' : Y' ⟶ Spec (.of S)) (hφ : φ ≫ p = p')

/-- Transport of sections along an isomorphism over the base preserves the base algebra. -/
def transportAlgEquiv :
    let _ : Algebra S Γ(Y, W) := algebraOfHom p W
    let _ : Algebra S Γ(Y', W') := algebraOfHom p' W'
    Γ(Y, W) ≃ₐ[S] Γ(Y', W') := by
  intro iW iW'
  exact AlgEquiv.ofRingEquiv (f := (transportIso φ hW).commRingCatIsoToRingEquiv) (fun a => by
    change (transportIso φ hW).hom.hom ((p.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (.of S)).inv.hom
      a))
      = (p'.appLE ⊤ W' le_top).hom ((Scheme.ΓSpecIso (.of S)).inv.hom a)
    rw [transportIso_hom]
    exact congrArg (fun k : Γ(Spec (.of S), ⊤) ⟶ Γ(Y', W') => k.hom ((Scheme.ΓSpecIso (.of
      S)).inv.hom a))
      ((_root_.AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE φ p ⊤ W W' le_top hW.ge).trans
        (appLE_congrHom hφ ⊤ W' _ _)))

/-- The transport algebra equivalence acts by the restricted section map. -/
theorem transportAlgEquiv_apply (t : Γ(Y, W)) :
    let _ : Algebra S Γ(Y, W) := algebraOfHom p W
    let _ : Algebra S Γ(Y', W') := algebraOfHom p' W'
    transportAlgEquiv φ hW p p' hφ t = (φ.appLE W W' hW.ge).hom t := by
  intro iW iW'
  change (transportIso φ hW).hom.hom t = _
  rw [transportIso_hom]

include hφ in
/-- A scheme isomorphism over the base transports the algebras of sections. -/
theorem exists_transportAlgEquiv :
    let _ : Algebra S Γ(Y, W) := algebraOfHom p W
    let _ : Algebra S Γ(Y', W') := algebraOfHom p' W'
    ∃ τ : Γ(Y, W) ≃ₐ[S] Γ(Y', W'), ∀ t, τ t = (φ.appLE W W' hW.ge).hom t := by
  intro iW iW'
  exact ⟨transportAlgEquiv φ hW p p' hφ, transportAlgEquiv_apply φ hW p p' hφ⟩

end AlgebraicGeometry.RelPicard.LFP.StageTransport

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Spec.map_comp
  Scheme.Hom.map_appLE
  Scheme.Opens.topIso_inv
  pullbackSpecIso_inv_snd
  Scheme.Hom
  Scheme.Hom.appLE_comp_appLE
  Scheme.Γ
  IsAffineOpen.fromSpec_top
  IsAffineOpen.SpecMap_appLE_fromSpec
  Spec
  Spec.map
  Scheme.ΓSpecIso_inv_naturality
  Scheme
  pullbackSpecIso
  Scheme.isoSpec_Spec_inv
  IsAffineOpen.isoSpec_hom_appTop
  pullbackRestrictIsoRestrict_inv_fst_assoc
  Scheme.Opens.topIso_hom
  Scheme.Hom.comp_appTop
  IsAffineOpen.isoSpec
  pullbackSpecIso_inv_fst
  isAffineOpen_top
  IsAffineOpen
  pullbackRestrictIsoRestrict
  Scheme.Opens
  Scheme.Hom.appLE_map
  Scheme.Hom.app_eq_appLE
  Scheme.Hom.comp_preimage
  Scheme.Opens.ι_appTop
  Scheme.Hom.appLE
  morphismRestrict_appLE
  Scheme.ΓSpecIso
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom
  RelPicard.baseChangeSnd
  RelPicard.LFP.stageHom
  RelPicard.isPullback_baseChangeSnd)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd LFP.stageHom isPullback_baseChangeSnd)

namespace LFP

export _root_.AlgebraicGeometry.RelPicard.LFP (stageHom)

namespace Stage

open _root_.AlgebraicGeometry.RelPicard.LFP
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A']
    [IsScalarTower R A₀ A']

/-- The curve after extension of its coefficient algebra. -/
abbrev CA (A : Type u) [CommRing A] [Algebra R A] : Scheme.{u} := pullback c (specMap R A)

/-- The projection from the curve at a stage to the coefficient spectrum. -/
abbrev prA (A : Type u) [CommRing A] [Algebra R A] :
    CA R c A ⟶ Spec (.of A) := pullback.snd c (specMap R A)

/-- The curve morphism induced by a tower of coefficient algebras. -/
abbrev σ : CA R c A' ⟶ CA R c A₀ := RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R
  A₀ A'))

/-- The stage morphism is the spectrum map of the intermediate algebra map. -/
theorem stageHom_toAlgHom_val :
    (stageHom R (IsScalarTower.toAlgHom R A₀ A')).1 = specMap A₀ A' := rfl

/-- The transition between stages is a pullback square. -/
theorem hsq : IsPullback (σ R c A₀ A') (prA R c A') (prA R c A₀) (specMap A₀ A') :=
  RelPicard.isPullback_baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))

/-- The iterated base-change scheme. -/
abbrev X' : Scheme.{u} := pullback (prA R c A₀) (specMap A₀ A')

/-- The canonical isomorphism between direct and iterated stage base change. -/
def φ : CA R c A' ≅ X' R c A₀ A' := (hsq R c A₀ A').isoPullback

/-- The stage comparison isomorphism preserves the first projection. -/
@[scoped simp] theorem φ_hom_fst : (φ R c A₀ A').hom ≫ pullback.fst (prA R c A₀) (specMap A₀ A') =
  σ R c A₀ A' :=
  (hsq R c A₀ A').isoPullback_hom_fst
/-- The stage comparison isomorphism preserves the second projection. -/
@[scoped simp] theorem φ_hom_snd : (φ R c A₀ A').hom ≫ pullback.snd (prA R c A₀) (specMap A₀ A') =
  prA R c A' :=
  (hsq R c A₀ A').isoPullback_hom_snd
/-- The inverse stage comparison preserves the transition morphism. -/
@[scoped simp] theorem φ_inv_σ : (φ R c A₀ A').inv ≫ σ R c A₀ A' = pullback.fst (prA R c A₀)
  (specMap A₀ A') :=
  (hsq R c A₀ A').isoPullback_inv_fst
/-- The inverse stage comparison preserves the coefficient projection. -/
@[scoped simp] theorem φ_inv_prA : (φ R c A₀ A').inv ≫ prA R c A' = pullback.snd (prA R c A₀)
  (specMap A₀ A') :=
  (hsq R c A₀ A').isoPullback_inv_snd

/-- The stage comparison identifies the pullback of an open. -/
theorem φ_hom_preimage_fst_preimage (U : (CA R c A₀).Opens) :
    (φ R c A₀ A').hom ⁻¹ᵁ ((pullback.fst (prA R c A₀) (specMap A₀ A')) ⁻¹ᵁ U) = (σ R c A₀ A') ⁻¹ᵁ U
      := by
  rw [← Scheme.Hom.comp_preimage, φ_hom_fst]

end AlgebraicGeometry.RelPicard.LFP.Stage

attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_fst
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_snd
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_σ
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_prA

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Spec.map_comp
  Scheme.Hom.map_appLE
  Scheme.Opens.topIso_inv
  pullbackSpecIso_inv_snd
  Scheme.Hom
  Scheme.Hom.appLE_comp_appLE
  Scheme.Γ
  IsAffineOpen.fromSpec_top
  IsAffineOpen.SpecMap_appLE_fromSpec
  Spec
  Spec.map
  Scheme.ΓSpecIso_inv_naturality
  Scheme
  pullbackSpecIso
  Scheme.isoSpec_Spec_inv
  IsAffineOpen.isoSpec_hom_appTop
  pullbackRestrictIsoRestrict_inv_fst_assoc
  Scheme.Opens.topIso_hom
  Scheme.Hom.comp_appTop
  IsAffineOpen.isoSpec
  pullbackSpecIso_inv_fst
  isAffineOpen_top
  IsAffineOpen
  pullbackRestrictIsoRestrict
  Scheme.Opens
  Scheme.Hom.appLE_map
  Scheme.Hom.app_eq_appLE
  Scheme.Hom.comp_preimage
  Scheme.Opens.ι_appTop
  Scheme.Hom.appLE
  morphismRestrict_appLE
  Scheme.ΓSpecIso
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap
  Scheme.TwoAffineOpenCover.algebraOfHom
  RelPicard.baseChangeSnd
  RelPicard.LFP.stageHom
  RelPicard.isPullback_baseChangeSnd)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd LFP.stageHom isPullback_baseChangeSnd)

namespace LFP

export _root_.AlgebraicGeometry.RelPicard.LFP (stageHom)

namespace Stage

open _root_.AlgebraicGeometry.RelPicard.LFP
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

open AlgebraicGeometry.RelPicard.LFP.StageTransport

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A']
    [IsScalarTower R A₀ A']

/-- The first projection of the iterated base change. -/
abbrev fst' : X' R c A₀ A' ⟶ CA R c A₀ := pullback.fst (prA R c A₀) (specMap A₀ A')

/-- The second projection of the iterated base change. -/
abbrev snd' : X' R c A₀ A' ⟶ Spec (.of A') := pullback.snd (prA R c A₀) (specMap A₀ A')

/-- The stage comparison transports a specified inverse-image open. -/
theorem φ_hom_preimage_eq (U : (CA R c A₀).Opens) (U' : (CA R c A').Opens)
    (hU : (σ R c A₀ A') ⁻¹ᵁ U = U') :
    (φ R c A₀ A').hom ⁻¹ᵁ ((fst' R c A₀ A') ⁻¹ᵁ U) = U' := by
  rw [φ_hom_preimage_fst_preimage]; exact hU

/-- The stage comparison commutes with pullback of a section. -/
theorem φ_appLE_fst_app (U : (CA R c A₀).Opens) (U' : (CA R c A').Opens)
    (hU : (σ R c A₀ A') ⁻¹ᵁ U = U')
    (h : U' ≤ (φ R c A₀ A').hom ⁻¹ᵁ ((fst' R c A₀ A') ⁻¹ᵁ U)) (s : Γ(CA R c A₀, U)) :
    ((φ R c A₀ A').hom.appLE ((fst' R c A₀ A') ⁻¹ᵁ U) U' h).hom (((fst' R c A₀ A').app U).hom s)
      = ((σ R c A₀ A').appLE U U' hU.ge).hom s := by
  rw [← CommRingCat.comp_apply ((fst' R c A₀ A').app U) ((φ R c A₀ A').hom.appLE _ U' h),
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun k : Γ(CA R c A₀, U) ⟶ Γ(CA R c A', U') => k.hom s)
    (appLE_congrHom (φ_hom_fst R c A₀ A') U U' _ _)

end AlgebraicGeometry.RelPicard.LFP.Stage

attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_fst
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_snd
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_σ
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_prA

attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_fst
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_snd
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_σ
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_prA

attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_fst
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_snd
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_σ
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_prA

attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_fst
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_snd
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_σ
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_prA

end

attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_fst
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_hom_snd
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_σ
attribute [local simp] AlgebraicGeometry.RelPicard.LFP.Stage.φ_inv_prA

open AlgebraicGeometry.RelPicard.LFP.Stage AlgebraicGeometry.RelPicard.LFP.StageTransport

/-- Sections on an affine stage base change are the scalar extension of the original sections. -/
theorem _root_.AlgebraicGeometry.RelPicard.exists_algEquiv_sections_stage_baseChange_of_isAffineOpen
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A']
      [IsScalarTower R A₀ A']
    (U : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Opens) (hU : IsAffineOpen U)
    (U' : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A')).Opens)
    (hU' : RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))
      ⁻¹ᵁ U = U') :
    let _ : Algebra A₀ Γ(Limits.pullback c
        (Scheme.TwoAffineOpenCover.specMap R A₀), U) :=
      Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) U
    let _ : Algebra A' Γ(Limits.pullback c
        (Scheme.TwoAffineOpenCover.specMap R A'), U') :=
      Scheme.TwoAffineOpenCover.algebraOfHom
        (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A')) U'
    ∃ e : (A' ⊗[A₀] Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀), U)) ≃ₐ[A']
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A'), U'),
      ∀ s, e ((1 : A') ⊗ₜ[A₀] s) =
        ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀
          A'))).appLE U U' hU'.ge).hom s := by
  intro iU iU'
  let iW : Algebra A' Γ(X' R c A₀ A', (fst' R c A₀ A') ⁻¹ᵁ U) :=
    Scheme.TwoAffineOpenCover.algebraOfHom (snd' R c A₀ A') ((fst' R c A₀ A') ⁻¹ᵁ U)
  obtain ⟨e, he⟩ :=
    AlgebraicGeometry.Scheme.exists_algEquiv_tensor_sections_pullback_fst_preimage_of_isAffineOpen
      (prA R c A₀) U hU A'
  obtain ⟨τ, hτ⟩ := exists_transportAlgEquiv (φ R c A₀ A').hom
    (W := (fst' R c A₀ A') ⁻¹ᵁ U) (W' := U')
    (φ_hom_preimage_eq R c A₀ A' U U' hU') (snd' R c A₀ A') (prA R c A') (φ_hom_snd R c A₀ A')
  refine ⟨e.trans τ, fun s => ?_⟩
  rw [AlgEquiv.trans_apply, he]
  exact (hτ _).trans (φ_appLE_fst_app R c A₀ A' U U' hU' _ s)
end JacobianVarieties.Picard.Proofs.StageSectionsBaseChange
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec
  GoodReductionJacobian.AvatarSchemeBridge.mk.injEq
  GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe
  NeronModelInfra.schemeHomOverEquivOverHom_apply
  GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe
  GoodReductionJacobian.RelativeGroupLaw.mk.injEq
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
