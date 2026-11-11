/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.Local.BoundaryHomHartogs
public import Nyll.SchemeTheory.Modules.Functoriality.PushforwardIhom
public import Nyll.SchemeTheory.Modules.Sections.BidualEvaluation
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeTransport
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
public import Nyll.SchemeTheory.RingTheory.Localization.LocalAlgebra

/-!
# Scalar and dual Hartogs on a locally Noetherian scheme

The depth hypothesis transports through actual affine-chart stalk maps.
The affine scalar theorem then proves bijectivity on the affine basis,
so the original structure-module restriction unit is an isomorphism.
The native closed adjunction identifies duals with their open direct images.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open AlgebraicCurves.Foundations.Algebra.Proofs.Module_depth_quotSMulTop_succ_eq
open Ws14Port.IsLocalRing.IsCohenMacaulayOfDim

open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection

namespace AlgebraicGeometry

/-- The original scalar restriction on any affine chart is bijective
across a depth-two boundary of a locally Noetherian scheme. -/
theorem restrict_affine_bijective_of_boundary_two_le_depth
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (W : X.Opens) (hW : IsAffineOpen W) :
    Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) := by
  let R : CommRingCat.{u} := Γ(X, W)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let j : Spec R ⟶ X := hW.fromSpec
  have : IsOpenImmersion j := hW.isOpenImmersion_fromSpec
  let T : (Spec R).Opens := j ⁻¹ᵁ U
  have hT : ∀ p : Spec R, p ∉ T →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p) := by
    intro p hp
    exact (hdepth (j p) hp).trans
      (Module.depth_le_depth_of_ringEquiv
        (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv)
  let res : Γ(X, j ''ᵁ ⊤) ⟶ Γ(X, j ''ᵁ T) :=
    X.presheaf.map (homOfLE (j.image_mono (le_top : T ≤ ⊤))).op
  have hnat :
      (Spec R).presheaf.map (homOfLE (le_top : T ≤ ⊤)).op ≫ (j.appIso T).inv =
        (j.appIso ⊤).inv ≫ res :=
    j.appIso_inv_naturality (homOfLE (le_top : T ≤ ⊤)).op
  have hcomp : Function.Bijective ((j.appIso ⊤).inv ≫ res) := by
    rw [← hnat]
    exact (ConcreteCategory.bijective_of_isIso (j.appIso T).inv).comp
      (restrict_bijective_of_boundary_two_le_depth R T hT)
  have hres : Function.Bijective res :=
    (Function.Bijective.of_comp_iff res
      (ConcreteCategory.bijective_of_isIso (j.appIso ⊤).inv)).mp hcomp
  have htop : j ''ᵁ ⊤ = W :=
    j.image_top_eq_opensRange.trans hW.opensRange_fromSpec
  have hTimage : j ''ᵁ T = W ⊓ U := by
    rw [j.image_preimage_eq_opensRange_inf, hW.opensRange_fromSpec]
  dsimp only [res] at hres
  have transport (A B : X.Opens) (hA : A = W) (hB : B = W ⊓ U)
      (hBA : B ≤ A) (hres : Function.Bijective
        (X.presheaf.map (homOfLE hBA).op)) :
      Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : W ⊓ U ≤ W)).op) := by
    subst A
    subst B
    exact hres
  exact transport _ _ htop hTimage _ hres

namespace Scheme.Modules

/-- Scalar Hartogs makes the original structure-module restriction unit
invertible globally on a locally Noetherian scheme. -/
theorem isIso_structure_unit_of_locallyNoetherian_boundary_two_le_depth
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    IsIso ((restrictAdjunction U.ι).unit.app (𝟙_ X.Modules)) := by
  let O : X.Modules := 𝟙_ X.Modules
  let P : X.Modules := (pushforward U.ι).obj (O.restrict U.ι)
  let η : O ⟶ P := (restrictAdjunction U.ι).unit.app O
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨O.presheaf, O.isSheaf⟩
  let G : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨P.presheaf, P.isSheaf⟩
  let ψ : F ⟶ G := ⟨η.mapPresheaf⟩
  have hb : Opens.IsBasis (Set.range (fun W : X.affineOpens => W.1)) := by
    rw [Subtype.range_coe_subtype]
    exact X.isBasis_affineOpens
  have hη (W : X.affineOpens) : Function.Bijective (η.app W.1) := by
    change Function.Bijective
      (X.presheaf.map (homOfLE (U.ι.image_preimage_le W.1)).op)
    have heq : U.ι ''ᵁ (U.ι ⁻¹ᵁ W.1) = W.1 ⊓ U := by
      rw [U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
    have hres (A : X.Opens) (hA : A = W.1 ⊓ U) (hAW : A ≤ W.1) :
        Function.Bijective (X.presheaf.map (homOfLE hAW).op) := by
      subst A
      exact restrict_affine_bijective_of_boundary_two_le_depth X U hdepth W.1 W.2
    exact hres _ heq _
  have hψ : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hb
    (fun W => (ConcreteCategory.isIso_iff_bijective (η.app W.1)).mpr (hη W))
  have hForget : IsIso ((TopCat.Sheaf.forget AddCommGrpCat.{u} X).map ψ) := inferInstance
  have hPresheaf : IsIso ((toPresheaf X).map η) := hForget
  exact isIso_of_reflects_iso η (toPresheaf X)

/-- The actual dual over a locally Noetherian scheme is the original
open direct image of the restricted dual across a depth-two boundary. -/
def dualOpenDirectImageIsoOfLocallyNoetherian
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (M : X.Modules) :
    dual M ≅ (pushforward U.ι).obj (dual (M.restrict U.ι)) := by
  have : IsIso ((restrictAdjunction U.ι).unit.app (𝟙_ X.Modules)) :=
    isIso_structure_unit_of_locallyNoetherian_boundary_two_le_depth X U hdepth
  let e : (𝟙_ X.Modules) ≅ (pushforward U.ι).obj (𝟙_ U.toScheme.Modules) :=
    asIso ((restrictAdjunction U.ι).unit.app (𝟙_ X.Modules)) ≪≫
      (pushforward U.ι).mapIso (restrictUnitIso U.ι)
  exact (ihom M).mapIso e ≪≫ ihomPushforwardRestrictIso U.ι M (𝟙_ U.toScheme.Modules)


/-- Canonical reflexivity supplies the original global Hartogs unit. -/
theorem isIso_reflexive_unit_of_locallyNoetherian_boundary_two_le_depth
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (M : X.Modules) [IsIso (ZeroSchemeCanonMC.toBidual M)] :
    IsIso ((restrictAdjunction U.ι).unit.app M) :=
  (restrictAdjunction U.ι).isIso_unit_app_of_iso
    (asIso (ZeroSchemeCanonMC.toBidual M) ≪≫
      dualOpenDirectImageIsoOfLocallyNoetherian X U hdepth (dual M))

/-- An actual dual which is finite locally free on the given open is
reflexive globally across its depth-two boundary. -/
theorem isIso_toBidual_dual_of_locallyNoetherian_boundary_two_le_depth
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (M : X.Modules) (hfree : U ≤ finiteFreeLocus M) :
    IsIso (ZeroSchemeCanonMC.toBidual (dual M)) := by
  let F := restrictFunctor U.ι
  let a := ZeroSchemeCanonMC.toBidual (dual M)
  let b := (MonoidalClosed.pre (ZeroSchemeCanonMC.toBidual M)).app (𝟙_ X.Modules)
  have : IsIso (F.map a) := isIso_restrict_toBidual_of_le_finiteFreeLocus
    (dual M) U (hfree.trans (finiteFreeLocus_le_dual M))
  have hunit : IsIso ((restrictAdjunction U.ι).unit.app (dual (dual (dual M)))) :=
    (restrictAdjunction U.ι).isIso_unit_app_of_iso
      (dualOpenDirectImageIsoOfLocallyNoetherian X U hdepth (dual (dual M)))
  have hab : a ≫ b = 𝟙 (dual M) := toBidual_dual_comp_pre M
  have hba : b ≫ a = 𝟙 (dual (dual (dual M))) := by
    apply (hom_restrict_bijective_of_unit_isIso U.ι
      (dual (dual (dual M))) (dual (dual (dual M)))).1
    change F.map (b ≫ a) = F.map (𝟙 _)
    apply (cancel_epi (F.map a)).mp
    rw [← F.map_comp, ← Category.assoc, hab, Category.id_comp,
      F.map_id, Category.comp_id]
  exact ⟨⟨b, hab, hba⟩⟩

/-- The actual open direct image of a finite locally free module has
invertible canonical bidual evaluation over any locally Noetherian base
with boundary depth at least two. -/
theorem isIso_toBidual_pushforward_of_locallyNoetherian_boundary_two_le_depth
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (V : U.toScheme.Modules) (hfree : finiteFreeLocus V = ⊤) :
    IsIso (ZeroSchemeCanonMC.toBidual ((pushforward U.ι).obj V)) := by
  let F : X.Modules := (pushforward U.ι).obj (dual V)
  let e : F.restrict U.ι ≅ dual V := asIso ((restrictAdjunction U.ι).counit.app (dual V))
  have hdual : finiteFreeLocus (dual V) = ⊤ :=
    top_unique (hfree ▸ finiteFreeLocus_le_dual V)
  have hFU : finiteFreeLocus (F.restrict U.ι) = ⊤ :=
    (finiteFreeLocus_eq_of_iso e).trans hdual
  have hF : U ≤ finiteFreeLocus F := le_finiteFreeLocus_of_restrict_eq_top F U hFU
  have : IsIso (ZeroSchemeCanonMC.toBidual (dual F)) :=
    isIso_toBidual_dual_of_locallyNoetherian_boundary_two_le_depth X U hdepth F hF
  have : IsIso (ZeroSchemeCanonMC.toBidual V) :=
    isIso_toBidual_of_finiteFreeLocus_eq_top V hfree
  let eDual : dual (F.restrict U.ι) ≅ dual (dual V) :=
    ((MonoidalClosed.internalHom (C := U.toScheme.Modules)).mapIso e.symm.op).app
      (𝟙_ U.toScheme.Modules)
  let eOpen : dual (F.restrict U.ι) ≅ V :=
    eDual ≪≫ (asIso (ZeroSchemeCanonMC.toBidual V)).symm
  let d : dual F ≅ (pushforward U.ι).obj V :=
    dualOpenDirectImageIsoOfLocallyNoetherian X U hdepth F ≪≫
      (pushforward U.ι).mapIso eOpen
  exact isIso_toBidual_of_iso d

/-- A prescribed open identification of a reflexive module extends to
exactly one identification with the original direct image globally. -/
theorem existsUnique_reflexive_extensionIso_of_locallyNoetherian_boundary_two_le_depth
    (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ U →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x) (X.presheaf.stalk x))
    (M : X.Modules) [IsIso (ZeroSchemeCanonMC.toBidual M)]
    (V : U.toScheme.Modules) (eU : M.restrict U.ι ≅ V) :
    ∃! e : M ≅ (pushforward U.ι).obj V,
      (restrictFunctor U.ι).map e.hom ≫ (restrictAdjunction U.ι).counit.app V =
        eU.hom := by
  let adj := restrictAdjunction U.ι
  have : IsIso (adj.unit.app M) :=
    isIso_reflexive_unit_of_locallyNoetherian_boundary_two_le_depth X U hdepth M
  let e : M ≅ (pushforward U.ι).obj V :=
    asIso (adj.unit.app M) ≪≫ (pushforward U.ι).mapIso eU
  have he : (restrictFunctor U.ι).map e.hom ≫ adj.counit.app V = eU.hom :=
    (adj.homEquiv M V).symm_apply_apply eU.hom
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply (adj.homEquiv M V).symm.injective
  exact hd.trans he.symm

end Scheme.Modules
end AlgebraicGeometry
