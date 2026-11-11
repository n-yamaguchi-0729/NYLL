/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.Local.BoundaryDualHartogs
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeCoherence
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteFreeTransport
public import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeOfFiniteSections
public import Nyll.SchemeTheory.Modules.Sections.AffineIhomSections
public import Nyll.SchemeTheory.Modules.Submodules.FiniteModuleExtension

/-!
# Finite direct images across a depth-two boundary

For a finite locally free module on an open in a Noetherian affine scheme,
extend its actual dual to a finite quasicoherent module. Scalar Hartogs
and the native closed adjunction identify the dual of that extension
with the original open direct image. Its finite global sections then
prove finite type of that very direct image.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection

namespace AlgebraicGeometry.Scheme.Modules

/-- The original open direct image is the dual of an actual finite QC
extension of the original dual module. -/
theorem exists_dualIso_pushforward_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (V : U.toScheme.Modules) (hfree : finiteFreeLocus V = ⊤) :
    ∃ F : (Spec R).Modules, F.IsQuasicoherent ∧ F.IsFiniteType ∧
      Nonempty (F.restrict U.ι ≅ dual V) ∧
      Nonempty (dual F ≅ (pushforward U.ι).obj V) := by
  have hdual : finiteFreeLocus (dual V) = ⊤ :=
    top_unique (hfree ▸ finiteFreeLocus_le_dual V)
  have : (dual V).IsQuasicoherent :=
    isQuasicoherent_of_finiteFreeLocus_eq_top (dual V) hdual
  have : (dual V).IsFiniteType :=
    isFiniteType_of_finiteFreeLocus_eq_top (dual V) hdual
  obtain ⟨F, hFqc, hFft, ⟨e⟩⟩ := exists_finiteType_extension_of_qcqs U
    (NoetherianSpace.isCompact _) (dual V)
  have : IsIso (ZeroSchemeCanonMC.toBidual V) :=
    isIso_toBidual_of_finiteFreeLocus_eq_top V hfree
  let eDual : dual (F.restrict U.ι) ≅ dual (dual V) :=
    ((MonoidalClosed.internalHom (C := U.toScheme.Modules)).mapIso e.symm.op).app
      (𝟙_ U.toScheme.Modules)
  let eOpen : dual (F.restrict U.ι) ≅ V :=
    eDual ≪≫ (asIso (ZeroSchemeCanonMC.toBidual V)).symm
  exact ⟨F, hFqc, hFft, ⟨e⟩,
    ⟨dualOpenDirectImageIso R U hdepth F ≪≫ (pushforward U.ι).mapIso eOpen⟩⟩

/-- The actual direct image of a finite locally free module is finite
type across any affine Noetherian depth-two boundary. -/
theorem isFiniteType_pushforward_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (V : U.toScheme.Modules) (hfree : finiteFreeLocus V = ⊤) :
    ((pushforward U.ι).obj V).IsFiniteType := by
  have : V.IsQuasicoherent := isQuasicoherent_of_finiteFreeLocus_eq_top V hfree
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _)
  have : QuasiCompact U.ι := inferInstance
  let P : (Spec R).Modules := (pushforward U.ι).obj V
  have : P.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_openImmersion U.ι V
  obtain ⟨F, hFqc, hFft, _, ⟨e⟩⟩ :=
    exists_dualIso_pushforward_of_boundary_two_le_depth R U hdepth V hfree
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (dual F)) :=
    moduleFinite_moduleSpecΓ_dual_of_isFiniteType F
  have : Module.Finite R ((moduleSpecΓFunctor (R := R)).obj P) :=
    Module.Finite.equiv ((moduleSpecΓFunctor (R := R)).mapIso e).toLinearEquiv
  exact isFiniteType_of_finite_moduleSpecΓ P

/-- The original direct image is reflexive through its canonical bidual
map, for an arbitrary affine Noetherian depth-two boundary. -/
theorem isIso_toBidual_pushforward_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (V : U.toScheme.Modules) (hfree : finiteFreeLocus V = ⊤) :
    IsIso (ZeroSchemeCanonMC.toBidual ((pushforward U.ι).obj V)) := by
  obtain ⟨F, _, _, ⟨e⟩, ⟨d⟩⟩ :=
    exists_dualIso_pushforward_of_boundary_two_le_depth R U hdepth V hfree
  have hdual : finiteFreeLocus (dual V) = ⊤ :=
    top_unique (hfree ▸ finiteFreeLocus_le_dual V)
  have hFU : finiteFreeLocus (F.restrict U.ι) = ⊤ :=
    (finiteFreeLocus_eq_of_iso e).trans hdual
  have hF : U ≤ finiteFreeLocus F := le_finiteFreeLocus_of_restrict_eq_top F U hFU
  have : IsIso (ZeroSchemeCanonMC.toBidual (dual F)) :=
    isIso_toBidual_dual_of_boundary_two_le_depth R U hdepth F hF
  exact isIso_toBidual_of_iso d

/-- A specified open identification of a reflexive module with the
given finite locally free module extends to exactly one identification
with its original direct image. Uniqueness retains that identification. -/
theorem existsUnique_iso_pushforward_of_reflexive_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (M : (Spec R).Modules) [IsIso (ZeroSchemeCanonMC.toBidual M)]
    (V : U.toScheme.Modules) (eU : M.restrict U.ι ≅ V) :
    ∃! e : M ≅ (pushforward U.ι).obj V,
      (restrictFunctor U.ι).map e.hom ≫ (restrictAdjunction U.ι).counit.app V =
        eU.hom := by
  let adj := restrictAdjunction U.ι
  have : IsIso (adj.unit.app M) :=
    isIso_unit_of_reflexive_of_boundary_two_le_depth R U hdepth M
  let e : M ≅ (pushforward U.ι).obj V :=
    asIso (adj.unit.app M) ≪≫ (pushforward U.ι).mapIso eU
  have he : (restrictFunctor U.ι).map e.hom ≫ adj.counit.app V = eU.hom :=
    (adj.homEquiv M V).symm_apply_apply eU.hom
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply (adj.homEquiv M V).symm.injective
  exact hd.trans he.symm

end AlgebraicGeometry.Scheme.Modules
