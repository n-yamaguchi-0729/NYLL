/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Purity.Local.BoundaryHomHartogs
public import Nyll.SchemeTheory.Modules.Functoriality.PushforwardIhom
public import Nyll.SchemeTheory.Modules.Sections.BidualEvaluation
public import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal

/-!
# Detecting dual morphisms across a depth-two boundary

Scalar Hom-Hartogs and tensor-Hom adjunction show that restriction detects
equality of all morphisms into an actual dual. The canonical split bidual
map of a dual is therefore an isomorphism as soon as it is an isomorphism
on the given open. No separate dual or unspecified extension is used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual dual equals the original direct image of its restricted
dual across an affine Noetherian depth-two boundary. -/
def dualOpenDirectImageIso
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (M : (Spec R).Modules) :
    dual M ≅ (pushforward U.ι).obj (dual (M.restrict U.ι)) := by
  have : IsIso ((restrictAdjunction U.ι).unit.app (𝟙_ (Spec R).Modules)) :=
    isIso_structure_unit_of_scalar_hartogs R U
      (restrict_bijective_of_boundary_two_le_depth R U hdepth)
  let e : (𝟙_ (Spec R).Modules) ≅
      (pushforward U.ι).obj (𝟙_ U.toScheme.Modules) :=
    asIso ((restrictAdjunction U.ι).unit.app (𝟙_ (Spec R).Modules)) ≪≫
      (pushforward U.ι).mapIso (restrictUnitIso U.ι)
  exact (ihom M).mapIso e ≪≫ ihomPushforwardRestrictIso U.ι M (𝟙_ U.toScheme.Modules)

/-- Every actual dual satisfies Hartogs for the original open-restriction
unit. The inverse is supplied by the constructed direct-image comparison. -/
theorem isIso_dual_unit_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (M : (Spec R).Modules) :
    IsIso ((restrictAdjunction U.ι).unit.app (dual M)) :=
  (restrictAdjunction U.ι).isIso_unit_app_of_iso (dualOpenDirectImageIso R U hdepth M)

/-- Canonical reflexivity supplies the original Hartogs unit, without
any extra extension hypothesis on the given module. -/
theorem isIso_unit_of_reflexive_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (M : (Spec R).Modules) [IsIso (ZeroSchemeCanonMC.toBidual M)] :
    IsIso ((restrictAdjunction U.ι).unit.app M) :=
  (restrictAdjunction U.ι).isIso_unit_app_of_iso
    (asIso (ZeroSchemeCanonMC.toBidual M) ≪≫ dualOpenDirectImageIso R U hdepth (dual M))

/-- Every morphism into a reflexive module extends uniquely from the
open complement of an affine Noetherian depth-two boundary. -/
theorem hom_restrict_to_reflexive_bijective_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (M N : (Spec R).Modules) [IsIso (ZeroSchemeCanonMC.toBidual N)] :
    Function.Bijective (fun f : M ⟶ N => (restrictFunctor U.ι).map f) := by
  have : IsIso ((restrictAdjunction U.ι).unit.app N) :=
    isIso_unit_of_reflexive_of_boundary_two_le_depth R U hdepth N
  exact hom_restrict_bijective_of_unit_isIso U.ι M N

/-- Actual morphisms into a dual are determined by their restrictions
across an arbitrary affine Noetherian depth-two boundary. -/
theorem hom_restrict_to_dual_injective_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (M N : (Spec R).Modules) :
    Function.Injective (fun f : N ⟶ dual M => (restrictFunctor U.ι).map f) := by
  intro f g hfg
  change (restrictFunctor U.ι).map f = (restrictFunctor U.ι).map g at hfg
  let e := restrictFunctorIsoPullback U.ι
  have hfg' : (pullback U.ι).map f = (pullback U.ι).map g := by
    rw [← NatIso.naturality_1 e f, ← NatIso.naturality_1 e g, hfg]
  have huncurry : (pullback U.ι).map (MonoidalClosed.uncurry f) =
      (pullback U.ι).map (MonoidalClosed.uncurry g) := by
    rw [MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_eq,
      Functor.map_comp, Functor.map_comp,
      Functor.Monoidal.map_whiskerLeft, Functor.Monoidal.map_whiskerLeft, hfg']
  have hrestrict : (restrictFunctor U.ι).map (MonoidalClosed.uncurry f) =
      (restrictFunctor U.ι).map (MonoidalClosed.uncurry g) := by
    rw [← NatIso.naturality_1 e.symm, ← NatIso.naturality_1 e.symm, huncurry]
  have h := (hom_restrict_to_structure_bijective_of_boundary_two_le_depth
    R U hdepth (M ⊗ N)).1 hrestrict
  exact (MonoidalClosed.curry_uncurry f).symm.trans
    ((congrArg MonoidalClosed.curry h).trans (MonoidalClosed.curry_uncurry g))

/-- The actual bidual map of a dual is an isomorphism globally whenever
its restriction is one on the complement of a depth-two boundary. -/
theorem isIso_toBidual_dual_of_restrict_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (M : (Spec R).Modules)
    [IsIso ((restrictFunctor U.ι).map (ZeroSchemeCanonMC.toBidual (dual M)))] :
    IsIso (ZeroSchemeCanonMC.toBidual (dual M)) := by
  let F := restrictFunctor U.ι
  let a := ZeroSchemeCanonMC.toBidual (dual M)
  let b := (MonoidalClosed.pre (ZeroSchemeCanonMC.toBidual M)).app
    (𝟙_ (Spec R).Modules)
  have hab : a ≫ b = 𝟙 (dual M) := toBidual_dual_comp_pre M
  have hba : b ≫ a = 𝟙 (dual (dual (dual M))) := by
    apply hom_restrict_to_dual_injective_of_boundary_two_le_depth R U hdepth
      (dual (dual M)) (dual (dual (dual M)))
    change F.map (b ≫ a) = F.map (𝟙 _)
    apply (cancel_epi (F.map a)).mp
    rw [← F.map_comp, ← Category.assoc, hab, Category.id_comp,
      F.map_id, Category.comp_id]
  exact ⟨⟨b, hab, hba⟩⟩

/-- A module locally free on the complement of a depth-two boundary has
a reflexive actual dual. The open bidual isomorphism is constructed from
finite local bases rather than supplied as an additional premise. -/
theorem isIso_toBidual_dual_of_boundary_two_le_depth
    (R : CommRingCat.{u}) [IsNoetherianRing R]
    (U : (Spec R).Opens)
    (hdepth : ∀ p : Spec R, p ∉ U →
      (2 : ℕ∞) ≤ Module.depth ((Spec R).presheaf.stalk p)
        ((Spec R).presheaf.stalk p))
    (M : (Spec R).Modules) (hfree : U ≤ finiteFreeLocus M) :
    IsIso (ZeroSchemeCanonMC.toBidual (dual M)) := by
  have : IsIso ((restrictFunctor U.ι).map (ZeroSchemeCanonMC.toBidual (dual M))) :=
    isIso_restrict_toBidual_of_le_finiteFreeLocus (dual M) U
      (hfree.trans (finiteFreeLocus_le_dual M))
  exact isIso_toBidual_dual_of_restrict_of_boundary_two_le_depth R U hdepth M

end AlgebraicGeometry.Scheme.Modules
