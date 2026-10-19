/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Invertible.InvertibleUniqueAppEqSmul
import Nyll.AlgebraicCurves.Geometry.Picard.Rigidification.RigidifiedBundleIsoMapPullbackRigSectionCompEq
import Nyll.SchemeTheory.Modules.Frames.ScalarFrames

/-! Actual automorphisms of an invertible module are multiplication by global units. -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Picard.Proofs
  RigidifiedLineBundle_exists_iso_map_pullback_rigSection_comp_eq.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GeneralizedJacobian.Scalars

variable {X : Scheme.{u}} (M : X.Modules)

/-- Multiplication by global functions, as actual sheaf endomorphisms. -/
def scalarEndHom : Γ(X, ⊤) →* End M where
  toFun s := smulHom s M
  map_one' := smulHom_one M
  map_mul' s t := smulHom_mul s t M

variable {M} (hM : Scheme.Modules.IsInvertible M)

include hM in
/-- Local freeness of rank one makes the scalar endomorphism map injective. -/
theorem scalarEndHom_injective : Function.Injective (scalarEndHom M) := by
  intro a b hab
  apply (hM.existsUnique_app_eq_smul (smulHom a M)).unique
  · intro U x
    rfl
  · intro U x
    exact congrArg (fun φ : M ⟶ M => φ.app U x) hab

include hM in
/-- Every endomorphism is supplied by the actual global scalar theorem. -/
theorem scalarEndHom_surjective : Function.Surjective (scalarEndHom M) := by
  intro φ
  obtain ⟨a, ha, _⟩ := hM.existsUnique_app_eq_smul φ
  refine ⟨a, ?_⟩
  change smulHom a M = φ
  ext U x
  exact (ha U x).symm

/-- The global section ring and the monoid of endomorphisms of the given line bundle. -/
def scalarEndEquiv : Γ(X, ⊤) ≃* End M :=
  MulEquiv.ofBijective (scalarEndHom M)
    ⟨scalarEndHom_injective hM, scalarEndHom_surjective hM⟩

/-- Global units give exactly the automorphisms of the actual invertible module. -/
def scalarAutEquiv : Γ(X, ⊤)ˣ ≃* Aut M :=
  (Units.mapEquiv (scalarEndEquiv hM)).trans (Aut.unitsEndEquivAut M)

theorem scalarAutEquiv_apply (a : Γ(X, ⊤)ˣ) :
    scalarAutEquiv hM a = smulIso a M := CategoryTheory.Iso.ext rfl

include hM in
/-- An arbitrary line-bundle automorphism is an actual scalar automorphism. -/
theorem exists_scalarAut (e : M ≅ M) : ∃ a : Γ(X, ⊤)ˣ, smulIso a M = e := by
  obtain ⟨a, ha⟩ := (scalarAutEquiv hM).surjective e
  exact ⟨a, (scalarAutEquiv_apply hM a).symm.trans ha⟩

/-- On the tensor unit this scalar agrees with the actual global-unit coordinate. -/
theorem unitAutEquivUnits_smulIso (a : Γ(X, ⊤)ˣ) :
    unitAutEquivUnits X (smulIso a (𝟙_ X.Modules)) = a := by
  apply Units.ext
  change resTop (a : Γ(X, ⊤)) ⊤ * (1 : Γ(X, ⊤)) = (a : Γ(X, ⊤))
  rw [resTop_top, mul_one]

/-- The ratio of a frame and its scalar translate is that very unit. -/
theorem frameRatio_scalar (e : M ≅ 𝟙_ X.Modules) (a : Γ(X, ⊤)ˣ) :
    frameRatio e (smulIso a M ≪≫ e) = a := by
  have he : (e.symm ≪≫ (smulIso a M ≪≫ e) : Aut (𝟙_ X.Modules)) =
      smulIso a (𝟙_ X.Modules) := by
    apply CategoryTheory.Iso.ext
    change e.inv ≫ (smulHom (a : Γ(X, ⊤)) M ≫ e.hom) =
      smulHom (a : Γ(X, ⊤)) (𝟙_ X.Modules)
    rw [smulHom_comp, e.inv_hom_id_assoc]
  exact (congrArg (unitAutEquivUnits X) he).trans (unitAutEquivUnits_smulIso a)

end AlgebraicGeometry.GeneralizedJacobian.Scalars
