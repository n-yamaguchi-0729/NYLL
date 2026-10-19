/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeSchemeRestriction
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentLocal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Finite type from the actual affine spectrum restrictions

Transport the actual finite local generators from each affine spectrum
to the open subscheme, and then to the native slice site. The canonical
affine open cover combines those local generating families into finite
type of the original module sheaf. No quasicoherence or Noetherian
hypothesis is needed for this local criterion.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite type is supplied by the actual restrictions to the spectra
of the rings of sections on the canonical affine open cover. -/
theorem isFiniteType_of_affineSpecRestrictions {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      (M.restrict hU.fromSpec).IsFiniteType) : M.IsFiniteType := by
  apply SheafOfModules.IsFiniteType.of_coversTop M (fun U : X.affineOpens => U.1)
    ((Opens.coversTop_iff X _).mpr (iSup_affineOpens_eq_top X))
  intro U
  have hU : IsAffineOpen U.1 := U.2
  let j : Spec Γ(X, U.1) ⟶ X := hU.fromSpec
  have hspec : (M.restrict j).IsFiniteType := h U.1 hU
  have hopen : ((M.restrict j).restrict hU.isoSpec.hom).IsFiniteType :=
    isFiniteType_restrictFunctor hU.isoSpec.hom (M.restrict j) hspec
  let e : ((M.restrict j).restrict hU.isoSpec.hom) ≅ M.restrict U.1.ι :=
    ((restrictFunctorComp hU.isoSpec.hom j).app M).symm ≪≫
      (restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M
  have hrestr : (M.restrict U.1.ι).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (C := U.1.toScheme.Opens) (R := U.1.toScheme.ringCatSheaf)
      (M := (M.restrict j).restrict hU.isoSpec.hom) (N := M.restrict U.1.ι)
      ((sheafOfModulesEquivalence U.1.toScheme).functor.mapIso e) hopen
  exact isFiniteType_over_of_restrict M U.1 hrestr

end AlgebraicGeometry.Scheme.Modules
