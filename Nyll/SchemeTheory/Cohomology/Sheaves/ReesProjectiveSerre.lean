/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.ModulePresheafDEqDDMemPow
import Nyll.SchemeTheory.Cohomology.Sheaves.ModuleSheafPresheaf
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.BaseChangeStandardCover
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheaf
import Nyll.SchemeTheory.ProjectiveSpace.TwistingSheafSerreBaseChange
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Serre vanishing on the original projective Rees cover

The ordered cover in the Rees coefficient construction is the
first-projection pullback of the original standard coordinate cover.
It therefore equals the cover transported from projective space over
the Rees algebra through the actual base-change isomorphism.

Use that equality to place native coherent Serre vanishing on the
original Rees Čech complex. The sheaf and twisting line bundle remain
the original sheaf on the literal pullback and the original
first-projection pullback of the twisting sheaf. No identification of
the successive kernels of a formal system is assumed here.
-/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS

open AlgebraicGeometry AlgebraicGeometry.ProjSpace Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ)

local notation "X" => Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)

/-- The ordered Rees cover retains exactly the coordinate opens
pulled back by the original first projection. -/
theorem reesProjectiveCover_eq_firstProjection :
    K' I (π R n) (stdCoverPullback (𝟙 X)) = stdCoverPullback (fst' I (π R n)) := rfl

/-- The existing Rees cover is the coordinate cover transported by
the inverse of the actual projective-space base-change isomorphism. -/
theorem reesProjectiveCover_eq_baseChangeIso :
    K' I (π R n) (stdCoverPullback (𝟙 X)) =
      stdCoverPullback (isPullback_map R (Rr I) n).isoPullback.inv :=
  (reesProjectiveCover_eq_firstProjection R I n).trans
    (stdCoverPullback_baseChangeIso_inv R (Rr I) n).symm

/-- One twist bound kills every positive Čech degree of a native
coherent sheaf on the original projective Rees cover. -/
theorem exists_rees_twisting_bound_subsingleton_HSucc [IsNoetherianRing R]
    (F : (P' I (π R n)).Modules)
    [SheafOfModules.IsQuasicoherent (R := (P' I (π R n)).ringCatSheaf) F]
    [SheafOfModules.IsFiniteType (R := (P' I (π R n)).ringCatSheaf) F] :
    ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ q : ℕ,
      Subsingleton ((toOModulePresheaf (π' I (π R n))
        (F ⊗ ((Scheme.Modules.pullback (fst' I (π R n))).obj
          (twistingSheaf R n)).tensorPow d)).HSucc
            (K' I (π R n) (stdCoverPullback (𝟙 X))) q) := by
  obtain ⟨c, hc⟩ := exists_baseChange_twisting_bound_subsingleton_HSucc R (Rr I) n F
  refine ⟨c, ?_⟩
  intro d hd q
  rw [reesProjectiveCover_eq_baseChangeIso R I n]
  exact hc d hd q

end AlgebraicCurves.Cohomology.Sheaves.Proofs.ReesCechApproximation.SolKS
