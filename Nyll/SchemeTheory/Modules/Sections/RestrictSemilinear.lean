/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Ring.CompTypeclasses

/-!
# Actual coefficient and section comparisons for an affine chart

The global sections of a module restricted to an affine spectrum use
the spectrum's coefficient ring. The original sections over the image
open use its actual structure sheaf ring. Their comparison is semilinear
for the composite of the canonical spectrum isomorphism and the open
immersion's actual section isomorphism.

The underlying additive comparison is the original `restrictAppIso`.
This retains the original section morphisms while supplying the exact
coefficient change needed for tensor products of sections.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {R : CommRingCat.{u}}
  (j : Spec R ⟶ X) [IsOpenImmersion j]

/-- The actual coefficient isomorphism from a spectrum to its image
open, using the canonical spectrum and open-immersion section maps. -/
def specRestrictionRingEquiv : R ≃+* Γ(X, j ''ᵁ ⊤) :=
  ((ΓSpecIso R).symm ≪≫ (j.appIso ⊤).symm).commRingCatIsoToRingEquiv

local instance :
    RingHomInvPair (specRestrictionRingEquiv j : R →+* Γ(X, j ''ᵁ ⊤))
      ((specRestrictionRingEquiv j).symm : Γ(X, j ''ᵁ ⊤) →+* R) :=
  RingHomInvPair.of_ringEquiv (specRestrictionRingEquiv j)

local instance :
    RingHomInvPair ((specRestrictionRingEquiv j).symm : Γ(X, j ''ᵁ ⊤) →+* R)
      (specRestrictionRingEquiv j : R →+* Γ(X, j ''ᵁ ⊤)) :=
  RingHomInvPair.of_ringEquiv_symm (specRestrictionRingEquiv j)

/-- The section comparison for an affine chart is semilinear for the
actual coefficient isomorphism of that chart. -/
def specRestrictionSectionsEquiv (M : X.Modules) :
    LinearEquiv
      (σ' := ((specRestrictionRingEquiv j).symm : Γ(X, j ''ᵁ ⊤) →+* R))
      (specRestrictionRingEquiv j : R →+* Γ(X, j ''ᵁ ⊤))
      ((moduleSpecΓFunctor (R := R)).obj (M.restrict j)) Γ(M, j ''ᵁ ⊤) := by
  let N : (Spec R).Modules := M.restrict j
  let e : Γ(N, ⊤) ≅ Γ(M, j ''ᵁ ⊤) := M.restrictAppIso j ⊤
  refine { e.addCommGroupIsoToAddEquiv with map_smul' := ?_ }
  intro r x
  let x₀ : Γ(N, ⊤) := x
  have hid : (Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ := by
    rw [Subsingleton.elim (⊤ : (Spec R).Opens).leTop (𝟙 _), op_id,
      CategoryTheory.Functor.map_id]
  have hscalar : r • x₀ = (ΓSpecIso R).inv r • x₀ := by
    rw [smul_Spec_def, hid]
    rfl
  have h := congrArg (fun k : Γ(N, ⊤) ⟶ Γ(M, j ''ᵁ ⊤) => k x₀)
    (M.smul_restrictAppIso_hom j ⊤ ((ΓSpecIso R).inv r))
  exact (congrArg (fun y : Γ(N, ⊤) => e.hom y) hscalar).trans h

/-- The semilinear comparison keeps the original open-immersion
section isomorphism as its actual function. -/
theorem specRestrictionSectionsEquiv_apply (M : X.Modules)
    (x : (moduleSpecΓFunctor (R := R)).obj (M.restrict j)) :
    specRestrictionSectionsEquiv j M x = (M.restrictAppIso j ⊤).hom x := rfl

/-- The inverse comparison is the original inverse section map. -/
theorem specRestrictionSectionsEquiv_symm_apply (M : X.Modules)
    (x : Γ(M, j ''ᵁ ⊤)) :
    (specRestrictionSectionsEquiv j M).symm x = (M.restrictAppIso j ⊤).inv x := rfl

/-- The semilinear section comparison commutes with the original
module morphism on both sides of the affine chart. -/
theorem specRestrictionSectionsEquiv_naturality {M N : X.Modules}
    (θ : M ⟶ N) (x : (moduleSpecΓFunctor (R := R)).obj (M.restrict j)) :
    specRestrictionSectionsEquiv j N
        (((moduleSpecΓFunctor (R := R)).map ((restrictFunctor j).map θ)) x) =
      θ.app (j ''ᵁ ⊤) (specRestrictionSectionsEquiv j M x) := rfl

end AlgebraicGeometry.Scheme.Modules
