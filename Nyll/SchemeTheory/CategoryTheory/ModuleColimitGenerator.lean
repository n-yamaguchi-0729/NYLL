/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.Tensor.PresheafPullbackMonoidal
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Exact.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The coefficient module detects isomorphisms of cocontinuous functors

The actual free module on all elements surjects onto a module. Applying
the same construction to its actual kernel gives a cokernel presentation
by two coproducts of the coefficient module. Thus a natural transformation
between colimit-preserving functors is invertible everywhere once its
component on the coefficient module is invertible.
-/

noncomputable section

universe u v w

open CategoryTheory Limits

namespace CategoryTheory.NatTrans

variable {R : Type u} [CommRing R] {C : Type v} [Category.{w} C]
  {F G : ModuleCat.{u} R ⥤ C}
  [PreservesColimitsOfSize.{u, u} F] [PreservesColimitsOfSize.{u, u} G]
  (τ : F ⟶ G) (hR : IsIso (τ.app (ModuleCat.of R R)))

include hR

private theorem isIso_app_finsupp (ι : Type u) :
    IsIso (τ.app (ModuleCat.of R (ι →₀ R))) :=
  isIso_app_of_isColimit τ (ModuleCat.finsuppCoconeIsColimit R R ι) (fun _ => hR)

/-- The coefficient module detects all components of a natural transformation
between actual colimit-preserving functors on modules. -/
theorem isIso_app_of_module_unit (M : ModuleCat.{u} R) : IsIso (τ.app M) := by
  classical
  let P : ModuleCat.{u} R := ModuleCat.of R (M →₀ R)
  let p : P ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination R id)
  have hp : Function.Surjective p.hom := by
    intro x
    refine ⟨Finsupp.single x 1, ?_⟩
    exact (Finsupp.linearCombination_single (R := R) (v := id) 1 x).trans (one_smul R x)
  let K : Submodule R P := p.hom.ker
  let Q : ModuleCat.{u} R := ModuleCat.of R (K →₀ R)
  let q : Q ⟶ P :=
    ModuleCat.ofHom (K.subtype.comp (Finsupp.linearCombination R id))
  have hq : Function.Exact q.hom p.hom := by
    intro x
    constructor
    · intro hx
      refine ⟨Finsupp.single (⟨x, hx⟩ : K) 1, ?_⟩
      change (Finsupp.linearCombination R id
        (Finsupp.single (⟨x, hx⟩ : K) 1)).val = x
      rw [Finsupp.linearCombination_single, one_smul]
      rfl
    · rintro ⟨y, rfl⟩
      exact (Finsupp.linearCombination R id y).property
  have : PreservesColimitsOfSize.{0, 0} F :=
    preservesSmallestColimits_of_preservesColimits F
  have : PreservesColimitsOfSize.{0, 0} G :=
    preservesSmallestColimits_of_preservesColimits G
  apply isIso_app_of_isColimit τ (ModuleCat.isColimitCokernelCofork q p hq hp)
  intro j
  cases j with
  | zero => exact isIso_app_finsupp τ hR K
  | one => exact isIso_app_finsupp τ hR M

end CategoryTheory.NatTrans
