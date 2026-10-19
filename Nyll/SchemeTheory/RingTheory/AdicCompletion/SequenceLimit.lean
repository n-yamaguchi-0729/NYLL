/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.AdicCompletion.FiniteModuleSystem
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Cones

/-!
# Native limits and the actual compatible-sequence module

The module of sequences satisfying the original successor equations is
the categorical limit of a module diagram indexed by the opposite of the
natural numbers. The universal cone is constructed explicitly. Its unique
comparison with the native limit preserves every original projection.

This comparison applies after evaluating a diagram of module sheaves on
an open, without assuming finiteness or surjectivity of its transitions.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace AdicModuleSystem

universe u v

variable {R : Type u} [CommRing R] (D : ℕᵒᵖ ⥤ ModuleCat.{v} R)

local notation "M" => fun n : ℕ => D.obj (op n)
local notation "t" => fun n : ℕ =>
  ModuleCat.Hom.hom (D.map (Quiver.Hom.op (homOfLE (Nat.le_add_right n 1))))

/-- The cone whose point is the original module of compatible sequences. -/
def sequenceCone : Cone D where
  pt := ModuleCat.of R (sections M t)
  π := NatTrans.ofOpSequence (fun n => ModuleCat.ofHom (eval M t n)) (by
    intro n
    change 𝟙 (ModuleCat.of R (sections M t)) ≫ ModuleCat.ofHom (eval M t n) =
      ModuleCat.ofHom (eval M t (n + 1)) ≫ D.map (homOfLE (Nat.le_add_right n 1)).op
    rw [Category.id_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (transition_eval M t n x).symm)

/-- Compatible projections into the original stages give the unique map
to the actual sequence module. -/
def sequenceConeIsLimit : IsLimit (sequenceCone D) where
  lift s := ModuleCat.ofHom
    { toFun := fun x => ⟨fun n => (s.π.app (op n)).hom x, by
        intro n
        have h := s.w (homOfLE (Nat.le_add_right n 1)).op
        exact congrArg (fun a : s.pt ⟶ D.obj (op n) => a.hom x) h⟩
      map_add' := fun x y => by
        apply Subtype.ext
        funext n
        exact (s.π.app (op n)).hom.map_add x y
      map_smul' := fun r x => by
        apply Subtype.ext
        funext n
        exact (s.π.app (op n)).hom.map_smul r x }
  fac s j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  uniq s m hm := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext n
    exact congrArg (fun a : s.pt ⟶ D.obj (op n) => a.hom x) (hm (op n))

/-- The native limit is the constructed module of original compatible sequences. -/
def sequenceLimitIso : limit D ≅ ModuleCat.of R (sections M t) :=
  (limit.isLimit D).conePointUniqueUpToIso (sequenceConeIsLimit D)

/-- The comparison with the actual sequence module as a linear equivalence. -/
def sequenceLimitEquiv : ↥(limit D) ≃ₗ[R] sections M t :=
  (sequenceLimitIso D).toLinearEquiv

/-- The comparison preserves the literal original projection in every degree. -/
theorem sequenceLimitEquiv_apply (x : ↥(limit D)) (n : ℕ) :
    (sequenceLimitEquiv D x).val n = (limit.π D (op n)).hom x := by
  have h := IsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit D) (sequenceConeIsLimit D) (op n)
  exact congrArg (fun a : limit D ⟶ D.obj (op n) => a.hom x) h

/-- A compatible family has its original components under every native projection. -/
theorem sequenceLimitEquiv_symm_apply (x : sections M t) (n : ℕ) :
    (limit.π D (op n)).hom ((sequenceLimitEquiv D).symm x) = x.val n := by
  rw [← sequenceLimitEquiv_apply]
  exact congrArg (fun y : sections M t => y.val n) ((sequenceLimitEquiv D).apply_symm_apply x)

end AdicModuleSystem
