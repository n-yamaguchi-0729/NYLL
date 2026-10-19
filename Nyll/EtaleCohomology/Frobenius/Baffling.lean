/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.PullbackCohomology
import Nyll.EtaleCohomology.Frobenius.SheafComparison
import Nyll.EtaleCohomology.Sites.ConstantPullbackComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Absolute finite-field Frobenius is trivial on étale cohomology

The actual pullback on cohomology becomes the identity after the sheaf
comparison defined by relative Frobenius. The constant-integer comparison
in the definition of cohomological pullback is identified with this same
sheaf comparison using the constant-sheaf adjunction.

This is the finite-field q-power instance of the baffling theorem. It does
not identify the base change of Frobenius on a scheme defined over the
finite field with absolute Frobenius after extending the constant field.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Abelian

namespace EtaleCohomology

variable (k : Type u) [Field k] [Fintype k] (X : Scheme.{u})
  [X.Over (Spec (.of k))]

/-- Absolute q-power Frobenius acts as the identity on étale cohomology
under the canonical comparison supplied by relative Frobenius. -/
theorem etaleAbelianCohomologyFrobeniusPullback_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) (x : Sheaf.H.{u} F n) :
    Sheaf.H.map ((etaleAbelianFrobeniusPullbackIso k X).hom.app F) n
        (etaleAbelianCohomologyPullbackMap (X.finiteFieldFrobenius k) F n x) = x := by
  let Z := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let eZ := (etaleAbelianPullbackConstantIso (X.finiteFieldFrobenius k)).app
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let τ := (etaleAbelianFrobeniusPullbackIso k X).hom
  have hZ : eZ.hom = τ.app Z :=
    Sites.constantSheafCompLeftAdjointIso_hom_of_siteIso X.smallEtaleTopology AddCommGrpCat.{u}
      (etaleBaseChange (X.finiteFieldFrobenius k))
      (Scheme.Etale.finiteFieldFrobeniusPullbackIso k X).symm
      terminalIsTerminal
      (terminalIsTerminal.isTerminalObj (etaleBaseChange (X.finiteFieldFrobenius k))
        (⊤_ X.Etale))
      (etaleAbelianPullback (X.finiteFieldFrobenius k))
      (etaleAbelianPullbackPushforwardAdjunction (X.finiteFieldFrobenius k))
      (AddCommGrpCat.of (ULift.{u} ℤ))
  have hx := Ext.mapExactFunctor_comp_mk₀_natTransApp x τ
  rw [Ext.id_mapExactFunctor, ← hZ] at hx
  rw [Sheaf.H.map_apply, etaleAbelianCohomologyPullbackMap_apply,
    Ext.comp_assoc_of_third_deg_zero]
  change (Ext.mk₀ eZ.inv).comp
    ((x.mapExactFunctor (etaleAbelianPullback (X.finiteFieldFrobenius k))).comp
      (Ext.mk₀ (τ.app F)) (add_zero n)) (zero_add n) = x
  rw [hx, Ext.mk₀_comp_mk₀_assoc, eZ.inv_hom_id, Ext.mk₀_id_comp]

/-- With constant abelian coefficients, the canonical constant-sheaf
identification makes absolute q-power Frobenius the identity in every degree. -/
theorem etaleAbelianConstantCohomologyFrobeniusPullback_eq
    (A : AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n) :
    Sheaf.H.map ((etaleAbelianPullbackConstantIso (X.finiteFieldFrobenius k)).hom.app A) n
        (etaleAbelianCohomologyPullbackMap (X.finiteFieldFrobenius k)
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) n x) = x := by
  let F := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A
  have hA : ((etaleAbelianPullbackConstantIso (X.finiteFieldFrobenius k)).hom.app A) =
      (etaleAbelianFrobeniusPullbackIso k X).hom.app F :=
    Sites.constantSheafCompLeftAdjointIso_hom_of_siteIso X.smallEtaleTopology AddCommGrpCat.{u}
      (etaleBaseChange (X.finiteFieldFrobenius k))
      (Scheme.Etale.finiteFieldFrobeniusPullbackIso k X).symm
      terminalIsTerminal
      (terminalIsTerminal.isTerminalObj (etaleBaseChange (X.finiteFieldFrobenius k))
        (⊤_ X.Etale))
      (etaleAbelianPullback (X.finiteFieldFrobenius k))
      (etaleAbelianPullbackPushforwardAdjunction (X.finiteFieldFrobenius k)) A
  exact (congrArg (fun φ : (etaleAbelianPullback (X.finiteFieldFrobenius k)).obj F ⟶ F =>
    Sheaf.H.map φ n
      (etaleAbelianCohomologyPullbackMap (X.finiteFieldFrobenius k) F n x)) hA).trans
      (etaleAbelianCohomologyFrobeniusPullback_eq k X F n x)

end EtaleCohomology
