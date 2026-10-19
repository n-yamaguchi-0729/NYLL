/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverSheaves
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicLevelPullbackModules
import Nyll.SchemeTheory.Affine.ClosedBaseChangeSections
import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionUnit
import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionUnitKernel
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Original affine sections of the actual closed-level pullbacks

The cartesian closed immersion has the original extended ideal power
as its kernel on affine coefficient rings. The actual pullback unit is
therefore surjective on affine sections, with that same ideal power
times the original section module as its kernel. Both statements refer
to the original adjunction unit, without changing the section action.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)

/-- The original section-ring map of an adic closed level has the
literal extended ideal power as its kernel. -/
theorem levelProjection_app_ker (n : ℕ) (U : X.affineOpens) :
    RingHom.ker ((Limits.pullback.fst f (baseInclusion I n)).app U.1).hom =
      (sectionsIdeal f I U.1) ^ (n + 1) := by
  let q : A →+* A ⧸ levelIdeal I n := Ideal.Quotient.mk (levelIdeal I n)
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  let g : level f I n ⟶ Spec (.of (A ⧸ levelIdeal I n)) :=
    Limits.pullback.snd f (baseInclusion I n)
  let σ : A →+* Γ(X, U.1) := (f.constToPresheaf.app (op U.1)).hom
  have hs : IsPullback i g f (Spec.map (CommRingCat.ofHom q)) :=
    IsPullback.of_hasPullback f (baseInclusion I n)
  have hker : RingHom.ker (i.app U.1).hom = (RingHom.ker q).map σ :=
    Scheme.Hom.ker_app_of_closed_baseChange f g i (CommRingCat.ofHom q)
      hs Ideal.Quotient.mk_surjective U.1 U.property
  have hq : RingHom.ker q = levelIdeal I n := Ideal.mk_ker
  calc
    RingHom.ker (i.app U.1).hom = (RingHom.ker q).map σ := hker
    _ = (I ^ (n + 1)).map σ :=
      congrArg (Ideal.map σ) (hq.trans (levelIdeal_eq_pow I n))
    _ = (sectionsIdeal f I U.1) ^ (n + 1) := by
      rw [Ideal.map_pow]
      rfl

variable (M : X.Modules) [M.IsQuasicoherent]

/-- Each original affine section on the closed-level pullback
comes from an original affine section of the ambient module. -/
theorem levelPullbackUnit_app_surjective (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((levelPullbackUnit f I M n).app U.1) :=
  Scheme.Modules.pullbackUnit_app_surjective_of_isClosedImmersion
    (Limits.pullback.fst f (baseInclusion I n)) M U.1 U.property

/-- The kernel of the original closed-level unit on an affine open
is exactly the corresponding power of the original extended ideal. -/
theorem levelPullbackUnit_app_eq_zero_iff (n : ℕ) (U : X.affineOpens)
    (x : Γ(M, U.1)) :
    (levelPullbackUnit f I M n).app U.1 x = 0 ↔
      x ∈ (sectionsIdeal f I U.1) ^ (n + 1) • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  have h := Scheme.Modules.pullbackUnit_app_eq_zero_iff_of_isClosedImmersion
    (Limits.pullback.fst f (baseInclusion I n)) M U.1 U.property x
  exact h.trans (Iff.of_eq (congrArg
    (fun J : Ideal Γ(X, U.1) => x ∈ J • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)))
      (levelProjection_app_ker f I n U)))

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
