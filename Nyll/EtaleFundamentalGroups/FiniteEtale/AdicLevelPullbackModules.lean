/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.AdicCoverTower
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypeFinitePushforward
import Nyll.SchemeTheory.Modules.FiniteType.FiniteTypePullback
import Nyll.SchemeTheory.Modules.Functoriality.ClosedImmersionUnit
import Nyll.SchemeTheory.Modules.Functoriality.PullbackQuotientTransition
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPullback
import Nyll.SchemeTheory.Modules.Quasicoherent.QuasicoherentPushforward
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Actual module quotients on the adic thickenings

At each original closed level, pull the ambient module back to that
level and then take its actual direct image. The original adjunction
unit gives the quotient map. The constructed transition between these
modules commutes with both original units.

For a quasicoherent module all these maps are epimorphic, and every
level remains quasicoherent. Finite type is retained as well. In the
free case these are the actual free modules on the thickenings, as
opposed to a fixed ambient free module used at every level.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale.AdicCoverTower

open Scheme.Modules

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) (I : Ideal A)

instance levelProjection_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (Limits.pullback.fst f (baseInclusion I n)) := by
  have : IsClosedImmersion (baseInclusion I n) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (levelIdeal I n)))
      Ideal.Quotient.mk_surjective
  infer_instance

variable (M : X.Modules)

/-- The actual direct image of the module pulled back to the
specified original closed level. -/
def levelPullbackModule (n : ℕ) : X.Modules :=
  (pushforward (Limits.pullback.fst f (baseInclusion I n))).obj
    ((Scheme.Modules.pullback (Limits.pullback.fst f (baseInclusion I n))).obj M)

/-- The quotient map is the original pullback adjunction unit. -/
def levelPullbackUnit (n : ℕ) : M ⟶ levelPullbackModule f I M n :=
  (pullbackPushforwardAdjunction (Limits.pullback.fst f (baseInclusion I n))).unit.app M

/-- The transition is constructed from the actual intermediate
inclusion and both original pullback quotients. -/
def levelPullbackTransition (n : ℕ) :
    levelPullbackModule f I M (n + 1) ⟶ levelPullbackModule f I M n :=
  pullbackQuotientTransition (transition f I n)
    (Limits.pullback.fst f (baseInclusion I (n + 1)))
    (Limits.pullback.fst f (baseInclusion I n)) (transition_fst f I n) M

/-- The level quotient retains the original adjunction unit as its
literal native morphism. This equation fixes its functor-object boundary. -/
theorem levelPullbackUnit_def (n : ℕ) :
    levelPullbackUnit f I M n =
      (pullbackPushforwardAdjunction (Limits.pullback.fst f (baseInclusion I n))).unit.app M :=
  rfl

/-- The level transition retains the actual intermediate-unit map
and the original commutative triangle of scheme morphisms. -/
theorem levelPullbackTransition_def (n : ℕ) :
    levelPullbackTransition f I M n =
      pullbackQuotientTransition (transition f I n)
        (Limits.pullback.fst f (baseInclusion I (n + 1)))
        (Limits.pullback.fst f (baseInclusion I n)) (transition_fst f I n) M := rfl

private theorem levelPullbackUnit_transition_native (n : ℕ) :
    (pullbackPushforwardAdjunction (Limits.pullback.fst f (baseInclusion I (n + 1)))).unit.app M ≫
      pullbackQuotientTransition (transition f I n)
        (Limits.pullback.fst f (baseInclusion I (n + 1)))
        (Limits.pullback.fst f (baseInclusion I n)) (transition_fst f I n) M =
      (pullbackPushforwardAdjunction (Limits.pullback.fst f (baseInclusion I n))).unit.app M :=
  unit_pullbackQuotientTransition (transition f I n)
    (Limits.pullback.fst f (baseInclusion I (n + 1)))
    (Limits.pullback.fst f (baseInclusion I n)) (transition_fst f I n) M

/-- The original level transition commutes with the original
quotient maps from the ambient module. -/
theorem levelPullbackUnit_transition (n : ℕ) :
    levelPullbackUnit f I M (n + 1) ≫ levelPullbackTransition f I M n =
      levelPullbackUnit f I M n := by
  rw [levelPullbackUnit_def, levelPullbackUnit_def, levelPullbackTransition_def]
  exact levelPullbackUnit_transition_native f I M n

instance levelPullbackModule_isQuasicoherent [M.IsQuasicoherent] (n : ℕ) :
    (levelPullbackModule f I M n).IsQuasicoherent := by
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  let N : (level f I n).Modules := (Scheme.Modules.pullback i).obj M
  have : IsClosedImmersion i := levelProjection_isClosedImmersion f I n
  have : N.IsQuasicoherent := isQuasicoherent_pullback i M
  exact isQuasicoherent_pushforward_of_isAffineHom i N

instance levelPullbackModule_isFiniteType [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    (levelPullbackModule f I M n).IsFiniteType := by
  let i : level f I n ⟶ X := Limits.pullback.fst f (baseInclusion I n)
  let N : (level f I n).Modules := (Scheme.Modules.pullback i).obj M
  have : IsClosedImmersion i := levelProjection_isClosedImmersion f I n
  have : N.IsQuasicoherent := isQuasicoherent_pullback i M
  have : N.IsFiniteType := isFiniteType_pullback i M
  exact isFiniteType_pushforward_of_isFinite i N

instance levelPullbackUnit_epi [M.IsQuasicoherent] (n : ℕ) :
    Epi (levelPullbackUnit f I M n) :=
  epi_pullbackUnit_of_isClosedImmersion (Limits.pullback.fst f (baseInclusion I n)) M

instance levelPullbackTransition_epi [M.IsQuasicoherent] (n : ℕ) :
    Epi (levelPullbackTransition f I M n) :=
  epi_pullbackQuotientTransition_of_isClosedImmersion (transition f I n)
    (Limits.pullback.fst f (baseInclusion I (n + 1)))
    (Limits.pullback.fst f (baseInclusion I n)) (transition_fst f I n) M

end AlgebraicGeometry.FiniteEtale.AdicCoverTower
