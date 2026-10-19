/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository: https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.RelEffCartierDiv
import Nyll.AlgebraicCurves.Geometry.Sheaves.Pullback.InvertiblePullbackPreimageIsoTensorUnit
import Nyll.SchemeTheory.Modules.Functoriality.LocallyFreePushforwardFinite
import Nyll.JacobianVarieties.Generalized.RigidifiedLineBundle

/-!
# Restriction of line-bundle families to a finite flat modulus

Restrict a line bundle to the actual divisor subscheme and push it forward
to the parameter scheme. The resulting module is locally free of the degree
of the divisor. Local frames are supplied by finite-morphism trivialization
of invertible sheaves, with no reducedness or finite-étale assumption.

In particular this applies to an existing Poincaré family. Constructing a
projective frame quotient and proving that it represents rigidified families
remain separate tasks; neither is assumed here.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.GeneralizedJacobian

variable {C S T : Scheme.{u}} {c : C ⟶ S} {t : T ⟶ S} {d : ℕ}

/-- The vector bundle used for the modulus frame construction: restriction
to the whole divisor, followed by its finite pushforward. -/
def modulusSections (D : RelEffCartierDiv c d t) (L : (pullback c t).Modules) :
    T.Modules :=
  (Scheme.Modules.pushforward (D.I.subschemeι ≫ pullback.snd c t)).obj
    ((Scheme.Modules.pullback D.I.subschemeι).obj L)

/-- The restricted family has rank equal to the degree of the full modulus.
This includes arbitrary nonreduced divisors and arbitrary parameter schemes. -/
theorem modulusSections_isLocallyFreeOfRank (D : RelEffCartierDiv c d t)
    (L : (pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsLocallyFreeOfRank d (modulusSections D L) := by
  have : IsFinite (D.I.subschemeι ≫ pullback.snd c t) := D.isFinite
  have : Flat (D.I.subschemeι ≫ pullback.snd c t) := D.flat
  have : LocallyOfFinitePresentation (D.I.subschemeι ≫ pullback.snd c t) :=
    D.locallyOfFinitePresentation
  apply Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
    (D.I.subschemeι ≫ pullback.snd c t) d D.finrank_eq
  intro x
  exact (hL.pullback D.I.subschemeι).exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
    (D.I.subschemeι ≫ pullback.snd c t) x

/-- A chosen rigidification supplies a chosen isomorphism of the restricted
vector bundle with the algebra of functions on the divisor. -/
def modulusSectionsTrivialization (D : RelEffCartierDiv c d t)
    (M : RigidifiedLineBundle D.I.subschemeι) :
    modulusSections D M.L ≅
      (Scheme.Modules.pushforward (D.I.subschemeι ≫ pullback.snd c t)).obj
        (𝟙_ D.I.subscheme.Modules) :=
  (Scheme.Modules.pushforward (D.I.subschemeι ≫ pullback.snd c t)).mapIso M.trivialization

end AlgebraicGeometry.GeneralizedJacobian
