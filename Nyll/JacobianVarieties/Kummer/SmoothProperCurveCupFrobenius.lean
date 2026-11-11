/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.AdicCupPullback
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FiniteLevelCupPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Nyll.EtaleCohomology.Frobenius.RationalAdic
public import Nyll.JacobianVarieties.Kummer.SmoothProperCurveH2Frobenius
public import Nyll.SchemeTheory.Morphisms.FrobeniusBaseChange
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius similitude of the original curve cup products

The original pullback preserves cup. Its proved action on the original
H² is multiplication by the finite-field cardinality. Together these
give the actual degree-two cup similitude, including the middle pairing
H¹ × H¹, on the literal geometric base change. Every rational Frobenius
power has the corresponding multiplier. No perfectness or alternating
property of the middle pairing is assumed or asserted here.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology.Classical

namespace EtaleCohomology

variable (k K : Type u) [Field k] [Fintype k] [Field K] [IsAlgClosed K]
  [Algebra k K] [Algebra.IsAlgebraic k K]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
  [IsProper (X ↘ Spec (CommRingCat.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k))]
  [GeometricallyConnected (X ↘ Spec (CommRingCat.of k))]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

local notation "XK" => pullback (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))

include hℓ

/-- Original finite coefficient cup in total degree two is a
similitude for the actual geometric Frobenius, with multiplier q. -/
theorem finiteLevelCup_geometricFrobenius (n i j : ℕ) (h : i + j = 2)
    (x : finiteLevelCohomology XK ℓ n i) (y : finiteLevelCohomology XK ℓ n j) :
    finiteLevelCup XK ℓ n i j 2 h
        (finiteLevelCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) n i x)
        (finiteLevelCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) n j y) =
      (Fintype.card k) • finiteLevelCup XK ℓ n i j 2 h x y := by
  rw [← finiteLevelCohomologyPullback_cup]
  exact finiteLevelH2_geometricFrobenius k K X ℓ hℓ n
    (finiteLevelCup XK ℓ n i j 2 h x y)

/-- The same actual cup similitude holds on the original integral
inverse limits, with no replacement of the original cohomology. -/
theorem ellAdicCup_geometricFrobenius (i j : ℕ) (h : i + j = 2)
    (x : ellAdicCohomology XK ℓ i) (y : ellAdicCohomology XK ℓ j) :
    ellAdicCup XK ℓ i j 2 h
        (finiteFieldFrobeniusEllAdicCohomology k K X ℓ i x)
        (finiteFieldFrobeniusEllAdicCohomology k K X ℓ j y) =
      (Fintype.card k) • ellAdicCup XK ℓ i j 2 h x y := by
  change ellAdicCup XK ℓ i j 2 h
    (ellAdicCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) i x)
    (ellAdicCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) j y) = _
  rw [← ellAdicCohomologyPullback_cup]
  exact ellAdicH2_geometricFrobenius_apply k K X ℓ hℓ
    (ellAdicCup XK ℓ i j 2 h x y)

/-- The original rational cup in total degree two has Frobenius
multiplier q, in particular for the original H¹ × H¹ pairing. -/
theorem rationalEllAdicCup_geometricFrobenius (i j : ℕ) (h : i + j = 2)
    (x : rationalEllAdicCohomology ℓ XK i) (y : rationalEllAdicCohomology ℓ XK j) :
    rationalEllAdicCup XK ℓ i j 2 h
        (finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ i x)
        (finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ j y) =
      (Fintype.card k) • rationalEllAdicCup XK ℓ i j 2 h x y := by
  change rationalEllAdicCup XK ℓ i j 2 h
    (rationalEllAdicCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) i x)
    (rationalEllAdicCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) j y) = _
  rw [← rationalEllAdicCohomologyPullback_cup]
  exact rationalEllAdicH2_geometricFrobenius_apply k K X ℓ hℓ
    (rationalEllAdicCup XK ℓ i j 2 h x y)

/-- Every original rational Frobenius power preserves the actual
degree-two cup with multiplier q^m, on the literal geometric base change. -/
theorem rationalEllAdicCup_geometricFrobenius_pow
    (i j : ℕ) (h : i + j = 2) (m : ℕ)
    (x : rationalEllAdicCohomology ℓ XK i) (y : rationalEllAdicCohomology ℓ XK j) :
    rationalEllAdicCup XK ℓ i j 2 h
        (((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ i) ^ m) x)
        (((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ j) ^ m) y) =
      (Fintype.card k ^ m) • rationalEllAdicCup XK ℓ i j 2 h x y := by
  have hc :
      rationalEllAdicCup XK ℓ i j 2 h
          (((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ i) ^ m) x)
          (((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ j) ^ m) y) =
        ((finiteFieldFrobeniusRationalEllAdicCohomology k K X ℓ 2) ^ m)
          (rationalEllAdicCup XK ℓ i j 2 h x y) := by
    change rationalEllAdicCup XK ℓ i j 2 h
      (((rationalEllAdicCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) i) ^ m) x)
      (((rationalEllAdicCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) j) ^ m) y) =
      ((rationalEllAdicCohomologyPullback ℓ (Scheme.constantBaseChangeFrobenius k K X) 2) ^ m)
        (rationalEllAdicCup XK ℓ i j 2 h x y)
    rw [rationalEllAdicCohomologyPullback_pow, rationalEllAdicCohomologyPullback_pow,
      rationalEllAdicCohomologyPullback_pow]
    exact (rationalEllAdicCohomologyPullback_cup ℓ
      ((End.of (Scheme.constantBaseChangeFrobenius k K X)) ^ m).asHom i j 2 h x y).symm
  rw [hc]
  exact LinearMap.congr_fun (rationalEllAdicH2_geometricFrobenius_pow k K X ℓ hℓ m)
    (rationalEllAdicCup XK ℓ i j 2 h x y)

end EtaleCohomology
