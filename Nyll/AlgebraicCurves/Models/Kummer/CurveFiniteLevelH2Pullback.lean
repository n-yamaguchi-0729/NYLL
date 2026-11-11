/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Kummer.CurveFiniteLevelH2
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.FiniteLevelKummerKernelPullback
public import Nyll.EtaleCohomology.Classical.KummerH2Functoriality
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Pullback for the original finite H² of curves

The actual finite coefficient H² comparison with native H¹(Gm) modulo
the exponent is natural for scheme morphisms between smooth proper
integral curves over the same algebraically closed field. The maps are
the existing coefficient pullbacks and the original pullbacks on units.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open EtaleCohomology EtaleCohomology.Classical

namespace AlgebraicCurve

variable (K : Type u) [Field K] [IsAlgClosed K]
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) (c : Y ⟶ Spec (.of K))
  [SmoothOfRelativeDimension 1 c] [IsProper c]
  [SmoothOfRelativeDimension 1 (f ≫ c)] [IsProper (f ≫ c)]
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- The original finite pullback sends the native Kummer boundary of
a quotient class to the boundary of its original H¹(Gm) pullback. -/
theorem smoothProperCurveFiniteLevelH2EquivH1Quotient_symm_pullback (n : ℕ)
    (a : Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1 ⧸
      (nsmulAddMonoidHom (α := Sheaf.H.{u} (etaleMultiplicativeGroupSheaf Y) 1)
        (ℓ ^ (n + 1))).range) :
    finiteLevelCohomologyPullback ℓ f n 2
        ((smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ n).symm a) =
      (smoothProperCurveFiniteLevelH2EquivH1Quotient K (f ≫ c) ℓ hℓ n).symm
        (etaleKummerH1QuotientPullback f (ℓ ^ (n + 1)) a) :=
  congrArg Subtype.val
    (finiteLevelKummerH1QuotientEquivH2Kernel_pullback f c ℓ hℓ n a)

/-- The actual finite H² comparison commutes with the original finite
coefficient pullback and the original native H¹(Gm) quotient pullback. -/
theorem smoothProperCurveFiniteLevelH2EquivH1Quotient_pullback (n : ℕ)
    (a : finiteLevelCohomology Y ℓ n 2) :
    smoothProperCurveFiniteLevelH2EquivH1Quotient K (f ≫ c) ℓ hℓ n
        (finiteLevelCohomologyPullback ℓ f n 2 a) =
      etaleKummerH1QuotientPullback f (ℓ ^ (n + 1))
        (smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ n a) := by
  apply (smoothProperCurveFiniteLevelH2EquivH1Quotient K (f ≫ c) ℓ hℓ n).symm.injective
  rw [AddEquiv.symm_apply_apply]
  simpa only [AddEquiv.symm_apply_apply] using
    smoothProperCurveFiniteLevelH2EquivH1Quotient_symm_pullback K f c ℓ hℓ n
      (smoothProperCurveFiniteLevelH2EquivH1Quotient K c ℓ hℓ n a)

end AlgebraicCurve
