/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProductIntegral
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperComponents
public import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.CartierAdicCycleClass
public import Nyll.EtaleCohomology.Classical.CartierTensorRootVanishing
public import Nyll.EtaleCohomology.Classical.DiagonalDivisorBundle
public import Nyll.EtaleCohomology.Classical.GraphCartierCycleClass
public import Nyll.JacobianVarieties.Kummer.DiagonalDivisionRoot
public import Nyll.SchemeTheory.Modules.Tensor.TensorPowers
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Vanishing of the normalized diagonal class on its division cover

The actual Picard multiplication cover supplies a tensor root of the
normalized diagonal bundle. Properness makes this cover finite. Its
smooth proper source has domain stalks and finitely many components,
so the original finite cohomology decomposes into the original integral
component groups. The tensor root annihilates the original signed cycle
class on every component and hence on the whole original cover.

The cover and root may depend on the finite coefficient level. This
does not assert vanishing of the rational diagonal class, or identify
its middle Künneth component.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory
open EtaleCohomology.Classical

namespace EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyIntegral f] (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K))

/-- At every original finite coefficient level, the actual normalized
diagonal bundle has a tensor root on a finite surjective étale cover,
and its original signed cycle class pulls back to zero on that same
cover. No connectedness of the division cover is required. -/
theorem finiteDiagonalSignedCycleClass_exists_finiteEtale_vanishing (n : ℕ) :
    let _ : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
    let _ : IsIntegral (pullback f f) := isIntegral_pullback_of_smooth_of_isAlgClosed f f
    let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
    let E := diagonalEdgeEffectiveCartierDivisor f p hp
    ∃ (U : Scheme.{u}) (q : U ⟶ pullback f f),
      IsFinite q ∧ Etale q ∧ Surjective q ∧
        ∃ (L : U.Modules), Scheme.Modules.IsInvertible L ∧
          Nonempty ((Scheme.Modules.pullback q).obj (D.1.invModule ⊗ E.1.module) ≅
            L.tensorPow (ℓ ^ (n + 1))) ∧
          finiteLevelCohomologyPullback ℓ q n 2
            (finiteEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ n D -
              finiteEffectiveCartierCycleClass (pullback.snd f f ≫ f) ℓ hℓ n E) = 0 := by
  intro hX hP D E
  obtain ⟨U, q, hfinite, hetale, hsurj, L, hL, ⟨e⟩⟩ :=
    diagonalMiddleBundle_exists_etale_tensorPowRoot f p hp (ℓ ^ (n + 1))
      (by simpa only [Nat.cast_pow] using hℓ.pow (n + 1))
  have : IsFinite q := hfinite
  have : Etale q := hetale
  let cU : U ⟶ Spec (.of K) := q ≫ (pullback.snd f f ≫ f)
  have : Smooth cU := by dsimp only [cU]; infer_instance
  have : IsProper cU := by dsimp only [cU]; infer_instance
  have : IsNoetherian U := smoothProperScheme_isNoetherian cU
  refine ⟨U, q, hfinite, hetale, hsurj, L, hL, ⟨e⟩, ?_⟩
  exact finiteSignedCartierCycleClass_pullback_eq_zero_of_tensorPowIso_components
    (pullback.snd f f ≫ f) ℓ hℓ (smoothSchemeDomainStalks cU) q n D E L hL e

end EtaleCohomology
