/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicPullback
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1IsomorphismPullback
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Actual adic H¹ pullback along a scheme isomorphism

The original finite-coefficient pullback equivalences prove that pullback on
the existing compatible families is invertible. Its inverse remains pullback
along the original inverse scheme morphism. Rationalization uses the same
tensor product as classical rational adic cohomology.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {X Y : Scheme} [ConnectedSpace X] [ConnectedSpace Y]
  (e : X ≅ Y) {Ω : Type} [Field Ω] [IsSepClosed Ω]
  (geom : Spec (.of Ω) ⟶ X)

/-- The actual integral H¹ pullback is an equivalence with inverse the
actual inverse-morphism pullback on the original compatible families. -/
def ellAdicH1PullbackEquiv :
    ellAdicCohomology Y ℓ 1 ≃ₗ[ℤ_[ℓ]] ellAdicCohomology X ℓ 1 := by
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  exact
    { ellAdicCohomologyPullback ℓ e.hom 1 with
      invFun := ellAdicCohomologyPullback ℓ e.inv 1
      left_inv a := ellAdicCohomology_ext Y ℓ 1 fun n =>
        (constantFiniteH1PullbackEquiv e geom
          (ellPowerCoefficients ℓ n)).symm_apply_apply (a.val n)
      right_inv a := ellAdicCohomology_ext X ℓ 1 fun n =>
        (constantFiniteH1PullbackEquiv e geom
          (ellPowerCoefficients ℓ n)).apply_symm_apply (a.val n) }

/-- The equivalence retains the original integral pullback map. -/
theorem ellAdicH1PullbackEquiv_apply (a : ellAdicCohomology Y ℓ 1) :
    ellAdicH1PullbackEquiv ℓ e geom a = ellAdicCohomologyPullback ℓ e.hom 1 a := rfl

/-- Its inverse retains pullback by the original inverse morphism. -/
theorem ellAdicH1PullbackEquiv_symm_apply (a : ellAdicCohomology X ℓ 1) :
    (ellAdicH1PullbackEquiv ℓ e geom).symm a =
      ellAdicCohomologyPullback ℓ e.inv 1 a := rfl

/-- Rational H¹ transport is scalar extension of the same actual integral
pullback equivalence. -/
def rationalEllAdicH1PullbackEquiv :
    rationalEllAdicCohomology ℓ Y 1 ≃ₗ[ℚ_[ℓ]] rationalEllAdicCohomology ℓ X 1 :=
  (ellAdicH1PullbackEquiv ℓ e geom).baseChange ℤ_[ℓ] ℚ_[ℓ]
    (ellAdicCohomology Y ℓ 1) (ellAdicCohomology X ℓ 1)

end EtaleFundamentalGroups.Cohomology
