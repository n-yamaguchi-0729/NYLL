/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.Adic
public import Nyll.EtaleCohomology.Classical.AdicCup
public import Nyll.EtaleCohomology.Classical.CupH0Centrality
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.RationalAdic
public import Nyll.EtaleCohomology.Classical.RationalAdicCup
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Original adic degree-zero classes are central on arbitrary schemes

Native degree-zero Ext centrality passes through the original finite
coefficient comparisons, the original compatible families, and the
original rational scalar extension. These statements require no
connectedness assumption on the original scheme.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open scoped TensorProduct

namespace EtaleCohomology.Classical

variable (X : Scheme.{u}) (ℓ : ℕ)

/-- Degree-zero classes commute with the actual original finite cup
in every degree, on arbitrary schemes and at every finite level. -/
theorem finiteLevelCup_comm_zero_left (n i : ℕ)
    (x : finiteLevelCohomology X ℓ n 0) (y : finiteLevelCohomology X ℓ n i) :
    finiteLevelCup X ℓ n 0 i i (zero_add i) x y =
      finiteLevelCup X ℓ n i 0 i (add_zero i) y x := by
  rw [finiteLevelCup_apply, finiteLevelCup_apply, etaleCohomologyCup_comm_zero_left]

variable [Fact ℓ.Prime]

/-- Degree-zero classes commute with the actual original integral
adic cup on arbitrary schemes. -/
theorem ellAdicCup_comm_zero_left (i : ℕ)
    (x : ellAdicCohomology X ℓ 0) (y : ellAdicCohomology X ℓ i) :
    ellAdicCup X ℓ 0 i i (zero_add i) x y =
      ellAdicCup X ℓ i 0 i (add_zero i) y x := by
  apply ellAdicCohomology_ext X ℓ i
  intro n
  exact finiteLevelCup_comm_zero_left X ℓ n i (x.val n) (y.val n)

/-- Degree-zero classes commute with the actual original rational
adic cup on arbitrary schemes. -/
theorem rationalEllAdicCup_comm_zero_left (i : ℕ)
    (x : rationalEllAdicCohomology ℓ X 0) (y : rationalEllAdicCohomology ℓ X i) :
    rationalEllAdicCup X ℓ 0 i i (zero_add i) x y =
      rationalEllAdicCup X ℓ i 0 i (add_zero i) y x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
      induction y using TensorProduct.inductionOn with
      | tmul s y =>
          rw [rationalEllAdicCup_tmul, rationalEllAdicCup_tmul,
            ellAdicCup_comm_zero_left, mul_comm r s]
      | add y y' hy hy' =>
          let F : rationalEllAdicCohomology ℓ X i →ₗ[ℚ_[ℓ]]
              rationalEllAdicCohomology ℓ X i :=
            rationalEllAdicCup X ℓ 0 i i (zero_add i) (r ⊗ₜ[ℤ_[ℓ]] x)
          let G : rationalEllAdicCohomology ℓ X i →ₗ[ℚ_[ℓ]]
              rationalEllAdicCohomology ℓ X i :=
            (rationalEllAdicCup X ℓ i 0 i (add_zero i)).flip (r ⊗ₜ[ℤ_[ℓ]] x)
          exact (F.map_add y y').trans
            ((congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X i => u + v)
              hy hy').trans (G.map_add y y').symm)
  | add x x' hx hx' =>
      let F : rationalEllAdicCohomology ℓ X 0 →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X i :=
        (rationalEllAdicCup X ℓ 0 i i (zero_add i)).flip y
      let G : rationalEllAdicCohomology ℓ X 0 →ₗ[ℚ_[ℓ]]
          rationalEllAdicCohomology ℓ X i :=
        rationalEllAdicCup X ℓ i 0 i (add_zero i) y
      exact (F.map_add x x').trans
        ((congrArg₂ (fun u v : rationalEllAdicCohomology ℓ X i => u + v)
          hx hx').trans (G.map_add x x').symm)

end EtaleCohomology.Classical
