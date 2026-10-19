/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Degree.FiniteTypePoleBound
import Nyll.AlgebraicCurves.Divisors.Degree.UnitriangularRamifiedDescent

/-! # A uniform conductor for an actual unitriangular matrix

The finitely many entries of a rational matrix have a common finite pole bound
`B₀`. Replacing each positive coefficient by `(r - 1) * B₀(v) + 1` gives one
modulus that works for every rational-function parameter and every actual
embedding product which descends. Its support is exactly the union of the
entry pole sets. Embeddings may repeat, so product multiplicities are retained.

This constructs a matrix conductor; it does not assume or assert a faithful
representation of an arbitrary algebraic group.
-/

noncomputable section

universe u

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  [HasPrincipalDivisors K F]

/-- A fixed upper unitriangular matrix has one finite modulus such that every
actual descended embedding product is integral at `1` whenever its rational
parameter is congruent to one. The modulus is independent of the parameter,
the common extension, the repeated embedding list, and the descended matrix. -/
theorem exists_unitriangular_product_conductor {r : ℕ} (hr : 1 < r)
    (A : Matrix (Fin r) (Fin r) F)
    (hA : A.IsUpperTriangular) (hd : ∀ i, A i i = 1) :
    ∃ D : Modulus K F,
      (∀ v : Place K F, D v = 0 ↔ ∀ i j, 0 ≤ v.ord (A i j)) ∧
      ∀ (E : Type u) [Field E] [Algebra K E]
        (ψ : RatFunc K →ₐ[K] F), ψ.toRingHom.IsIntegral →
        ∀ (φ : RatFunc K →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral) (w : Place K E),
          w.restrictAlong φ hφ = RationalFunctionField.placeOfPoint K 1 →
          ∀ (embeddings : List (F →ₐ[K] E)),
            (∀ σ ∈ embeddings, σ.toRingHom.IsIntegral) →
            (∀ σ ∈ embeddings, σ.comp ψ = φ) →
            D.CongruentOne (ψ RatFunc.X) →
            ∀ (B : Matrix (Fin r) (Fin r) (RatFunc K)),
              B.map φ = (embeddings.map (fun σ : F →ₐ[K] E => A.map σ)).prod →
              ∀ i j, B i j ∈ (RationalFunctionField.placeOfPoint K 1).toValuationSubring := by
  classical
  obtain ⟨B₀, hbound, hzero⟩ := exists_finset_pole_bound (K := K)
    (Finset.univ : Finset (Fin r × Fin r)) (fun ij => A ij.1 ij.2)
  let D : Modulus K F := B₀.mapRange
    (fun n : ℕ => if n = 0 then 0 else (r - 1) * n + 1)
    (by exact ite_eq_left rfl)
  have hcoeff (v : Place K F) :
      D v = if B₀ v = 0 then 0 else (r - 1) * B₀ v + 1 := rfl
  have hDzero (v : Place K F) : D v = 0 ↔ B₀ v = 0 := by
    constructor
    · intro h
      by_contra hn
      rw [hcoeff, ite_eq_right hn] at h
      exact Nat.succ_ne_zero _ h
    · intro h
      rw [hcoeff, ite_eq_left h]
  refine ⟨D, ?_, ?_⟩
  · intro v
    rw [hDzero, hzero]
    constructor
    · intro h i j
      exact h (i, j) (Finset.mem_univ _)
    · intro h ij _
      exact h ij.1 ij.2
  · intro E _ _ ψ hψ φ hφ w hw embeddings hEmb hcomp hcong B hdesc i j
    let b : (F →ₐ[K] E) → ℕ := fun σ =>
      if hσ : σ ∈ embeddings then B₀ (w.restrictAlong σ (hEmb σ hσ)) else 0
    have hb (σ : F →ₐ[K] E) (hσ : σ ∈ embeddings) :
        b σ = B₀ (w.restrictAlong σ (hEmb σ hσ)) := by
      simp only [b, dite_eq_left hσ]
    have hmem := w.descended_unitriangular_embedding_product_mem_of_principal_congruence
      ψ hψ φ hφ hw hr A hA hd embeddings hEmb hcomp b
      (by
        intro σ hσ k l
        rw [hb σ hσ]
        exact hbound (w.restrictAlong σ (hEmb σ hσ)) (k, l) (Finset.mem_univ _))
      D hcong
      (by
        intro σ hσ hn
        rw [hb σ hσ] at hn ⊢
        rw [hcoeff, ite_eq_right hn])
      B hdesc i j
    simpa only [hw] using hmem

end AlgebraicCurve
