/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.PrincipalCompletionSmoothFactorization
public import Nyll.SchemeTheory.RingTheory.Henselian.AlgHomLiftIsSmoothAt

/-!
# Henselian approximation from original strictly-standard data

For a principal completion, the correction construction produces its own
smooth stage. Henselian lifting then returns a map from the original
polynomial quotient to the original ring, preserving the actual closed
point of the specified completed solution.
-/

@[expose] public section

noncomputable section

universe u

namespace HenselianLocalRing

open MvPolynomial IsLocalRing

/-- A completed solution with original strictly-standard presentation data
has a solution over the original henselian ring with the same closed point.
The smooth intermediate algebra and the approximate section are constructed. -/
theorem exists_principal_completion_approximation_of_strictStandard_data
    {R m n k : Type u} [CommRing R] [HenselianLocalRing R] [IsNoetherianRing R]
    [Fintype m] [Finite n] [DecidableEq m]
    (π : R) (f : m → MvPolynomial n R) (h : k → MvPolynomial n R)
    (hminor : C π ∈
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ⊔
        Ideal.span (Set.range fun c : m → n =>
          ((Matrix.of fun j i => pderiv i (f j)).submatrix _root_.id c).det))
    (hrelations : ∀ j, C π * h j ∈ Ideal.span (Set.range f) ⊔
      (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h)) ^ 2)
    (hπ : π ∈ maximalIdeal R)
    (φ : (MvPolynomial n R ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R]
      AdicCompletion (Ideal.span {π}) R) :
    ∃ ψ : (MvPolynomial n R ⧸
        (Ideal.span (Set.range f) ⊔ Ideal.span (Set.range h))) →ₐ[R] R,
      ∀ x, algebraMap R (ResidueField R) (ψ x) =
        Ideal.Quotient.factorₐ R ((maximalIdeal R).span_singleton_le_iff_mem.mpr hπ)
          (AdicCompletion.evalOneₐ (Ideal.span {π}) (φ x)) := by
  obtain ⟨D, _, _, hD, α, β, hβα⟩ :=
    Algebra.exists_smooth_factorization_principalCompletion_of_strictStandard_data
      π f h hminor hrelations hπ φ
  have : Algebra.Smooth R D := hD
  let κ : D →ₐ[R] ResidueField R :=
    ((Ideal.Quotient.factorₐ R ((maximalIdeal R).span_singleton_le_iff_mem.mpr hπ)).comp
      (AdicCompletion.evalOneₐ (Ideal.span {π}))).comp β
  have : (RingHom.ker κ).IsPrime := RingHom.ker_isPrime κ
  obtain ⟨δ, hδ⟩ := exists_algHom_lift_of_isSmoothAt D κ
  refine ⟨δ.comp α, fun x => ?_⟩
  change algebraMap R (ResidueField R) (δ (α x)) = _
  rw [hδ]
  change Ideal.Quotient.factorₐ R
    ((maximalIdeal R).span_singleton_le_iff_mem.mpr hπ)
    (AdicCompletion.evalOneₐ (Ideal.span {π}) (β (α x))) = _
  rw [show β (α x) = φ x from AlgHom.congr_fun hβα x]

end HenselianLocalRing
