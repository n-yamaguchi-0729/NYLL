/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The actual finite factor at a quasi-finite prime

The quasi-finite local structure theorem supplies an idempotent in an etale
base change. Its away localization has a unique prime over the selected base
prime, contracting to the original source prime. The singleton-fiber proof
is shared by pointwise flat purity and pointwise normal branch purity.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace SchemeTheory

universe u v

/-- Construct the actual finite idempotent factor with its selected prime
and singleton fiber. Consequently its local ring is finite over the selected
base local ring, by `Localization.finite_of_primesOver_eq_singleton`. -/
theorem exists_etale_finite_factor_prime_of_quasiFiniteAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] [Algebra.QuasiFiniteAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (e : R' ⊗[R] S) (_ : IsIdempotentElem e),
      Module.Finite R' (Localization.Away e) ∧
      let : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
      ∃ (Q : Ideal (Localization.Away e)) (_ : Q.IsPrime) (_ : Q.LiesOver P),
        Q.under S = q ∧ P.primesOver (Localization.Away e) = {Q} := by
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', _, hfinite, hunique⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let B := R' ⊗[R] S
  let : Algebra S B := Algebra.TensorProduct.rightAlgebra
  let D := Localization.Away e
  let : Module.Finite R' D := hfinite
  let Q : Ideal D := P'.map (algebraMap B D)
  have hdisj : Disjoint ((Submonoid.powers e : Submonoid B) : Set B) (P' : Set B) := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact heP'
  let : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers e) D P' inferInstance hdisj
  let : Q.LiesOver P' :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (.powers e) D hdisj
  let : Q.LiesOver P := .trans Q P' P
  have hQunder : Q.under B = P' := (Q.over_def P').symm
  have hQq : Q.under S = q := by
    rw [← Ideal.under_under (A := S) (B := B), hQunder]
    exact hP'q
  let : Q.LiesOver q := ⟨hQq.symm⟩
  have hQunique : P.primesOver D = {Q} := by
    ext J
    constructor
    · rintro ⟨hJprime, hJover⟩
      let : J.IsPrime := hJprime
      let : J.LiesOver P := hJover
      let J₀ : Ideal B := J.under B
      let : J₀.LiesOver P := .tower_bot J J₀ P
      have heJ₀ : e ∉ J₀ := by
        intro heJ
        exact hJprime.ne_top (J.eq_top_of_isUnit_mem heJ
          (IsLocalization.map_units D ⟨e, Submonoid.mem_powers e⟩))
      have hJ₀ : J₀ = P' := hunique J₀ inferInstance inferInstance heJ₀
      rw [Set.mem_singleton_iff]
      calc
        J = J₀.map (algebraMap B D) := (IsLocalization.map_under (.powers e) D J).symm
        _ = P'.map (algebraMap B D) := congrArg (Ideal.map (algebraMap B D)) hJ₀
        _ = Q := rfl
    · intro hJ
      rw [Set.mem_singleton_iff] at hJ
      subst J
      exact ⟨inferInstance, inferInstance⟩
  exact ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance,
    inferInstance, e, he, hfinite, Q, inferInstance, inferInstance, hQq, hQunique⟩

end SchemeTheory
