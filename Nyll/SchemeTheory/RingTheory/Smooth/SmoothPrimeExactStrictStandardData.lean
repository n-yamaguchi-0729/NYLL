/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.SmoothPrimeStrictStandardData
public import Nyll.SchemeTheory.RingTheory.Smooth.ConormalRelationLocalization

/-!
# Exact original strictly-standard data at a smooth prime

Apply local Nakayama to the original relation ideal at the inverse image
of the given smooth prime. Finite generation supplies one denominator
which removes the square of that ideal from every relation membership.
Multiplying the old parameter by this denominator preserves its Jacobian
minor membership and keeps its image outside the given prime.
-/

@[expose] public section

noncomputable section

universe u v w t

namespace Algebra

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- A strictly-standard parameter outside an ideal forces the selected
original relation indices to be distinct. Otherwise every maximal minor
has two equal rows, so the parameter belongs to the presentation kernel. -/
theorem Presentation.injective_selection_of_strictStandard_minor_notMem
    {ι : Type w} {σ : Type t} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (P : Presentation R B ι σ) (p : Ideal B) (a : κ → σ) (q : P.Ring)
    (hq : algebraMap P.Ring B q ∉ p)
    (hminor : q ∈ P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
      ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
        _root_.id c).det))) :
    Function.Injective a := by
  classical
  intro i j hij
  by_contra hne
  have hminors : Ideal.span (Set.range (fun c : κ → ι =>
      ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
        _root_.id c).det)) ≤ P.ker := by
    apply Ideal.span_le.mpr
    rintro _ ⟨c, rfl⟩
    have hzero : ((Matrix.of fun j i =>
        MvPolynomial.pderiv i (P.relation (a j))).submatrix _root_.id c).det = 0 := by
      apply Matrix.det_zero_of_row_eq hne
      funext k
      change MvPolynomial.pderiv (c k) (P.relation (a i)) =
        MvPolynomial.pderiv (c k) (P.relation (a j))
      rw [hij]
    change ((Matrix.of fun j i =>
      MvPolynomial.pderiv i (P.relation (a j))).submatrix _root_.id c).det ∈ P.ker
    rw [hzero]
    exact P.ker.zero_mem
  have hqker : q ∈ P.ker := (sup_le le_rfl hminors) hminor
  have hqzero : algebraMap P.Ring B q = 0 := hqker
  apply hq
  rw [hqzero]
  exact p.zero_mem

/-- A smooth prime admits actual original strictly-standard data whose
parameter multiplies every original relation into the selected relation
ideal itself. There is no squared-ideal remainder and no Noetherian
hypothesis on either ring. -/
theorem Presentation.exists_strictStandard_exact_data_at_smoothPrime
    {ι : Type w} {σ : Type t} [Finite ι] [Finite σ] (P : Presentation R B ι σ)
    (p : Ideal B) [p.IsPrime] [IsSmoothAt R p] :
    ∃ (κ : Type t) (_ : Fintype κ) (_ : DecidableEq κ) (a : κ → σ) (d : P.Ring),
      algebraMap P.Ring B d ∉ p ∧
      d ∈ P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
        ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
          _root_.id c).det)) ∧
      ∀ j, d * P.relation j ∈
        Ideal.span (Set.range (fun i => P.relation (a i))) := by
  obtain ⟨κ, hκ, hκdec, a, q, hq, hminor, hrelations⟩ :=
    P.exists_strictStandard_data_at_smoothPrime p
  let _ : Fintype κ := hκ
  let _ : DecidableEq κ := hκdec
  let J : Ideal P.Ring := Ideal.span (Set.range fun i => P.relation (a i))
  let p' : Ideal P.Ring := p.comap (algebraMap P.Ring B)
  have : p'.IsPrime := Ideal.comap_isPrime (algebraMap P.Ring B) p
  have hIp : P.ker ≤ p' := by
    intro x hx
    change algebraMap P.Ring B x ∈ p
    have hx' : algebraMap P.Ring B x = 0 := hx
    rw [hx']
    exact p.zero_mem
  have hrel : ∀ x ∈ P.ker, q * x ∈ J ⊔ P.ker ^ 2 := by
    have hle : P.ker ≤ Submodule.comap (LinearMap.mulLeft P.Ring q)
        (J ⊔ P.ker ^ 2 : Submodule P.Ring P.Ring) := by
      conv_lhs => rw [← P.span_range_relation_eq_ker]
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hrelations j
    intro x hx
    exact hle hx
  obtain ⟨r, hr, hrexact⟩ := Ideal.exists_notMem_mul_mem_of_conormal_generators
    P.ker J p' P.fg_ker hIp q hq hrel
  change algebraMap P.Ring B r ∉ p at hr
  refine ⟨κ, hκ, hκdec, a, r * q, ?_, ?_, fun j => ?_⟩
  · rw [map_mul]
    exact p.primeCompl.mul_mem hr hq
  · exact (P.ker ⊔ Ideal.span (Set.range (fun c : κ → ι =>
      ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
        _root_.id c).det))).mul_mem_left r hminor
  · have hj := J.mul_mem_left q (hrexact (P.relation j) (P.relation_mem_ker j))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hj

end Algebra
