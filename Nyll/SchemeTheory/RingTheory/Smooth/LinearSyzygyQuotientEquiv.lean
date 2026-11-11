/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Eliminating the complementary variables in a linear syzygy quotient

A normalized coefficient family with a unit parameter solves every original
variable in terms of the selected variables. Exact cross-coefficient identities
make this substitution kill all families of linear relations. The resulting
quotient equivalence retains the selected variables and the explicit solution.
-/

@[expose] public section

noncomputable section

namespace MvPolynomial

/-- The linear relation associated to one row of a syzygy coefficient system. -/
def linearSyzygyRelation {S m k : Type*} [CommRing S] [Fintype m]
    (A : k → S) (H : k → m → m → S) (s : k) (j : m) : MvPolynomial m S :=
  C (A s) * X j - ∑ l, C (H s j l) * X l

/-- Exact compatible linear syzygies eliminate every complementary variable.
The compatibility here is an explicit coefficient identity; its derivation
for a localized principal lifting algebra is a separate input to this lemma. -/
theorem exists_linearSyzygy_quotient_equiv
    {S m k κ : Type*} [CommRing S] [Fintype m] [DecidableEq m] [Fintype κ]
    (A : k → S) (H : k → m → m → S) (t : k)
    (a : κ → m) (ha : Function.Injective a) (hA : IsUnit (A t))
    (hdiag : ∀ i l, H t (a i) l = if l = a i then A t else 0)
    (hsupport : ∀ j l, l ∉ Set.range a → H t j l = 0)
    (hcross : ∀ s j l, A s * H t j l - ∑ r, H s j r * H t r l = 0) :
    ∃ e : (MvPolynomial m S ⧸
        Ideal.span (Set.range fun p : k × m => linearSyzygyRelation A H p.1 p.2)) ≃ₐ[S]
          MvPolynomial κ S,
      (∀ i, e (Ideal.Quotient.mk _ (X (a i))) = X i) ∧
        ∀ j, e (Ideal.Quotient.mk _ (X j)) =
          C ((hA.unit⁻¹ : Sˣ) : S) * ∑ i, C (H t j (a i)) * X i := by
  classical
  let J := Ideal.span (Set.range fun p : k × m => linearSyzygyRelation A H p.1 p.2)
  let Q := MvPolynomial m S ⧸ J
  let q : MvPolynomial m S →ₐ[S] Q := Ideal.Quotient.mkₐ S J
  let u : Sˣ := hA.unit
  have hu : (u : S) = A t := hA.unit_spec
  have huinv : (↑u⁻¹ : S) * A t = 1 := by
    rw [← hu]
    exact Units.inv_mul u
  let w : m → MvPolynomial κ S := fun j => ∑ i, C (H t j (a i)) * X i
  let v : m → MvPolynomial κ S := fun j => C (↑u⁻¹ : S) * w j
  have hcomb (s : k) (j : m) :
      C (A s) * w j = ∑ l, C (H s j l) * w l := by
    dsimp only [w]
    calc
      _ = ∑ i, C (A s * H t j (a i)) * X i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_mul, mul_assoc]
      _ = ∑ i, C (∑ l, H s j l * H t l (a i)) * X i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [sub_eq_zero.mp (hcross s j (a i))]
      _ = ∑ i, ∑ l, C (H s j l) * (C (H t l (a i)) * X i) := by
        simp only [map_sum, Finset.sum_mul, map_mul, mul_assoc]
      _ = ∑ l, ∑ i, C (H s j l) * (C (H t l (a i)) * X i) :=
        Finset.sum_comm
      _ = _ := by simp only [Finset.mul_sum]
  have hfactor (s : k) (j : m) :
      (∑ l, C (H s j l) * (C (↑u⁻¹ : S) * w l)) =
        C (↑u⁻¹ : S) * ∑ l, C (H s j l) * w l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  let φ : MvPolynomial m S →ₐ[S] MvPolynomial κ S := aeval v
  have hkill (s : k) (j : m) : φ (linearSyzygyRelation A H s j) = 0 := by
    simp only [φ, linearSyzygyRelation, map_sub, map_mul, map_sum, aeval_C, aeval_X]
    change C (A s) * (C (↑u⁻¹ : S) * w j) -
      (∑ l, C (H s j l) * (C (↑u⁻¹ : S) * w l)) = 0
    rw [hfactor, ← hcomb]
    ring
  let F : Q →ₐ[S] MvPolynomial κ S := Ideal.Quotient.liftₐ J φ (by
    change J ≤ RingHom.ker φ.toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨s, j⟩, rfl⟩
    exact hkill s j)
  let G : MvPolynomial κ S →ₐ[S] Q := q.comp (rename a)
  have hF (p : MvPolynomial m S) : F (q p) = φ p := rfl
  have hGX (i : κ) : G (X i) = q (X (a i)) := by
    change q (rename a (X i)) = q (X (a i))
    rw [rename_X]
  have hGC (c : S) : G (C c) = q (C c) := by
    change q (rename a (C c)) = q (C c)
    rw [rename_C]
  have hw (i : κ) : w (a i) = C (A t) * X i := by
    dsimp only [w]
    simp only [hdiag, ha.eq_iff, apply_ite, map_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hv (i : κ) : v (a i) = X i := by
    change C (↑u⁻¹ : S) * w (a i) = X i
    rw [hw, ← mul_assoc, ← map_mul, huinv, map_one, one_mul]
  have hFG : F.comp G = AlgHom.id S (MvPolynomial κ S) := by
    apply algHom_ext
    intro i
    change F (G (X i)) = X i
    rw [hGX, hF]
    exact (aeval_X v (a i)).trans (hv i)
  have hsum (j : m) :
      (∑ l, q (C (H t j l)) * q (X l)) =
        ∑ i, q (C (H t j (a i))) * q (X (a i)) := by
    symm
    apply Fintype.sum_of_injective a ha
    · intro l hl
      rw [hsupport j l hl, map_zero, map_zero, zero_mul]
    · intro i
      rfl
  have hGw (j : m) : G (w j) =
      ∑ i, q (C (H t j (a i))) * q (X (a i)) := by
    dsimp only [w]
    simp only [map_sum, map_mul, hGC, hGX]
  have hchosen (j : m) : q (C (A t)) * q (X j) = G (w j) := by
    have hz : q (linearSyzygyRelation A H t j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨(t, j), rfl⟩)
    rw [linearSyzygyRelation, map_sub, sub_eq_zero, map_mul, map_sum] at hz
    simp only [map_mul] at hz
    rw [hsum, ← hGw] at hz
    exact hz
  have hqinv : q (C (↑u⁻¹ : S)) * q (C (A t)) = 1 := by
    rw [← map_mul, ← map_mul, huinv, map_one, map_one]
  have hGF : G.comp F = AlgHom.id S Q := by
    apply Ideal.Quotient.algHom_ext
    apply algHom_ext
    intro j
    change G (F (q (X j))) = q (X j)
    rw [hF, show φ (X j) = v j from aeval_X v j]
    change G (C (↑u⁻¹ : S) * w j) = q (X j)
    rw [map_mul, hGC, ← hchosen, ← mul_assoc, hqinv, one_mul]
  refine ⟨AlgEquiv.ofAlgHom F G hFG hGF, ?_, ?_⟩
  · intro i
    change F (q (X (a i))) = X i
    rw [hF]
    exact (aeval_X v (a i)).trans (hv i)
  · intro j
    change F (q (X j)) = v j
    rw [hF]
    exact aeval_X v j

end MvPolynomial
