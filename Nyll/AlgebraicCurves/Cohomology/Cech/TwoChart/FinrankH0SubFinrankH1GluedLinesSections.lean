/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_finrank_H0_sub_finrank_H1_gluedLinesSections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Algebra.Subalgebra.Prod
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.SplitIfs
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.GluedLines
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.FinrankH0GluedLinesSectionsEqOneSubsingletonH1
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChart.FinrankH0GluedLinesSections

/-!
# Two Chart Cech finrank H0 sub finrank H1 glued Lines Sections
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartFinrankH0SubFinrankH1


open _root_.TwoChartCech
open _root_.LaurentPolynomial
open GluedLinesH0OneH1Zero.TwoChartCech.GluedLinesMain
open GluedLinesH0NegativeTwist.GLH0Neg (levalUnit_toLaurent)


universe u v

namespace TwoChartCech

export _root_.TwoChartCech (levalUnit polyPart invPolyPart mem_invPolyPart_iff GluedCond
  gluedLinesM01 gluedLinesM0 gluedLinesM1 gluedLinesSections Sections Sections.cechDiff_apply
  finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1)


open _root_.TwoChartCech

namespace GluedLinesMain

variable {k : Type u} [Field k] {s : ℕ}

theorem T_eq_single (j : ℤ) : (T j : k[T;T⁻¹]) = AddMonoidAlgebra.single j 1 := rfl

end GluedLinesMain
end TwoChartCech

namespace TwoChartCech

export _root_.TwoChartCech (levalUnit polyPart invPolyPart mem_invPolyPart_iff GluedCond
  gluedLinesM01 gluedLinesM0 gluedLinesM1 gluedLinesSections Sections Sections.cechDiff_apply
  finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1)


open _root_.TwoChartCech

namespace ChiStep

open Module Submodule

variable {k : Type u} [Field k] {F : Type v} [AddCommGroup F] [Module k F]
variable (A B B' W : Submodule k F)

/-- The quotient of the larger submodule by the intersection with the smaller submodule. -/
abbrev Q : Type v := ↥B' ⧸ (B.comap B'.subtype)

/-- Include the intersection into the larger submodule and pass to its quotient. -/
def ψ : ↥(A ⊓ B') →ₗ[k] Q B B' := (mkQ _).comp (Submodule.inclusion inf_le_right)

/-- The map on submodule quotients induced by inclusion into the ambient submodule. -/
def φbar (hB'W : B' ≤ W) : Q B B' →ₗ[k] ↥W ⧸ ((A ⊔ B).comap W.subtype) :=
  (B.comap B'.subtype).liftQ ((mkQ _).comp (Submodule.inclusion hB'W)) (by
    intro v hv
    rw [LinearMap.mem_ker, LinearMap.comp_apply, mkQ_apply, Quotient.mk_eq_zero, mem_comap]
    exact mem_sup_right hv)

/-- The quotient map induced by enlarging the second submodule. -/
def π (hBB' : B ≤ B') : (↥W ⧸ ((A ⊔ B).comap W.subtype)) →ₗ[k] ↥W ⧸ ((A ⊔ B').comap W.subtype) :=
  Submodule.factor (comap_mono (sup_le_sup_left hBB' A))

theorem ker_ψ : LinearMap.ker (ψ A B B') = (A ⊓ B).comap (A ⊓ B').subtype := by
  ext v
  simp only [ψ, LinearMap.mem_ker, LinearMap.comp_apply, mkQ_apply, Quotient.mk_eq_zero, mem_comap,
    Submodule.subtype_apply, Submodule.coe_inclusion, mem_inf]
  exact ⟨fun h => ⟨v.2.1, h⟩, fun h => h.2⟩

theorem range_ψ_eq_ker_φbar (hBB' : B ≤ B') (hB'W : B' ≤ W) :
    LinearMap.range (ψ A B B') = LinearMap.ker (φbar A B B' W hB'W) := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | _ v =>
    simp only [LinearMap.mem_range, LinearMap.mem_ker, φbar, liftQ_apply, LinearMap.comp_apply,
      mkQ_apply,
      Quotient.mk_eq_zero, mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion]
    constructor
    · rintro ⟨w, hw⟩
      have hvw : (v : F) - w ∈ B := by
        have := (Submodule.Quotient.eq _).mp hw.symm
        exact Submodule.mem_comap.mp this
      have : (v : F) = w + ((v : F) - w) := by abel
      rw [this]
      exact add_mem (mem_sup_left w.2.1) (mem_sup_right hvw)
    · intro hv
      obtain ⟨a, ha, b, hb, hab⟩ := mem_sup.mp hv
      have haB' : a ∈ B' := by
        have : a = (v : F) - b := by rw [← hab]; abel
        rw [this]; exact sub_mem v.2 (hBB' hb)
      refine ⟨⟨a, ha, haB'⟩, ?_⟩
      simp only [ψ, LinearMap.comp_apply, mkQ_apply]
      apply (Submodule.Quotient.eq _).mpr
      simp only [mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
      have : a - (v : F) = -b := by rw [← hab]; abel
      rw [this]; exact neg_mem hb

theorem range_φbar_eq_ker_π (hBB' : B ≤ B') (hB'W : B' ≤ W) :
    LinearMap.range (φbar A B B' W hB'W) = LinearMap.ker (π A B B' W hBB') := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | _ w =>
    simp only [LinearMap.mem_range, LinearMap.mem_ker, π, Submodule.factor, mapQ_apply,
      LinearMap.id_apply,
      Quotient.mk_eq_zero, mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨q, hq⟩
      induction q using Submodule.Quotient.induction_on with
      | _ v =>
        simp only [φbar, liftQ_apply, LinearMap.comp_apply, mkQ_apply] at hq
        have hvw : (v : F) - w ∈ A ⊔ B := by
          have := (Submodule.Quotient.eq _).mp hq
          exact Submodule.mem_comap.mp this
        have : (w : F) = v - ((v : F) - w) := by abel
        rw [this]
        exact sub_mem (mem_sup_right v.2) (sup_le_sup_left hBB' A hvw)
    · intro hw
      obtain ⟨a, ha, b, hb, hab⟩ := mem_sup.mp hw
      refine ⟨Submodule.Quotient.mk ⟨b, hb⟩, ?_⟩
      simp only [φbar, liftQ_apply, LinearMap.comp_apply, mkQ_apply]
      apply (Submodule.Quotient.eq _).mpr
      simp only [mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
      have : b - (w : F) = -a := by rw [← hab]; abel
      rw [this]; exact neg_mem (mem_sup_left ha)

theorem finite_forward (hBB' : B ≤ B') (hcodim : Module.finrank k (Q B B') = 1)
    [Module.Finite k ↥(A ⊓ B)] [Module.Finite k (↥W ⧸ ((A ⊔ B).comap W.subtype))] :
    Module.Finite k ↥(A ⊓ B') ∧ Module.Finite k (↥W ⧸ ((A ⊔ B').comap W.subtype)) := by
  have : Module.Finite k (Q B B') := Module.finite_of_finrank_eq_succ hcodim
  have hfinK : Module.Finite k ↥(LinearMap.ker (ψ A B B')) := by
    rw [ker_ψ]
    exact Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (inf_le_inf_left A hBB')).symm
  have : Module.Finite k (↥(A ⊓ B') ⧸ LinearMap.ker (ψ A B B')) :=
    Module.Finite.equiv (LinearMap.quotKerEquivRange (ψ A B B')).symm
  exact ⟨Module.Finite.of_submodule_quotient (LinearMap.ker (ψ A B B')),
    Module.Finite.of_surjective (π A B B' W hBB') (Submodule.factor_surjective (comap_mono
      (sup_le_sup_left hBB' A)))⟩

theorem finite_backward (hBB' : B ≤ B') (hB'W : B' ≤ W) (hcodim : Module.finrank k (Q B B') = 1)
    [Module.Finite k ↥(A ⊓ B')] [Module.Finite k (↥W ⧸ ((A ⊔ B').comap W.subtype))] :
    Module.Finite k ↥(A ⊓ B) ∧ Module.Finite k (↥W ⧸ ((A ⊔ B).comap W.subtype)) := by
  have : Module.Finite k (Q B B') := Module.finite_of_finrank_eq_succ hcodim
  refine ⟨Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (inf_le_inf_left A hBB'))
      (M := ↥((A ⊓ B).comap (A ⊓ B').subtype)), ?_⟩
  have hker : Module.Finite k ↥(LinearMap.ker (π A B B' W hBB')) := by
    rw [← range_φbar_eq_ker_π A B B' W hBB' hB'W]
    exact Module.Finite.range (φbar A B B' W hB'W)
  have : Module.Finite k ((↥W ⧸ ((A ⊔ B).comap W.subtype)) ⧸ LinearMap.ker (π A B B' W hBB')) :=
    Module.Finite.equiv
      (LinearMap.quotKerEquivOfSurjective (π A B B' W hBB')
        (Submodule.factor_surjective (comap_mono (sup_le_sup_left hBB' A)))).symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker (π A B B' W hBB'))

theorem finrank_step (hBB' : B ≤ B') (hB'W : B' ≤ W) (hcodim : Module.finrank k (Q B B') = 1)
    [Module.Finite k ↥(A ⊓ B)] [Module.Finite k (↥W ⧸ ((A ⊔ B).comap W.subtype))]
    [Module.Finite k ↥(A ⊓ B')] [Module.Finite k (↥W ⧸ ((A ⊔ B').comap W.subtype))] :
    (Module.finrank k ↥(A ⊓ B') : ℤ) - Module.finrank k (↥W ⧸ ((A ⊔ B').comap W.subtype)) =
      (Module.finrank k ↥(A ⊓ B) : ℤ) - Module.finrank k (↥W ⧸ ((A ⊔ B).comap W.subtype)) + 1 := by
  have : Module.Finite k (Q B B') := Module.finite_of_finrank_eq_succ hcodim
  have h1 := LinearMap.finrank_range_add_finrank_ker (ψ A B B')
  have h2 := LinearMap.finrank_range_add_finrank_ker (φbar A B B' W hB'W)
  have h3 := LinearMap.finrank_range_add_finrank_ker (π A B B' W hBB')
  rw [hcodim] at h2
  have hkψ : Module.finrank k ↥(LinearMap.ker (ψ A B B')) = Module.finrank k ↥(A ⊓ B) := by
    rw [ker_ψ]; exact (Submodule.comapSubtypeEquivOfLe (inf_le_inf_left A hBB')).finrank_eq
  have hrψ : Module.finrank k ↥(LinearMap.range (ψ A B B')) = Module.finrank k ↥(LinearMap.ker
    (φbar A B B' W hB'W)) := by
    rw [range_ψ_eq_ker_φbar A B B' W hBB' hB'W]
  have hrφ : Module.finrank k ↥(LinearMap.range (φbar A B B' W hB'W)) =
      Module.finrank k ↥(LinearMap.ker (π A B B' W hBB')) := by
    rw [range_φbar_eq_ker_π A B B' W hBB' hB'W]
  have hrπ : Module.finrank k ↥(LinearMap.range (π A B B' W hBB')) =
      Module.finrank k (↥W ⧸ ((A ⊔ B').comap W.subtype)) := by
    have hsurj : Function.Surjective (π A B B' W hBB') := Submodule.factor_surjective (comap_mono
      (sup_le_sup_left hBB' A))
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
  omega

end ChiStep
end TwoChartCech

noncomputable section

namespace TwoChartCech

export _root_.TwoChartCech (levalUnit polyPart invPolyPart mem_invPolyPart_iff GluedCond
  gluedLinesM01 gluedLinesM0 gluedLinesM1 gluedLinesSections Sections Sections.cechDiff_apply
  finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1)


open _root_.TwoChartCech

namespace GluedLinesChi

open Module Submodule

variable {k : Type u} [Field k] {s : ℕ} (a b lam : Fin s → kˣ)

/-- The ambient space of pairs of Laurent polynomials. -/
abbrev Amb (k : Type u) [Field k] : Type u := k[T;T⁻¹] × k[T;T⁻¹]

/-- First-chart sections viewed as a subspace of the ambient Laurent-polynomial pairs. -/
def Asub : Submodule k (Amb k) := (gluedLinesM0 k a b lam).restrictScalars k

/-- Second-chart sections with the specified twists, viewed as a subspace of the ambient pairs. -/
def Bsub (n m : ℤ) : Submodule k (Amb k) := (gluedLinesM1 k a b lam n m).restrictScalars k

/-- Overlap sections viewed as a subspace of the ambient pairs. -/
def Wsub : Submodule k (Amb k) := (gluedLinesM01 k a b lam).restrictScalars k

theorem A_le_W : Asub a b lam ≤ Wsub a b lam := fun _ hv => hv.1
theorem B_le_W (n m : ℤ) : Bsub a b lam n m ≤ Wsub a b lam := fun _ hv => hv.1

theorem mul_T_mem_invPolyPart_mono {f : k[T;T⁻¹]} {j j' : ℤ} (hj : j' ≤ j) (h : f * T j ∈
  invPolyPart k) :
    f * T j' ∈ invPolyPart k := by
  rw [mul_T_mem_invPolyPart_iff] at h ⊢
  intro n hn; have := h n hn; omega

theorem B_mono_fst (n m : ℤ) : Bsub a b lam (n - 1) m ≤ Bsub a b lam n m :=
  fun _ hv => ⟨hv.1, mul_T_mem_invPolyPart_mono (by omega) hv.2.1, hv.2.2⟩

theorem B_mono_snd (n m : ℤ) : Bsub a b lam n (m - 1) ≤ Bsub a b lam n m :=
  fun _ hv => ⟨hv.1, hv.2.1, mul_T_mem_invPolyPart_mono (by omega) hv.2.2⟩

/-- Identify global sections with the intersection of the two chart subspaces. -/
def H0equiv (n m : ℤ) : ↥(gluedLinesSections k a b lam n m).H0 ≃ₗ[k] ↥(Asub a b lam ⊓ Bsub a b lam
  n m) where
  toFun x := ⟨x.1.1.1, x.1.1.2, by
    have hH := ((gluedLinesSections k a b lam n m).mem_H0_iff x.1).mp x.2
    have heq : x.1.2.1 = x.1.1.1 := (congrArg Subtype.val hH).symm
    rw [← heq]; exact x.1.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨(⟨v.1, v.2.1⟩, ⟨v.1, v.2.2⟩), ((gluedLinesSections k a b lam n m).mem_H0_iff _).mpr
    rfl⟩
  left_inv x := by
    have hH := ((gluedLinesSections k a b lam n m).mem_H0_iff x.1).mp x.2
    have heq : x.1.2.1 = x.1.1.1 := (congrArg Subtype.val hH).symm
    apply Subtype.ext; apply Prod.ext
    · rfl
    · exact Subtype.ext heq.symm
  right_inv v := rfl

/-- Identify overlap sections with their ambient subspace. -/
def M01equiv : (gluedLinesSections k a b lam 0 0).M01 ≃ₗ[k] ↥(Wsub a b lam) where
  toFun w := ⟨w.1, w.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨w.1, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem map_range_cechDiff (n m : ℤ) :
    (LinearMap.range (gluedLinesSections k a b lam n m).cechDiff).map (M01equiv a b
      lam).toLinearMap =
      (Asub a b lam ⊔ Bsub a b lam n m).comap (Wsub a b lam).subtype := by
  ext w
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨x, ⟨⟨u, v⟩, rfl⟩, rfl⟩
    rw [Sections.cechDiff_apply]
    change (v.1 - u.1 : Amb k) ∈ Asub a b lam ⊔ Bsub a b lam n m
    rw [sub_eq_add_neg]
    exact add_mem (mem_sup_right v.2) (mem_sup_left (neg_mem u.2))
  · intro hw
    obtain ⟨u, hu, v, hv, huv⟩ := mem_sup.mp hw
    refine ⟨⟨w.1, w.2⟩, ⟨(⟨-u, neg_mem (show u ∈ gluedLinesM0 k a b lam from hu)⟩, ⟨v, hv⟩), ?_⟩,
      rfl⟩
    rw [Sections.cechDiff_apply]
    apply Subtype.ext
    change v - -u = (w : Amb k)
    rw [sub_neg_eq_add, add_comm]; exact huv

/-- Identify first cohomology with the overlap subspace modulo the chart subspaces. -/
def H1equiv (n m : ℤ) :
    (gluedLinesSections k a b lam n m).H1 ≃ₗ[k] ↥(Wsub a b lam) ⧸ (Asub a b lam ⊔ Bsub a b lam n
      m).comap (Wsub a b lam).subtype :=
  Submodule.Quotient.equiv _ _ (M01equiv a b lam) (map_range_cechDiff a b lam n m)

end GluedLinesChi
end TwoChartCech

end

noncomputable section

namespace TwoChartCech

export _root_.TwoChartCech (levalUnit polyPart invPolyPart mem_invPolyPart_iff GluedCond
  gluedLinesM01 gluedLinesM0 gluedLinesM1 gluedLinesSections Sections Sections.cechDiff_apply
  finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1)


open _root_.TwoChartCech

namespace GluedLinesChi

open Module Submodule GluedLinesMain

variable {k : Type u} [Field k] {s : ℕ}

theorem levalUnit_invert (u : kˣ) (f : k[T;T⁻¹]) :
    levalUnit k u (LaurentPolynomial.invert f) = levalUnit k u⁻¹ f := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T n c =>
    have hinv : LaurentPolynomial.invert (LaurentPolynomial.C c * T n : k[T;T⁻¹]) =
      LaurentPolynomial.C c * T (-n) := by
      rw [map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
    rw [hinv, levalUnit, LaurentPolynomial.eval₂_C_mul_T, LaurentPolynomial.eval₂_C_mul_T,
      inv_zpow']

theorem mul_T_apply (f : k[T;T⁻¹]) (j m : ℤ) : (f * T j : k[T;T⁻¹]).coeff m = f.coeff (m - j) := by
  rw [T_eq_single, AddMonoidAlgebra.coeff_mul_single_apply, mul_one, sub_eq_add_neg]

theorem T_apply_self (j : ℤ) : (T j : k[T;T⁻¹]).coeff j = 1 := by
  rw [T_eq_single, AddMonoidAlgebra.coeff_single]; exact Finsupp.single_eq_same

theorem toLaurent_apply_neg (r : Polynomial k) {j : ℤ} (hj : j < 0) : (Polynomial.toLaurent
  r).coeff j = 0 := by
  by_contra hne
  have := toLaurent_mem_polyPart r j (Finsupp.mem_support_iff.mpr hne)
  omega

theorem exists_laurent_eval_eq (a : Fin s → kˣ) (ha : Function.Injective a) (n : ℤ) (t : Fin s → k)
  :
    ∃ p : k[T;T⁻¹], p * T (-(n - 1)) ∈ invPolyPart k ∧ p.coeff n = 0 ∧ ∀ i, levalUnit k (a i) p = t
      i := by
  classical
  have hInj : Set.InjOn (fun i => (((a i)⁻¹ : kˣ) : k)) ↑(Finset.univ : Finset (Fin s)) :=
    fun i _ j _ h => ha (inv_injective (Units.ext h))
  set r : Polynomial k := Lagrange.interpolate Finset.univ (fun i => (((a i)⁻¹ : kˣ) : k))
    (fun i => t i * ((a i ^ (1 - n) : kˣ) : k)) with hr
  have hev : ∀ i, r.eval (((a i)⁻¹ : kˣ) : k) = t i * ((a i ^ (1 - n) : kˣ) : k) := fun i =>
    Lagrange.eval_interpolate_at_node _ hInj (Finset.mem_univ i)
  refine ⟨T (n - 1) * LaurentPolynomial.invert (Polynomial.toLaurent r), ?_, ?_, ?_⟩
  · rw [mul_comm (T (n - 1)), mul_assoc, ← T_add, show (n - 1) + -(n - 1) = 0
      by ring, T_zero, mul_one]
    intro j hj
    have hne : (LaurentPolynomial.invert (Polynomial.toLaurent r)).coeff j ≠ 0 :=
      Finsupp.mem_support_iff.mp hj
    rw [LaurentPolynomial.invert_apply] at hne
    have := toLaurent_mem_polyPart r (-j) (Finsupp.mem_support_iff.mpr hne)
    omega
  · rw [mul_comm, mul_T_apply, LaurentPolynomial.invert_apply]
    exact toLaurent_apply_neg r (by omega)
  · intro i
    rw [map_mul, levalUnit_invert, levalUnit_toLaurent, hev i]
    change LaurentPolynomial.eval₂ (RingHom.id k) (a i) (T (n - 1)) * _ = _
    rw [LaurentPolynomial.eval₂_T]
    have hu : ((a i ^ (n - 1) : kˣ) : k) * ((a i ^ (1 - n) : kˣ) : k) = 1 := by
      rw [← Units.val_mul, ← zpow_add, show n - 1 + (1 - n) = 0 by ring, zpow_zero, Units.val_one]
    linear_combination (t i) * hu

variable (a b lam : Fin s → kˣ)

/-- The coefficient in degree `n` of the first component on the second chart. -/
def lead (n m : ℤ) : ↥(Bsub a b lam n m) →ₗ[k] k where
  toFun v := v.1.1.coeff n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_lead (n m : ℤ) : LinearMap.ker (lead a b lam n m) = (Bsub a b lam (n - 1) m).comap
  (Bsub a b lam n m).subtype := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  change v.1.1.coeff n = 0 ↔ (v : Amb k) ∈ gluedLinesM1 k a b lam (n - 1) m
  obtain ⟨hcond, h1, h2⟩ := v.2
  rw [mul_T_mem_invPolyPart_iff] at h1
  constructor
  · intro h0
    refine ⟨hcond, ?_, h2⟩
    rw [mul_T_mem_invPolyPart_iff]
    intro j hj
    have hle := h1 j hj
    have hne : j ≠ n := fun hjn => (Finsupp.mem_support_iff.mp hj) (hjn ▸ h0)
    omega
  · rintro ⟨-, h1', -⟩
    rw [mul_T_mem_invPolyPart_iff] at h1'
    by_contra hne
    have := h1' n (Finsupp.mem_support_iff.mpr hne)
    omega

theorem lead_surjective (ha : Function.Injective a) (n m : ℤ) : Function.Surjective (lead a b lam n
  m) := by
  obtain ⟨p, hp, hp0, hpev⟩ := exists_laurent_eval_eq a ha n (fun i => -((a i ^ n : kˣ) : k))
  have hcond : GluedCond a b lam (T n + p, 0) := fun i => by
    change levalUnit k (a i) (T n + p) = lam i * levalUnit k (b i) 0
    rw [map_add, map_zero, mul_zero, hpev]
    change LaurentPolynomial.eval₂ (RingHom.id k) (a i) (T n) + _ = 0
    rw [LaurentPolynomial.eval₂_T, add_neg_cancel]
  have hmem : ((T n + p, 0) : Amb k) ∈ Bsub a b lam n m := by
    refine ⟨hcond, ?_, ?_⟩
    · change (T n + p) * T (-n) ∈ invPolyPart k
      rw [add_mul, ← T_add, add_neg_cancel, T_zero]
      exact Subalgebra.add_mem _ (Subalgebra.one_mem _) (mul_T_mem_invPolyPart_mono (by omega) hp)
    · change (0 : k[T;T⁻¹]) * T (-m) ∈ invPolyPart k
      rw [zero_mul]; exact Subalgebra.zero_mem _
  have hlead : lead a b lam n m ⟨_, hmem⟩ = 1 := by
    change (T n + p : k[T;T⁻¹]).coeff n = 1
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp0, add_zero, T_apply_self]
  intro c
  exact ⟨c • ⟨_, hmem⟩, by rw [map_smul, hlead, smul_eq_mul, mul_one]⟩

theorem codim_fst (ha : Function.Injective a) (n m : ℤ) :
    Module.finrank k (↥(Bsub a b lam n m) ⧸ (Bsub a b lam (n - 1) m).comap (Bsub a b lam n
      m).subtype) = 1 := by
  rw [← ker_lead]
  exact ((lead a b lam n m).quotKerEquivOfSurjective (lead_surjective a b lam ha n
    m)).finrank_eq.trans
    (Module.finrank_self k)

/-- The coefficient in degree `m` of the second component on the second chart. -/
def lead₂ (n m : ℤ) : ↥(Bsub a b lam n m) →ₗ[k] k where
  toFun v := v.1.2.coeff m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_lead₂ (n m : ℤ) : LinearMap.ker (lead₂ a b lam n m) = (Bsub a b lam n (m - 1)).comap
  (Bsub a b lam n m).subtype := by
  ext v
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
  change v.1.2.coeff m = 0 ↔ (v : Amb k) ∈ gluedLinesM1 k a b lam n (m - 1)
  obtain ⟨hcond, h1, h2⟩ := v.2
  rw [mul_T_mem_invPolyPart_iff] at h2
  constructor
  · intro h0
    refine ⟨hcond, h1, ?_⟩
    rw [mul_T_mem_invPolyPart_iff]
    intro j hj
    have hle := h2 j hj
    have hne : j ≠ m := fun hjm => (Finsupp.mem_support_iff.mp hj) (hjm ▸ h0)
    omega
  · rintro ⟨-, -, h2'⟩
    rw [mul_T_mem_invPolyPart_iff] at h2'
    by_contra hne
    have := h2' m (Finsupp.mem_support_iff.mpr hne)
    omega

theorem lead₂_surjective (ha : Function.Injective a) (n m : ℤ) : Function.Surjective (lead₂ a b lam
  n m) := by
  obtain ⟨p, hp, -, hpev⟩ := exists_laurent_eval_eq a ha n (fun i => lam i * ((b i ^ m : kˣ) : k))
  have hcond : GluedCond a b lam (p, T m) := fun i => by
    change levalUnit k (a i) p = lam i * levalUnit k (b i) (T m)
    rw [hpev]
    change _ = (lam i : k) * LaurentPolynomial.eval₂ (RingHom.id k) (b i) (T m)
    rw [LaurentPolynomial.eval₂_T]
  have hmem : ((p, T m) : Amb k) ∈ Bsub a b lam n m := by
    refine ⟨hcond, mul_T_mem_invPolyPart_mono (by omega) hp, ?_⟩
    change T m * T (-m) ∈ invPolyPart k
    rw [← T_add, add_neg_cancel, T_zero]; exact Subalgebra.one_mem _
  have hlead : lead₂ a b lam n m ⟨_, hmem⟩ = 1 := T_apply_self m
  intro c
  exact ⟨c • ⟨_, hmem⟩, by rw [map_smul, hlead, smul_eq_mul, mul_one]⟩

theorem codim_snd (ha : Function.Injective a) (n m : ℤ) :
    Module.finrank k (↥(Bsub a b lam n m) ⧸ (Bsub a b lam n (m - 1)).comap (Bsub a b lam n
      m).subtype) = 1 := by
  rw [← ker_lead₂]
  exact ((lead₂ a b lam n m).quotKerEquivOfSurjective (lead₂_surjective a b lam ha n
    m)).finrank_eq.trans
    (Module.finrank_self k)

/-- The finite-dimensionality and Euler-characteristic assertion for the two twists. -/
def Claim (n m : ℤ) : Prop :=
  Module.Finite k ↥(Asub a b lam ⊓ Bsub a b lam n m) ∧
  Module.Finite k (↥(Wsub a b lam) ⧸ (Asub a b lam ⊔ Bsub a b lam n m).comap (Wsub a b
    lam).subtype) ∧
  (Module.finrank k ↥(Asub a b lam ⊓ Bsub a b lam n m) : ℤ)
    - Module.finrank k (↥(Wsub a b lam) ⧸ (Asub a b lam ⊔ Bsub a b lam n m).comap (Wsub a b
      lam).subtype) = n + m + 2 - s

theorem claim_step_fst (ha : Function.Injective a) (n m : ℤ) : Claim a b lam (n - 1) m ↔ Claim a b
  lam n m := by
  have hBB' := B_mono_fst a b lam n m
  have hB'W := B_le_W a b lam n m
  have hcod := codim_fst a b lam ha n m
  constructor
  · rintro ⟨hf0, hf1, hχ⟩
    have := hf0; have := hf1
    obtain ⟨hf0', hf1'⟩ := ChiStep.finite_forward (Asub a b lam) _ _ (Wsub a b lam) hBB' hcod
    have := hf0'; have := hf1'
    refine ⟨hf0', hf1', ?_⟩
    have := ChiStep.finrank_step (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    omega
  · rintro ⟨hf0', hf1', hχ⟩
    have := hf0'; have := hf1'
    obtain ⟨hf0, hf1⟩ := ChiStep.finite_backward (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    have := hf0; have := hf1
    refine ⟨hf0, hf1, ?_⟩
    have := ChiStep.finrank_step (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    omega

theorem claim_step_snd (ha : Function.Injective a) (n m : ℤ) : Claim a b lam n (m - 1) ↔ Claim a b
  lam n m := by
  have hBB' := B_mono_snd a b lam n m
  have hB'W := B_le_W a b lam n m
  have hcod := codim_snd a b lam ha n m
  constructor
  · rintro ⟨hf0, hf1, hχ⟩
    have := hf0; have := hf1
    obtain ⟨hf0', hf1'⟩ := ChiStep.finite_forward (Asub a b lam) _ _ (Wsub a b lam) hBB' hcod
    have := hf0'; have := hf1'
    refine ⟨hf0', hf1', ?_⟩
    have := ChiStep.finrank_step (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    omega
  · rintro ⟨hf0', hf1', hχ⟩
    have := hf0'; have := hf1'
    obtain ⟨hf0, hf1⟩ := ChiStep.finite_backward (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    have := hf0; have := hf1
    refine ⟨hf0, hf1, ?_⟩
    have := ChiStep.finrank_step (Asub a b lam) _ _ (Wsub a b lam) hBB' hB'W hcod
    omega

theorem claim_base
    (hmain : Module.finrank k ↥(gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H0 = 1 ∧
      Subsingleton (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H1) :
    Claim a b lam ((s : ℤ) - 1) 0 := by
  obtain ⟨h0, h1⟩ := hmain
  have e0 := H0equiv a b lam ((s : ℤ) - 1) 0
  have e1 := H1equiv a b lam ((s : ℤ) - 1) 0
  have hr0 : Module.finrank k ↥(Asub a b lam ⊓ Bsub a b lam ((s : ℤ) - 1) 0) = 1 :=
    by rw [← e0.finrank_eq, h0]
  have : Subsingleton (↥(Wsub a b lam) ⧸ (Asub a b lam ⊔ Bsub a b lam ((s : ℤ) - 1) 0).comap (Wsub
    a b lam).subtype) :=
    e1.symm.toEquiv.subsingleton
  refine ⟨Module.finite_of_finrank_eq_succ hr0, Module.Finite.of_finite, ?_⟩
  rw [hr0, Module.finrank_zero_of_subsingleton]
  push_cast
  ring

theorem claim_all (ha : Function.Injective a)
    (hmain : Module.finrank k ↥(gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H0 = 1 ∧
      Subsingleton (gluedLinesSections k a b lam ((s : ℤ) - 1) 0).H1)
    (n m : ℤ) : Claim a b lam n m := by
  have hbase := claim_base a b lam hmain
  have hm : Claim a b lam ((s : ℤ) - 1) m := by
    induction m using Int.induction_on with
    | zero => exact hbase
    | succ j ih =>
        exact (claim_step_snd a b lam ha _ ((j : ℤ) + 1)).mp (by rwa [add_sub_cancel_right])
    | pred j ih => exact (claim_step_snd a b lam ha _ (-(j : ℤ))).mpr ih
  have hd : ∀ d : ℤ, Claim a b lam ((s : ℤ) - 1 + d) m := by
    intro d
    induction d using Int.induction_on with
    | zero => rwa [add_zero]
    | succ j ih =>
      refine (claim_step_fst a b lam ha ((s : ℤ) - 1 + ((j : ℤ) + 1)) m).mp ?_
      rwa [show (s : ℤ) - 1 + ((j : ℤ) + 1) - 1 = (s : ℤ) - 1 + j by ring]
    | pred j ih =>
      have h := (claim_step_fst a b lam ha ((s : ℤ) - 1 + -(j : ℤ)) m).mpr ih
      rwa [show (s : ℤ) - 1 + -(j : ℤ) - 1 = (s : ℤ) - 1 + (-(j : ℤ) - 1) by ring] at h
  have h := hd (n - ((s : ℤ) - 1))
  rwa [show (s : ℤ) - 1 + (n - ((s : ℤ) - 1)) = n by ring] at h

end GluedLinesChi
end TwoChartCech

end

open _root_.TwoChartCech
  _root_.AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartFinrankH0SubFinrankH1.TwoChartCech
  TwoChartCech.GluedLinesChi in
theorem _root_.TwoChartCech.finrank_H0_sub_finrank_H1_gluedLinesSections
    (k : Type u) [Field k] {s : ℕ} (a b lam : Fin s → kˣ) (ha : Function.Injective a) (n m : ℤ) :
    Module.Finite k ↥(gluedLinesSections k a b lam n m).H0 ∧
      Module.Finite k (gluedLinesSections k a b lam n m).H1 ∧
      (Module.finrank k ↥(gluedLinesSections k a b lam n m).H0 : ℤ)
        - Module.finrank k (gluedLinesSections k a b lam n m).H1 = n + m + 2 - s := by
  obtain ⟨hf0, hf1, hχ⟩ := claim_all a b lam ha
    (TwoChartCech.finrank_H0_gluedLinesSections_eq_one_and_subsingleton_H1 k a b lam ha) n m
  have := hf0; have := hf1
  have e0 := H0equiv a b lam n m
  have e1 := H1equiv a b lam n m
  refine ⟨Module.Finite.equiv e0.symm, Module.Finite.equiv e1.symm, ?_⟩
  rw [e0.finrank_eq, e1.finrank_eq]
  exact hχ
end AlgebraicCurves.Cohomology.Cech.Proofs.TwoChartFinrankH0SubFinrankH1
end ProofImplementation
