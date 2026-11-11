/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Tactic.Ring
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.Basic

/-!
# Local domains in characteristic-zero Hopf algebras

Use the augmentation filtration and a homogeneous Taylor expansion to prove that localizations
at rational points of a finite-type Hopf algebra over a characteristic-zero field are domains.
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.CartierFiltration

noncomputable section

open TensorProduct Bialgebra Coalgebra MvPolynomial

universe u v w

namespace CartierHopf

section Filtration

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A]

/-- Augmentation ideal of the coordinate Hopf algebra. -/
abbrev kwCartier68a_augIdeal : Ideal A := RingHom.ker (counitAlgHom k A).toRingHom

variable {k A}

theorem kwCartier68a_rTensor_counit_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    ((Coalgebra.counit (R := k)).rTensor A)
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x) = 0 := by
  have hεx : Coalgebra.counit (R := k) x = 0 := hx
  simp only [map_sub, LinearMap.rTensor_tmul, Coalgebra.rTensor_counit_comul, hεx,
    Bialgebra.counit_one, TensorProduct.zero_tmul, sub_zero, sub_self]

theorem kwCartier68a_lTensor_counit_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    ((Coalgebra.counit (R := k)).lTensor A)
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x) = 0 := by
  have hεx : Coalgebra.counit (R := k) x = 0 := hx
  simp only [map_sub, LinearMap.lTensor_tmul, Coalgebra.lTensor_counit_comul, hεx,
    Bialgebra.counit_one, TensorProduct.tmul_zero, sub_self]

end Filtration
section AugProj

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A]

/-- Projection onto the augmentation ideal along the scalars. -/
def kwCartier68c_augProj : A →ₗ[k] A :=
  LinearMap.id - (Algebra.linearMap k A).comp (Coalgebra.counit (R := k))

variable {k A}

theorem kwCartier68c_augProj_apply (a : A) :
    kwCartier68c_augProj k A a = a - algebraMap k A (Coalgebra.counit (R := k) a) := rfl

theorem kwCartier68c_augProj_mem_augIdeal (a : A) :
    kwCartier68c_augProj k A a ∈ kwCartier68a_augIdeal k A := by
  change (counitAlgHom k A) (a - algebraMap k A (Coalgebra.counit (R := k) a)) = 0
  rw [map_sub, AlgHom.commutes]
  exact sub_self _

theorem kwCartier68c_augProj_lTensor_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (kwCartier68c_augProj k A).lTensor A
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x)
      = (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x := by
  set y := (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x
  have hL : ((Coalgebra.counit (R := k)).lTensor A) y = 0 :=
    kwCartier68a_lTensor_counit_comulDefect hx
  change (kwCartier68c_augProj k A).lTensor A y = y
  rw [kwCartier68c_augProj, LinearMap.lTensor_sub, LinearMap.sub_apply,
    LinearMap.lTensor_id, LinearMap.id_apply, LinearMap.lTensor_comp,
    LinearMap.comp_apply, hL, map_zero, sub_zero]

theorem kwCartier68c_augProj_rTensor_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (kwCartier68c_augProj k A).rTensor A
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x)
      = (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x := by
  set y := (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x
  have hR : ((Coalgebra.counit (R := k)).rTensor A) y = 0 :=
    kwCartier68a_rTensor_counit_comulDefect hx
  change (kwCartier68c_augProj k A).rTensor A y = y
  rw [kwCartier68c_augProj, LinearMap.rTensor_sub, LinearMap.sub_apply,
    LinearMap.rTensor_id, LinearMap.id_apply, LinearMap.rTensor_comp,
    LinearMap.comp_apply, hR, map_zero, sub_zero]

theorem kwCartier68c_augProj_tmul_augProj_comulDefect
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (TensorProduct.map (kwCartier68c_augProj k A) (kwCartier68c_augProj k A))
        ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x)
      = (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x := by
  rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply,
    kwCartier68c_augProj_rTensor_comulDefect hx,
    kwCartier68c_augProj_lTensor_comulDefect hx]

end AugProj
section ComulDefectMap

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]

theorem kwCartier68c_comulDefect_mem_map_includeRight
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x ∈
      (kwCartier68a_augIdeal k A).map
        (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom := by
  set I := kwCartier68a_augIdeal k A
  set y := (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x with hy
  set K := I.map (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom
  have hfix : (TensorProduct.map (kwCartier68c_augProj k A) (kwCartier68c_augProj k A)) y
      = y := by rw [hy]; exact kwCartier68c_augProj_tmul_augProj_comulDefect hx
  rw [← hfix]
  refine TensorProduct.inductionOn y ?_ (fun _ _ hp hr => by
    rw [map_add]; exact K.add_mem hp hr)
  intro a b
  simp only [TensorProduct.map_tmul]
  have hσb : kwCartier68c_augProj k A b ∈ I := kwCartier68c_augProj_mem_augIdeal b
  rw [show (kwCartier68c_augProj k A a) ⊗ₜ[k] (kwCartier68c_augProj k A b)
      = ((kwCartier68c_augProj k A a) ⊗ₜ[k] (1 : A))
        * ((1 : A) ⊗ₜ[k] (kwCartier68c_augProj k A b)) from
    by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
  exact Ideal.mul_mem_left K _ (Ideal.mem_map_of_mem _ hσb)

theorem kwCartier68c_comulDefect_mem_map_includeLeft
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x ∈
      (kwCartier68a_augIdeal k A).map
        (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom := by
  set I := kwCartier68a_augIdeal k A
  set y := (Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x with hy
  set K := I.map (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom
  have hfix : (TensorProduct.map (kwCartier68c_augProj k A) (kwCartier68c_augProj k A)) y
      = y := by rw [hy]; exact kwCartier68c_augProj_tmul_augProj_comulDefect hx
  rw [← hfix]
  refine TensorProduct.inductionOn y ?_ (fun _ _ hp hr => by
    rw [map_add]; exact K.add_mem hp hr)
  intro a b
  simp only [TensorProduct.map_tmul]
  have hσa : kwCartier68c_augProj k A a ∈ I := kwCartier68c_augProj_mem_augIdeal a
  rw [show (kwCartier68c_augProj k A a) ⊗ₜ[k] (kwCartier68c_augProj k A b)
      = ((kwCartier68c_augProj k A a) ⊗ₜ[k] (1 : A))
        * ((1 : A) ⊗ₜ[k] (kwCartier68c_augProj k A b)) from
    by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
  exact Ideal.mul_mem_right _ K (Ideal.mem_map_of_mem _ hσa)

end ComulDefectMap
section ComulFiltered

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]

theorem kwCartier68e_comul_mem_sup_map
    {x : A} (hx : x ∈ kwCartier68a_augIdeal k A) :
    (comulAlgHom k A) x ∈
      (kwCartier68a_augIdeal k A).map
          (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom ⊔
        (kwCartier68a_augIdeal k A).map
          (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom := by
  have hΔ : (comulAlgHom k A) x
      = x ⊗ₜ[k] (1 : A) + ((1 : A) ⊗ₜ[k] x
        + ((Coalgebra.comul (R := k) x) - x ⊗ₜ[k] 1 - 1 ⊗ₜ[k] x)) := by
    change (Coalgebra.comul (R := k) x) = _; ring
  rw [hΔ]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hx)) ?_
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hx))
    (Ideal.mem_sup_right (kwCartier68c_comulDefect_mem_map_includeRight hx))

end ComulFiltered
section NilpotentSup

variable {S : Type v} [CommRing S]

theorem kwCartier68e_sup_pow_succ_le_of_sq_eq_bot
    {L R : Ideal S} (hR : R ^ 2 = ⊥) (m : ℕ) :
    (L ⊔ R) ^ (m + 1) ≤ L ^ (m + 1) ⊔ L ^ m * R := by
  induction m with
  | zero => simp only [Nat.zero_add, pow_zero, pow_one, one_mul, le_refl]
  | succ m ih =>
    calc (L ⊔ R) ^ (m + 2)
        = (L ⊔ R) * (L ⊔ R) ^ (m + 1) := by ring
      _ ≤ (L ⊔ R) * (L ^ (m + 1) ⊔ L ^ m * R) := Ideal.mul_mono_right ih
      _ = L * L ^ (m + 1) ⊔ L * (L ^ m * R)
            ⊔ (R * L ^ (m + 1) ⊔ R * (L ^ m * R)) := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
      _ ≤ L ^ (m + 2) ⊔ L ^ (m + 1) * R := by
          refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
          · exact le_sup_of_le_left (le_of_eq (by ring))
          · exact le_sup_of_le_right (le_of_eq (by ring))
          · exact le_sup_of_le_right
              (le_of_eq (by rw [Ideal.mul_comm]))
          · rw [show R * (L ^ m * R) = L ^ m * R ^ 2 by ring, hR,
              Ideal.mul_bot]
            exact bot_le

end NilpotentSup
section PsiKill

variable (k : Type u) [Field k] (A : Type v) [CommRing A] [HopfAlgebra k A] (n : ℕ)

/-- Comultiplication truncated in the augmentation filtrations of the two factors. -/
def kwCartier68e_Ψ : A →ₐ[k]
    (A ⧸ (kwCartier68a_augIdeal k A) ^ n) ⊗[k] (A ⧸ (kwCartier68a_augIdeal k A) ^ 2) :=
  (Algebra.TensorProduct.map
      (Ideal.Quotient.mkₐ k ((kwCartier68a_augIdeal k A) ^ n))
      (Ideal.Quotient.mkₐ k ((kwCartier68a_augIdeal k A) ^ 2))).comp
    (comulAlgHom k A)

variable {k A n}

theorem kwCartier68e_Ψ_apply_eq_zero_of_mem_pow_succ
    {z : A} (hz : z ∈ (kwCartier68a_augIdeal k A) ^ (n + 1)) :
    kwCartier68e_Ψ k A n z = 0 := by
  set I := kwCartier68a_augIdeal k A
  suffices hmap : (I.map (kwCartier68e_Ψ k A n).toRingHom) ^ (n + 1) = ⊥ by
    have hz' : (kwCartier68e_Ψ k A n) z ∈
        (I.map (kwCartier68e_Ψ k A n).toRingHom) ^ (n + 1) := by
      rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hz
    rwa [hmap, Ideal.mem_bot] at hz'
  let πn := Ideal.Quotient.mkₐ k (I ^ n)
  let π2 := Ideal.Quotient.mkₐ k (I ^ 2)
  let L : Ideal ((A ⧸ I ^ n) ⊗[k] (A ⧸ I ^ 2)) :=
    (I.map πn.toRingHom).map
      (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A ⧸ I ^ 2)).toRingHom
  let R : Ideal ((A ⧸ I ^ n) ⊗[k] (A ⧸ I ^ 2)) :=
    (I.map π2.toRingHom).map
      (Algebra.TensorProduct.includeRight (R := k) (A := A ⧸ I ^ n)).toRingHom
  have hInker : ∀ m : ℕ, (I ^ m).map (Ideal.Quotient.mkₐ k (I ^ m)).toRingHom = ⊥ :=
    fun m => (Ideal.map_eq_bot_iff_le_ker _).mpr
      (by rw [← RingHom.ker_coe_toRingHom]; exact (Ideal.mk_ker).ge)
  have hLn : L ^ n = ⊥ := by
    rw [← Ideal.map_pow, ← Ideal.map_pow, hInker n, Ideal.map_bot]
  have hR2 : R ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, ← Ideal.map_pow, hInker 2, Ideal.map_bot]
  have hcommL :
      (Algebra.TensorProduct.map πn π2).toRingHom.comp
          (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom
        = (Algebra.TensorProduct.includeLeft (R := k) (S := k)
              (B := A ⧸ I ^ 2)).toRingHom.comp πn.toRingHom := by
    ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul, map_one]
  have hcommR :
      (Algebra.TensorProduct.map πn π2).toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom
        = (Algebra.TensorProduct.includeRight (R := k)
              (A := A ⧸ I ^ n)).toRingHom.comp π2.toRingHom := by
    ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]
  have hle : I.map (kwCartier68e_Ψ k A n).toRingHom ≤ L ⊔ R := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    have hΔx := kwCartier68e_comul_mem_sup_map (k := k) hx
    change (Algebra.TensorProduct.map πn π2) ((comulAlgHom k A) x) ∈ L ⊔ R
    have hfact : (Algebra.TensorProduct.map πn π2) ((comulAlgHom k A) x) ∈
        ((kwCartier68a_augIdeal k A).map
            (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom ⊔
          (kwCartier68a_augIdeal k A).map
            (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom).map
          (Algebra.TensorProduct.map πn π2).toRingHom :=
      Ideal.mem_map_of_mem _ hΔx
    rw [Ideal.map_sup, Ideal.map_map, Ideal.map_map, hcommL, hcommR,
      ← Ideal.map_map, ← Ideal.map_map] at hfact
    exact hfact
  refine le_bot_iff.mp ?_
  calc (I.map (kwCartier68e_Ψ k A n).toRingHom) ^ (n + 1)
      ≤ (L ⊔ R) ^ (n + 1) := pow_le_pow_left' hle _
    _ ≤ L ^ (n + 1) ⊔ L ^ n * R := kwCartier68e_sup_pow_succ_le_of_sq_eq_bot hR2 n
    _ = ⊥ := by
        rw [show L ^ (n + 1) = L ^ n * L from by ring, hLn, Ideal.bot_mul, Ideal.bot_mul,
          bot_sup_eq]

end PsiKill
section SqZeroTaylor

variable {k : Type u} [CommRing k] {S : Type v} [CommRing S] [Algebra k S]
variable {ι : Type w} [Fintype ι]

theorem kwCartier68e_aeval_add_of_sq_eq_zero
    {K : Ideal S} (hK : K ^ 2 = ⊥) (a b : ι → S) (hb : ∀ i, b i ∈ K)
    (p : MvPolynomial ι k) :
    aeval (a + b) p = aeval a p + ∑ i, aeval a (pderiv i p) * b i := by
  have hbb : ∀ i j, b i * b j = 0 := fun i j => by
    have hmem : b i * b j ∈ K ^ 2 := by rw [sq]; exact Ideal.mul_mem_mul (hb i) (hb j)
    rwa [hK, Ideal.mem_bot] at hmem
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp only [aeval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero,
      add_zero]
  | add p q hp hq =>
    simp only [map_add, hp, hq, Finset.sum_add_distrib, add_mul]; ring
  | mul_X p j hp =>
    have hsumR : ∑ i, aeval a (pderiv i (p * X j)) * b i
        = (∑ i, aeval a (pderiv i p) * b i) * a j + aeval a p * b j := by
      have hterm : ∀ i, aeval a (pderiv i (p * X j)) * b i
          = aeval a (pderiv i p) * b i * a j
            + aeval a p * (if i = j then b j else 0) := fun i => by
        rw [pderiv_mul, map_add, map_mul, map_mul, aeval_X, add_mul]
        congr 1
        · ring
        rcases eq_or_ne i j with rfl | hne
        · rw [ite_eq_left rfl, pderiv_X_self, map_one, mul_one]
        · rw [ite_eq_right hne, pderiv_X_of_ne (Ne.symm hne), map_zero, mul_zero, zero_mul]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_ite_eq' Finset.univ j (fun _ => b j), ite_eq_left (Finset.mem_univ j)]
    have hkill : (∑ i, aeval a (pderiv i p) * b i) * b j = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_assoc, hbb, mul_zero]
    rw [map_mul, aeval_X, Pi.add_apply, hp, map_mul, aeval_X, hsumR,
      add_mul, mul_add, mul_add, hkill]
    ring

end SqZeroTaylor
section TmulLinIndep

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
variable {W : Type w} [AddCommGroup W] [Module k W] {ι : Type*} [Fintype ι]

theorem kwCartier68e_eq_zero_of_sum_tmul_linearIndependent
    {w : ι → W} (hw : LinearIndependent k w) {m : ι → V}
    (h0 : ∑ i, m i ⊗ₜ[k] w i = 0) (j : ι) : m j = 0 := by
  classical
  let lc := Finsupp.linearCombination k w
  have hinj : Function.Injective (lc.lTensor V) :=
    Module.Flat.lTensor_preserves_injective_linearMap lc hw
  have heq : (lc.lTensor V) (∑ i, m i ⊗ₜ[k] Finsupp.single i (1 : k)) = 0 := by
    rw [map_sum]
    simp only [LinearMap.lTensor_tmul, lc, Finsupp.linearCombination_single, one_smul]
    exact h0
  have hzero : ∑ i, m i ⊗ₜ[k] Finsupp.single i (1 : k) = 0 :=
    hinj (by rw [heq, map_zero])
  have hcoord := congrArg
    (fun z => (TensorProduct.rid k V) (((Finsupp.lapply j).lTensor V) z)) hzero
  simp only [map_sum, LinearMap.lTensor_tmul, Finsupp.lapply_apply,
    Finsupp.single_apply, map_zero] at hcoord
  have hterm : ∀ i, (TensorProduct.rid k V)
        (m i ⊗ₜ[k] (if (i : ι) = j then (1 : k) else 0))
      = if i = j then m i else 0 := fun i => by
    by_cases h : i = j
    · subst i; simp only [ite_true, TensorProduct.rid_tmul, one_smul]
    · simp only [ite_eq_right h, TensorProduct.rid_tmul, zero_smul]
  rw [Finset.sum_congr rfl fun i _ => hterm i,
    Finset.sum_ite_eq' Finset.univ j m, ite_eq_left (Finset.mem_univ j)] at hcoord
  exact hcoord

end TmulLinIndep
section Main

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]
variable {ι : Type w}

theorem kwCartier68e_aeval_homogeneous_mem_augIdeal_pow
    {ξ : ι → A} (hξI : ∀ i, ξ i ∈ kwCartier68a_augIdeal k A)
    {n : ℕ} {p : MvPolynomial ι k} (hp : p.IsHomogeneous n) :
    aeval ξ p ∈ (kwCartier68a_augIdeal k A) ^ n := by
  set I := kwCartier68a_augIdeal k A
  classical
  rw [aeval_def, eval₂_eq]
  refine Ideal.sum_mem _ fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h1 := hp (Finsupp.mem_support_iff.mp hd)
    simpa only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using h1
  have hmem : (∏ i ∈ d.support, ξ i ^ d i) ∈ I ^ n := by
    rw [← hdeg, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hξI i) _
  exact Ideal.mul_mem_left _ _ hmem

variable [Finite ι] [CharZero k]

theorem kwCartier68e_aeval_homogeneous_not_mem_augIdeal_pow_succ
    {ξ : ι → A} (hξI : ∀ i, ξ i ∈ kwCartier68a_augIdeal k A)
    (hξli : LinearIndependent k
      (fun i => Ideal.Quotient.mk ((kwCartier68a_augIdeal k A) ^ 2) (ξ i)))
    {n : ℕ} {p : MvPolynomial ι k} (hp : p.IsHomogeneous n) (hp0 : p ≠ 0) :
    aeval ξ p ∉ (kwCartier68a_augIdeal k A) ^ (n + 1) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  set I := kwCartier68a_augIdeal k A with hI
  induction n using Nat.strong_induction_on generalizing p with
  | _ n IH =>
  intro hmem
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hpC : p = C (p.coeff 0) := by
      rw [← totalDegree_zero_iff_isHomogeneous] at hp
      exact (totalDegree_eq_zero_iff_eq_C.mp hp)
    have hc0 : p.coeff 0 ≠ 0 := fun h => hp0 (by rw [hpC, h, map_zero])
    rw [hpC, aeval_C, pow_one] at hmem
    have heps : (counitAlgHom k A) (algebraMap k A (p.coeff 0)) = 0 := hmem
    rw [AlgHom.commutes] at heps
    exact hc0 heps
  let πn := Ideal.Quotient.mkₐ k (I ^ n)
  let π2 := Ideal.Quotient.mkₐ k (I ^ 2)
  let Rng := (A ⧸ I ^ n) ⊗[k] (A ⧸ I ^ 2)
  let Ψ := kwCartier68e_Ψ k A n
  let aL : ι → Rng := fun i => πn (ξ i) ⊗ₜ[k] 1
  let bR : ι → Rng := fun i => Ψ (ξ i) - aL i
  let K : Ideal Rng :=
    (I.map π2.toRingHom).map
      (Algebra.TensorProduct.includeRight (R := k) (A := A ⧸ I ^ n)).toRingHom
  have hK2 : K ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, ← Ideal.map_pow,
      show (I ^ 2).map π2.toRingHom = ⊥ from
        (Ideal.map_eq_bot_iff_le_ker _).mpr
          (by rw [← RingHom.ker_coe_toRingHom]; exact Ideal.mk_ker.ge),
      Ideal.map_bot]
  have hcommR :
      (Algebra.TensorProduct.map πn π2).toRingHom.comp
          (Algebra.TensorProduct.includeRight (R := k) (A := A)).toRingHom
        = (Algebra.TensorProduct.includeRight (R := k)
              (A := A ⧸ I ^ n)).toRingHom.comp π2.toRingHom := by
    ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_one]
  have hcommL :
      (Algebra.TensorProduct.map πn π2).toRingHom.comp
          (Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A)).toRingHom
        = (Algebra.TensorProduct.includeLeft (R := k) (S := k)
              (B := A ⧸ I ^ 2)).toRingHom.comp πn.toRingHom := by
    ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.map_tmul, map_one]
  have hΨi : ∀ i, Ψ (ξ i)
      = πn (ξ i) ⊗ₜ[k] (1 : A ⧸ I ^ 2) + (1 : A ⧸ I ^ n) ⊗ₜ[k] π2 (ξ i)
        + (Algebra.TensorProduct.map πn π2)
            ((Coalgebra.comul (R := k) (ξ i)) - (ξ i) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] (ξ i)) := by
    intro i
    change (Algebra.TensorProduct.map πn π2) (comulAlgHom k A (ξ i)) = _
    have hc : (comulAlgHom k A) (ξ i)
        = (ξ i) ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] (ξ i)
          + ((Coalgebra.comul (R := k) (ξ i)) - (ξ i) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] (ξ i)) := by
      change (Coalgebra.comul (R := k) (ξ i)) = _; ring
    rw [hc, map_add, map_add, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, map_one, map_one]
  have hbR_eq : ∀ i, bR i = (1 : A ⧸ I ^ n) ⊗ₜ[k] π2 (ξ i)
      + (Algebra.TensorProduct.map πn π2)
          ((Coalgebra.comul (R := k) (ξ i)) - (ξ i) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] (ξ i)) := by
    intro i
    have : bR i = Ψ (ξ i) - aL i := rfl
    rw [this, hΨi i]; simp only [aL]; ring
  have hbK : ∀ i, bR i ∈ K := by
    intro i
    rw [hbR_eq i]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hξI i))
    · have hy := kwCartier68c_comulDefect_mem_map_includeRight (k := k) (hξI i)
      have hmem := Ideal.mem_map_of_mem (Algebra.TensorProduct.map πn π2).toRingHom hy
      rwa [Ideal.map_map, hcommR, ← Ideal.map_map] at hmem
  let iL' : (A ⧸ I ^ n) →ₐ[k] Rng :=
    Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := A ⧸ I ^ 2)
  have haLbR : aL + bR = fun i => Ψ (ξ i) := funext fun i => by
    change aL i + (Ψ (ξ i) - aL i) = Ψ (ξ i)
    exact add_sub_cancel _ _
  have haevaL : ∀ q : MvPolynomial ι k, aeval aL q = iL' (πn (aeval ξ q)) := fun q => by
    have heq : (aeval aL : MvPolynomial ι k →ₐ[k] Rng) = (iL'.comp πn).comp (aeval ξ) :=
      MvPolynomial.algHom_ext fun i => by
        simp only [aeval_X, AlgHom.comp_apply]; rfl
    exact DFunLike.congr_fun heq q
  have haevΨ : ∀ q : MvPolynomial ι k,
      (aeval (fun i => Ψ (ξ i)) : MvPolynomial ι k →ₐ[k] Rng) q = Ψ (aeval ξ q) := fun q => by
    have heq : (aeval (fun i => Ψ (ξ i)) : MvPolynomial ι k →ₐ[k] Rng) = Ψ.comp (aeval ξ) :=
      MvPolynomial.algHom_ext fun i => by simp only [aeval_X, AlgHom.comp_apply]
    exact DFunLike.congr_fun heq q
  have hTaylor := kwCartier68e_aeval_add_of_sq_eq_zero hK2 aL bR hbK p
  rw [haLbR, haevΨ] at hTaylor
  have hΨz : Ψ (aeval ξ p) = 0 :=
    kwCartier68e_Ψ_apply_eq_zero_of_mem_pow_succ hmem
  have haLz : aeval aL p = 0 := by
    rw [haevaL]
    have : πn (aeval ξ p) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.pow_le_pow_right (Nat.le_succ n) hmem)
    rw [this, map_zero]
  rw [hΨz, haLz, zero_add] at hTaylor
  have hdefect : ∀ i, aeval aL (pderiv i p) * bR i
      = πn (aeval ξ (pderiv i p)) ⊗ₜ[k] π2 (ξ i) := by
    intro i
    rw [haevaL, show iL' (πn (aeval ξ (pderiv i p)))
          = πn (aeval ξ (pderiv i p)) ⊗ₜ[k] (1 : A ⧸ I ^ 2) from rfl,
      hbR_eq i, mul_add, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    convert add_zero _
    have hdp : aeval ξ (pderiv i p) ∈ I ^ (n - 1) :=
      kwCartier68e_aeval_homogeneous_mem_augIdeal_pow hξI hp.pderiv
    have hyL := kwCartier68c_comulDefect_mem_map_includeLeft (k := k) (hξI i)
    have hwL : (Algebra.TensorProduct.map πn π2)
          ((Coalgebra.comul (R := k) (ξ i)) - (ξ i) ⊗ₜ[k] 1 - 1 ⊗ₜ[k] (ξ i)) ∈
        (I.map πn.toRingHom).map
          (Algebra.TensorProduct.includeLeft (R := k) (S := k)
            (B := A ⧸ I ^ 2)).toRingHom := by
      have hmem := Ideal.mem_map_of_mem (Algebra.TensorProduct.map πn π2).toRingHom hyL
      rwa [Ideal.map_map, hcommL, ← Ideal.map_map] at hmem
    have hleft : πn (aeval ξ (pderiv i p)) ⊗ₜ[k] (1 : A ⧸ I ^ 2) ∈
        ((I ^ (n - 1)).map πn.toRingHom).map
          (Algebra.TensorProduct.includeLeft (R := k) (S := k)
            (B := A ⧸ I ^ 2)).toRingHom :=
      Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hdp)
    have hnil : (I ^ (n - 1)).map πn.toRingHom * I.map πn.toRingHom = ⊥ := by
      rw [← Ideal.map_mul, ← pow_succ, Nat.sub_add_cancel hnpos]
      exact (Ideal.map_eq_bot_iff_le_ker _).mpr
        (by rw [← RingHom.ker_coe_toRingHom]; exact Ideal.mk_ker.ge)
    have hprod := Ideal.mul_mem_mul hleft hwL
    rw [← Ideal.map_mul, hnil, Ideal.map_bot, Ideal.mem_bot] at hprod
    exact hprod
  rw [Finset.sum_congr rfl fun i _ => hdefect i] at hTaylor
  have hcoef : ∀ i, πn (aeval ξ (pderiv i p)) = 0 :=
    fun i => kwCartier68e_eq_zero_of_sum_tmul_linearIndependent hξli hTaylor.symm i
  have hpderiv0 : ∀ i, pderiv i p = 0 := by
    intro i
    by_contra hne
    have hmemn : aeval ξ (pderiv i p) ∈ I ^ n :=
      Ideal.Quotient.eq_zero_iff_mem.mp (hcoef i)
    have hrw : I ^ n = I ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hnpos]
    rw [hrw] at hmemn
    exact IH (n - 1) (Nat.sub_lt hnpos one_pos) hp.pderiv hne hmemn
  have heuler := hp.sum_X_mul_pderiv
  simp only [hpderiv0, mul_zero, Finset.sum_const_zero] at heuler
  have hnp : (n : MvPolynomial ι k) * p = 0 := by
    have h := heuler.symm; rwa [nsmul_eq_mul] at h
  have hncast : (n : MvPolynomial ι k) ≠ 0 := by
    rw [show (n : MvPolynomial ι k) = C (n : k) from (map_natCast _ _).symm]
    exact fun h => (Nat.cast_ne_zero.mpr hnpos.ne') (C_injective ι k (by rwa [map_zero]))
  exact hp0 ((mul_eq_zero.mp hnp).resolve_left hncast)

end Main
section Surj

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [HopfAlgebra k A]
variable {ι : Type w} [Fintype ι]

theorem kwCartier68e_exists_homogeneous_aeval_congr_of_mem_pow
    {ξ : ι → A} (hξI : ∀ i, ξ i ∈ kwCartier68a_augIdeal k A)
    (hξspan : ∀ a ∈ kwCartier68a_augIdeal k A,
      ∃ c : ι → k, a - ∑ i, c i • ξ i ∈ (kwCartier68a_augIdeal k A) ^ 2) :
    ∀ (n : ℕ) (z : A), z ∈ (kwCartier68a_augIdeal k A) ^ n →
      ∃ p : MvPolynomial ι k, p.IsHomogeneous n ∧
        z - aeval ξ p ∈ (kwCartier68a_augIdeal k A) ^ (n + 1) := by
  set I := kwCartier68a_augIdeal k A
  intro n
  induction n with
  | zero =>
    intro z _
    refine ⟨C (counitAlgHom k A z), isHomogeneous_C _ _, ?_⟩
    rw [aeval_C, pow_one]
    exact kwCartier68c_augProj_mem_augIdeal z
  | succ n ih =>
    intro z hz
    rw [pow_succ] at hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro y hy x hx
      obtain ⟨q, hq, hyq⟩ := ih y hy
      obtain ⟨c, hxc⟩ := hξspan x hx
      refine ⟨∑ i, C (c i) * (q * X i), ?_, ?_⟩
      · refine IsHomogeneous.sum _ _ _ fun i _ => ?_
        have h0 : (0 : ℕ) + (n + 1) = n + 1 := zero_add _
        exact h0 ▸ (isHomogeneous_C _ (c i)).mul (hq.mul (isHomogeneous_X _ i))
      · have hsum : aeval ξ (∑ i, C (c i) * (q * X i)) = aeval ξ q * ∑ i, c i • ξ i := by
          rw [map_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by
            rw [map_mul, map_mul, aeval_C, aeval_X, Algebra.smul_def]; ring
        have hexp : y * x - aeval ξ (∑ i, C (c i) * (q * X i))
            = (y - aeval ξ q) * x + aeval ξ q * (x - ∑ i, c i • ξ i) := by
          rw [hsum]; ring
        rw [hexp, pow_succ, pow_succ]
        refine Ideal.add_mem _ (Ideal.mul_mem_mul (pow_succ I n ▸ hyq) hx) ?_
        have hqn : aeval ξ q ∈ I ^ n :=
          kwCartier68e_aeval_homogeneous_mem_augIdeal_pow hξI hq
        have hle : I ^ n * I ^ 2 ≤ I ^ n * I * I := le_of_eq (by rw [mul_assoc, sq])
        exact hle (Ideal.mul_mem_mul hqn hxc)
    · rintro a b ⟨pa, hpa, ha⟩ ⟨pb, hpb, hb⟩
      exact ⟨pa + pb, hpa.add hpb, by
        rw [map_add]; convert Ideal.add_mem _ ha hb using 1; ring⟩

variable [CharZero k]

theorem kwCartier68e_mul_not_mem_pow_of_not_mem_pow
    {ξ : ι → A} (hξI : ∀ i, ξ i ∈ kwCartier68a_augIdeal k A)
    (hξli : LinearIndependent k
      (fun i => Ideal.Quotient.mk ((kwCartier68a_augIdeal k A) ^ 2) (ξ i)))
    (hξspan : ∀ a ∈ kwCartier68a_augIdeal k A,
      ∃ c : ι → k, a - ∑ i, c i • ξ i ∈ (kwCartier68a_augIdeal k A) ^ 2)
    {a b : ℕ} {x y : A}
    (hxa : x ∈ (kwCartier68a_augIdeal k A) ^ a)
    (hxa' : x ∉ (kwCartier68a_augIdeal k A) ^ (a + 1))
    (hyb : y ∈ (kwCartier68a_augIdeal k A) ^ b)
    (hyb' : y ∉ (kwCartier68a_augIdeal k A) ^ (b + 1)) :
    x * y ∉ (kwCartier68a_augIdeal k A) ^ (a + b + 1) := by
  set I := kwCartier68a_augIdeal k A
  obtain ⟨p, hp, hxp⟩ :=
    kwCartier68e_exists_homogeneous_aeval_congr_of_mem_pow hξI hξspan a x hxa
  obtain ⟨q, hq, hyq⟩ :=
    kwCartier68e_exists_homogeneous_aeval_congr_of_mem_pow hξI hξspan b y hyb
  have hp0 : p ≠ 0 := fun h => hxa' (by simpa only [h, map_zero, sub_zero] using hxp)
  have hq0 : q ≠ 0 := fun h => hyb' (by simpa only [h, map_zero, sub_zero] using hyq)
  have hcong : x * y - aeval ξ (p * q) ∈ I ^ (a + b + 1) := by
    have hexpand : x * y - aeval ξ (p * q)
        = (x - aeval ξ p) * y + aeval ξ p * (y - aeval ξ q) := by rw [map_mul]; ring
    rw [hexpand]
    refine Ideal.add_mem _ ?_ ?_
    · have h1 := Ideal.mul_mem_mul hxp hyb
      rwa [show I ^ (a + 1) * I ^ b = I ^ (a + b + 1) from by ring] at h1
    · have hpa : aeval ξ p ∈ I ^ a :=
        kwCartier68e_aeval_homogeneous_mem_augIdeal_pow hξI hp
      have h2 := Ideal.mul_mem_mul hpa hyq
      rwa [show I ^ a * I ^ (b + 1) = I ^ (a + b + 1) from by ring] at h2
  intro hxy
  have haepq : aeval ξ (p * q) ∈ I ^ (a + b + 1) := by
    have := Ideal.sub_mem _ hxy hcong; simpa only [sub_sub_cancel] using this
  exact kwCartier68e_aeval_homogeneous_not_mem_augIdeal_pow_succ hξI hξli
    (hp.mul hq) (mul_ne_zero hp0 hq0) haepq

end Surj
end CartierHopf

open CartierHopf in
theorem _root_.HopfAlgebra.mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A]
    {ι : Type*} [Fintype ι] {ξ : ι → A}
    (hξI : ∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom)
    (hξli : LinearIndependent K
      (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)))
    (hξspan : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
      ∃ c : ι → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2)
    {m n : ℕ} {x y : A}
    (hxm : x ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ m)
    (hxm' : x ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + 1))
    (hyn : y ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ n)
    (hyn' : y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (n + 1)) :
    x * y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + n + 1) :=
  kwCartier68e_mul_not_mem_pow_of_not_mem_pow (k := K) hξI hξli hξspan hxm hxm' hyn hyn'

end

end AbelianVarieties.NOSProofs.CartierFiltration
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.CartierCotangentBasis

open Bialgebra Coalgebra

noncomputable section

theorem _root_.HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    ∃ (n : ℕ) (ξ : Fin n → A),
      (∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ∧
      LinearIndependent K
        (fun i ↦ Ideal.Quotient.mk
          ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)) ∧
      (∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
        ∃ c : Fin n → K,
          a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) := by
  classical
  set I := RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom with hI
  have haugProj_mem : ∀ a : A, a - algebraMap K A (Coalgebra.counit (R := K) a) ∈ I := by
    intro a
    change Coalgebra.counit (R := K) (a - algebraMap K A (Coalgebra.counit (R := K) a)) = 0
    have hε1 : Coalgebra.counit (R := K) (algebraMap K A (Coalgebra.counit (R := K) a))
        = Coalgebra.counit (R := K) a := (Bialgebra.counitAlgHom K A).commutes _
    rw [map_sub, hε1, sub_self]
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  let Q := Ideal.Quotient.mk (I ^ 2)
  have hspanA : ∀ a ∈ I, Q a ∈ Submodule.span K (Q '' (↑s : Set A)) := by
    intro a ha
    have ha' : a ∈ Submodule.span A (↑s : Set A) := hs ▸ ha
    rw [Finsupp.mem_span_iff_linearCombination] at ha'
    obtain ⟨r, rfl⟩ := ha'
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Submodule.sum_mem _ fun j hj => ?_
    have hsmul : (r j • (↑j : A)) = r j * ↑j := rfl
    have hdecomp : r j * (↑j : A)
        = algebraMap K A (Coalgebra.counit (R := K) (r j)) * (↑j : A)
          + (r j - algebraMap K A (Coalgebra.counit (R := K) (r j))) * (↑j : A) := by ring
    have hjI : (↑j : A) ∈ I := hs ▸ Ideal.subset_span j.2
    have hI2 : (r j - algebraMap K A (Coalgebra.counit (R := K) (r j))) * (↑j : A) ∈ I ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (haugProj_mem (r j)) hjI
    rw [hsmul, hdecomp, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hI2, add_zero, map_mul]
    rw [show Q (algebraMap K A (Coalgebra.counit (R := K) (r j)))
        = algebraMap K (A ⧸ I^2) (Coalgebra.counit (R := K) (r j)) from rfl,
      ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨↑j, j.2, rfl⟩)
  let V : Submodule K (A ⧸ I ^ 2) := Submodule.span K (Q '' (↑s : Set A))
  have : Module.Finite K V := Module.Finite.span_of_finite K (s.finite_toSet.image _)
  let B := Module.Free.chooseBasis K V
  have : Fintype (Module.Free.ChooseBasisIndex K V) := inferInstance
  have hVsub : ∀ v ∈ V, ∃ a ∈ I, Q a = v := by
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨g, hg, rfl⟩; exact ⟨g, hs ▸ Ideal.subset_span hg, rfl⟩
    · exact ⟨0, I.zero_mem, map_zero Q⟩
    · rintro x y _ _ ⟨a, haI, rfl⟩ ⟨b, hbI, rfl⟩
      exact ⟨a + b, I.add_mem haI hbI, map_add Q a b⟩
    · rintro c x _ ⟨a, haI, rfl⟩
      refine ⟨c • a, ?_, map_smul (Ideal.Quotient.mkₐ K (I^2)) c a⟩
      rw [Algebra.smul_def]; exact I.mul_mem_left _ haI
  choose ξ' hξ'I hξ'Q using fun j => hVsub (B j).1 (B j).2
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex K V)).symm
  let n := Fintype.card (Module.Free.ChooseBasisIndex K V)
  refine ⟨n, fun i => ξ' (e i), fun i => hξ'I (e i), ?_, ?_⟩
  · have hBli' : LinearIndependent K (fun j => ((B j : V) : A ⧸ I^2)) :=
      B.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
    have hQξ' : (fun j => Q (ξ' j)) = (fun j => ((B j : V) : A ⧸ I^2)) := funext hξ'Q
    have : LinearIndependent K (fun j => Q (ξ' j)) := hQξ' ▸ hBli'
    exact this.comp e e.injective
  · intro a haI
    have haV : Q a ∈ V := hspanA a haI
    set v : V := ⟨Q a, haV⟩
    refine ⟨fun i => B.repr v (e i), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_sum]
    have hsubv : V.subtype v = ∑ j, B.repr v j • (B j : A ⧸ I^2) := by
      conv_lhs => rw [← B.sum_repr v]
      simp only [map_sum, map_smul, Submodule.coe_subtype]
    have hsumeq : Q a = ∑ i : Fin n, B.repr v (e i) • Q (ξ' (e i)) := by
      rw [show Q a = V.subtype v from rfl, hsubv, ← e.sum_comp]
      exact Finset.sum_congr rfl fun j _ => by rw [hξ'Q (e j)]
    rw [hsumeq]
    refine sub_eq_zero.mpr (Finset.sum_congr rfl fun i _ => ?_)
    exact (map_smul (Ideal.Quotient.mkₐ K (I^2)) (B.repr v (e i)) (ξ' (e i))).symm

end

end AbelianVarieties.NOSProofs.CartierCotangentBasis
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.CartierLocalDomain

open Bialgebra

noncomputable section

theorem _root_.HopfAlgebra.isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    have : (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).IsPrime :=
      RingHom.ker_isPrime (Bialgebra.counitAlgHom K A).toRingHom
    IsDomain (Localization.AtPrime (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom)) := by
  have hIp : (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).IsPrime :=
    RingHom.ker_isPrime (Bialgebra.counitAlgHom K A).toRingHom
  classical
  set I := RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom with hI
  set S := Localization.AtPrime I
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨d, ξ, hξI, hξli, hξspan⟩ :=
    HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType K A
  have hgr : ∀ {m n : ℕ} {x y : A}, x ∈ I ^ m → x ∉ I ^ (m + 1) → y ∈ I ^ n →
      y ∉ I ^ (n + 1) → x * y ∉ I ^ (m + n + 1) := fun {m n x y} hxm hxm' hyn hyn' =>
    HopfAlgebra.mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
      K A hξI hξli hξspan hxm hxm' hyn hyn'
  have hsat : ∀ {x y : A}, x ∉ I → ∀ N, x * y ∈ I ^ N → y ∈ I ^ N := by
    intro x y hx N hxy
    by_contra hyn
    have hne : ∃ j, y ∉ I ^ j := ⟨N, hyn⟩
    set m₀ := Nat.find hne
    have hym₀ : y ∉ I ^ m₀ := Nat.find_spec hne
    have hm₀N : m₀ ≤ N := Nat.find_le hyn
    have hm₀pos : 1 ≤ m₀ := by
      rcases Nat.eq_zero_or_pos m₀ with h0 | hp
      · exact absurd (by rw [h0, pow_zero, Ideal.one_eq_top]; exact trivial) hym₀
      · exact hp
    have hym₀' : y ∈ I ^ (m₀ - 1) :=
      not_not.mp (Nat.find_min hne (show m₀ - 1 < m₀ by omega))
    have hx0 : x ∈ I ^ 0 := by rw [pow_zero, Ideal.one_eq_top]; exact trivial
    have hx1 : x ∉ I ^ (0 + 1) := by rwa [zero_add, pow_one]
    have hym₀'' : y ∉ I ^ (m₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hm₀pos]
    have hnot : x * y ∉ I ^ (0 + (m₀ - 1) + 1) := hgr hx0 hx1 hym₀' hym₀''
    exact hnot (Ideal.pow_le_pow_right (by omega) hxy)
  have hKrullW : ∀ a : A, algebraMap A S a ≠ 0 → ∃ n, a ∉ I ^ n := by
    intro a ha
    set J := I.map (algebraMap A S) with hJ
    have hJmax : J = IsLocalRing.maximalIdeal S := by
      rw [hJ]; exact Localization.AtPrime.map_eq_maximalIdeal
    have hJne : J ≠ ⊤ := hJmax ▸ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    have hKrull : ⨅ n, J ^ n = ⊥ := J.iInf_pow_eq_bot_of_isLocalRing hJne
    have hnotbot : algebraMap A S a ∉ (⊥ : Ideal S) := by simpa only [Ideal.mem_bot] using ha
    rw [← hKrull, Ideal.mem_iInf] at hnotbot
    simp only [not_forall] at hnotbot
    obtain ⟨n, hn⟩ := hnotbot
    exact ⟨n, fun han => hn (by rw [hJ, ← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ han)⟩
  have hNZD : ∀ z w : S, z * w = 0 → z = 0 ∨ w = 0 := by
    intro z w hzw
    by_contra hc
    rw [not_or] at hc
    obtain ⟨hz, hw⟩ := hc
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl z
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl w
    rw [← IsLocalization.mk'_mul] at hzw
    obtain ⟨u, hu⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hzw
    have hab_all : ∀ N, a * b ∈ I ^ N := fun N =>
      hsat u.2 N (by rw [hu]; exact Ideal.zero_mem _)
    have haφ : algebraMap A S a ≠ 0 := fun h0 => hz <| by
      have hspec := IsLocalization.mk'_spec S a s
      rw [h0] at hspec
      exact (IsLocalization.map_units S s).mul_left_eq_zero.mp hspec
    have hbφ : algebraMap A S b ≠ 0 := fun h0 => hw <| by
      have hspec := IsLocalization.mk'_spec S b t
      rw [h0] at hspec
      exact (IsLocalization.map_units S t).mul_left_eq_zero.mp hspec
    obtain ⟨m, hm⟩ := hKrullW a haφ
    obtain ⟨n, hn⟩ := hKrullW b hbφ
    have hnea : ∃ j, a ∉ I ^ j := ⟨m, hm⟩
    have hneb : ∃ j, b ∉ I ^ j := ⟨n, hn⟩
    set m₀ := Nat.find hnea
    set n₀ := Nat.find hneb
    have ham₀ : a ∉ I ^ m₀ := Nat.find_spec hnea
    have hbn₀ : b ∉ I ^ n₀ := Nat.find_spec hneb
    have hm₀pos : 1 ≤ m₀ := by
      rcases Nat.eq_zero_or_pos m₀ with h0 | hp
      · exact absurd (by rw [h0, pow_zero, Ideal.one_eq_top]; exact trivial) ham₀
      · exact hp
    have hn₀pos : 1 ≤ n₀ := by
      rcases Nat.eq_zero_or_pos n₀ with h0 | hp
      · exact absurd (by rw [h0, pow_zero, Ideal.one_eq_top]; exact trivial) hbn₀
      · exact hp
    have ham₀' : a ∈ I ^ (m₀ - 1) :=
      not_not.mp (Nat.find_min hnea (show m₀ - 1 < m₀ by omega))
    have hbn₀' : b ∈ I ^ (n₀ - 1) :=
      not_not.mp (Nat.find_min hneb (show n₀ - 1 < n₀ by omega))
    have ham₀'' : a ∉ I ^ (m₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hm₀pos]
    have hbn₀'' : b ∉ I ^ (n₀ - 1 + 1) := by rwa [Nat.sub_add_cancel hn₀pos]
    exact hgr ham₀' ham₀'' hbn₀' hbn₀'' (hab_all _)
  have : NoZeroDivisors S := ⟨fun {a b} => hNZD a b⟩
  exact { }

end

end AbelianVarieties.NOSProofs.CartierLocalDomain
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties.NOSProofs.CartierRationalPoint

open Bialgebra

theorem _root_.HopfAlgebra.isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A]
    (χ : A →ₐ[K] K) :
    have : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime χ.toRingHom
    IsDomain (Localization.AtPrime (RingHom.ker χ.toRingHom)) := by
  have hMp : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime χ.toRingHom
  have hIp : (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).IsPrime :=
    RingHom.ker_isPrime (Bialgebra.counitAlgHom K A).toRingHom
  set I := RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom with hI
  set M := RingHom.ker χ.toRingHom with hM
  obtain ⟨e, hcomap⟩ :=
    HopfAlgebra.exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom K A χ
  rw [← hI, ← hM] at hcomap
  have hmap : M.primeCompl.map e.toRingEquiv.toMonoidHom = I.primeCompl := by
    have happ : ∀ b : A, e.toRingEquiv.toMonoidHom b = e.toRingEquiv.toRingHom b :=
      fun _ => rfl
    ext a
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe, ← hcomap, Ideal.mem_comap]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [happ]
    · intro ha
      refine ⟨e.symm a, ?_, e.toRingEquiv.apply_symm_apply a⟩
      rw [show e.toRingEquiv.toRingHom (e.symm a) = a from e.toRingEquiv.apply_symm_apply a]
      exact ha
  let E : Localization.AtPrime M ≃+* Localization.AtPrime I :=
    IsLocalization.ringEquivOfRingEquiv (M := M.primeCompl) (T := I.primeCompl)
      (Localization.AtPrime M) (Localization.AtPrime I) e.toRingEquiv hmap
  have : IsDomain (Localization.AtPrime I) :=
    HopfAlgebra.isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero K A
  exact Function.Injective.isDomain E.toRingHom E.injective

end AbelianVarieties.NOSProofs.CartierRationalPoint
end
