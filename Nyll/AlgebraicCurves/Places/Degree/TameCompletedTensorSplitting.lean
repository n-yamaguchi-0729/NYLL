/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Henselian.LaurentRootOfUnityAutomorphisms
import Nyll.SchemeTheory.RingTheory.Henselian.TensorSplittingOfEmbeddings
import Nyll.AlgebraicCurves.Places.Degree.LaurentCompletionDegEqOne
import Nyll.AlgebraicCurves.FunctionFields.NormTrace.CompletionTraceSumSeparable

/-! # Actual splitting of a tame completed curve-field factor

A degree-one completed place is normalized so the specified rational base
parameter becomes the exact tame power of the Laurent parameter. Rescaling
by roots of unity fixes the whole completed base: continuity extends equality
from its dense rational-function subfield. The actual completion degree is
the ramification index, so evaluation in these embeddings splits the tensor.
-/

noncomputable section

open scoped WithZero Topology TensorProduct AlgebraicCurve.Place

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- An order-preserving Laurent field map preserves its native valuation. -/
theorem valuation_eq_of_order_preserving
    (f : LaurentSeries K →+* LaurentSeries K)
    (hf : ∀ x, (f x).order = x.order) (x : LaurentSeries K) :
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (f x) = Valued.v x := by
  by_cases hx : x = 0
  · subst x
    rw [map_zero, map_zero]
  have hfx : f x ≠ 0 := (map_ne_zero_iff f f.injective).mpr hx
  have hxlog := (orderPlace (K := K)).ord_eq_neg_log_of_valuationSubring_eq
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) rfl
    (valuation_single_zpow K 1) hx
  have hfxlog := (orderPlace (K := K)).ord_eq_neg_log_of_valuationSubring_eq
    (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) rfl
    (valuation_single_zpow K 1) hfx
  rw [orderPlace_ord] at hxlog hfxlog
  rw [hf x] at hfxlog
  have hvx : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) x ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hx
  have hvfx : (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰) (f x) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hfx
  rw [← WithZero.exp_log hvfx, ← WithZero.exp_log hvx]
  congr 1
  omega

/-- Order preservation gives continuity for the actual Laurent topology. -/
theorem continuous_of_order_preserving
    (f : LaurentSeries K →+* LaurentSeries K)
    (hf : ∀ x, (f x).order = x.order) : Continuous f := by
  apply (uniformContinuous_of_continuousAt_zero f ?_).continuous
  simp_rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero (LaurentSeries K) ℤᵐ⁰).tendsto_iff
      (Valued.hasBasis_nhds_zero (LaurentSeries K) ℤᵐ⁰), true_and, forall_const]
  intro γ
  refine ⟨γ, fun x hx => ?_⟩
  apply (Valued.v.restrict_lt_iff_lt_embedding).mpr
  rw [valuation_eq_of_order_preserving f hf]
  exact (Valued.v.restrict_lt_iff_lt_embedding).mp hx

end LaurentSeries

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The actual completed field can be normalized at any tame positive-order
function. Both the parameter equation and the original field orders are retained. -/
theorem exists_adicCompletion_tame_normalized [IsAlgClosed K]
    (w : Place K F) (hw : w.deg = 1) (s : F) (e : ℕ)
    (he : (e : K) ≠ 0) (hs : w.ord s = (e : ℤ)) :
    ∃ E : w.adicCompletion ≃ₐ[K] LaurentSeries K,
      E (algebraMap F w.adicCompletion s) = HahnSeries.single (e : ℤ) (1 : K) ∧
      Continuous E ∧
      ∀ x : F, (E (algebraMap F w.adicCompletion x)).order = w.ord x := by
  obtain ⟨t, ht⟩ := w.exists_ord_eq_one
  obtain ⟨E₀, _hE₀t, hE₀ord, hE₀c, _hE₀ic, _hE₀v⟩ :=
    w.exists_adicCompletion_algEquiv_laurentSeries_of_deg_eq_one hw t ht
  obtain ⟨A, hAs, hAord⟩ := LaurentSeries.exists_tameNormalization
    (E₀ (algebraMap F w.adicCompletion s)) e he ((hE₀ord s).trans hs)
  refine ⟨E₀.trans A, hAs, ?_, ?_⟩
  · exact (LaurentSeries.continuous_of_order_preserving A.toRingHom hAord).comp hE₀c
  · intro x
    exact (hAord (E₀ (algebraMap F w.adicCompletion x))).trans (hE₀ord x)

section RationalBase

variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [Algebra.IsIntegral (RatFunc K) F]

/-- Fixing the exact normalized base parameter fixes the entire actual
completed base. The rational coordinate is reparametrized by an actual
algebra automorphism; the native completed-base algebra is unchanged.
Equality on its rational subfield extends along the dense completion map. -/
theorem fixes_completed_base_of_parameter
    (w : Place K F) (E : w.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hEc : Continuous E) (e : ℕ)
    (q : RatFunc K ≃ₐ[K] RatFunc K)
    (hEs : E (algebraMap F w.adicCompletion (algebraMap (RatFunc K) F (q RatFunc.X))) =
      HahnSeries.single (e : ℤ) (1 : K))
    (f : LaurentSeries K →ₐ[K] LaurentSeries K)
    (hford : ∀ x, (f x).order = x.order)
    (hfs : f (HahnSeries.single (1 : ℤ) (1 : K) ^ e) =
      HahnSeries.single (1 : ℤ) (1 : K) ^ e)
    (a : (w.restrict (RatFunc K)).adicCompletion) :
    f (E (algebraMap (w.restrict (RatFunc K)).adicCompletion w.adicCompletion a)) =
      E (algebraMap (w.restrict (RatFunc K)).adicCompletion w.adicCompletion a) := by
  let j : RatFunc K →ₐ[K] w.adicCompletion :=
    (IsScalarTower.toAlgHom K F w.adicCompletion).comp
      (IsScalarTower.toAlgHom K (RatFunc K) F)
  have hpower : HahnSeries.single (1 : ℤ) (1 : K) ^ e =
      HahnSeries.single (e : ℤ) (1 : K) := by
    rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  have hratq : (f.comp (E.toAlgHom.comp j)).comp q.toAlgHom =
      (E.toAlgHom.comp j).comp q.toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    change f (E (algebraMap F w.adicCompletion
      (algebraMap (RatFunc K) F (q RatFunc.X)))) =
        E (algebraMap F w.adicCompletion (algebraMap (RatFunc K) F (q RatFunc.X)))
    rw [hEs, ← hpower]
    exact hfs
  have hrat : f.comp (E.toAlgHom.comp j) = E.toAlgHom.comp j := by
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := q.surjective x
    exact AlgHom.congr_fun hratq y
  have hbasec : Continuous
      (algebraMap (w.restrict (RatFunc K)).adicCompletion w.adicCompletion) :=
    continuous_adicCompletionComap (RatFunc K) w
  refine (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (RatFunc K)
    (w.restrict (RatFunc K)).heightOneSpectrum).induction_on a ?_ ?_
  · exact isClosed_eq
      ((LaurentSeries.continuous_of_order_preserving f.toRingHom hford).comp
        (hEc.comp hbasec)) (hEc.comp hbasec)
  · intro x
    rw [← adicCompletionComap_algebraMap_algebraMap (RatFunc K) w]
    exact AlgHom.congr_fun hrat x

end RationalBase

/-- A degree-one tame completed factor splits over its actual normalized
Laurent field into exactly `ramificationIndex` copies. Base-linearity,
completed degree, and the splitting equivalence are all constructed. The
normalizing coordinate `q X` may be the inverse of the original trace
coordinate, without changing the original rational-function algebra. -/
theorem exists_tame_completed_tensor_splitting [IsAlgClosed K]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    [HasPrincipalDivisors K (RatFunc K)] [HasPrincipalDivisors K F]
    (w : Place K F) (hw : w.deg = 1)
    (q : RatFunc K ≃ₐ[K] RatFunc K)
    (hs : (w.restrict (RatFunc K)).ord (q RatFunc.X) = 1)
    (he : ((w.ramificationIndex (RatFunc K) : ℕ) : K) ≠ 0) :
    ∃ E : w.adicCompletion ≃ₐ[K] LaurentSeries K,
      E (algebraMap F w.adicCompletion (algebraMap (RatFunc K) F (q RatFunc.X))) =
        HahnSeries.single (w.ramificationIndex (RatFunc K) : ℤ) (1 : K) ∧
      Continuous E ∧
      let algL : Algebra (w.restrict (RatFunc K)).adicCompletion (LaurentSeries K) :=
        (E.toRingHom.comp
          (algebraMap (w.restrict (RatFunc K)).adicCompletion w.adicCompletion)).toAlgebra
      let _ : Module (w.restrict (RatFunc K)).adicCompletion (LaurentSeries K) :=
        algL.toModule
      ∃ ι : Fin (w.ramificationIndex (RatFunc K)) →
          w.adicCompletion →ₐ[(w.restrict (RatFunc K)).adicCompletion] LaurentSeries K,
        Function.Injective ι ∧
        (∀ j x, (ι j (algebraMap F w.adicCompletion x)).order = w.ord x) ∧
        ∃ split : (LaurentSeries K ⊗[(w.restrict (RatFunc K)).adicCompletion]
            w.adicCompletion) ≃ₐ[LaurentSeries K]
              (Fin (w.ramificationIndex (RatFunc K)) → LaurentSeries K),
          ∀ a x j, split (a ⊗ₜ[(w.restrict (RatFunc K)).adicCompletion] x) j =
            a * ι j x := by
  let e := w.ramificationIndex (RatFunc K)
  have hs' : w.ord (algebraMap (RatFunc K) F (q RatFunc.X)) = (e : ℤ) := by
    rw [w.ord_restrict, hs, mul_one]
  obtain ⟨E, hEs, hEc, hEord⟩ := w.exists_adicCompletion_tame_normalized hw
    (algebraMap (RatFunc K) F (q RatFunc.X)) e he hs'
  refine ⟨E, hEs, hEc, ?_⟩
  intro algL modL
  obtain ⟨ρ, hρinj, hρord, hρs⟩ := LaurentSeries.exists_tame_parameter_embeddings e he
  have hbase (j : Fin e) (a : (w.restrict (RatFunc K)).adicCompletion) :
      ρ j (E (algebraMap (w.restrict (RatFunc K)).adicCompletion w.adicCompletion a)) =
        E (algebraMap (w.restrict (RatFunc K)).adicCompletion w.adicCompletion a) :=
    w.fixes_completed_base_of_parameter E hEc e q hEs (ρ j) (hρord j) (hρs j) a
  let ι (j : Fin e) :
      w.adicCompletion →ₐ[(w.restrict (RatFunc K)).adicCompletion] LaurentSeries K :=
    { toRingHom := (ρ j).toRingHom.comp E.toRingHom
      commutes' a := hbase j a }
  have hιinj : Function.Injective ι := by
    intro i j hij
    apply hρinj
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := E.surjective x
    exact AlgHom.congr_fun hij y
  have hinertia : w.inertiaDeg (RatFunc K) = 1 := by
    have h := w.deg_restrict_mul_inertiaDeg (F := RatFunc K)
    rw [hw] at h
    exact Nat.eq_one_of_mul_eq_one_left h
  have hdegree : Module.finrank (w.restrict (RatFunc K)).adicCompletion
      w.adicCompletion = e := by
    have h := w.finrank_adicCompletion_restrict (K := RatFunc K)
    rw [hinertia, Nat.cast_one, mul_one] at h
    exact_mod_cast h
  let : Algebra.IsSeparable (w.restrict (RatFunc K)).adicCompletion w.adicCompletion :=
    Place.isSeparable_fiberCompletion (w.restrict (RatFunc K))
      ⟨w, w.restrict_mem_fiber⟩
  obtain ⟨split, hsplit⟩ := Algebra.TensorProduct.exists_equiv_pi_of_embeddings
    e hdegree ι hιinj
  refine ⟨ι, hιinj, ?_, split, hsplit⟩
  intro j x
  exact (hρord j (E (algebraMap F w.adicCompletion x))).trans (hEord x)

end AlgebraicCurve.Place
