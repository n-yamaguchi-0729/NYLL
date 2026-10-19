/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Degree.TameCompletedTensorSplitting

/-! # Tame completed factors over the native function field of a rational curve

A rational coordinate is provided by an actual algebra equivalence with
`RatFunc K`. The original base field, its completion and all scalar maps
remain unchanged. This allows the literal curve-model function fields in
the finite Cartier family to use the normalized tame splitting directly.
-/

noncomputable section

open scoped WithZero Topology TensorProduct AlgebraicCurve.Place

namespace AlgebraicCurve.Place

variable {K B F : Type*} [Field K] [Field B] [Field F]
  [Algebra K B] [Algebra K F]

section Base

variable [Algebra B F] [IsScalarTower K B F] [Algebra.IsIntegral B F]

/-- Fixing a rational uniformizing coordinate fixes the entire native
completed base, by equality on its dense rational subfield. -/
theorem fixes_rational_completed_base_of_parameter
    (w : Place K F) (E : w.adicCompletion ≃ₐ[K] LaurentSeries K)
    (hEc : Continuous E) (e : ℕ)
    (p : RatFunc K ≃ₐ[K] B)
    (hEs : E (algebraMap F w.adicCompletion (algebraMap B F (p RatFunc.X))) =
      HahnSeries.single (e : ℤ) (1 : K))
    (f : LaurentSeries K →ₐ[K] LaurentSeries K)
    (hford : ∀ x, (f x).order = x.order)
    (hfs : f (HahnSeries.single (1 : ℤ) (1 : K) ^ e) =
      HahnSeries.single (1 : ℤ) (1 : K) ^ e)
    (a : (w.restrict B).adicCompletion) :
    f (E (algebraMap (w.restrict B).adicCompletion w.adicCompletion a)) =
      E (algebraMap (w.restrict B).adicCompletion w.adicCompletion a) := by
  let j : B →ₐ[K] w.adicCompletion :=
    (IsScalarTower.toAlgHom K F w.adicCompletion).comp
      (IsScalarTower.toAlgHom K B F)
  have hpower : HahnSeries.single (1 : ℤ) (1 : K) ^ e =
      HahnSeries.single (e : ℤ) (1 : K) := by
    rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  have hratq : (f.comp (E.toAlgHom.comp j)).comp p.toAlgHom =
      (E.toAlgHom.comp j).comp p.toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Polynomial K))
    apply Polynomial.algHom_ext
    change f (E (algebraMap F w.adicCompletion
      (algebraMap B F (p RatFunc.X)))) =
        E (algebraMap F w.adicCompletion (algebraMap B F (p RatFunc.X)))
    rw [hEs, ← hpower]
    exact hfs
  have hrat : f.comp (E.toAlgHom.comp j) = E.toAlgHom.comp j := by
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := p.surjective x
    exact AlgHom.congr_fun hratq y
  have hbasec : Continuous
      (algebraMap (w.restrict B).adicCompletion w.adicCompletion) :=
    continuous_adicCompletionComap B w
  refine (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap B
    (w.restrict B).heightOneSpectrum).induction_on a ?_ ?_
  · exact isClosed_eq
      ((LaurentSeries.continuous_of_order_preserving f.toRingHom hford).comp
        (hEc.comp hbasec)) (hEc.comp hbasec)
  · intro x
    rw [← adicCompletionComap_algebraMap_algebraMap B w]
    exact AlgHom.congr_fun hrat x


end Base

/-- The actual tame factor over a rational native base splits over its
normalized Laurent field, with every original source map retained. -/
theorem exists_tame_rational_completed_tensor_splitting [IsAlgClosed K]
    [Algebra B F] [IsScalarTower K B F]
    [FiniteDimensional B F] [Algebra.IsSeparable B F]
    [HasPrincipalDivisors K B] [HasPrincipalDivisors K F]
    (w : Place K F) (hw : w.deg = 1)
    (p : RatFunc K ≃ₐ[K] B)
    (hs : (w.restrict B).ord (p RatFunc.X) = 1)
    (he : ((w.ramificationIndex B : ℕ) : K) ≠ 0) :
    ∃ E : w.adicCompletion ≃ₐ[K] LaurentSeries K,
      E (algebraMap F w.adicCompletion (algebraMap B F (p RatFunc.X))) =
        HahnSeries.single (w.ramificationIndex B : ℤ) (1 : K) ∧
      Continuous E ∧
      let algL : Algebra (w.restrict B).adicCompletion (LaurentSeries K) :=
        (E.toRingHom.comp
          (algebraMap (w.restrict B).adicCompletion w.adicCompletion)).toAlgebra
      let _ : Module (w.restrict B).adicCompletion (LaurentSeries K) :=
        algL.toModule
      ∃ ι : Fin (w.ramificationIndex B) →
          w.adicCompletion →ₐ[(w.restrict B).adicCompletion] LaurentSeries K,
        Function.Injective ι ∧
        (∀ j x, (ι j (algebraMap F w.adicCompletion x)).order = w.ord x) ∧
        ∃ split : (LaurentSeries K ⊗[(w.restrict B).adicCompletion]
            w.adicCompletion) ≃ₐ[LaurentSeries K]
              (Fin (w.ramificationIndex B) → LaurentSeries K),
          ∀ a x j, split (a ⊗ₜ[(w.restrict B).adicCompletion] x) j =
            a * ι j x := by
  let e := w.ramificationIndex B
  have hs' : w.ord (algebraMap B F (p RatFunc.X)) = (e : ℤ) := by
    rw [w.ord_restrict, hs, mul_one]
  obtain ⟨E, hEs, hEc, hEord⟩ := w.exists_adicCompletion_tame_normalized hw
    (algebraMap B F (p RatFunc.X)) e he hs'
  refine ⟨E, hEs, hEc, ?_⟩
  intro algL modL
  obtain ⟨ρ, hρinj, hρord, hρs⟩ := LaurentSeries.exists_tame_parameter_embeddings e he
  have hbase (j : Fin e) (a : (w.restrict B).adicCompletion) :
      ρ j (E (algebraMap (w.restrict B).adicCompletion w.adicCompletion a)) =
        E (algebraMap (w.restrict B).adicCompletion w.adicCompletion a) :=
    w.fixes_rational_completed_base_of_parameter E hEc e p hEs (ρ j) (hρord j) (hρs j) a
  let ι (j : Fin e) :
      w.adicCompletion →ₐ[(w.restrict B).adicCompletion] LaurentSeries K :=
    { toRingHom := (ρ j).toRingHom.comp E.toRingHom
      commutes' a := hbase j a }
  have hιinj : Function.Injective ι := by
    intro i j hij
    apply hρinj
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := E.surjective x
    exact AlgHom.congr_fun hij y
  have hinertia : w.inertiaDeg B = 1 := by
    have h := w.deg_restrict_mul_inertiaDeg (F := B)
    rw [hw] at h
    exact Nat.eq_one_of_mul_eq_one_left h
  have hdegree : Module.finrank (w.restrict B).adicCompletion
      w.adicCompletion = e := by
    have h := w.finrank_adicCompletion_restrict (K := B)
    rw [hinertia, Nat.cast_one, mul_one] at h
    exact_mod_cast h
  let : Algebra.IsSeparable (w.restrict B).adicCompletion w.adicCompletion :=
    Place.isSeparable_fiberCompletion (w.restrict B)
      ⟨w, w.restrict_mem_fiber⟩
  obtain ⟨split, hsplit⟩ := Algebra.TensorProduct.exists_equiv_pi_of_embeddings
    e hdegree ι hιinj
  refine ⟨ι, hιinj, ?_, split, hsplit⟩
  intro j x
  exact (hρord j (E (algebraMap F w.adicCompletion x))).trans (hEord x)


end AlgebraicCurve.Place
