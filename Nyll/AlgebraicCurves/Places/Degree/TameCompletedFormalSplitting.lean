/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Places.Degree.TameRationalCompletedTensorSplitting
import Nyll.SchemeTheory.Normalization.FormalFieldFiberSplitting

/-! # The formal fibre of an actual tame completed boundary factor

The tame completed-field theorem constructs the residue embeddings. Their
formal lifts split the actual spectrum pullback for the chosen deformation
of the native completed base, over the same Laurent coefficient field.
The deformation is allowed to be the one constructed from the regular block;
no separate deformation of the completed source field is chosen here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicCurve.Place

namespace AlgebraicCurve.Place

universe u

variable {K B F : Type u} [Field K] [Field B] [Field F]
  [Algebra K B] [Algebra K F]

/-- The actual tame completed factor has a labelled formal splitting for
every deformation of its native completed base. The embeddings, their
normalization, and the spectrum splitting are constructed internally. -/
theorem exists_tame_completed_formal_fibre [IsAlgClosed K]
    [Algebra B F] [IsScalarTower K B F]
    [FiniteDimensional B F] [Algebra.IsSeparable B F]
    [HasPrincipalDivisors K B] [HasPrincipalDivisors K F]
    (w : Place K F) (hw : w.deg = 1)
    (p : RatFunc K ≃ₐ[K] B)
    (hs : (w.restrict B).ord (p RatFunc.X) = 1)
    (he : ((w.ramificationIndex B : ℕ) : K) ≠ 0) :
    let _ : Algebra.IsSeparable (w.restrict B).adicCompletion w.adicCompletion :=
      Place.isSeparable_fiberCompletion (w.restrict B) ⟨w, w.restrict_mem_fiber⟩
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
        (∀ j, ι j (algebraMap F w.adicCompletion
            (algebraMap B F (p RatFunc.X))) =
          HahnSeries.single (w.ramificationIndex B : ℤ) (1 : K)) ∧
        ∀ (τ : (w.restrict B).adicCompletion →+*
            PowerSeries (LaurentSeries K))
          (hτ : PowerSeries.constantCoeff.comp τ =
            algebraMap (w.restrict B).adicCompletion (LaurentSeries K)),
          ∃ d : (∐ fun _ : Fin (w.ramificationIndex B) =>
              Spec (.of (PowerSeries (LaurentSeries K)))) ≅
              pullback (Spec.map (CommRingCat.ofHom
                  (algebraMap (w.restrict B).adicCompletion w.adicCompletion)))
                (Spec.map (CommRingCat.ofHom τ)),
            d.hom ≫ pullback.snd
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (w.restrict B).adicCompletion w.adicCompletion)))
                (Spec.map (CommRingCat.ofHom τ)) =
              Sigma.desc (fun _ : Fin (w.ramificationIndex B) =>
                𝟙 (Spec (.of (PowerSeries (LaurentSeries K))))) ∧
            ∀ j : Fin (w.ramificationIndex B),
              Sigma.ι (fun _ : Fin (w.ramificationIndex B) =>
                  Spec (.of (PowerSeries (LaurentSeries K)))) j ≫
                d.hom ≫ pullback.fst
                  (Spec.map (CommRingCat.ofHom
                    (algebraMap (w.restrict B).adicCompletion w.adicCompletion)))
                  (Spec.map (CommRingCat.ofHom τ)) =
                Spec.map (CommRingCat.ofHom
                  (PowerSeries.formalEmbeddingLift τ hτ (ι j))) := by
  intro sep
  obtain ⟨E, hEs, hEc, hsplit⟩ :=
    w.exists_tame_rational_completed_tensor_splitting hw p hs he
  refine ⟨E, hEs, hEc, ?_⟩
  intro algL modL
  obtain ⟨ι, hι, horder, _split, _hformula⟩ := hsplit
  have hnormal (j : Fin (w.ramificationIndex B)) :
      ι j (algebraMap F w.adicCompletion
          (algebraMap B F (p RatFunc.X))) =
        HahnSeries.single (w.ramificationIndex B : ℤ) (1 : K) := by
    rw [adicCompletionComap_algebraMap_algebraMap B w, (ι j).commutes]
    change E (algebraMap (w.restrict B).adicCompletion w.adicCompletion
      (algebraMap B (w.restrict B).adicCompletion (p RatFunc.X))) = _
    rw [← adicCompletionComap_algebraMap_algebraMap B w]
    exact hEs
  have hinertia : w.inertiaDeg B = 1 := by
    have h := w.deg_restrict_mul_inertiaDeg (F := B)
    rw [hw] at h
    exact Nat.eq_one_of_mul_eq_one_left h
  have hdegree : Module.finrank (w.restrict B).adicCompletion
      w.adicCompletion = w.ramificationIndex B := by
    have h := w.finrank_adicCompletion_restrict (K := B)
    rw [hinertia, Nat.cast_one, mul_one] at h
    exact_mod_cast h
  refine ⟨ι, hι, horder, hnormal, ?_⟩
  intro τ hτ
  exact Scheme.exists_formal_field_fiber_coprod_iso
    (w.ramificationIndex B) hdegree ι hι τ hτ

end AlgebraicCurve.Place
