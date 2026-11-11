/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Frobenius.ScalarPowerRanges
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Trace

/-!
# The operator on the intrinsic scalar-power quotient

An endomorphism preserves the intersection of its scalar-power difference
images. It therefore acts on that intrinsic quotient. Intertwining linear
equivalences induce intertwining quotient equivalences and preserve the trace.
-/

@[expose] public section

noncomputable section

namespace LinearMap

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Every scalar-power difference image is preserved by the original
operator, and hence so is their intersection. -/
theorem map_mem_scalarPowerCore (F : Module.End K V) (a : K)
    {x : V} (hx : x ∈ scalarPowerCore F a) : F x ∈ scalarPowerCore F a := by
  simp only [scalarPowerCore, Submodule.mem_iInf] at hx ⊢
  intro n
  obtain ⟨y, hy⟩ := hx n
  refine ⟨F y, ?_⟩
  have hpow : (F ^ (n : ℕ)) (F y) = F ((F ^ (n : ℕ)) y) :=
    congrArg (fun T : Module.End K V => T y)
      ((pow_succ F (n : ℕ)).symm.trans (pow_succ' F (n : ℕ)))
  calc
    scalarPowerDifference F a n (F y) = F (scalarPowerDifference F a n y) := by
      change (F ^ (n : ℕ)) (F y) - a ^ (n : ℕ) • F y =
        F ((F ^ (n : ℕ)) y - a ^ (n : ℕ) • y)
      rw [map_sub, map_smul, hpow]
    _ = F x := congrArg F hy

/-- The original operator on its intrinsically specified quotient. -/
def scalarPowerQuotient (F : Module.End K V) (a : K) :
    Module.End K (V ⧸ scalarPowerCore F a) :=
  (scalarPowerCore F a).mapQ (scalarPowerCore F a) F
    (fun _ hx => map_mem_scalarPowerCore F a hx)

/-- The quotient operator is induced by the original operator. -/
theorem scalarPowerQuotient_mk (F : Module.End K V) (a : K) (x : V) :
    scalarPowerQuotient F a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (F x) := rfl

/-- An intertwining equivalence induces the original quotient equivalence. -/
def scalarPowerQuotientEquiv (F : Module.End K V) (G : Module.End K W)
    (e : V ≃ₗ[K] W) (he : ∀ x, e (F x) = G (e x)) (a : K) :
    (V ⧸ scalarPowerCore F a) ≃ₗ[K] (W ⧸ scalarPowerCore G a) :=
  Submodule.Quotient.equiv _ _ e (scalarPowerCore_map_eq F G e he a)

/-- Quotient transport is literally induced by the same ambient equivalence. -/
theorem scalarPowerQuotientEquiv_mk (F : Module.End K V) (G : Module.End K W)
    (e : V ≃ₗ[K] W) (he : ∀ x, e (F x) = G (e x)) (a : K) (x : V) :
    scalarPowerQuotientEquiv F G e he a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := rfl

/-- The induced equivalence intertwines the induced operators. -/
theorem scalarPowerQuotientEquiv_intertwines
    (F : Module.End K V) (G : Module.End K W)
    (e : V ≃ₗ[K] W) (he : ∀ x, e (F x) = G (e x)) (a : K)
    (x : V ⧸ scalarPowerCore F a) :
    scalarPowerQuotientEquiv F G e he a (scalarPowerQuotient F a x) =
      scalarPowerQuotient G a (scalarPowerQuotientEquiv F G e he a x) := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro v
  change Submodule.Quotient.mk (e (F v)) = Submodule.Quotient.mk (G (e v))
  exact congrArg (Submodule.Quotient.mk : W → W ⧸ scalarPowerCore G a) (he v)

/-- Trace on the intrinsic quotient is preserved by the same ambient
intertwining equivalence, without choosing a splitting. -/
theorem trace_scalarPowerQuotient_eq_of_equivariant
    (F : Module.End K V) (G : Module.End K W)
    (e : V ≃ₗ[K] W) (he : ∀ x, e (F x) = G (e x)) (a : K) :
    trace K (V ⧸ scalarPowerCore F a) (scalarPowerQuotient F a) =
      trace K (W ⧸ scalarPowerCore G a) (scalarPowerQuotient G a) := by
  let E := scalarPowerQuotientEquiv F G e he a
  have hconj : E.conj (scalarPowerQuotient F a) = scalarPowerQuotient G a := by
    apply LinearMap.ext
    intro y
    change E (scalarPowerQuotient F a (E.symm y)) = scalarPowerQuotient G a y
    rw [scalarPowerQuotientEquiv_intertwines F G e he a, E.apply_symm_apply]
  rw [← hconj]
  exact (LinearMap.trace_conj' (scalarPowerQuotient F a) E).symm

end LinearMap
