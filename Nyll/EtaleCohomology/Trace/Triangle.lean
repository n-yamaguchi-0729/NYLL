/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Trace.Hopf
public import Nyll.EtaleCohomology.Trace.Perfect
public import Nyll.EtaleCohomology.Trace.PerfectHomology
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace additivity for actual distinguished triangles

The three exact pieces of the native derived cohomology sequence express
the cohomology traces in terms of the traces on their images. The images
of the connecting maps cancel in the alternating sum. Perfect models
supply finiteness and bounded support for the actual cohomology modules.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory Limits Pretriangulated

namespace EtaleCohomology

variable {k : Type u} [Field k]
variable [HasDerivedCategory.{w} (ModuleCat.{v} k)]

omit [HasDerivedCategory.{w} (ModuleCat.{v} k)] in
private lemma trace_exact_shortComplex (S : ShortComplex (ModuleCat.{v} k))
    [Module.Finite k S.X₂]
    (hS : S.Exact) (φ : S ⟶ S) :
    LinearMap.trace k S.X₂ φ.τ₂.hom =
      LinearMap.trace k S.f.hom.range
        (rangeEndomorphism S.f φ.τ₁ φ.τ₂ φ.comm₁₂).hom +
      LinearMap.trace k S.g.hom.range
        (rangeEndomorphism S.g φ.τ₂ φ.τ₃ φ.comm₂₃).hom := by
  have hz : IsZero S.homology := S.exact_iff_isZero_homology.mp hS
  have hm : ShortComplex.homologyMap φ = 0 := hz.eq_of_src _ _
  simpa only [hm, ModuleCat.hom_zero, map_zero, zero_add] using trace_shortComplex S φ

private def derivedHomologyTrace (A : DerivedCategory (ModuleCat.{v} k))
    (f : A ⟶ A) (i : ℤ) : k :=
  LinearMap.trace k ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A)
    ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f).hom

private lemma perfect_homology_isZero_outside
    {A : DerivedCategory (ModuleCat.{v} k)} (P : PerfectComplexModel k A)
    (i : ℤ) (hi : i ∉ Set.Icc P.lower P.upper) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj A) := by
  apply (P.homologyIso i).isZero_iff.mp
  by_cases hl : i < P.lower
  · exact P.complex.isZero_of_isGE P.lower i hl
  · have hr : P.upper < i := by
      simp only [Set.mem_Icc] at hi
      omega
    exact P.complex.isZero_of_isLE P.upper i hr

private lemma signedDerivedHomologyTrace_finite
    {A : DerivedCategory (ModuleCat.{v} k)} (hA : IsPerfectComplex k A) (f : A ⟶ A) :
    Function.HasFiniteSupport (fun i : ℤ => i.negOnePow • derivedHomologyTrace A f i) := by
  let P := Classical.choice hA
  apply (Set.finite_Icc P.lower P.upper).subset
  intro i hi
  by_contra hout
  have hz := perfect_homology_isZero_outside P i hout
  have hf : (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map f = 0 :=
    hz.eq_of_src _ _
  exact (Function.mem_support.mp hi) (by
    dsimp only [derivedHomologyTrace]
    rw [hf, ModuleCat.hom_zero, map_zero, smul_zero])

private lemma triangle_homology_comm₁
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (φ : T ⟶ T) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map φ.hom₁ ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map T.mor₁ =
      (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map T.mor₁ ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map φ.hom₂ := by
  rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁]

private lemma triangle_homology_comm₂
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (φ : T ⟶ T) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map φ.hom₂ ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map T.mor₂ =
      (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map T.mor₂ ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map φ.hom₃ := by
  rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂]

private lemma triangle_homology_commδ
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (φ : T ⟶ T)
    (i j : ℤ) (h : i + 1 = j) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map φ.hom₃ ≫
        DerivedCategory.HomologySequence.δ T i j h =
      DerivedCategory.HomologySequence.δ T i j h ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{v} k) j).map φ.hom₁ :=
  Functor.homologySequenceδ_naturality
    (DerivedCategory.homologyFunctor (ModuleCat.{v} k) 0) φ i j h

private def connectingRangeTraceAt
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (φ : T ⟶ T)
    (i j : ℤ) (h : i + 1 = j) : k :=
  LinearMap.trace k (DerivedCategory.HomologySequence.δ T i j h).hom.range
    (rangeEndomorphism (DerivedCategory.HomologySequence.δ T i j h)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map φ.hom₃)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) j).map φ.hom₁)
      (triangle_homology_commδ T φ i j h)).hom

private def connectingRangeTrace
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (φ : T ⟶ T) (i : ℤ) : k :=
  connectingRangeTraceAt T φ i (i + 1) rfl

private lemma connectingRangeTraceAt_eq
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (φ : T ⟶ T)
    (i j : ℤ) (h : i + 1 = j) :
    connectingRangeTraceAt T φ i j h = connectingRangeTrace T φ i := by
  subst j
  rfl

private lemma connectingRangeTrace_eq_zero
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (φ : T ⟶ T) (i : ℤ)
    (hi : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).obj T.obj₃)) :
    connectingRangeTrace T φ i = 0 := by
  have hd : DerivedCategory.HomologySequence.δ T i (i + 1) rfl = 0 :=
    hi.eq_of_src _ _
  have hr : rangeEndomorphism (DerivedCategory.HomologySequence.δ T i (i + 1) rfl)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) i).map φ.hom₃)
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) (i + 1)).map φ.hom₁)
      (triangle_homology_commδ T φ i (i + 1) rfl) = 0 := by
    ext x
    obtain ⟨y, hy⟩ := x.property
    have hx : x.val = 0 := by
      rw [← hy, hd]
      rfl
    change ((DerivedCategory.homologyFunctor (ModuleCat.{v} k) (i + 1)).map φ.hom₁).hom
      x.val = 0
    rw [hx, map_zero]
  dsimp only [connectingRangeTrace, connectingRangeTraceAt]
  rw [hr, ModuleCat.hom_zero, map_zero]

private lemma signedConnectingRangeTrace_finite
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (φ : T ⟶ T)
    (h₃ : IsPerfectComplex k T.obj₃) :
    Function.HasFiniteSupport (fun i : ℤ => i.negOnePow • connectingRangeTrace T φ i) := by
  let P := Classical.choice h₃
  apply (Set.finite_Icc P.lower P.upper).subset
  intro i hi
  by_contra hout
  have hz := perfect_homology_isZero_outside P i hout
  exact (Function.mem_support.mp hi) (by
    rw [connectingRangeTrace_eq_zero T φ i hz, smul_zero])

private lemma triangle_trace_degree
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (hT : T ∈ distTriang _)
    (h₁ : IsPerfectComplex k T.obj₁) (h₂ : IsPerfectComplex k T.obj₂)
    (h₃ : IsPerfectComplex k T.obj₃) (φ : T ⟶ T) (i : ℤ) :
    derivedHomologyTrace T.obj₂ φ.hom₂ i +
        connectingRangeTrace T φ (i - 1) + connectingRangeTrace T φ i =
      derivedHomologyTrace T.obj₁ φ.hom₁ i + derivedHomologyTrace T.obj₃ φ.hom₃ i := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} k)
  let u := (H i).map T.mor₁
  let v := (H i).map T.mor₂
  let α := (H i).map φ.hom₁
  let β := (H i).map φ.hom₂
  let γ := (H i).map φ.hom₃
  let U := LinearMap.trace k u.hom.range
    (rangeEndomorphism u α β (triangle_homology_comm₁ T φ i)).hom
  let V := LinearMap.trace k v.hom.range
    (rangeEndomorphism v β γ (triangle_homology_comm₂ T φ i)).hom
  have : Module.Finite k ((H i).obj T.obj₁) := (Classical.choice h₁).finite_homology i
  have : Module.Finite k ((H (i + 1)).obj T.obj₁) :=
    (Classical.choice h₁).finite_homology (i + 1)
  have : Module.Finite k ((H i).obj T.obj₂) := (Classical.choice h₂).finite_homology i
  have : Module.Finite k ((H i).obj T.obj₃) := (Classical.choice h₃).finite_homology i
  have hcomp : u ≫ v = 0 := by
    dsimp only [u, v]
    rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero]
  let S₂ : ShortComplex (ModuleCat.{v} k) := ShortComplex.mk u v hcomp
  let ψ₂ : S₂ ⟶ S₂ :=
    { τ₁ := α
      τ₂ := β
      τ₃ := γ
      comm₁₂ := triangle_homology_comm₁ T φ i
      comm₂₃ := triangle_homology_comm₂ T φ i }
  have hex₂ : S₂.Exact := DerivedCategory.HomologySequence.exact₂ T hT i
  have hb : derivedHomologyTrace T.obj₂ φ.hom₂ i = U + V :=
    trace_exact_shortComplex S₂ hex₂ ψ₂
  let S₃ : ShortComplex (ModuleCat.{v} k) := ShortComplex.mk v
    (DerivedCategory.HomologySequence.δ T i (i + 1) rfl)
    (DerivedCategory.HomologySequence.comp_δ T hT i (i + 1) rfl)
  let ψ₃ : S₃ ⟶ S₃ :=
    { τ₁ := β
      τ₂ := γ
      τ₃ := (H (i + 1)).map φ.hom₁
      comm₁₂ := triangle_homology_comm₂ T φ i
      comm₂₃ := triangle_homology_commδ T φ i (i + 1) rfl }
  have hex₃ : S₃.Exact := DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl
  have hc : derivedHomologyTrace T.obj₃ φ.hom₃ i = V + connectingRangeTrace T φ i :=
    trace_exact_shortComplex S₃ hex₃ ψ₃
  have hprev : i - 1 + 1 = i := sub_add_cancel i 1
  let S₁ : ShortComplex (ModuleCat.{v} k) := ShortComplex.mk
    (DerivedCategory.HomologySequence.δ T (i - 1) i hprev) u
    (DerivedCategory.HomologySequence.δ_comp T hT (i - 1) i hprev)
  let ψ₁ : S₁ ⟶ S₁ :=
    { τ₁ := (H (i - 1)).map φ.hom₃
      τ₂ := α
      τ₃ := β
      comm₁₂ := triangle_homology_commδ T φ (i - 1) i hprev
      comm₂₃ := triangle_homology_comm₁ T φ i }
  have hex₁ : S₁.Exact := DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i hprev
  have ha : derivedHomologyTrace T.obj₁ φ.hom₁ i =
      connectingRangeTraceAt T φ (i - 1) i hprev + U :=
    trace_exact_shortComplex S₁ hex₁ ψ₁
  rw [connectingRangeTraceAt_eq] at ha
  rw [ha, hb, hc]
  abel

/-- The intrinsic perfect trace is additive for an endomorphism of an
actual distinguished triangle. Exactness and connecting-map naturality
are supplied by the native derived cohomology sequence. -/
theorem perfectComplexTrace_triangle
    (T : Triangle (DerivedCategory (ModuleCat.{v} k))) (hT : T ∈ distTriang _)
    (h₁ : IsPerfectComplex k T.obj₁) (h₂ : IsPerfectComplex k T.obj₂)
    (h₃ : IsPerfectComplex k T.obj₃) (φ : T ⟶ T) :
    perfectComplexTrace k T.obj₂ h₂ φ.hom₂ =
      perfectComplexTrace k T.obj₁ h₁ φ.hom₁ +
        perfectComplexTrace k T.obj₃ h₃ φ.hom₃ := by
  let a : ℤ → k := fun i => i.negOnePow • derivedHomologyTrace T.obj₁ φ.hom₁ i
  let b : ℤ → k := fun i => i.negOnePow • derivedHomologyTrace T.obj₂ φ.hom₂ i
  let c : ℤ → k := fun i => i.negOnePow • derivedHomologyTrace T.obj₃ φ.hom₃ i
  let p : ℤ → k := fun i => i.negOnePow • connectingRangeTrace T φ i
  let q : ℤ → k := fun i => -(p (i - 1))
  have ha : Function.HasFiniteSupport a := signedDerivedHomologyTrace_finite h₁ φ.hom₁
  have hb : Function.HasFiniteSupport b := signedDerivedHomologyTrace_finite h₂ φ.hom₂
  have hc : Function.HasFiniteSupport c := signedDerivedHomologyTrace_finite h₃ φ.hom₃
  have hp : Function.HasFiniteSupport p := signedConnectingRangeTrace_finite T φ h₃
  have hbij : Function.Bijective (fun i : ℤ => i - 1) := by
    constructor
    · intro i j hij
      change i - 1 = j - 1 at hij
      omega
    · intro i
      refine ⟨i + 1, ?_⟩
      change i + 1 - 1 = i
      omega
  have hq : Function.HasFiniteSupport q :=
    (hp.comp_of_injective hbij.injective).neg
  have hdegree (i : ℤ) : b i + q i + p i = a i + c i := by
    have hsign : i.negOnePow = -(i - 1).negOnePow :=
      (congrArg Int.negOnePow (sub_add_cancel i 1)).symm.trans
        (Int.negOnePow_succ (i - 1))
    have heq := congrArg (fun x : k => i.negOnePow • x)
      (triangle_trace_degree T hT h₁ h₂ h₃ φ i)
    rw [smul_add, smul_add, smul_add] at heq
    change b i + i.negOnePow • connectingRangeTrace T φ (i - 1) + p i = a i + c i at heq
    rw [hsign, Units.neg_smul] at heq
    exact heq
  have htotal := finsum_congr hdegree
  have hs₁ : (∑ᶠ i : ℤ, (b i + q i + p i)) =
      (∑ᶠ i : ℤ, (b i + q i)) + ∑ᶠ i : ℤ, p i :=
    finsum_add_distrib (hb.add hq) hp
  have hs₂ : (∑ᶠ i : ℤ, (b i + q i)) =
      (∑ᶠ i : ℤ, b i) + ∑ᶠ i : ℤ, q i := finsum_add_distrib hb hq
  have hs₃ : (∑ᶠ i : ℤ, (a i + c i)) =
      (∑ᶠ i : ℤ, a i) + ∑ᶠ i : ℤ, c i := finsum_add_distrib ha hc
  have hcancel : (∑ᶠ i : ℤ, q i) = -(∑ᶠ i : ℤ, p i) := by
    dsimp only [q]
    rw [finsum_neg_distrib, finsum_comp (fun i : ℤ => i - 1) hbij]
  rw [hs₁, hs₂, hs₃, hcancel] at htotal
  rw [perfectComplexTrace_eq_finsum_homology, perfectComplexTrace_eq_finsum_homology,
    perfectComplexTrace_eq_finsum_homology]
  change (∑ᶠ i : ℤ, b i) = (∑ᶠ i : ℤ, a i) + ∑ᶠ i : ℤ, c i
  calc
    _ = (∑ᶠ i : ℤ, b i) + -(∑ᶠ i : ℤ, p i) + ∑ᶠ i : ℤ, p i := by abel
    _ = _ := htotal

end EtaleCohomology
