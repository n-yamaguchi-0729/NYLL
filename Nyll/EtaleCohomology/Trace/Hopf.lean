/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Trace.Complex
public import Nyll.EtaleCohomology.Trace.ShortExact
public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.FiniteProjectiveTrace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.LeftHomology
public import Mathlib.Algebra.Homology.ShortComplex.Homology
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Trace

/-!
# Hopf's trace formula for bounded complexes of vector spaces

The alternating trace on the terms equals the alternating trace on the
actual homology functor. The proof uses the two short exact sequences
of cycles and boundaries, and cancels the boundary traces by reindexing.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Limits

namespace EtaleCohomology

variable {K : Type u} [Field K]

/-- The endomorphism induced on the actual image of an equivariant differential. -/
def rangeEndomorphism {X Y : ModuleCat.{v} K} (d : X ⟶ Y)
    (a : X ⟶ X) (b : Y ⟶ Y) (h : a ≫ d = d ≫ b) :
    ModuleCat.of K d.hom.range ⟶ ModuleCat.of K d.hom.range :=
  ModuleCat.ofHom ((b.hom.comp d.hom.range.subtype).codRestrict _ (by
    intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨a.hom x, ?_⟩
    exact (congrArg (fun t : X ⟶ Y => t.hom x) h).trans (congrArg b.hom hx)))

private def cycleEndomorphism (S : ShortComplex (ModuleCat.{v} K)) (φ : S ⟶ S) :
    ModuleCat.of K S.g.hom.ker ⟶ ModuleCat.of K S.g.hom.ker :=
  S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫ S.moduleCatCyclesIso.hom

private lemma cycleEndomorphism_subtype (S : ShortComplex (ModuleCat.{v} K))
    (φ : S ⟶ S) :
    cycleEndomorphism S φ ≫ ModuleCat.ofHom S.g.hom.ker.subtype =
      ModuleCat.ofHom S.g.hom.ker.subtype ≫ φ.τ₂ := by
  change cycleEndomorphism S φ ≫ S.moduleCatLeftHomologyData.i =
    S.moduleCatLeftHomologyData.i ≫ φ.τ₂
  change (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫
    S.moduleCatCyclesIso.hom) ≫ S.moduleCatLeftHomologyData.i = _
  calc
    _ = S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫
        (S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.i) := rfl
    _ = S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫ S.iCycles :=
      congrArg (fun t : S.cycles ⟶ S.X₂ =>
        S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫ t)
        S.moduleCatCyclesIso_hom_i
    _ = S.moduleCatCyclesIso.inv ≫ (S.iCycles ≫ φ.τ₂) :=
      congrArg (fun t : S.cycles ⟶ S.X₂ => S.moduleCatCyclesIso.inv ≫ t)
        (ShortComplex.cyclesMap_i φ)
    _ = (S.moduleCatCyclesIso.inv ≫ S.iCycles) ≫ φ.τ₂ := rfl
    _ = S.moduleCatLeftHomologyData.i ≫ φ.τ₂ :=
      congrArg (fun t : S.moduleCatLeftHomologyData.K ⟶ S.X₂ => t ≫ φ.τ₂)
        S.moduleCatCyclesIso_inv_iCycles

private def cycleClass (S : ShortComplex (ModuleCat.{v} K)) :
    ModuleCat.of K S.g.hom.ker ⟶ S.homology :=
  S.moduleCatCyclesIso.inv ≫ S.homologyπ

private lemma cycleClass_naturality (S : ShortComplex (ModuleCat.{v} K))
    (φ : S ⟶ S) :
    cycleEndomorphism S φ ≫ cycleClass S =
      cycleClass S ≫ ShortComplex.homologyMap φ := by
  change (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ ≫
    S.moduleCatCyclesIso.hom) ≫ (S.moduleCatCyclesIso.inv ≫ S.homologyπ) =
      (S.moduleCatCyclesIso.inv ≫ S.homologyπ) ≫ ShortComplex.homologyMap φ
  calc
    _ = (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ) ≫
        (S.moduleCatCyclesIso.hom ≫ S.moduleCatCyclesIso.inv) ≫ S.homologyπ := rfl
    _ = (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ) ≫
        𝟙 S.cycles ≫ S.homologyπ :=
      congrArg (fun t : S.cycles ⟶ S.cycles =>
        (S.moduleCatCyclesIso.inv ≫ ShortComplex.cyclesMap φ) ≫ t ≫ S.homologyπ)
        S.moduleCatCyclesIso.hom_inv_id
    _ = S.moduleCatCyclesIso.inv ≫ (ShortComplex.cyclesMap φ ≫ S.homologyπ) := rfl
    _ = S.moduleCatCyclesIso.inv ≫ (S.homologyπ ≫ ShortComplex.homologyMap φ) :=
      congrArg (fun t : S.cycles ⟶ S.homology => S.moduleCatCyclesIso.inv ≫ t)
        (ShortComplex.homologyπ_naturality φ).symm
    _ = (S.moduleCatCyclesIso.inv ≫ S.homologyπ) ≫ ShortComplex.homologyMap φ := rfl

private lemma cycleClass_eq_zero_iff (S : ShortComplex (ModuleCat.{v} K))
    (x : S.g.hom.ker) : cycleClass S x = 0 ↔ x ∈ S.moduleCatToCycles.range := by
  have hq : cycleClass S =
      S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv :=
    S.moduleCatCyclesIso_inv_π
  have hinj : Function.Injective S.moduleCatHomologyIso.inv.hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  rw [hq]
  change S.moduleCatHomologyIso.inv.hom
      (Submodule.Quotient.mk x : S.g.hom.ker ⧸ S.moduleCatToCycles.range) = 0 ↔ _
  constructor
  · intro hx
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply hinj
    exact hx.trans (S.moduleCatHomologyIso.inv.hom.map_zero).symm
  · intro hx
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hx]
    exact S.moduleCatHomologyIso.inv.hom.map_zero

private def boundaryInCycles (S : ShortComplex (ModuleCat.{v} K)) :
    ModuleCat.of K S.f.hom.range ⟶ ModuleCat.of K S.g.hom.ker :=
  ModuleCat.ofHom (S.f.hom.range.subtype.codRestrict _ (by
    intro x
    obtain ⟨y, hy⟩ := x.property
    change S.g.hom x.val = 0
    rw [← hy]
    exact S.moduleCat_zero_apply y))

private lemma boundaryInCycles_naturality (S : ShortComplex (ModuleCat.{v} K))
    (φ : S ⟶ S) :
    rangeEndomorphism S.f φ.τ₁ φ.τ₂ φ.comm₁₂ ≫ boundaryInCycles S =
      boundaryInCycles S ≫ cycleEndomorphism S φ := by
  ext x
  exact (congrArg
    (fun t : ModuleCat.of K S.g.hom.ker ⟶ S.X₂ => t.hom (boundaryInCycles S x))
    (cycleEndomorphism_subtype S φ)).symm

/-- The middle trace splits into actual homology and the two adjacent image traces. -/
theorem trace_shortComplex (S : ShortComplex (ModuleCat.{v} K))
    [Module.Finite K S.X₂] (φ : S ⟶ S) :
    LinearMap.trace K S.X₂ φ.τ₂.hom =
      LinearMap.trace K S.homology (ShortComplex.homologyMap φ).hom +
        LinearMap.trace K S.f.hom.range
          (rangeEndomorphism S.f φ.τ₁ φ.τ₂ φ.comm₁₂).hom +
        LinearMap.trace K S.g.hom.range
          (rangeEndomorphism S.g φ.τ₂ φ.τ₃ φ.comm₂₃).hom := by
  have : Module.Finite K S.g.hom.range :=
    Module.Finite.of_surjective S.g.hom.rangeRestrict S.g.hom.surjective_rangeRestrict
  let T : ShortComplex (ModuleCat.{v} K) := ShortComplex.mk
    (ModuleCat.ofHom S.g.hom.ker.subtype)
    (ModuleCat.ofHom S.g.hom.rangeRestrict) (by
      ext x
      exact x.property)
  have hT : T.ShortExact := by
    apply ModuleCat.shortComplex_shortExact T
    · intro x
      constructor
      · intro hx
        refine ⟨⟨x, ?_⟩, rfl⟩
        exact congrArg Subtype.val hx
      · rintro ⟨x, rfl⟩
        apply Subtype.ext
        exact x.property
    · exact Subtype.val_injective
    · exact S.g.hom.surjective_rangeRestrict
  let ψ : T ⟶ T :=
    { τ₁ := cycleEndomorphism S φ
      τ₂ := φ.τ₂
      τ₃ := rangeEndomorphism S.g φ.τ₂ φ.τ₃ φ.comm₂₃
      comm₁₂ := cycleEndomorphism_subtype S φ
      comm₂₃ := by
        ext x
        exact congrArg (fun t : S.X₂ ⟶ S.X₃ => t.hom x) φ.comm₂₃ }
  have h₁ : LinearMap.trace K S.X₂ φ.τ₂.hom =
      LinearMap.trace K S.g.hom.ker (cycleEndomorphism S φ).hom +
        LinearMap.trace K S.g.hom.range
          (rangeEndomorphism S.g φ.τ₂ φ.τ₃ φ.comm₂₃).hom := by
    simpa only [LinearMap.projectiveTrace_eq_trace] using
      projectiveTrace_eq_add_of_shortExact hT ψ
  have hsurjπ : Function.Surjective S.homologyπ.hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hsurje : Function.Surjective S.moduleCatCyclesIso.inv.hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hsurj : Function.Surjective (cycleClass S).hom := hsurjπ.comp hsurje
  have : Module.Finite K S.homology :=
    Module.Finite.of_surjective (cycleClass S).hom hsurj
  let U : ShortComplex (ModuleCat.{v} K) :=
    ShortComplex.mk (boundaryInCycles S) (cycleClass S) (by
      ext x
      apply (cycleClass_eq_zero_iff S (boundaryInCycles S x)).mpr
      obtain ⟨y, hy⟩ := x.property
      refine ⟨y, ?_⟩
      apply Subtype.ext
      exact hy)
  have hU : U.ShortExact := by
    apply ModuleCat.shortComplex_shortExact U
    · intro x
      change cycleClass S x = 0 ↔ x ∈ Set.range (boundaryInCycles S)
      rw [cycleClass_eq_zero_iff]
      constructor
      · rintro ⟨y, hy⟩
        exact ⟨⟨S.f.hom y, ⟨y, rfl⟩⟩, hy⟩
      · rintro ⟨y, hy⟩
        obtain ⟨z, hz⟩ := y.property
        refine ⟨z, ?_⟩
        apply Subtype.ext
        exact hz.trans (congrArg Subtype.val hy)
    · intro x y hxy
      apply Subtype.ext
      change (boundaryInCycles S).hom x = (boundaryInCycles S).hom y at hxy
      exact congrArg (fun z : S.g.hom.ker => z.val) hxy
    · exact hsurj
  let χ : U ⟶ U :=
    { τ₁ := rangeEndomorphism S.f φ.τ₁ φ.τ₂ φ.comm₁₂
      τ₂ := cycleEndomorphism S φ
      τ₃ := ShortComplex.homologyMap φ
      comm₁₂ := boundaryInCycles_naturality S φ
      comm₂₃ := cycleClass_naturality S φ }
  have h₂ : LinearMap.trace K S.g.hom.ker (cycleEndomorphism S φ).hom =
      LinearMap.trace K S.f.hom.range
          (rangeEndomorphism S.f φ.τ₁ φ.τ₂ φ.comm₁₂).hom +
        LinearMap.trace K S.homology (ShortComplex.homologyMap φ).hom := by
    simpa only [LinearMap.projectiveTrace_eq_trace] using
      projectiveTrace_eq_add_of_shortExact hU χ
  rw [h₁, h₂]
  ac_rfl

variable (K) (C : CochainComplex (ModuleCat.{v} K) ℤ)
variable [∀ i : ℤ, Module.Finite K (C.X i)]

private def differentialRangeTrace (f : C ⟶ C) (i j : ℤ) : K :=
  LinearMap.trace K (C.d i j).hom.range
    (rangeEndomorphism (C.d i j) (f.f i) (f.f j) (f.comm i j)).hom

private def outgoingBoundaryTrace (f : C ⟶ C) (i : ℤ) : K :=
  differentialRangeTrace K C f i (i + 1)

private lemma trace_degree (f : C ⟶ C) (i : ℤ) :
    LinearMap.trace K (C.X i) (f.f i).hom =
      LinearMap.trace K (C.homology i) (HomologicalComplex.homologyMap f i).hom +
        outgoingBoundaryTrace K C f (i - 1) + outgoingBoundaryTrace K C f i := by
  have : Module.Finite K (C.sc i).X₂ := by
    change Module.Finite K (C.X i)
    infer_instance
  have h := trace_shortComplex (C.sc i)
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{v} K) (.up ℤ) i).map f)
  change LinearMap.trace K (C.X i) (f.f i).hom =
    LinearMap.trace K (C.homology i) (HomologicalComplex.homologyMap f i).hom +
      differentialRangeTrace K C f ((ComplexShape.up ℤ).prev i) i +
      differentialRangeTrace K C f i ((ComplexShape.up ℤ).next i) at h
  simpa only [CochainComplex.prev, CochainComplex.next, outgoingBoundaryTrace,
    sub_add_cancel] using h

omit [∀ i : ℤ, Module.Finite K (C.X i)] in
private lemma outgoingBoundaryTrace_eq_zero (f : C ⟶ C) (i : ℤ)
    (hi : IsZero (C.X i)) : outgoingBoundaryTrace K C f i = 0 := by
  have hd : C.d i (i + 1) = 0 := hi.eq_of_src _ _
  have hb : rangeEndomorphism (C.d i (i + 1)) (f.f i) (f.f (i + 1))
      (f.comm i (i + 1)) = 0 := by
    ext x
    obtain ⟨y, hy⟩ := x.property
    have hx : x.val = 0 := by
      rw [← hy, hd]
      rfl
    change (f.f (i + 1)).hom x.val = 0
    rw [hx, map_zero]
  dsimp only [outgoingBoundaryTrace, differentialRangeTrace]
  rw [hb, ModuleCat.hom_zero, map_zero]

omit [∀ i : ℤ, Module.Finite K (C.X i)] in
private lemma signedHomologyTrace_support_subset
    (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b] (f : C ⟶ C) :
    Function.support (fun i : ℤ => i.negOnePow •
      LinearMap.trace K (C.homology i) (HomologicalComplex.homologyMap f i).hom) ⊆
        Set.Icc a b := by
  intro i hi
  by_contra hout
  have hz : IsZero (C.homology i) := by
    by_cases hl : i < a
    · exact C.isZero_of_isGE a i hl
    · have hr : b < i := by
        simp only [Set.mem_Icc] at hout
        omega
      exact C.isZero_of_isLE b i hr
  have hf : HomologicalComplex.homologyMap f i = 0 := hz.eq_of_src _ _
  exact (Function.mem_support.mp hi) (by
    rw [hf, ModuleCat.hom_zero, map_zero, smul_zero])

/-- Hopf's trace formula uses the endomorphisms induced by the actual
homology functor; no homology model or comparison is assumed. -/
theorem boundedComplexTrace_eq_finsum_homology
    (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b] (f : C ⟶ C) :
    boundedComplexTrace K C a b f =
      ∑ᶠ i : ℤ, i.negOnePow •
        LinearMap.trace K (C.homology i) (HomologicalComplex.homologyMap f i).hom := by
  let h : ℤ → K := fun i => i.negOnePow •
    LinearMap.trace K (C.homology i) (HomologicalComplex.homologyMap f i).hom
  let p : ℤ → K := fun i => i.negOnePow • outgoingBoundaryTrace K C f i
  let q : ℤ → K := fun i => -(p (i - 1))
  have hh : Function.HasFiniteSupport h :=
    (Set.finite_Icc a b).subset (signedHomologyTrace_support_subset K C a b f)
  have hp : Function.HasFiniteSupport p := by
    apply (Set.finite_Icc a b).subset
    intro i hi
    by_contra hout
    have hz : IsZero (C.X i) := by
      by_cases hl : i < a
      · exact C.isZero_of_isStrictlyGE a i hl
      · have hr : b < i := by
          simp only [Set.mem_Icc] at hout
          omega
        exact C.isZero_of_isStrictlyLE b i hr
    exact (Function.mem_support.mp hi) (by
      dsimp only [p]
      rw [outgoingBoundaryTrace_eq_zero K C f i hz, smul_zero])
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
  have hdegree (i : ℤ) :
      i.negOnePow • LinearMap.projectiveTrace K (C.X i) (f.f i).hom =
        h i + q i + p i := by
    have hsign : i.negOnePow = -(i - 1).negOnePow := by
      exact (congrArg Int.negOnePow (sub_add_cancel i 1)).symm.trans
        (Int.negOnePow_succ (i - 1))
    rw [LinearMap.projectiveTrace_eq_trace, trace_degree K C f i, smul_add, smul_add]
    change h i + i.negOnePow • outgoingBoundaryTrace K C f (i - 1) + p i = _
    rw [hsign, Units.neg_smul]
  change (∑ᶠ i : ℤ, i.negOnePow •
    LinearMap.projectiveTrace K (C.X i) (f.f i).hom) = ∑ᶠ i : ℤ, h i
  rw [finsum_congr hdegree]
  have hs₁ : (∑ᶠ i : ℤ, (h i + q i + p i)) =
      (∑ᶠ i : ℤ, (h i + q i)) + ∑ᶠ i : ℤ, p i :=
    finsum_add_distrib (hh.add hq) hp
  have hs₂ : (∑ᶠ i : ℤ, (h i + q i)) =
      (∑ᶠ i : ℤ, h i) + ∑ᶠ i : ℤ, q i := finsum_add_distrib hh hq
  rw [hs₁, hs₂]
  have hcancel : (∑ᶠ i : ℤ, q i) = -(∑ᶠ i : ℤ, p i) := by
    dsimp only [q]
    rw [finsum_neg_distrib, finsum_comp (fun i : ℤ => i - 1) hbij]
  rw [hcancel]
  abel

/-- The actual homology traces may be summed on the same finite interval
that bounds the original cochain complex. -/
theorem boundedComplexTrace_eq_sum_homology
    (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b] (f : C ⟶ C) :
    boundedComplexTrace K C a b f =
      ∑ i ∈ Finset.Icc a b, i.negOnePow •
        LinearMap.trace K (C.homology i) (HomologicalComplex.homologyMap f i).hom := by
  rw [boundedComplexTrace_eq_finsum_homology K C a b f]
  apply finsum_eq_sum_of_support_subset
  simpa only [Finset.coe_Icc] using signedHomologyTrace_support_subset K C a b f

end EtaleCohomology
