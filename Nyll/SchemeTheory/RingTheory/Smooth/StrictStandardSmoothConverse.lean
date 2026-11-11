/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.Smooth.SmoothPrimeCotangentBasis
public import Nyll.SchemeTheory.RingTheory.LinearAlgebra.MatrixMinorScalarFactorization
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Original strictly-standard data imply smoothness

The original residual relations generate the localized conormal module.
The actual Jacobian minor condition supplies a scaled inverse, and its
scalar is a unit on the specified principal open. This splits the original
localized cotangent complex and proves smoothness there.
-/

@[expose] public section

noncomputable section

universe u v w t z

open scoped TensorProduct Matrix

private theorem retraction_of_unit_maximalMinors
    {T C V κ ι : Type*} [CommRing T] [AddCommGroup C] [Module T C]
    [AddCommGroup V] [Module T V] [Fintype κ] [Finite ι] [DecidableEq κ]
    (b : Module.Basis ι T V) (v : κ → C) (g : C →ₗ[T] V) (d : T)
    (hd : IsUnit d) (hv : Submodule.span T (Set.range v) = ⊤)
    (hminor : d ∈ Ideal.span (Set.range fun c : κ → ι =>
      ((Matrix.of fun j i => b.repr (g (v j)) i).submatrix _root_.id c).det)) :
    ∃ l : V →ₗ[T] C, l.comp g = LinearMap.id := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let bκ := Pi.basisFun T κ
  let F : (κ → T) →ₗ[T] C := bκ.constr T v
  have hF : Function.Surjective F := by
    apply LinearMap.range_eq_top.mp
    rw [show F = bκ.constr T v from rfl, Module.Basis.constr_range, hv]
  let A : Matrix κ ι T := Matrix.of fun j i => b.repr (g (v j)) i
  obtain ⟨S, hS⟩ := Matrix.exists_mul_eq_smul_one_of_mem_span_maximalMinors A d hminor
  let U : V →ₗ[T] (κ → T) := Matrix.toLin b bκ S.transpose
  have hA : LinearMap.toMatrix bκ b (g.comp F) = A.transpose := by
    apply Matrix.ext
    intro i j
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply]
    change b.repr (g ((bκ.constr T v) (bκ j))) i = _
    rw [Module.Basis.constr_basis]
    rfl
  have hUF : U.comp (g.comp F) = d • (LinearMap.id : (κ → T) →ₗ[T] (κ → T)) := by
    apply (LinearMap.toMatrix bκ bκ).injective
    rw [LinearMap.toMatrix_comp bκ b bκ, hA]
    change LinearMap.toMatrix b bκ (Matrix.toLin b bκ S.transpose) * A.transpose = _
    rw [LinearMap.toMatrix_toLin, ← Matrix.transpose_mul, hS,
      Matrix.transpose_smul, Matrix.transpose_one, map_smul, LinearMap.toMatrix_id]
  have hsplit : (F.comp U).comp g = d • (LinearMap.id : C →ₗ[T] C) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := hF x
    have hy := LinearMap.congr_fun hUF y
    change U (g (F y)) = d • y at hy
    change F (U (g (F y))) = d • F y
    rw [hy, map_smul]
  refine ⟨(↑hd.unit⁻¹ : T) • F.comp U, ?_⟩
  rw [LinearMap.smul_comp, hsplit, smul_smul, hd.val_inv_mul, one_smul]

namespace Algebra

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

/-- A genuine retraction of the base-changed original cotangent complex
implies formal smoothness of the localization. -/
theorem Generators.formallySmooth_localization_of_retraction_baseChangeCotangent
    {ι : Type w} (P : Generators R B ι) (M : Submonoid B)
    (T : Type*) [CommRing T] [Algebra B T] [IsLocalization M T]
    [Algebra R T] [IsScalarTower R B T]
    (l : (T ⊗[B] P.toExtension.CotangentSpace) →ₗ[T] T ⊗[B] P.toExtension.Cotangent)
    (hl : l.comp (P.toExtension.cotangentComplex.baseChange T) = LinearMap.id) :
    FormallySmooth R T := by
  have : Module.Flat B T := IsLocalization.flat T M
  have : FormallyEtale B T := FormallyEtale.of_isLocalization M
  let d := P.toExtension.cotangentComplex.baseChange T
  let q := P.toExtension.toKaehler.baseChange T
  let h := P.toExtension.h1Cotangentι.baseChange T
  have hd : Function.Injective d := by
    intro x y hxy
    have heq := congrArg l hxy
    change (l.comp d) x = (l.comp d) y at heq
    rw [hl] at heq
    exact heq
  have hh : Function.Injective h :=
    Module.Flat.lTensor_preserves_injective_linearMap P.toExtension.h1Cotangentι
      P.toExtension.h1Cotangentι_injective
  have hExact₀ : Function.Exact h d :=
    Module.Flat.lTensor_exact T P.toExtension.exact_hCotangentι_cotangentComplex
  have hhzero (x : T ⊗[B] P.toExtension.H1Cotangent) : h x = 0 := by
    apply hd
    rw [map_zero]
    exact hExact₀.apply_apply_eq_zero x
  have : Subsingleton (T ⊗[B] P.toExtension.H1Cotangent) :=
    ⟨fun x y => hh ((hhzero x).trans (hhzero y).symm)⟩
  let eH : (T ⊗[B] P.toExtension.H1Cotangent) ≃ₗ[T] H1Cotangent R T :=
    (P.equivH1Cotangent.baseChange B T _ _).trans (tensorH1CotangentOfIsLocalization R T M)
  have : Subsingleton (H1Cotangent R T) := eH.toEquiv.symm.subsingleton
  have hExact : Function.Exact d q :=
    Module.Flat.lTensor_exact T P.toExtension.exact_cotangentComplex_toKaehler
  have hq : Function.Surjective q :=
    LinearMap.baseChange_surjective T P.toExtension.toKaehler_surjective
  have hsplit : (Function.Injective d ∧
      ∃ s : (T ⊗[B] KaehlerDifferential R B) →ₗ[T]
        T ⊗[B] P.toExtension.CotangentSpace, q.comp s = LinearMap.id) ↔
      (Function.Surjective q ∧
        ∃ l' : (T ⊗[B] P.toExtension.CotangentSpace) →ₗ[T]
          T ⊗[B] P.toExtension.Cotangent, l'.comp d = LinearMap.id) :=
    hExact.split_tfae'.out 1 2 rfl rfl
  obtain ⟨s, hs⟩ := (hsplit.mpr ⟨hq, l, hl⟩).2
  have : Module.Free T (T ⊗[B] P.toExtension.CotangentSpace) :=
    Module.Free.of_basis (P.cotangentSpaceBasis.baseChange T)
  have : Module.Projective T (T ⊗[B] KaehlerDifferential R B) :=
    Module.Projective.of_split s q hs
  have : Module.Projective T (KaehlerDifferential R T) :=
    Module.Projective.of_equiv (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B T)
  exact ⟨inferInstance, inferInstance⟩

private theorem cotangent_mk_mem_span_of_relation_mem
    (P : Extension R B) {κ : Type*} (v : κ → P.ker) (x : P.ker)
    (hx : x.val ∈ Ideal.span (Set.range fun i => (v i).val)) :
    Extension.Cotangent.mk (P := P) x ∈
      Submodule.span B (Set.range fun i => Extension.Cotangent.mk (P := P) (v i)) := by
  let K := Submodule.span B (Set.range fun i => Extension.Cotangent.mk (P := P) (v i))
  have hle : Ideal.span (Set.range fun i => (v i).val) ≤ P.ker := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (v i).property
  have hspan (y : P.Ring) (hy : y ∈ Ideal.span (Set.range fun i => (v i).val)) :
      ∀ hyker : y ∈ P.ker, Extension.Cotangent.mk (P := P) ⟨y, hyker⟩ ∈ K := by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      intro hyker
      exact Submodule.subset_span (Set.mem_range_self i)
    | zero =>
      intro hyker
      change Extension.Cotangent.mk (P := P) 0 ∈ K
      rw [map_zero]
      exact K.zero_mem
    | add y z hy hz ihy ihz =>
      intro hyz
      change Extension.Cotangent.mk (P := P) (⟨y, hle hy⟩ + ⟨z, hle hz⟩) ∈ K
      rw [map_add]
      exact K.add_mem (ihy _) (ihz _)
    | smul r y hy ih =>
      intro hry
      change Extension.Cotangent.mk (P := P) (r • ⟨y, hle hy⟩) ∈ K
      rw [map_smul, ← algebraMap_smul B]
      exact K.smul_mem (algebraMap P.Ring B r) (ih _)
  exact hspan x.val hx x.property

private theorem cotangent_smul_mem_span_of_residual_relation
    (P : Extension R B) {κ : Type*} (v : κ → P.ker) (x : P.ker) (q : P.Ring)
    (hx : q * x.val ∈ Ideal.span (Set.range fun i => (v i).val) ⊔ P.ker ^ 2) :
    algebraMap P.Ring B q • Extension.Cotangent.mk (P := P) x ∈
      Submodule.span B (Set.range fun i => Extension.Cotangent.mk (P := P) (v i)) := by
  obtain ⟨y, hy, z, hz, heq⟩ := Submodule.mem_sup.mp hx
  have hyker : y ∈ P.ker := by
    have hle : Ideal.span (Set.range fun i => (v i).val) ≤ P.ker := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (v i).property
    exact hle hy
  have hzker : z ∈ P.ker := P.ker.pow_le_self (by decide : (2 : ℕ) ≠ 0) hz
  have hmkz : Extension.Cotangent.mk (P := P) ⟨z, hzker⟩ = 0 :=
    (Extension.Cotangent.mk_eq_zero_iff (P := P) ⟨z, hzker⟩).mpr hz
  have hxy : q • x = (⟨y, hyker⟩ : P.ker) + ⟨z, hzker⟩ :=
    Subtype.ext heq.symm
  rw [algebraMap_smul B, ← map_smul, hxy, map_add, hmkz, add_zero]
  exact cotangent_mk_mem_span_of_relation_mem P v ⟨y, hyker⟩ hy

private theorem Presentation.span_baseChangeCotangent_of_residual_relations
    {ι : Type w} {σ : Type t} {κ : Type z} (P : Presentation R B ι σ)
    (a : κ → σ) (q : P.Ring) (T : Type*) [CommRing T] [Algebra B T]
    (hq : IsUnit (algebraMap B T (algebraMap P.Ring B q)))
    (hrelations : ∀ j, q * P.relation j ∈
      Ideal.span (Set.range fun i => P.relation (a i)) ⊔ P.ker ^ 2) :
    Submodule.span T (Set.range fun i : κ => (1 : T) ⊗ₜ[B]
      Extension.Cotangent.mk (P := P.toExtension)
        ⟨P.relation (a i), P.relation_mem_ker (a i)⟩) = ⊤ := by
  let v₀ : σ → P.toExtension.Cotangent := fun j =>
    Extension.Cotangent.mk (P := P.toExtension) ⟨P.relation j, P.relation_mem_ker j⟩
  let v : κ → T ⊗[B] P.toExtension.Cotangent := fun i => (1 : T) ⊗ₜ[B] v₀ (a i)
  let K₀ := Submodule.span B (Set.range fun i => v₀ (a i))
  let K := Submodule.span T (Set.range v)
  let f : P.toExtension.Cotangent →ₗ[B] T ⊗[B] P.toExtension.Cotangent :=
    TensorProduct.mk B T P.toExtension.Cotangent 1
  have hmap : K₀ ≤ (K.restrictScalars B).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  have hres (j : σ) : algebraMap P.Ring B q • v₀ j ∈ K₀ :=
    cotangent_smul_mem_span_of_residual_relation P.toExtension
      (fun i => ⟨P.relation (a i), P.relation_mem_ker (a i)⟩)
      ⟨P.relation j, P.relation_mem_ker j⟩ q (hrelations j)
  have hspan₀ : Submodule.span B (Set.range v₀) = ⊤ :=
    Extension.Cotangent.span_eq_top_of_span_eq_ker (P := P.toExtension)
      P.relation P.span_range_relation_eq_ker
  have hspanAll : Submodule.span T (Set.range fun j => (1 : T) ⊗ₜ[B] v₀ j) = ⊤ := by
    have h := congrArg (fun U : Submodule B P.toExtension.Cotangent => U.baseChange T) hspan₀
    simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp,
      Function.comp_def, TensorProduct.mk_apply] using h
  change K = ⊤
  apply top_unique
  rw [← hspanAll]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  have hj := hmap (hres j)
  change f (algebraMap P.Ring B q • v₀ j) ∈ K at hj
  rw [map_smul, ← algebraMap_smul T] at hj
  exact (K.smul_mem_iff_of_isUnit hq).mp hj

private theorem Presentation.cotangentComplex_baseChange_relation_matrix
    {ι : Type w} {σ : Type t} {κ : Type z} (P : Presentation R B ι σ)
    (a : κ → σ) (T : Type*) [CommRing T] [Algebra B T] :
    (Matrix.of fun j i => (P.cotangentSpaceBasis.baseChange T).repr
      ((P.toExtension.cotangentComplex.baseChange T) ((1 : T) ⊗ₜ[B]
        Extension.Cotangent.mk (P := P.toExtension)
          ⟨P.relation (a j), P.relation_mem_ker (a j)⟩)) i) =
    Matrix.of fun j i => algebraMap B T
      (algebraMap P.Ring B (MvPolynomial.pderiv i (P.relation (a j)))) := by
  apply Matrix.ext
  intro j i
  rw [Matrix.of_apply, LinearMap.baseChange_tmul, Extension.cotangentComplex_mk,
    Module.Basis.baseChange_repr_tmul, Generators.cotangentSpaceBasis_repr_one_tmul]
  change MvPolynomial.aeval P.val (MvPolynomial.pderiv i (P.relation (a j))) • (1 : T) =
    algebraMap B T (algebraMap P.Ring B (MvPolynomial.pderiv i (P.relation (a j))))
  rw [Algebra.smul_def, mul_one, P.algebraMap_apply]

private theorem Presentation.jacobian_minor_mem_of_strictStandard_data
    {ι : Type w} {σ : Type t} {κ : Type z} [Fintype κ] [DecidableEq κ]
    (P : Presentation R B ι σ) (a : κ → σ) (q : P.Ring)
    (T : Type*) [CommRing T] [Algebra B T]
    (hminor : q ∈ P.ker ⊔ Ideal.span (Set.range fun c : κ → ι =>
      ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
        _root_.id c).det)) :
    algebraMap B T (algebraMap P.Ring B q) ∈
      Ideal.span (Set.range fun c : κ → ι =>
        ((Matrix.of fun j i => algebraMap B T
          (algebraMap P.Ring B (MvPolynomial.pderiv i (P.relation (a j))))).submatrix
            _root_.id c).det) := by
  let ψ : P.Ring →+* T := (algebraMap B T).comp (algebraMap P.Ring B)
  let A : Matrix κ ι T := Matrix.of fun j i => ψ (MvPolynomial.pderiv i (P.relation (a j)))
  have hker : Ideal.map ψ P.ker = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker ψ).mpr
    intro x hx
    have hx' : algebraMap P.Ring B x = 0 := hx
    change algebraMap B T (algebraMap P.Ring B x) = 0
    rw [hx', map_zero]
  have hminors : Ideal.map ψ (Ideal.span (Set.range fun c : κ → ι =>
      ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
        _root_.id c).det)) =
      Ideal.span (Set.range fun c : κ → ι => (A.submatrix _root_.id c).det) := by
    rw [Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext c
    simp only [Function.comp_apply]
    rw [RingHom.map_det]
    rfl
  have h := Ideal.mem_map_of_mem ψ hminor
  rw [Ideal.map_sup, hker, hminors, bot_sup_eq] at h
  exact h

private theorem Presentation.exists_retraction_of_strictStandard_data
    {ι : Type w} {σ : Type t} {κ : Type z} [Finite ι]
    [Fintype κ] [DecidableEq κ] (P : Presentation R B ι σ)
    (a : κ → σ) (q : P.Ring) (T : Type*) [CommRing T] [Algebra B T]
    (hq : IsUnit (algebraMap B T (algebraMap P.Ring B q)))
    (hminor : q ∈ P.ker ⊔ Ideal.span (Set.range fun c : κ → ι =>
      ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
        _root_.id c).det))
    (hrelations : ∀ j, q * P.relation j ∈
      Ideal.span (Set.range fun i => P.relation (a i)) ⊔ P.ker ^ 2) :
    ∃ l : (T ⊗[B] P.toExtension.CotangentSpace) →ₗ[T]
      T ⊗[B] P.toExtension.Cotangent,
      l.comp (P.toExtension.cotangentComplex.baseChange T) = LinearMap.id := by
  let v : κ → T ⊗[B] P.toExtension.Cotangent := fun i => (1 : T) ⊗ₜ[B]
    Extension.Cotangent.mk (P := P.toExtension)
      ⟨P.relation (a i), P.relation_mem_ker (a i)⟩
  apply retraction_of_unit_maximalMinors (P.cotangentSpaceBasis.baseChange T) v
    (P.toExtension.cotangentComplex.baseChange T)
    (algebraMap B T (algebraMap P.Ring B q)) hq
  · exact P.span_baseChangeCotangent_of_residual_relations a q T hq hrelations
  · change algebraMap B T (algebraMap P.Ring B q) ∈
      Ideal.span (Set.range fun c : κ → ι =>
        ((Matrix.of fun j i => (P.cotangentSpaceBasis.baseChange T).repr
          ((P.toExtension.cotangentComplex.baseChange T) ((1 : T) ⊗ₜ[B]
            Extension.Cotangent.mk (P := P.toExtension)
              ⟨P.relation (a j), P.relation_mem_ker (a j)⟩)) i).submatrix _root_.id c).det)
    rw [P.cotangentComplex_baseChange_relation_matrix a T]
    exact P.jacobian_minor_mem_of_strictStandard_data a q T hminor

/-- Actual original strictly-standard polynomial data imply smoothness
on the principal open where that polynomial is invertible. -/
theorem Presentation.smooth_away_of_strictStandard_data
    {ι : Type w} {σ : Type t} {κ : Type z} [Finite ι] [Finite σ]
    [Fintype κ] [DecidableEq κ] (P : Presentation R B ι σ)
    (a : κ → σ) (q : P.Ring)
    (hminor : q ∈ P.ker ⊔ Ideal.span (Set.range fun c : κ → ι =>
      ((Matrix.of fun j i => MvPolynomial.pderiv i (P.relation (a j))).submatrix
        _root_.id c).det))
    (hrelations : ∀ j, q * P.relation j ∈
      Ideal.span (Set.range fun i => P.relation (a i)) ⊔ P.ker ^ 2) :
    Smooth R (Localization.Away (algebraMap P.Ring B q)) := by
  let T := Localization.Away (algebraMap P.Ring B q)
  have hq : IsUnit (algebraMap B T (algebraMap P.Ring B q)) :=
    IsLocalization.Away.algebraMap_isUnit (algebraMap P.Ring B q)
  obtain ⟨l, hl⟩ := P.exists_retraction_of_strictStandard_data a q T hq hminor hrelations
  have : FormallySmooth R T :=
    P.toGenerators.formallySmooth_localization_of_retraction_baseChangeCotangent
      (.powers (algebraMap P.Ring B q)) T l hl
  have : FinitePresentation R B := P.finitePresentation_of_isFinite
  have : FinitePresentation B T := IsLocalization.Away.finitePresentation (algebraMap P.Ring B q)
  have : FinitePresentation R T := FinitePresentation.trans R B T
  exact ⟨inferInstance, inferInstance⟩

end Algebra
