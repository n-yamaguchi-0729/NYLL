/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.RegularLocal.CommonRegularElement
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalDepthFreeness
public import Nyll.SchemeTheory.RingTheory.RegularLocal.RegularLocalQuotientLift

/-!
# Minimal free covers and the Serre criterion

A basis of the actual residue-field tensor product gives a finite free
cover whose kernel has all coordinates in the maximal ideal. If the
maximal ideal annihilates a nonzero ring element, such a kernel cannot be
a nonzero free module. Induction on projective dimension then makes every
finite module of finite projective dimension free.

Applied to the residue field, this proves that a nonfield local ring with
finite residue-field projective dimension has a regular element in its
maximal ideal. Quotient projective dimension and an explicit cotangent-space
retraction then prove the Serre criterion: finite projective dimension of
the residue field implies regularity of the Noetherian local ring.
No minimal-resolution or regularity hypothesis is introduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory Module TensorProduct

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A finite module has an actual finite free cover whose relations have
all coordinates in the maximal ideal. -/
theorem exists_minimal_free_cover (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f ∧
      ∀ c, f c = 0 → ∀ i, c i ∈ maximalIdeal R := by
  classical
  let k := ResidueField R
  let n := Module.finrank k (k ⊗[R] M)
  let b : Module.Basis (Fin n) k (k ⊗[R] M) := Module.finBasis k (k ⊗[R] M)
  have hsurj : Function.Surjective (TensorProduct.mk R k M 1) :=
    TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
  let v : Fin n → M := fun i => (hsurj (b i)).choose
  have hv (i : Fin n) : (1 : k) ⊗ₜ[R] v i = b i := (hsurj (b i)).choose_spec
  let f : (Fin n → R) →ₗ[R] M := Fintype.linearCombination R v
  refine ⟨n, f, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top]
    change LinearMap.range (Fintype.linearCombination R v) = ⊤
    rw [Fintype.range_linearCombination]
    exact span_eq_top_of_tmul_eq_basis v b hv
  · intro c hc i
    have hsum : (∑ j, algebraMap R k (c j) • b j) = 0 := by
      calc
        _ = (1 : k) ⊗ₜ[R] f c := by
          change (∑ j, algebraMap R k (c j) • b j) =
            (1 : k) ⊗ₜ[R] ∑ j, c j • v j
          rw [TensorProduct.tmul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [← hv j, IsScalarTower.algebraMap_smul, TensorProduct.tmul_smul]
        _ = 0 := by rw [hc, TensorProduct.tmul_zero]
    have hi : algebraMap R k (c i) = 0 :=
      (Fintype.linearIndependent_iff.mp b.linearIndependent) _ hsum i
    exact (residue_eq_zero_iff (c i)).mp hi

/-- The free kernel of a minimal free cover vanishes when the ring has a
nonzero element annihilated by its maximal ideal. -/
theorem subsingleton_minimal_free_kernel_of_socle
    {M : Type u} [AddCommGroup M] [Module R M] {n : ℕ}
    (f : (Fin n → R) →ₗ[R] M)
    (hmin : ∀ c, f c = 0 → ∀ i, c i ∈ maximalIdeal R)
    (s : R) (hs : s ≠ 0) (hsoc : ∀ r ∈ maximalIdeal R, s * r = 0)
    [Module.Free R (LinearMap.ker f)] : Subsingleton (LinearMap.ker f) := by
  rcases subsingleton_or_nontrivial (LinearMap.ker f) with h | h
  · exact h
  · exfalso
    apply hs
    apply eq_of_smul_eq_smul (α := LinearMap.ker f)
    intro x
    rw [zero_smul]
    apply Subtype.ext
    funext i
    change s * x.val i = 0
    exact hsoc (x.val i) (hmin x.val x.property i)

variable [IsNoetherianRing R]

/-- In a noetherian local ring with nonzero socle, a finite module of
finite projective dimension is free. -/
theorem free_of_hasProjectiveDimensionLE_of_socle
    (s : R) (hs : s ≠ 0) (hsoc : ∀ r ∈ maximalIdeal R, s * r = 0) :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of R M) n → Module.Free R M := by
  intro n
  induction n with
  | zero =>
    intro M _ _ _ h
    have : Module.Projective R M :=
      (IsProjective.iff_projective (R := R) M).mpr
        ((projective_iff_hasProjectiveDimensionLE_zero _).mpr h)
    exact Module.free_of_flat_of_isLocalRing
  | succ n ih =>
    intro M _ _ _ h
    obtain ⟨k, f, hf, hmin⟩ := exists_minimal_free_cover (R := R) M
    have hker : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n :=
      ((LinearMap.shortExact_shortComplexKer hf).hasProjectiveDimensionLT_X₃_iff
        n ((IsProjective.iff_projective (R := R) (Fin k → R)).mp
          Module.Projective.of_free)).mp h
    have : Module.Free R (LinearMap.ker f) := ih (LinearMap.ker f) hker
    have hzero : Subsingleton (LinearMap.ker f) :=
      subsingleton_minimal_free_kernel_of_socle f hmin s hs hsoc
    have hinj : Function.Injective f :=
      LinearMap.ker_eq_bot.mp (Submodule.subsingleton_iff_eq_bot.mp hzero)
    exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hf⟩)

/-- Finite projective dimension of the residue field and nonzero socle
force the local ring to have zero maximal ideal. -/
theorem maximalIdeal_eq_bot_of_residue_projectiveDimensionLE_of_socle
    (n : ℕ) (hpd : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n)
    (s : R) (hs : s ≠ 0) (hsoc : ∀ r ∈ maximalIdeal R, s * r = 0) :
    maximalIdeal R = ⊥ := by
  have : Module.Free R (ResidueField R) :=
    free_of_hasProjectiveDimensionLE_of_socle s hs hsoc n (ResidueField R) hpd
  refine le_antisymm ?_ bot_le
  intro r hr
  change r = 0
  apply eq_of_smul_eq_smul (α := ResidueField R)
  intro x
  rw [Algebra.smul_def, ResidueField.algebraMap_eq,
    (residue_eq_zero_iff r).mpr hr, zero_mul, zero_smul]

/-- A nonfield local ring with finite residue-field projective dimension
has no nonzero element annihilated by its maximal ideal. -/
theorem not_isAssociatedPrime_maximalIdeal_of_residue_projectiveDimensionLE
    (n : ℕ) (hpd : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n)
    (hm : maximalIdeal R ≠ ⊥) : ¬ IsAssociatedPrime (maximalIdeal R) R := by
  intro h
  obtain ⟨s, hs⟩ := (isAssociatedPrime_iff.mp h).2
  have hsoc (r : R) (hr : r ∈ maximalIdeal R) : s * r = 0 := by
    have hr' : r ∈ Submodule.colon (⊥ : Submodule R R) {s} := hs ▸ hr
    have hrs : r * s = 0 := by
      simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] using hr'
    exact (mul_comm s r).trans hrs
  have hsne : s ≠ 0 := by
    intro hsz
    have h1 : (1 : R) ∈ maximalIdeal R := by
      rw [hs]
      simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, hsz, smul_zero]
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  exact hm (maximalIdeal_eq_bot_of_residue_projectiveDimensionLE_of_socle n hpd s hsne hsoc)

/-- The first regular-element step of the Serre converse, obtained from
finite projective dimension of the actual residue field. -/
theorem exists_regular_element_of_residue_projectiveDimensionLE
    (n : ℕ) (hpd : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n)
    (hm : maximalIdeal R ≠ ⊥) : ∃ x ∈ maximalIdeal R, IsSMulRegular R x := by
  have hnot := not_isAssociatedPrime_maximalIdeal_of_residue_projectiveDimensionLE n hpd hm
  obtain ⟨x, hxm, hx, _⟩ :=
    Module.exists_mem_maximalIdeal_isSMulRegular_isSMulRegular R R hnot hnot
  exact ⟨x, hxm, hx⟩

/-- Quotienting a finite module and its ring by a common regular element
does not increase its projective-dimension bound. -/
theorem hasProjectiveDimensionLE_quotSMulTop_of_regular
    (x : R) (hxR : IsSMulRegular R x) :
    ∀ (n : ℕ) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      IsSMulRegular M x → HasProjectiveDimensionLE (ModuleCat.of R M) n →
      HasProjectiveDimensionLE
        (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) n := by
  intro n
  induction n with
  | zero =>
    intro M _ _ _ _ hpd
    have : Module.Projective R M :=
      (IsProjective.iff_projective (R := R) M).mpr
        ((projective_iff_hasProjectiveDimensionLE_zero _).mpr hpd)
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
      ((IsProjective.iff_projective (R := R ⧸ Ideal.span {x})
        (QuotSMulTop x M)).mp Module.Projective.of_free)
  | succ n ih =>
    intro M _ _ _ hxM hpd
    obtain ⟨k, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
    let f : (Fin k → R) →ₗ[R] M := Fintype.linearCombination R v
    have hf : Function.Surjective f := by
      rw [← LinearMap.range_eq_top]
      change LinearMap.range (Fintype.linearCombination R v) = ⊤
      rw [Fintype.range_linearCombination]
      exact hv
    let K := LinearMap.ker f
    let i : K →ₗ[R] (Fin k → R) := K.subtype
    have hi : Function.Injective i := K.injective_subtype
    have hif : Function.Exact i f := by
      intro z
      constructor
      · intro hz
        exact ⟨⟨z, hz⟩, rfl⟩
      · rintro ⟨z, rfl⟩
        exact z.property
    have hpdK : HasProjectiveDimensionLE (ModuleCat.of R K) n :=
      ((LinearMap.shortExact_shortComplexKer hf).hasProjectiveDimensionLT_X₃_iff
        n ((IsProjective.iff_projective (R := R) (Fin k → R)).mp
          Module.Projective.of_free)).mp hpd
    have hxF : IsSMulRegular (Fin k → R) x := by
      intro a b hab
      funext j
      exact hxR (congrFun hab j)
    have hxK : IsSMulRegular K x := hxF.of_injective i hi
    have hpdK' := ih K hxK hpdK
    let i' : QuotSMulTop x K →ₗ[R ⧸ Ideal.span {x}]
        QuotSMulTop x (Fin k → R) :=
      (QuotSMulTop.map x i).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    let f' : QuotSMulTop x (Fin k → R) →ₗ[R ⧸ Ideal.span {x}]
        QuotSMulTop x M :=
      (QuotSMulTop.map x f).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
    have hif' : Function.Exact i' f' := QuotSMulTop.map_exact x hif hf
    have hf' : Function.Surjective f' := QuotSMulTop.map_surjective x hf
    have hi' : Function.Injective i' := by
      have h0 : Function.Exact (0 : K →ₗ[R] K) i := by
        intro z
        simp only [LinearMap.zero_apply, Set.mem_range, exists_const]
        constructor
        · intro hz
          exact (hi (hz.trans (map_zero i).symm)).symm
        · rintro rfl
          exact map_zero i
      have he :=
        QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h0 hif hxM
      rw [map_zero] at he
      change Function.Injective (QuotSMulTop.map x i)
      rw [← LinearMap.ker_eq_bot, he.linearMap_ker_eq]
      exact LinearMap.range_zero
    let S := ModuleCat.shortComplexOfCompEqZero i' f' hif'.linearMap_comp_eq_zero
    have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hif' hi' hf'
    exact (hS.hasProjectiveDimensionLT_X₃_iff n
      ((IsProjective.iff_projective (R := R ⧸ Ideal.span {x})
        (QuotSMulTop x (Fin k → R))).mp Module.Projective.of_free)).mpr hpdK'

end IsLocalRing

open scoped Pointwise

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The cotangent class of a minimal generator gives an actual split
copy of the residue field in the maximal ideal modulo that generator. -/
theorem exists_residue_split_maximalIdeal_quotSMulTop
    (x : R) (hx : x ∈ maximalIdeal R) (hx₂ : x ∉ maximalIdeal R ^ 2) :
    ∃ (i : ResidueField R →ₗ[R] QuotSMulTop x (maximalIdeal R))
      (p : QuotSMulTop x (maximalIdeal R) →ₗ[R] ResidueField R),
      p.comp i = LinearMap.id := by
  classical
  let m := maximalIdeal R
  let q : m →ₗ[R] QuotSMulTop x m := (x • (⊤ : Submodule R m)).mkQ
  let v : m := ⟨x, hx⟩
  have hv : m.toCotangent v ≠ 0 := by
    intro h
    exact hx₂ ((m.toCotangent_eq_zero v).mp h)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ResidueField R) hv
  let i₀ : R →ₗ[R] QuotSMulTop x m :=
    q.comp (LinearMap.toSpanSingleton R m v)
  have hi₀ : m ≤ LinearMap.ker i₀ := by
    intro r hr
    change q (r • v) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have hcomm : r • v = x • (⟨r, hr⟩ : m) := by
      apply Subtype.ext
      exact mul_comm r x
    rw [hcomm]
    exact Submodule.smul_mem_pointwise_smul _ x ⊤ Submodule.mem_top
  let i : ResidueField R →ₗ[R] QuotSMulTop x m := m.liftQ i₀ hi₀
  let p₀ : m →ₗ[R] ResidueField R :=
    (φ.restrictScalars R).comp m.toCotangent
  have hp₀ : x • (⊤ : Submodule R m) ≤ LinearMap.ker p₀ := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y x ⊤).mp hy
    change p₀ (x • z) = 0
    rw [map_smul, Algebra.smul_def, ResidueField.algebraMap_eq,
      (residue_eq_zero_iff x).mpr hx, zero_mul]
  let p : QuotSMulTop x m →ₗ[R] ResidueField R :=
    (x • (⊤ : Submodule R m)).liftQ p₀ hp₀
  refine ⟨i, p, ?_⟩
  apply LinearMap.ext
  intro a
  obtain ⟨r, rfl⟩ := residue_surjective a
  change p₀ (r • v) = residue R r
  rw [map_smul]
  have hpv : p₀ v = 1 := hφ
  rw [hpv, Algebra.smul_def, ResidueField.algebraMap_eq, mul_one]

/-- The actual residue field of the quotient is a retract of `m/xm`
as a module over that quotient. -/
theorem nonempty_residue_quotient_retract_maximalIdeal_quotSMulTop
    (x : R) (hx : x ∈ maximalIdeal R) (hx₂ : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span {x})] :
    Nonempty (Retract
      (ModuleCat.of (R ⧸ Ideal.span {x}) (ResidueField (R ⧸ Ideal.span {x})))
      (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (maximalIdeal R)))) := by
  let S := R ⧸ Ideal.span {x}
  let f : R →ₐ[R] S := Algebra.ofId R S
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have : IsLocalHom f :=
    ⟨fun a ha => (IsLocalHom.of_surjective f.toRingHom hf).map_nonunit a ha⟩
  let g : ResidueField R →ₐ[R] ResidueField S := ResidueField.mapAlgHom f
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨s, rfl⟩ := residue_surjective a
    obtain ⟨r, rfl⟩ := hf s
    exact ⟨residue R r, ResidueField.mapAlgHom_residue f r⟩
  let e : ResidueField R ≃ₗ[R] ResidueField S :=
    LinearEquiv.ofBijective g.toLinearMap ⟨g.injective, hg⟩
  obtain ⟨i, p, hpi⟩ := exists_residue_split_maximalIdeal_quotSMulTop x hx hx₂
  let i' : ResidueField S →ₗ[S] QuotSMulTop x (maximalIdeal R) :=
    (i.comp e.symm.toLinearMap).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  let p' : QuotSMulTop x (maximalIdeal R) →ₗ[S] ResidueField S :=
    (e.toLinearMap.comp p).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  refine ⟨⟨ModuleCat.ofHom i', ModuleCat.ofHom p', ?_⟩⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change e (p (i (e.symm a))) = a
  have h := LinearMap.congr_fun hpi (e.symm a)
  change p (i (e.symm a)) = e.symm a at h
  rw [h, e.apply_symm_apply]

/-- A projective-dimension bound on `m/xm` bounds the quotient's actual
residue field, since the latter is the constructed direct summand. -/
theorem residue_quotient_hasProjectiveDimensionLE_of_maximalIdeal_quotSMulTop
    (x : R) (hx : x ∈ maximalIdeal R) (hx₂ : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span {x})] (n : ℕ)
    [HasProjectiveDimensionLE
      (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x (maximalIdeal R))) n] :
    HasProjectiveDimensionLE
      (ModuleCat.of (R ⧸ Ideal.span {x}) (ResidueField (R ⧸ Ideal.span {x}))) n := by
  obtain ⟨h⟩ := nonempty_residue_quotient_retract_maximalIdeal_quotSMulTop x hx hx₂
  exact h.hasProjectiveDimensionLT (n + 1)

end IsLocalRing

open Module
open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing

namespace IsLocalRing

/-- A noetherian local ring whose residue field has finite projective
dimension is regular. -/
theorem isRegularLocalRing_of_residue_hasProjectiveDimensionLE (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n →
      IsRegularLocalRing R := by
  induction n with
  | zero =>
    intro R _ _ _ hpd
    have : Module.Projective R (ResidueField R) :=
      (IsProjective.iff_projective (R := R) (ResidueField R)).mpr
        ((projective_iff_hasProjectiveDimensionLE_zero _).mpr hpd)
    have : Module.Free R (ResidueField R) := Module.free_of_flat_of_isLocalRing
    have hm : maximalIdeal R = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro r hr
      change r = 0
      apply eq_of_smul_eq_smul (α := ResidueField R)
      intro a
      rw [Algebra.smul_def, ResidueField.algebraMap_eq,
        (residue_eq_zero_iff r).mpr hr, zero_mul, zero_smul]
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    rw [hm, Submodule.spanFinrank_bot, Nat.cast_zero]
    exact ringKrullDim_nonneg_of_nontrivial
  | succ n ih =>
    intro R _ _ _ hpd
    by_cases hm : maximalIdeal R = ⊥
    · apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
      rw [hm, Submodule.spanFinrank_bot, Nat.cast_zero]
      exact ringKrullDim_nonneg_of_nontrivial
    have hnot :=
      not_isAssociatedPrime_maximalIdeal_of_residue_projectiveDimensionLE (n + 1) hpd hm
    have hnotMem : maximalIdeal R ∉ associatedPrimes R R :=
      fun h => hnot (AssociatedPrimes.mem_iff.mp h)
    obtain ⟨x, hxm, hx₂, hxR, _⟩ :=
      Ws14Port.IsLocalRing.exists_isSMulRegular_and_isSMulRegular_of_notMem_associatedPrimes
        R R hnotMem hnotMem hm
    let m := maximalIdeal R
    let i : m →ₗ[R] R := m.subtype
    let g : R →ₗ[R] ResidueField R := Algebra.linearMap R (ResidueField R)
    have hig : Function.Exact i g := by
      intro r
      constructor
      · intro hr
        exact ⟨⟨r, (residue_eq_zero_iff r).mp hr⟩, rfl⟩
      · rintro ⟨r, rfl⟩
        exact (residue_eq_zero_iff r.val).mpr r.property
    let E := ModuleCat.shortComplexOfCompEqZero i g hig.linearMap_comp_eq_zero
    have hE : E.ShortExact := ModuleCat.shortComplex_shortExact E hig
      m.injective_subtype residue_surjective
    have hpdm : HasProjectiveDimensionLE (ModuleCat.of R m) n :=
      (hE.hasProjectiveDimensionLT_X₃_iff n
        ((IsProjective.iff_projective (R := R) R).mp Module.Projective.of_free)).mp hpd
    have hxmreg : IsSMulRegular m x := hxR.of_injective i m.injective_subtype
    have hpdQ : HasProjectiveDimensionLE
        (ModuleCat.of (R ⧸ Ideal.span {x}) (QuotSMulTop x m)) n :=
      hasProjectiveDimensionLE_quotSMulTop_of_regular x hxR n m hxmreg hpdm
    have : Nontrivial (R ⧸ Ideal.span {x}) :=
      Ideal.Quotient.nontrivial_iff.mpr fun h =>
        (maximalIdeal.isMaximal R).ne_top
          (top_le_iff.mp (h ▸
            (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxm) :
              Ideal.span {x} ≤ maximalIdeal R)))
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective
    have hpdResidue : HasProjectiveDimensionLE
        (ModuleCat.of (R ⧸ Ideal.span {x}) (ResidueField (R ⧸ Ideal.span {x}))) n :=
      residue_quotient_hasProjectiveDimensionLE_of_maximalIdeal_quotSMulTop x hxm hx₂ n
    have : IsRegularLocalRing (R ⧸ Ideal.span {x}) := ih _ hpdResidue
    exact SchemeTheory.isRegularLocalRing_of_quotient_span_singleton R x hxm hxR

end IsLocalRing
