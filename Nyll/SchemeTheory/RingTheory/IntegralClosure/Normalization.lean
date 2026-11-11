/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.PurelyInseparable.Exponent
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.FiniteType

/-!
# Finite normalization and generic finiteness
-/

@[expose] public section

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsIntegralClosure_finite_of_finiteType.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace FiniteNormalization
open Polynomial

namespace IsIntegralClosure
open _root_.IsIntegralClosure
namespace FiniteOfFiniteType
open _root_.IsIntegralClosure

theorem finite_of_comp_finite_of_injective {R B T : Type*} [CommRing R] [CommRing B]
    [CommRing T] [IsNoetherianRing R] (φ : R →+* B) (g : B →+* T)
    (hg : Function.Injective g) (h : (g.comp φ).Finite) : φ.Finite := by
  let : Algebra R B := φ.toAlgebra
  let : Algebra R T := (g.comp φ).toAlgebra
  have : Module.Finite R T := h
  let g' : B →ₗ[R] T :=
    { toFun := g
      map_add' := map_add g
      map_smul' := fun r b => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, RingHom.coe_comp,
          Function.comp_apply, RingHom.id_apply] }
  exact Module.Finite.of_injective g' hg

theorem finite_integralClosure_of_factor
    {R A L R' F' Ω : Type*} [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Algebra.IsIntegral R A] [Field L] [Algebra A L] [Algebra R L] [IsScalarTower R A L]
    [CommRing R'] [IsDomain R'] [IsIntegrallyClosed R'] [IsNoetherianRing R']
    [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Field Ω] [Algebra F' Ω] [Algebra R' Ω]
    [IsScalarTower R' F' Ω] (L' : IntermediateField F' Ω) [FiniteDimensional F' L']
    [Algebra.IsSeparable F' L'] (σ : R →+* R') (hσ : σ.Finite) (ι : L →+* Ω)
    (hι : ∀ x, ι x ∈ L') (hcomm : (algebraMap R' Ω).comp σ = ι.comp (algebraMap R L)) :
    Module.Finite A (integralClosure A L) := by
  classical
  let : Algebra R' (integralClosure R' L') := (integralClosure R' L').algebra
  have : IsScalarTower R' (integralClosure R' L') L' :=
    IsScalarTower.subalgebra' R' L' L' (integralClosure R' L')
  have hC' : Module.Finite R' (integralClosure R' L') :=
    IsIntegralClosure.finite R' F' L' (integralClosure R' L')
  have hψ : ((algebraMap R' (integralClosure R' L')).comp σ).Finite :=
    RingHom.Finite.comp (RingHom.finite_algebraMap.mpr hC') hσ
  set C := integralClosure A L with hCdef
  have hint : ∀ c : C, IsIntegral R' (⟨ι (c : L), hι c⟩ : L') := by
    intro c
    obtain ⟨P, hPm, hPc⟩ := isIntegral_trans (R := R) (c : L) c.2
    have h2 : IsIntegral R' (ι (c : L)) := by
      refine ⟨P.map σ, hPm.map σ, ?_⟩
      rw [eval₂_map, hcomm, ← hom_eval₂, hPc, map_zero]
    have h3 : ((IntermediateField.val L').restrictScalars R') ⟨ι (c : L), hι c⟩ = ι (c : L) := rfl
    rw [← h3] at h2
    exact (isIntegral_algHom_iff _ Subtype.val_injective).mp h2
  let gC : C →+* integralClosure R' L' :=
    { toFun := fun c => ⟨⟨ι (c : L), hι c⟩, hint c⟩
      map_one' := by
        apply Subtype.ext; apply Subtype.ext
        change ι ((1 : C) : L) = 1
        rw [OneMemClass.coe_one, map_one]
      map_mul' := fun a b => by
        apply Subtype.ext; apply Subtype.ext
        change ι ((a * b : C) : L) = ι (a : L) * ι (b : L)
        rw [MulMemClass.coe_mul, map_mul]
      map_zero' := by
        apply Subtype.ext; apply Subtype.ext
        change ι ((0 : C) : L) = 0
        rw [ZeroMemClass.coe_zero, map_zero]
      map_add' := fun a b => by
        apply Subtype.ext; apply Subtype.ext
        change ι ((a + b : C) : L) = ι (a : L) + ι (b : L)
        rw [AddMemClass.coe_add, map_add] }
  have hgC : Function.Injective gC := by
    intro a b hab
    have h1 : ι (a : L) = ι (b : L) :=
      congrArg (fun z : integralClosure R' L' => ((z : L') : Ω)) hab
    exact Subtype.ext (ι.injective h1)
  set φ : R →+* C := (algebraMap A C).comp (algebraMap R A) with hφdef
  have hcomp : gC.comp φ = (algebraMap R' (integralClosure R' L')).comp σ := by
    refine RingHom.ext fun r => ?_
    apply Subtype.ext; apply Subtype.ext
    change ι (algebraMap A L (algebraMap R A r)) = algebraMap R' Ω (σ r)
    rw [← IsScalarTower.algebraMap_apply R A L]
    exact (congrArg (fun f : R →+* Ω => f r) hcomm).symm
  have hφ : φ.Finite := finite_of_comp_finite_of_injective φ gC hgC (hcomp ▸ hψ)
  have hAC : (algebraMap A C).Finite := RingHom.Finite.of_comp_finite hφ
  exact RingHom.finite_algebraMap.mp hAC

theorem exists_twist {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (p n : ℕ) [ExpChar k p]
    [ExpChar Ω p] [PerfectRing Ω p] {d : ℕ} (η : MvPolynomial (Fin d) k →+* Ω)
    (hη : Function.Injective η) (hηC : η.comp MvPolynomial.C = algebraMap k Ω)
    (CO : Finset k) :
    ∃ (k' : IntermediateField k Ω) (_ : FiniteDimensional k k')
      (θ : MvPolynomial (Fin d) k' →ₐ[k'] Ω)
      (σ : MvPolynomial (Fin d) k →+* MvPolynomial (Fin d) k'),
      Function.Injective θ ∧ σ.Finite ∧ θ.toRingHom.comp σ = η ∧
      ∀ f : MvPolynomial (Fin d) k, (∀ mo ∈ f.support, f.coeff mo ∈ CO) →
        (iterateFrobeniusEquiv Ω p n).symm (η f) ∈ θ.range := by
  classical
  set R := MvPolynomial (Fin d) k with hRdef
  have : ExpChar R p := inferInstance
  have hηC' : ∀ a : k, η (MvPolynomial.C a) = algebraMap k Ω a := fun a =>
    congrArg (fun f : k →+* Ω => f a) hηC
  let Φ : Ω ≃+* Ω := iterateFrobeniusEquiv Ω p n
  have hΦ : ∀ x : Ω, Φ x = x ^ p ^ n := fun x => iterateFrobeniusEquiv_def Ω p n x
  have hΦsymm : ∀ x : Ω, (Φ.symm x) ^ p ^ n = x := fun x => by
    rw [← hΦ, RingEquiv.apply_symm_apply]
  set T : Set Ω := (fun a : k => Φ.symm (algebraMap k Ω a)) '' (CO : Set k) with hTdef
  have : Finite T := (CO.finite_toSet.image _).to_subtype
  set k' : IntermediateField k Ω := IntermediateField.adjoin k T with hk'def
  have hTint : ∀ x ∈ T, IsIntegral k x := by
    rintro _ ⟨a, -, rfl⟩
    exact IsIntegral.of_pow (pow_pos (expChar_pos Ω p) n)
      (by rw [hΦsymm]; exact isIntegral_algebraMap)
  have hk'fd : FiniteDimensional k k' := IntermediateField.finiteDimensional_adjoin hTint
  have hΦadj : ∀ x : Ω, x ∈ Algebra.adjoin k T → Φ x ∈ (algebraMap k Ω).range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      exact ⟨a, (RingEquiv.apply_symm_apply Φ _).symm⟩
    | algebraMap a => exact ⟨a ^ p ^ n, by rw [hΦ, map_pow]⟩
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
  have hΦk' : ∀ x : k', ∃ a : k, algebraMap k Ω a = Φ (x : Ω) := by
    intro x
    have hx : (x : Ω) ∈ Algebra.adjoin k T := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
        (fun y hy => (hTint y hy).isAlgebraic)]
      exact x.2
    exact RingHom.mem_range.mp (hΦadj _ hx)
  choose ρf hρf using hΦk'
  have hinjk : Function.Injective (algebraMap k Ω) := (algebraMap k Ω).injective
  let ρ : k' →+* k :=
    { toFun := ρf
      map_one' := hinjk (by
        rw [hρf, map_one]; change Φ ((1 : k') : Ω) = 1
        rw [OneMemClass.coe_one, map_one])
      map_mul' := fun x y => hinjk (by
        rw [hρf, map_mul, hρf, hρf]; change Φ ((x * y : k') : Ω) = _
        rw [MulMemClass.coe_mul, map_mul])
      map_zero' := hinjk (by
        rw [hρf, map_zero]; change Φ ((0 : k') : Ω) = 0
        rw [ZeroMemClass.coe_zero, map_zero])
      map_add' := fun x y => hinjk (by
        rw [hρf, map_add, hρf, hρf]; change Φ ((x + y : k') : Ω) = _
        rw [AddMemClass.coe_add, map_add]) }
  have hρ : ∀ x : k', algebraMap k Ω (ρ x) = (x : Ω) ^ p ^ n := fun x => by
    change algebraMap k Ω (ρf x) = _
    rw [hρf, hΦ]
  have : ExpChar k' p := expChar_of_injective_ringHom (algebraMap k k').injective p
  have hρ' : ∀ x : k', algebraMap k k' (ρ x) = x ^ p ^ n := by
    intro x
    apply (algebraMap k' Ω).injective
    rw [← IsScalarTower.algebraMap_apply, hρ, map_pow]
    rfl
  set R' := MvPolynomial (Fin d) k' with hR'def
  let θ : R' →ₐ[k'] Ω := MvPolynomial.aeval fun i => Φ.symm (η (MvPolynomial.X i))
  have hθC : ∀ x : k', θ (MvPolynomial.C x) = (x : Ω) := fun x => by
    change θ (algebraMap k' R' x) = _
    rw [θ.commutes]; rfl
  have hθX : ∀ i, θ (MvPolynomial.X i) = Φ.symm (η (MvPolynomial.X i)) := fun i =>
    MvPolynomial.aeval_X _ i
  have hΦθ : Φ.toRingHom.comp θ.toRingHom = η.comp (MvPolynomial.map ρ) := by
    refine MvPolynomial.ringHom_ext (fun x => ?_) (fun i => ?_)
    · change Φ (θ (MvPolynomial.C x)) = η (MvPolynomial.map ρ (MvPolynomial.C x))
      rw [hθC, MvPolynomial.map_C, hΦ, ← hρ, hηC']
    · change Φ (θ (MvPolynomial.X i)) = η (MvPolynomial.map ρ (MvPolynomial.X i))
      rw [hθX, MvPolynomial.map_X, RingEquiv.apply_symm_apply]
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    have h1 : η (MvPolynomial.map ρ P) = 0 := by
      have := congrArg (fun f : R' →+* Ω => f P) hΦθ
      simp only [RingHom.coe_comp, Function.comp_apply] at this
      rw [← this]
      change Φ (θ P) = 0
      rw [hP, map_zero]
    have h2 : MvPolynomial.map ρ P = 0 := hη (by rw [h1, map_zero])
    exact MvPolynomial.map_injective ρ ρ.injective (by rw [h2, map_zero])
  let σ : R →+* R' :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp (algebraMap k k')) fun i => MvPolynomial.X i ^ p ^ n
  have hσC : ∀ a : k, σ (MvPolynomial.C a) = MvPolynomial.C (algebraMap k k' a) := fun a => by
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C a) = _
    rw [MvPolynomial.eval₂_C, RingHom.coe_comp, Function.comp_apply]
  have hσX : ∀ i, σ (MvPolynomial.X i) = MvPolynomial.X i ^ p ^ n := fun i => by
    change MvPolynomial.eval₂ _ _ (MvPolynomial.X i) = _
    rw [MvPolynomial.eval₂_X]
  have hθσ : θ.toRingHom.comp σ = η := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · change θ (σ (MvPolynomial.C a)) = η (MvPolynomial.C a)
      rw [hσC, hθC, hηC']
      rfl
    · change θ (σ (MvPolynomial.X i)) = η (MvPolynomial.X i)
      rw [hσX, map_pow, hθX, hΦsymm]
  have hσρ : ∀ P : R', σ (MvPolynomial.map ρ P) = P ^ p ^ n := by
    intro P
    have : σ.comp (MvPolynomial.map ρ) = iterateFrobenius R' p n := by
      refine MvPolynomial.ringHom_ext (fun x => ?_) (fun i => ?_)
      · change σ (MvPolynomial.map ρ (MvPolynomial.C x)) = (MvPolynomial.C x) ^ p ^ n
        rw [MvPolynomial.map_C, hσC, hρ', MvPolynomial.C_pow]
      · change σ (MvPolynomial.map ρ (MvPolynomial.X i)) = (MvPolynomial.X i) ^ p ^ n
        rw [MvPolynomial.map_X, hσX]
    have h := congrArg (fun f : R' →+* R' => f P) this
    simpa only [RingHom.coe_comp, Function.comp_apply, iterateFrobenius_def] using h
  have hσfin : σ.Finite := by
    have hFT : σ.FiniteType := by
      have hcomp : σ.comp (algebraMap k R) = algebraMap k R' := by
        refine RingHom.ext fun a => ?_
        change σ (MvPolynomial.C a) = MvPolynomial.C (algebraMap k k' a)
        exact hσC a
      have : Algebra.FiniteType k k' := inferInstance
      have : Algebra.FiniteType k R' :=
        Algebra.FiniteType.trans (S := k') inferInstance inferInstance
      have h1 : (algebraMap k R').FiniteType := RingHom.finiteType_algebraMap.mpr ‹_›
      rw [← hcomp] at h1
      exact h1.of_comp_finiteType
    have hI : σ.IsIntegral := by
      intro P
      refine ⟨X ^ (p ^ n) - Polynomial.C (MvPolynomial.map ρ P),
        monic_X_pow_sub_C _ (pow_ne_zero n (expChar_pos R p).ne'), ?_⟩
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hσρ, sub_self]
    exact hI.to_finite hFT
  have hcoef : ∀ f : R, (∀ mo ∈ f.support, f.coeff mo ∈ CO) →
      Φ.symm (η f) ∈ θ.range := by
    intro f hf
    have h1 : η f = MvPolynomial.eval₂ (algebraMap k Ω) (fun i => η (MvPolynomial.X i)) f := by
      have : η = MvPolynomial.eval₂Hom (algebraMap k Ω) (fun i => η (MvPolynomial.X i)) := by
        refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
        · rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, hηC']
        · rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
      exact congrArg (fun φ : R →+* Ω => φ f) this
    rw [h1, ← RingEquiv.coe_toRingHom Φ.symm, MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eq]
    refine Subalgebra.sum_mem _ fun mo hmo => Subalgebra.mul_mem _ ?_ ?_
    · have hc : f.coeff mo ∈ CO := hf mo hmo
      have hT : Φ.symm (algebraMap k Ω (f.coeff mo)) ∈ T := ⟨_, hc, rfl⟩
      have hk' : Φ.symm (algebraMap k Ω (f.coeff mo)) ∈ k' :=
        IntermediateField.subset_adjoin k T hT
      refine (AlgHom.mem_range θ).mpr ⟨MvPolynomial.C ⟨_, hk'⟩, ?_⟩
      rw [hθC]
      rfl
    · refine Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _
      exact (AlgHom.mem_range θ).mpr ⟨MvPolynomial.X i, by rw [hθX]; rfl⟩
  exact ⟨k', hk'fd, θ, σ, hθinj, hσfin, hθσ, hcoef⟩

theorem isIntegrallyClosed_mvPolynomial (K : Type*) [Field K] (d : ℕ) :
    IsIntegrallyClosed (MvPolynomial (Fin d) K) := inferInstance

theorem isNoetherianRing_mvPolynomial (K : Type*) [Field K] (d : ℕ) :
    IsNoetherianRing (MvPolynomial (Fin d) K) := inferInstance

theorem finite_integralClosure (k A K L : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] :
    Module.Finite A (integralClosure A L) := by
  classical
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : ExpChar k p := hp
  have hkA : Function.Injective (algebraMap k A) := (algebraMap k A).injective
  have : ExpChar A p := expChar_of_injective_ringHom hkA p
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : ExpChar L p := expChar_of_injective_ringHom hAL p
  let : Algebra k L := ((algebraMap A L).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k A L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨d, g, hg, hgfin⟩ := exists_finite_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin d) k) A := g.toRingHom.toAlgebra
  have : Module.Finite (MvPolynomial (Fin d) k) A := hgfin
  set R := MvPolynomial (Fin d) k with hRdef
  have hRA : Function.Injective (algebraMap R A) := hg
  have : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  let : Algebra R K := ((algebraMap A K).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : Algebra R L := ((algebraMap A L).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap A L (algebraMap R A r) = algebraMap K L (algebraMap A K (algebraMap R A r))
    exact IsScalarTower.algebraMap_apply A K L _)
  have : IsScalarTower k R L := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap A L (algebraMap k A c) = algebraMap A L (algebraMap R A (algebraMap k R c))
    rw [← IsScalarTower.algebraMap_apply k R A])
  have hRK : Function.Injective (algebraMap R K) := (IsFractionRing.injective A K).comp hRA
  have hRL : Function.Injective (algebraMap R L) := hAL.comp hRA
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hRA
  have : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr hRK
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hRL
  have : ExpChar R p := inferInstance
  have : IsNoetherianRing R := inferInstance
  let : Algebra (FractionRing R) K := FractionRing.liftAlgebra R K
  have : IsScalarTower R (FractionRing R) K := FractionRing.isScalarTower_liftAlgebra R K
  let : Algebra (FractionRing R) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing R) K)).toAlgebra
  have : IsScalarTower (FractionRing R) K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower R (FractionRing R) L := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R L r = algebraMap K L (algebraMap (FractionRing R) K (algebraMap R _ r))
    rw [← IsScalarTower.algebraMap_apply R (FractionRing R) K,
      ← IsScalarTower.algebraMap_apply R K L])
  set F := FractionRing R with hFdef
  have : ExpChar F p := expChar_of_injective_ringHom (IsFractionRing.injective R F) p
  have : Algebra.IsAlgebraic R A := Algebra.IsIntegral.isAlgebraic
  have : Module.Finite F K := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  have : Module.Finite F L := Module.Finite.trans K L
  set Ls : IntermediateField F L := separableClosure F L with hLsdef
  have : ExpChar Ls p := expChar_of_injective_ringHom (algebraMap F Ls).injective p
  have : IsPurelyInseparable Ls L := separableClosure.isPurelyInseparable F L
  set n := IsPurelyInseparable.exponent Ls L with hndef
  have hpow : ∀ x : L, x ^ p ^ n ∈ Ls := fun x => by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' Ls (L := L) p x
    rw [← hy]; exact y.2
  set m := Module.finrank F L with hmdef
  let b : Module.Basis (Fin m) F L := Module.finBasis F L
  set S : Fin m → F[X] := fun j => minpoly F ((b j) ^ p ^ n) with hSdef
  have hSsep : ∀ j, (S j).Separable := fun j => mem_separableClosure_iff.mp (hpow (b j))
  have hSmonic : ∀ j, (S j).Monic := fun j =>
    minpoly.monic (Algebra.IsIntegral.isIntegral ((b j) ^ p ^ n))
  have hfrac : ∀ (j : Fin m) (i : ℕ), ∃ z : R × (nonZeroDivisors R),
      (S j).coeff i * algebraMap R F z.2 = algebraMap R F z.1 :=
    fun j i => IsLocalization.surj (nonZeroDivisors R) ((S j).coeff i)
  choose nd hnd using hfrac
  set CO : Finset k := (Finset.univ : Finset (Fin m)).biUnion fun j =>
    (Finset.range ((S j).natDegree + 1)).biUnion fun i =>
      ((nd j i).1).coeffs ∪ ((nd j i).2 : R).coeffs with hCOdef
  have hCOnum : ∀ (j : Fin m) (i : ℕ), i ≤ (S j).natDegree →
      ∀ mo ∈ ((nd j i).1).support, (nd j i).1.coeff mo ∈ CO := by
    intro j i hi mo hmo
    rw [hCOdef, Finset.mem_biUnion]
    refine ⟨j, Finset.mem_univ j, Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), ?_⟩⟩
    exact Finset.mem_union_left _ (MvPolynomial.mem_coeffs_iff.mpr ⟨mo, hmo, rfl⟩)
  have hCOden : ∀ (j : Fin m) (i : ℕ), i ≤ (S j).natDegree →
      ∀ mo ∈ ((nd j i).2 : R).support, ((nd j i).2 : R).coeff mo ∈ CO := by
    intro j i hi mo hmo
    rw [hCOdef, Finset.mem_biUnion]
    refine ⟨j, Finset.mem_univ j, Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), ?_⟩⟩
    exact Finset.mem_union_right _ (MvPolynomial.mem_coeffs_iff.mpr ⟨mo, hmo, rfl⟩)
  let Ω := AlgebraicClosure L
  have : ExpChar Ω p := expChar_of_injective_ringHom (algebraMap L Ω).injective p
  let Φ : Ω ≃+* Ω := iterateFrobeniusEquiv Ω p n
  have hΦ : ∀ x : Ω, Φ x = x ^ p ^ n := fun x => iterateFrobeniusEquiv_def Ω p n x
  have hRΩ : algebraMap R Ω = (algebraMap L Ω).comp (algebraMap R L) :=
    IsScalarTower.algebraMap_eq R L Ω
  have hηinj : Function.Injective (algebraMap R Ω) := by
    rw [hRΩ]; exact (algebraMap L Ω).injective.comp hRL
  have : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).mpr hηinj
  have hηC : (algebraMap R Ω).comp MvPolynomial.C = algebraMap k Ω := by
    refine RingHom.ext fun a => ?_
    change algebraMap R Ω (algebraMap k R a) = algebraMap k Ω a
    rw [← IsScalarTower.algebraMap_apply]
  obtain ⟨k', hk'fd, θ, σ, hθinj, hσfin, hθσ, hcoef⟩ :=
    exists_twist (k := k) (Ω := Ω) p n (algebraMap R Ω) hηinj hηC CO
  have hθσ' : ∀ r : R, θ (σ r) = algebraMap R Ω r := fun r =>
    congrArg (fun f : R →+* Ω => f r) hθσ
  set R' := MvPolynomial (Fin d) k' with hR'def
  have : IsNoetherianRing R' := isNoetherianRing_mvPolynomial k' d
  have : IsIntegrallyClosed R' := isIntegrallyClosed_mvPolynomial k' d
  let : Algebra R' Ω := θ.toRingHom.toAlgebra
  have hR'Ω : ∀ P : R', algebraMap R' Ω P = θ P := fun _ => rfl
  have : FaithfulSMul R' Ω := (faithfulSMul_iff_algebraMap_injective R' Ω).mpr hθinj
  let : Algebra (FractionRing R') Ω := FractionRing.liftAlgebra R' Ω
  have : IsScalarTower R' (FractionRing R') Ω := FractionRing.isScalarTower_liftAlgebra R' Ω
  set F' := FractionRing R' with hF'def
  have hθrange : ∀ x : Ω, x ∈ θ.range → x ∈ (algebraMap F' Ω).fieldRange := by
    rintro _ ⟨P, rfl⟩
    refine ⟨algebraMap R' F' P, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    rfl
  have hlift : ∀ j : Fin m, ∃ Q : F'[X],
      Q.map (algebraMap F' Ω) = ((S j).map (algebraMap F Ω)).map Φ.symm.toRingHom := by
    intro j
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_map, Polynomial.coeff_map]
    by_cases hci : (S j).coeff i = 0
    · rw [hci, map_zero, map_zero]; exact ⟨0, map_zero _⟩
    have hi : i ≤ (S j).natDegree := Polynomial.le_natDegree_of_ne_zero hci
    have hden : algebraMap R Ω ((nd j i).2 : R) ≠ 0 := fun h0 =>
      nonZeroDivisors.ne_zero ((nd j i).2).2 (hηinj (by rw [h0, map_zero]))
    have hc : algebraMap F Ω ((S j).coeff i) =
        algebraMap R Ω (nd j i).1 / algebraMap R Ω ((nd j i).2 : R) := by
      rw [eq_div_iff hden, IsScalarTower.algebraMap_apply R F Ω, IsScalarTower.algebraMap_apply R F
          Ω,
        ← map_mul, hnd]
    change Φ.symm (algebraMap F Ω ((S j).coeff i)) ∈ Set.range (algebraMap F' Ω)
    rw [hc, map_div₀]
    exact (algebraMap F' Ω).fieldRange.div_mem (hθrange _ (hcoef _ (hCOnum j i hi)))
      (hθrange _ (hcoef _ (hCOden j i hi)))
  choose Q hQ using hlift
  have hbroot : ∀ j, Polynomial.aeval (algebraMap L Ω (b j)) (Q j) = 0 := by
    intro j
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hQ, Polynomial.eval_map]
    have h1 : algebraMap L Ω (b j) = Φ.symm.toRingHom (Φ (algebraMap L Ω (b j))) :=
      (RingEquiv.symm_apply_apply Φ _).symm
    rw [h1, Polynomial.eval₂_at_apply, Polynomial.eval_map, hΦ, ← map_pow,
      IsScalarTower.algebraMap_eq F L Ω, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
      minpoly.aeval, map_zero, map_zero]
  have hQne : ∀ j, Q j ≠ 0 := by
    intro j hQ0
    have := hQ j
    rw [hQ0, Polynomial.map_zero] at this
    exact (Polynomial.map_ne_zero (Polynomial.map_ne_zero (hSmonic j).ne_zero)) this.symm
  have hQsep : ∀ j, (Q j).Separable := by
    intro j
    rw [← Polynomial.separable_map (algebraMap F' Ω), hQ, Polynomial.separable_map,
      Polynomial.separable_map]
    exact hSsep j
  have hbint : ∀ j, IsIntegral F' (algebraMap L Ω (b j)) := fun j => by
    have ha : IsAlgebraic F' (algebraMap L Ω (b j)) := ⟨Q j, hQne j, hbroot j⟩
    exact ha.isIntegral
  have hbsep : ∀ j, IsSeparable F' (algebraMap L Ω (b j)) := fun j =>
    (hQsep j).of_dvd (minpoly.dvd F' _ (hbroot j))
  set BΩ : Set Ω := Set.range fun j : Fin m => algebraMap L Ω (b j) with hBΩdef
  have : Finite BΩ := Set.finite_range _ |>.to_subtype
  set L' : IntermediateField F' Ω := IntermediateField.adjoin F' BΩ with hL'def
  have : FiniteDimensional F' L' := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨j, rfl⟩; exact hbint j)
  have : Algebra.IsSeparable F' L' :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable F' Ω).mpr
      (by rintro _ ⟨j, rfl⟩; exact hbsep j)
  have hFΩ : ∀ z : F, algebraMap F Ω z ∈ L' := by
    intro z
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← hθσ' a, ← hθσ' s, ← hR'Ω, ← hR'Ω, IsScalarTower.algebraMap_apply R' F' Ω,
      IsScalarTower.algebraMap_apply R' F' Ω]
    exact div_mem (L'.algebraMap_mem _) (L'.algebraMap_mem _)
  have hLΩ : ∀ x : L, algebraMap L Ω x ∈ L' := by
    intro x
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun j _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]
    exact mul_mem (hFΩ _) (IntermediateField.subset_adjoin F' BΩ ⟨j, rfl⟩)
  have hcomm : (algebraMap R' Ω).comp σ = (algebraMap L Ω).comp (algebraMap R L) := by
    rw [← hRΩ]
    exact hθσ
  exact finite_integralClosure_of_factor (R := R) (A := A) (L := L) (R' := R') (F' := F')
    (Ω := Ω) L' σ hσfin (algebraMap L Ω) hLΩ hcomm

end IsIntegralClosure.FiniteOfFiniteType

theorem _root_.IsIntegralClosure.finite_of_finiteType
    (k A K L C : Type*) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    [CommRing C] [Algebra C L] [Algebra A C] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    Module.Finite A C := by
  have : Module.Finite A (integralClosure A L) :=
    IsIntegralClosure.FiniteOfFiniteType.finite_integralClosure k A K L
  exact Module.Finite.equiv
    (IsIntegralClosure.equiv A (integralClosure A L) L C).toLinearEquiv

end FiniteNormalization
end NOSProofs
end AbelianVarieties
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_Algebra_QuasiFinite_exists_not_mem_finite_awayMap_of_mem_minimalPrimes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace AbelianVarieties
namespace NOSProofs
namespace GenericFiniteness
universe u

namespace GFRingGC7

open _root_.Polynomial
open _root_.TensorProduct

theorem isIntegral_of_isLocalRing_of_forall_isNilpotent
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [Algebra.QuasiFinite R S]
    (h : ∀ x ∈ IsLocalRing.maximalIdeal R, IsNilpotent x) : Algebra.IsIntegral R S := by
  classical
  set I : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hI
  let e : (IsLocalRing.maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ I :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R))) .refl).trans
          <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (IsLocalRing.maximalIdeal
        R)).symm.restrictScalars R)
  have : Module.Finite R (S ⧸ I) :=
    have : Module.Finite R ((IsLocalRing.maximalIdeal R).Fiber S) :=
      .trans (IsLocalRing.maximalIdeal R).ResidueField _
    .of_surjective e.toLinearMap e.surjective
  have hInil : I ≤ nilradical S := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_nilradical.mpr ((h x hx).map (algebraMap R S))
  refine ⟨fun x => ?_⟩
  obtain ⟨F, hFm, hF⟩ : IsIntegral R (Ideal.Quotient.mkₐ R I x) := Algebra.IsIntegral.isIntegral _
  have hx : aeval x F ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R, ← aeval_algHom_apply,
      aeval_def]
    exact hF
  obtain ⟨n, hn⟩ := mem_nilradical.mp (hInil hx)
  exact ⟨F ^ n, hFm.pow n, by rw [← aeval_def, map_pow, hn]⟩

theorem exists_not_mem_isIntegral_smul
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.QuasiFinite R A]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) (a : A) :
    ∃ t : R, t ∉ p ∧ IsIntegral R (t • a) := by
  classical
  have hpI : p.IsPrime := hp.1.1
  let Rp := Localization.AtPrime p
  let S := Rp ⊗[R] A
  have hnil : ∀ x ∈ IsLocalRing.maximalIdeal Rp, IsNilpotent x := by
    intro x hx
    have hrad := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Rp) p ⊥ hp
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp, ← hrad, Ideal.map_bot,
      Ideal.mem_radical_iff] at hx
    obtain ⟨n, hn⟩ := hx
    exact ⟨n, Ideal.mem_bot.mp hn⟩
  have : Algebra.IsIntegral Rp S := isIntegral_of_isLocalRing_of_forall_isNilpotent hnil
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl
    (Rₘ := Rp) ((1 : Rp) ⊗ₜ[R] a : S) (Algebra.IsIntegral.isIntegral _)
  obtain ⟨G, hGm, hG⟩ := hm
  have h1 : (m • ((1 : Rp) ⊗ₜ[R] a) : S) = Algebra.TensorProduct.includeRight ((m : R) • a) := by
    rw [Algebra.TensorProduct.includeRight_apply, Submonoid.smul_def, TensorProduct.tmul_smul]
  have h2 : (TensorProduct.mk R Rp A 1) (aeval ((m : R) • a) G) = 0 := by
    rw [TensorProduct.mk_apply, ← Algebra.TensorProduct.includeRight_apply, ← aeval_algHom_apply,
      ← h1, aeval_def]
    exact hG
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl (TensorProduct.mk R Rp A 1)).mp h2
  refine ⟨s * m, fun h => (hpI.mem_or_mem h).elim s.2 m.2, ?_⟩
  have h3 : aeval ((m : R) • a) (C (s : R) * G) = 0 := by
    rw [map_mul, aeval_C, ← Algebra.smul_def, ← Submonoid.smul_def]
    exact hs
  have := isIntegral_leadingCoeff_smul (C (s : R) * G) ((m : R) • a) h3
  rwa [leadingCoeff_mul_monic hGm, leadingCoeff_C, smul_smul] at this

theorem finite_awayMap_of_forall_isIntegral_smul
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (gens : Finset A) (hgens : Algebra.adjoin R (gens : Set A) = ⊤)
    (t : A → R) (ht : ∀ a ∈ gens, IsIntegral R (t a • a)) :
    (Localization.awayMap (algebraMap R A) (∏ a ∈ gens, t a)).Finite := by
  classical
  set r : R := ∏ a ∈ gens, t a with hr
  let Rr := Localization.Away r
  let Ar := Localization.Away (algebraMap R A r)
  let φ : Rr →+* Ar := Localization.awayMap (algebraMap R A) r
  let : Algebra Rr Ar := φ.toAlgebra
  have : IsScalarTower R Rr Ar := IsScalarTower.of_algebraMap_eq fun x => by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply R A Ar]
    exact (IsLocalization.map_eq _ x).symm
  have : Algebra.FiniteType R A := ⟨⟨gens, hgens⟩⟩
  have hft : φ.FiniteType :=
    RingHom.localization_away_map_finiteType R A Rr Ar (algebraMap R A) r
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  let ψ : A →ₐ[R] Ar := IsScalarTower.toAlgHom R A Ar
  have hr_unit : IsUnit (algebraMap R Rr r) := IsLocalization.Away.algebraMap_isUnit r
  have hgen : ∀ a ∈ gens, IsIntegral Rr (ψ a) := by
    intro a ha
    have hu : IsUnit (algebraMap R Rr (t a)) :=
      isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem t ha)) hr_unit
    obtain ⟨u, hu'⟩ := hu
    have h1 : IsIntegral Rr (algebraMap Rr Ar (algebraMap R Rr (t a)) * ψ a) := by
      have := (ht a ha).map ψ
      rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply R Rr Ar] at this
      exact this.tower_top
    have h2 : ψ a = algebraMap Rr Ar ↑u⁻¹ * (algebraMap Rr Ar (algebraMap R Rr (t a)) * ψ a) := by
      rw [← mul_assoc, ← map_mul, ← hu', Units.inv_mul, map_one, one_mul]
    rw [h2]
    exact isIntegral_algebraMap.mul h1
  have hA : ∀ a : A, IsIntegral Rr (ψ a) := by
    have hle : Algebra.adjoin R (ψ '' (gens : Set A)) ≤
        (integralClosure Rr Ar).restrictScalars R := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨a, ha, rfl⟩
      exact (Subalgebra.mem_restrictScalars R).mpr (hgen a ha)
    intro a
    have ha : ψ a ∈ Algebra.adjoin R (ψ '' (gens : Set A)) := by
      rw [← AlgHom.map_adjoin, hgens]
      exact Subalgebra.mem_map.mpr ⟨a, Algebra.mem_top, rfl⟩
    exact (Subalgebra.mem_restrictScalars R).mp (hle ha)
  have hint : φ.IsIntegral := by
    intro x
    change IsIntegral Rr x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (algebraMap R A r)) x
    change _root_.IsIntegral Rr (IsLocalization.mk' Ar a s)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hu : IsUnit (algebraMap R Rr (r ^ n)) := by rw [map_pow]; exact hr_unit.pow n
    obtain ⟨u, hu'⟩ := hu
    have hx : IsLocalization.mk' Ar a s * algebraMap Rr Ar ↑u = ψ a := by
      rw [hu', ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A Ar, map_pow, hn]
      exact IsLocalization.mk'_spec Ar a s
    have key : IsIntegral Rr (IsLocalization.mk' Ar a s * algebraMap Rr Ar ↑u) := by
      rw [hx]; exact hA a
    have : IsLocalization.mk' Ar a s =
        algebraMap Rr Ar ↑u⁻¹ * (IsLocalization.mk' Ar a s * algebraMap Rr Ar ↑u) := by
      rw [mul_comm (IsLocalization.mk' Ar a s), ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
        one_mul]
    rw [this]
    exact isIntegral_algebraMap.mul key
  exact hint.to_finite hft

end GFRingGC7

theorem _root_.Algebra.QuasiFinite.exists_not_mem_finite_awayMap_of_mem_minimalPrimes
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
        [Algebra.QuasiFinite R A]
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ∃ r : R, r ∉ p ∧ (Localization.awayMap (algebraMap R A) r).Finite := by
  classical
  have hpI : p.IsPrime := hp.1.1
  obtain ⟨gens, hgens⟩ := ‹Algebra.FiniteType R A›
  choose t ht hti using fun a : A => GFRingGC7.exists_not_mem_isIntegral_smul p hp a
  refine ⟨∏ a ∈ gens, t a, ?_, GFRingGC7.finite_awayMap_of_forall_isIntegral_smul gens hgens t
    fun a _ => hti a⟩
  rw [hpI.prod_mem_iff]
  rintro ⟨a, -, ha⟩
  exact ht a ha

end GenericFiniteness
end NOSProofs
end AbelianVarieties
end
