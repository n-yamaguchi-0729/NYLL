/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.MonoidAlgebraConnected
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Nyll.SchemeTheory.RingTheory.Dimension.IdealNatCastLeKrullDimensionQuotient
public import Nyll.SchemeTheory.GroupSchemes.HopfAlgebra.Subalgebras
public import Nyll.SchemeTheory.Morphisms.SmoothRelativeDimension
public import Nyll.SchemeTheory.Morphisms.ReducedSmooth

/-!
# Group-like elements and torsion characters of Hopf algebras

Convolution characters trivial on group-like elements have no prime-to-characteristic
finite order. The character lattice of a connected smooth commutative Hopf algebra
is finite free, with rank bounded by its relative dimension.
-/

@[expose] public section

open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open Ideal_natCast_le_ringKrullDim_quotient_of_mem_minimalPrimes_map_of_algebraicIndependent
open P2mFibDim (ringKrullDim_localization_le)
open AlgebraicCurves.Geometry.Schemes.Proofs
open SmoothOfRelativeDimension_topologicalKrullDim_le.P2mSmoothOfRelativeDimensionKrullDim
  (ringKrullDim_le_of_faithfullyFlat)

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.HopfGroupLike

open _root_.Coalgebra
open _root_.TensorProduct
open _root_.Coalgebra.TensorProduct
open _root_.Module
open _root_.WithConv

universe u v w

namespace TorsionCharacters

section LinAlg

variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

theorem exists_common_eigenvector [IsAlgClosed k]
    (S : Set (Module.End k V)) (hS : ∀ f ∈ S, ∀ g ∈ S, Commute f g) :
    ∀ (n : ℕ) (p : Submodule k V), FiniteDimensional k p → Module.finrank k p = n → p ≠ ⊥ →
      (∀ f ∈ S, ∀ v ∈ p, f v ∈ p) →
      ∃ v ∈ p, v ≠ 0 ∧ ∀ f ∈ S, ∃ c : k, f v = c • v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hfd hn hp hstab
  by_cases hscalar : ∀ f ∈ S, ∃ c : k, ∀ v ∈ p, f v = c • v
  · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
    exact ⟨v, hv, hv0, fun f hf => (hscalar f hf).imp fun c hc => hc v hv⟩
  · push Not at hscalar
    obtain ⟨f, hfS, hf⟩ := hscalar
    have : FiniteDimensional k p := hfd
    have : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
    let fp : Module.End k p := f.restrict (fun v hv => hstab f hfS v hv)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue fp
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    let p' : Submodule k V := p ⊓ LinearMap.ker (f - μ • LinearMap.id)
    have hp'le : p' ≤ p := inf_le_left
    have hmem : ∀ v : V, v ∈ p' ↔ v ∈ p ∧ f v = μ • v := by
      intro v
      simp only [p', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have hp'ne : p' ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      refine ⟨(w : V), (hmem w).mpr ⟨w.2, ?_⟩, fun h0 => hw.2 (Subtype.ext h0)⟩
      have h1 := hw.apply_eq_smul
      have h2 : ((fp w : p) : V) = f w := rfl
      rw [← h2, h1]
      rfl
    have hp'lt : p' < p := by
      obtain ⟨v, hv, hvne⟩ := hf μ
      refine lt_of_le_of_ne hp'le ?_
      intro heq
      exact hvne ((hmem v).mp (heq ▸ hv)).2
    have : FiniteDimensional k p' := Submodule.finiteDimensional_of_le hp'le
    have hlt : Module.finrank k p' < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hp'lt
    have hstab' : ∀ g ∈ S, ∀ v ∈ p', g v ∈ p' := by
      intro g hg v hv
      obtain ⟨hvp, hfv⟩ := (hmem v).mp hv
      refine (hmem _).mpr ⟨hstab g hg v hvp, ?_⟩
      have hc := hS f hfS g hg
      calc f (g v) = g (f v) := by
            change (f * g) v = (g * f) v
            rw [hc.eq]
        _ = μ • g v := by rw [hfv, map_smul]
    obtain ⟨v, hv, hv0, hev⟩ := ih _ hlt p' inferInstance rfl hp'ne hstab'
    exact ⟨v, hp'le hv, hv0, hev⟩

theorem tmul_eq_zero_of_forall_lTensor {M : Type v} {N : Type w} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (t : M ⊗[k] N)
    (h : ∀ ξ : N →ₗ[k] k, LinearMap.lTensor M ξ t = 0) : t = 0 := by
  classical
  let 𝒞 := Module.Free.chooseBasis k N
  apply (TensorProduct.equivFinsuppOfBasisRight (M := M) 𝒞).injective
  rw [map_zero]
  ext i
  rw [TensorProduct.equivFinsuppOfBasisRight_apply, h, map_zero, Finsupp.zero_apply]

end LinAlg

section Rho

variable (k : Type u) [Field k] (H : Type v) [CommRing H] [HopfAlgebra k H]

/-- The right convolution action on the underlying coalgebra. -/
noncomputable def rho (ξ : H →ₗ[k] k) : H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H ξ ∘ₗ Coalgebra.comul

variable {k H}

theorem rho_apply (ξ : H →ₗ[k] k) (a : H) :
    rho k H ξ a = TensorProduct.rid k H (LinearMap.lTensor H ξ (Coalgebra.comul a)) := rfl

theorem rho_apply_repr (ξ : H →ₗ[k] k) {a : H} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr k a ι𝓡) :
    rho k H ξ a = ∑ i ∈ 𝓡.index, ξ (𝓡.right i) • 𝓡.left i := by
  rw [rho_apply, ← 𝓡.eq]
  simp only [map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

theorem rho_counit (a : H) : rho k H (Coalgebra.counit) a = a := by
  rw [rho_apply, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

theorem rho_convOne : rho k H (1 : WithConv (H →ₗ[k] k)).ofConv = LinearMap.id := by
  ext a
  rw [LinearMap.convOne_def]
  change rho k H (Algebra.linearMap k k ∘ₗ Coalgebra.counit) a = a
  have : (Algebra.linearMap k k ∘ₗ (Coalgebra.counit : H →ₗ[k] k)) = Coalgebra.counit := by
    ext x; rfl
  rw [this, rho_counit]

theorem rho_convMul (ξ ξ' : WithConv (H →ₗ[k] k)) :
    rho k H (ξ * ξ').ofConv = rho k H ξ.ofConv ∘ₗ rho k H ξ'.ofConv := by
  ext a
  let 𝓡 := ℛ k a
  let a₁ := fun (i : H × H) => ℛ k (𝓡.left i)
  let a₂ := fun (i : H × H) => ℛ k (𝓡.right i)
  have hco := sum_tmul_tmul_eq 𝓡 a₁ a₂
  let Φ : H ⊗[k] (H ⊗[k] H) →ₗ[k] H :=
    (TensorProduct.rid k H).toLinearMap ∘ₗ
      LinearMap.lTensor H (LinearMap.mul' k k ∘ₗ TensorProduct.map ξ.ofConv ξ'.ofConv)
  have hΦ : ∀ x y z : H, Φ (x ⊗ₜ (y ⊗ₜ z)) = (ξ.ofConv y * ξ'.ofConv z) • x := by
    intro x y z
    simp only [Φ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply, TensorProduct.rid_tmul]
  have h2 := congrArg Φ hco
  simp only [map_sum, hΦ] at h2
  rw [rho_apply_repr _ 𝓡]
  have hL : ∀ i ∈ 𝓡.index, (ξ * ξ').ofConv (𝓡.right i) • 𝓡.left i =
      ∑ j ∈ (a₂ i).index, (ξ.ofConv ((a₂ i).left j) * ξ'.ofConv ((a₂ i).right j)) • 𝓡.left i := by
    intro i _
    rw [← Finset.sum_smul]
    congr 1
    exact (a₂ i).convMul_apply ξ ξ'
  rw [Finset.sum_congr rfl hL, ← h2]
  rw [LinearMap.comp_apply, rho_apply_repr _ 𝓡, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, rho_apply_repr _ (a₁ i), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, mul_comm]

/-- The convolution action as a monoid homomorphism. -/
noncomputable def rhoHom : WithConv (H →ₗ[k] k) →* Module.End k H where
  toFun ξ := rho k H ξ.ofConv
  map_one' := rho_convOne
  map_mul' ξ ξ' := by
    rw [Module.End.mul_eq_comp]
    exact rho_convMul ξ ξ'

theorem rhoHom_apply (ξ : WithConv (H →ₗ[k] k)) : rhoHom ξ = rho k H ξ.ofConv := rfl

theorem counit_rho (ξ : H →ₗ[k] k) (a : H) : Coalgebra.counit (rho k H ξ a) = ξ a := by
  rw [rho_apply_repr _ (ℛ k a), map_sum]
  simp only [map_smul, smul_eq_mul]
  have h := sum_counit_smul (R := k) (ℛ k a)
  calc ∑ i ∈ (ℛ k a).index, ξ ((ℛ k a).right i) * Coalgebra.counit ((ℛ k a).left i)
      = ξ (∑ i ∈ (ℛ k a).index, Coalgebra.counit (R := k) ((ℛ k a).left i) • (ℛ k a).right i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
    _ = ξ a := by rw [h]

/-- The span of the convolution orbit of an element. -/
noncomputable def orbit (a : H) : Submodule k H :=
  Submodule.span k (Set.range fun ξ : H →ₗ[k] k => rho k H ξ a)

theorem rho_mem_orbit_gen (ξ : H →ₗ[k] k) (a : H) : rho k H ξ a ∈ orbit (k := k) a :=
  Submodule.subset_span ⟨ξ, rfl⟩

theorem self_mem_orbit (a : H) : a ∈ orbit (k := k) a := by
  have := rho_mem_orbit_gen (k := k) (Coalgebra.counit) a
  rwa [rho_counit] at this

theorem orbit_le_span (a : H) {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr k a ι𝓡) :
    orbit (k := k) a ≤ Submodule.span k (𝓡.left '' (𝓡.index : Set ι𝓡)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨ξ, rfl⟩
  change rho k H ξ a ∈ _
  rw [rho_apply_repr _ 𝓡]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨i, hi, rfl⟩

scoped instance orbit_finiteDimensional (a : H) : FiniteDimensional k (orbit (k := k) a) := by
  let 𝓡 := ℛ k a
  have hfin : (𝓡.left '' (𝓡.index : Set (H × H))).Finite := (Finset.finite_toSet _).image _
  have : FiniteDimensional k (Submodule.span k (𝓡.left '' (𝓡.index : Set (H × H)))) :=
    FiniteDimensional.span_of_finite k hfin
  exact Submodule.finiteDimensional_of_le (orbit_le_span a 𝓡)

theorem rho_mem_orbit (ξ : H →ₗ[k] k) {a v : H} (hv : v ∈ orbit (k := k) a) :
    rho k H ξ v ∈ orbit (k := k) a := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨ξ', rfl⟩ := hx
      have : rho k H ξ (rho k H ξ' a) = rho k H (toConv ξ * toConv ξ').ofConv a := by
        rw [rho_convMul]; rfl
      rw [this]
      exact rho_mem_orbit_gen _ a
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem exists_isGroupLikeElem_of_common_eigenvector {w : H} (hw : w ≠ 0)
    (hev : ∀ ξ : H →ₗ[k] k, ∃ c : k, rho k H ξ w = c • w) :
    ∃ b : H, IsGroupLikeElem k b ∧ ∀ ξ : H →ₗ[k] k, rho k H ξ w = ξ b • w := by
  obtain ⟨θ, hθ⟩ := Module.Projective.exists_dual_eq_one k hw
  let 𝓡 := ℛ k w
  let b : H := ∑ i ∈ 𝓡.index, θ (𝓡.left i) • 𝓡.right i
  have hb : ∀ ξ : H →ₗ[k] k, rho k H ξ w = ξ b • w := by
    intro ξ
    obtain ⟨c, hc⟩ := hev ξ
    have hξb : ξ b = c := by
      have h1 : θ (rho k H ξ w) = c := by rw [hc, map_smul, hθ, smul_eq_mul, mul_one]
      rw [← h1, rho_apply_repr _ 𝓡, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
    rw [hξb, hc]
  refine ⟨b, ?_, hb⟩
  have hΔ : Coalgebra.comul (R := k) w = w ⊗ₜ[k] b := by
    rw [← sub_eq_zero]
    apply tmul_eq_zero_of_forall_lTensor
    intro ξ
    rw [map_sub, sub_eq_zero]
    apply (TensorProduct.rid k H).injective
    rw [← rho_apply, hb ξ, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
  have hε : Coalgebra.counit (R := k) b = 1 := by
    have h1 := hb Coalgebra.counit
    rw [rho_counit] at h1
    have h2 : (Coalgebra.counit (R := k) b - 1) • w = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw
  refine ⟨hε, ?_⟩
  have hco := Coalgebra.coassoc_apply (R := k) w
  rw [hΔ, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hΔ, TensorProduct.assoc_tmul] at hco
  have h3 : w ⊗ₜ[k] (Coalgebra.comul (R := k) b - b ⊗ₜ[k] b) = 0 := by
    rw [TensorProduct.tmul_sub, hco, sub_self]
  have h4 := congrArg (fun t => TensorProduct.lid k _ (LinearMap.rTensor _ θ t)) h3
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hθ, one_smul, map_zero] at h4
  exact (sub_eq_zero.mp h4)

theorem main [IsAlgClosed k] [Coalgebra.IsCocomm k H]
    (φ : WithConv (H →ₐ[k] k)) (m : ℕ) (hm : (m : k) ≠ 0) (hφ : φ ^ m = 1)
    (h1 : ∀ g : H, IsGroupLikeElem k g → φ g = 1) : φ = 1 := by
  let ψ : WithConv (H →ₗ[k] k) := toConv φ.ofConv.toLinearMap
  have hψ : ψ ^ m = 1 := by
    change (toConv φ.ofConv.toLinearMap) ^ m = 1
    rw [← AlgHom.toLinearMap_convPow, hφ, AlgHom.toLinearMap_convOne]
  let R : Module.End k H := rhoHom ψ
  have hRψ : R = rho k H φ.ofConv.toLinearMap := rfl
  have hRm : R ^ m = 1 := by
    change (rhoHom ψ) ^ m = 1
    rw [← map_pow, hψ, map_one]
  have hcomm : ∀ ξ : H →ₗ[k] k, rho k H ξ ∘ₗ R = R ∘ₗ rho k H ξ := by
    intro ξ
    change rhoHom (toConv ξ) * rhoHom ψ = rhoHom ψ * rhoHom (toConv ξ)
    rw [← map_mul, ← map_mul, mul_comm]
  have key : ∀ (μ : k) (v : H), v ≠ 0 → R v = μ • v → μ = 1 := by
    intro μ v hv hRv
    let W := orbit (k := k) v
    have hWeig : ∀ x ∈ W, R x = μ • x := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨ξ, rfl⟩ := hx
          calc R (rho k H ξ v) = rho k H ξ (R v) := by
                rw [← LinearMap.comp_apply, ← hcomm ξ, LinearMap.comp_apply]
            _ = μ • rho k H ξ v := by rw [hRv, map_smul]
      | zero => rw [map_zero, smul_zero]
      | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
      | smul c x _ hx => rw [map_smul, hx, smul_comm]
    let S : Set (Module.End k H) := Set.range (rho k H)
    have hS : ∀ f ∈ S, ∀ g ∈ S, Commute f g := by
      rintro _ ⟨ξ, rfl⟩ _ ⟨ξ', rfl⟩
      change rhoHom (toConv ξ) * rhoHom (toConv ξ') = rhoHom (toConv ξ') * rhoHom (toConv ξ)
      rw [← map_mul, ← map_mul, mul_comm]
    have hstab : ∀ f ∈ S, ∀ x ∈ W, f x ∈ W := by
      rintro _ ⟨ξ, rfl⟩ x hx
      exact rho_mem_orbit ξ hx
    have hWne : W ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      exact ⟨v, self_mem_orbit v, hv⟩
    obtain ⟨w, hwW, hw0, hev⟩ :=
      exists_common_eigenvector S hS _ W inferInstance rfl hWne hstab
    have hev' : ∀ ξ : H →ₗ[k] k, ∃ c : k, rho k H ξ w = c • w := fun ξ => hev _ ⟨ξ, rfl⟩
    obtain ⟨b, hb, hbev⟩ := exists_isGroupLikeElem_of_common_eigenvector hw0 hev'
    have hφb : φ b = 1 := h1 b hb
    have e1 : R w = w := by
      rw [hRψ, hbev]
      change φ b • w = w
      rw [hφb, one_smul]
    have e2 : R w = μ • w := hWeig w hwW
    have e3 : (μ - 1) • w = 0 := by rw [sub_smul, one_smul, ← e2, e1, sub_self]
    rcases smul_eq_zero.mp e3 with h | h
    · exact (sub_eq_zero.mp h)
    · exact absurd h hw0
  have hRid : ∀ a : H, R a = a := by
    intro a
    let W := orbit (k := k) a
    have hWst : ∀ x ∈ W, R x ∈ W := fun x hx => rho_mem_orbit _ hx
    let T : Module.End k W := R.restrict hWst
    have hTm : T ^ m = 1 := by
      rw [Module.End.pow_restrict m hWst]
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change (R ^ m) x = x
      rw [hRm]
      rfl
    have hsep : Squarefree (Polynomial.X ^ m - Polynomial.C (1 : k)) :=
      (Polynomial.separable_X_pow_sub_C (1 : k) hm one_ne_zero).squarefree
    have haev : Polynomial.aeval T (Polynomial.X ^ m - Polynomial.C (1 : k)) = 0 := by
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one, hTm, sub_self]
    have hss : T.IsSemisimple := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep haev
    have hss1 : (T - algebraMap k (Module.End k W) 1).IsSemisimple :=
      (Module.End.isSemisimple_sub_algebraMap_iff).mpr hss
    have hT1 : T - algebraMap k (Module.End k W) 1 = 0 := by
      rw [hss1.eq_zero_iff_forall_eigenvalue]
      intro ν hν
      obtain ⟨x, hx⟩ := hν.exists_hasEigenvector
      have hxne : (x : H) ≠ 0 := fun h0 => hx.2 (Subtype.ext h0)
      have happ := hx.apply_eq_smul
      have hRx : R (x : H) = (ν + 1) • (x : H) := by
        have h3 : (((T - algebraMap k (Module.End k W) 1) x : W) : H) = R x - x := by
          rw [map_one]
          rfl
        have h4 : (((T - algebraMap k (Module.End k W) 1) x : W) : H) = ν • (x : H) := by
          rw [happ]; rfl
        rw [add_smul, one_smul, ← h4, h3, sub_add_cancel]
      have hν1 := key (ν + 1) x hxne hRx
      exact add_right_cancel (hν1.trans (zero_add 1).symm)
    have hT : T = 1 := by
      have := (sub_eq_zero (a := T)).mp hT1
      rw [this, map_one]
    have := LinearMap.congr_fun hT ⟨a, self_mem_orbit a⟩
    exact congrArg Subtype.val this
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro a
  have h := congrArg (Coalgebra.counit (R := k) (A := H)) (hRid a)
  rw [hRψ, counit_rho] at h
  change φ a = (1 : WithConv (H →ₐ[k] k)) a
  rw [AlgHom.convOne_apply]
  exact h

end Rho

end TorsionCharacters

end SchemeTheory.HopfGroupLike

namespace HopfAlgebra

universe u v w

open SchemeTheory.HopfGroupLike
open SchemeTheory.HopfGroupLike.TorsionCharacters

theorem withConv_algHom_eq_one_of_pow_eq_one_of_forall_isGroupLikeElem
    (k : Type u) [Field k] [IsAlgClosed k] (H : Type v) [CommRing H] [HopfAlgebra k H]
    [Coalgebra.IsCocomm k H]
    (φ : WithConv (H →ₐ[k] k)) (m : ℕ) (hm : (m : k) ≠ 0) (hφ : φ ^ m = 1)
    (h1 : ∀ g : H, IsGroupLikeElem k g → φ g = 1) :
    φ = 1 :=
  TorsionCharacters.main φ m hm hφ h1

end HopfAlgebra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AddMonoidAlgebra_natCard_withConv_algHom_pow_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.HopfGroupLike

open AddMonoidAlgebra WithConv

namespace CharacterCount

universe u v w

section Char

variable (k : Type u) [CommRing k] (M : Type v) [AddCommGroup M]
  (A : Type w) [CommRing A] [Algebra k A]

/-- Convolution characters of a group algebra are multiplicative characters. -/
noncomputable def convEquivChar :
    WithConv (AddMonoidAlgebra k M →ₐ[k] A) ≃* (Multiplicative M →* A) where
  toEquiv := (WithConv.equiv _).trans (AddMonoidAlgebra.lift k A M).symm
  map_mul' φ ψ := by
    refine MonoidHom.ext fun x => ?_
    rw [MonoidHom.mul_apply]
    change (AddMonoidAlgebra.lift k A M).symm (φ * ψ).ofConv x =
      (AddMonoidAlgebra.lift k A M).symm φ.ofConv x * (AddMonoidAlgebra.lift k A M).symm ψ.ofConv x
    rw [AddMonoidAlgebra.lift_symm_apply, AddMonoidAlgebra.lift_symm_apply,
      AddMonoidAlgebra.lift_symm_apply, AlgHom.convMul_apply]
    rw [(AddMonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k)
      (Multiplicative.toAdd x)).comul_eq_tmul_self, Algebra.TensorProduct.lift_tmul]

theorem convEquivChar_apply (φ : WithConv (AddMonoidAlgebra k M →ₐ[k] A)) (x : Multiplicative M) :
    convEquivChar k M A φ x = φ.ofConv (single (Multiplicative.toAdd x) 1) := rfl

end Char

section Count

variable {M : Type v} [AddCommGroup M] {A : Type w} [CommRing A]

theorem char_ext {ι : Type*} (b : Module.Basis ι ℤ M) (ψ ψ' : Multiplicative M →* A)
    (h : ∀ i, ψ (Multiplicative.ofAdd (b i)) = ψ' (Multiplicative.ofAdd (b i))) : ψ = ψ' := by
  have key : (MonoidHom.toAdditiveRight ψ.toHomUnits).toIntLinearMap =
      (MonoidHom.toAdditiveRight ψ'.toHomUnits).toIntLinearMap := by
    refine b.ext fun i => ?_
    simp only [AddMonoidHom.coe_toIntLinearMap]
    change Additive.ofMul (ψ.toHomUnits (Multiplicative.ofAdd (b i))) =
      Additive.ofMul (ψ'.toHomUnits (Multiplicative.ofAdd (b i)))
    congr 1
    exact Units.ext (h i)
  refine MonoidHom.ext fun x => ?_
  have hx := LinearMap.congr_fun key (Multiplicative.toAdd x)
  simp only [AddMonoidHom.coe_toIntLinearMap] at hx
  have hx' : ψ.toHomUnits x = ψ'.toHomUnits x := Additive.ofMul.injective hx
  have := congrArg (fun u : Aˣ => (u : A)) hx'
  exact this

variable (M A)

theorem natCard_char_pow_eq_one [Module.Free ℤ M] [Module.Finite ℤ M]
    (m : ℕ) [NeZero m] [HasEnoughRootsOfUnity A m] :
    Nat.card {ψ : Multiplicative M →* A // ψ ^ m = 1} = m ^ Module.finrank ℤ M := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℤ M
  let b : Module.Basis ι ℤ M := Module.Free.chooseBasis ℤ M
  have : Fintype ι := inferInstance
  have hpow : ∀ (ψ : Multiplicative M →* A) (x : Multiplicative M) (n : ℕ),
      (ψ ^ n) x = ψ x ^ n := fun ψ x n => MonoidHom.pow_apply ψ n x
  let F : {ψ : Multiplicative M →* A // ψ ^ m = 1} → (ι → rootsOfUnity m A) := fun ψ i =>
    ⟨ψ.1.toHomUnits (Multiplicative.ofAdd (b i)), by
      rw [mem_rootsOfUnity]
      ext
      rw [Units.val_pow_eq_pow_val, MonoidHom.coe_toHomUnits, ← hpow, ψ.2, Units.val_one,
        MonoidHom.one_apply]⟩
  have hF : ∀ ψ i, ((F ψ i : Aˣ) : A) = ψ.1 (Multiplicative.ofAdd (b i)) := fun ψ i => rfl
  have hinj : Function.Injective F := by
    intro ψ ψ' hψ
    apply Subtype.ext
    refine char_ext b _ _ fun i => ?_
    rw [← hF ψ i, ← hF ψ' i, hψ]
  have hsurj : Function.Surjective F := by
    intro ζ
    let θ : M →ₗ[ℤ] Additive Aˣ := b.constr ℤ fun i => Additive.ofMul (ζ i : Aˣ)
    have hθb : ∀ i, θ (b i) = Additive.ofMul (ζ i : Aˣ) :=
      fun i => b.constr_basis ℤ (fun j => Additive.ofMul (ζ j : Aˣ)) i
    let χ : Multiplicative M →* Aˣ := AddMonoidHom.toMultiplicativeLeft θ.toAddMonoidHom
    let ψ : Multiplicative M →* A := (Units.coeHom A).comp χ
    have hψ : ∀ x : M, ψ (Multiplicative.ofAdd x) = ((Additive.toMul (θ x) : Aˣ) : A) :=
      fun x => rfl
    have hmθ : (m : ℤ) • θ = 0 := by
      refine b.ext fun i => ?_
      rw [LinearMap.smul_apply, hθb, LinearMap.zero_apply]
      have hζ : ((ζ i : Aˣ)) ^ m = 1 := (mem_rootsOfUnity _ _).1 (ζ i).2
      change Additive.ofMul ((ζ i : Aˣ) ^ (m : ℤ)) = Additive.ofMul 1
      rw [zpow_natCast, hζ]
    have hψm : ψ ^ m = 1 := by
      refine MonoidHom.ext fun x => ?_
      rw [hpow, MonoidHom.one_apply]
      have hx := LinearMap.congr_fun hmθ (Multiplicative.toAdd x)
      rw [LinearMap.smul_apply, LinearMap.zero_apply] at hx
      have hx' : (Additive.toMul (θ (Multiplicative.toAdd x)) : Aˣ) ^ (m : ℤ) = 1 :=
        congrArg Additive.toMul hx
      rw [zpow_natCast] at hx'
      have := congrArg (fun u : Aˣ => (u : A)) hx'
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
      exact this
    refine ⟨⟨ψ, hψm⟩, funext fun i => ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [hF]
    change ψ (Multiplicative.ofAdd (b i)) = _
    rw [hψ, hθb]
    rfl
  rw [Nat.card_eq_of_bijective F ⟨hinj, hsurj⟩, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    HasEnoughRootsOfUnity.natCard_rootsOfUnity A m, Module.finrank_eq_card_basis b]

end Count

theorem main
    (k : Type u) [CommRing k] (M : Type v) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (A : Type w) [CommRing A] [Algebra k A]
    (m : ℕ) [NeZero m] [HasEnoughRootsOfUnity A m] :
    Nat.card {φ : WithConv (AddMonoidAlgebra k M →ₐ[k] A) // φ ^ m = 1} =
      m ^ Module.finrank ℤ M := by
  let e := convEquivChar k M A
  have he : {φ : WithConv (AddMonoidAlgebra k M →ₐ[k] A) // φ ^ m = 1} ≃
      {ψ : Multiplicative M →* A // ψ ^ m = 1} :=
    e.toEquiv.subtypeEquiv fun φ => by
      change φ ^ m = 1 ↔ e φ ^ m = 1
      rw [← map_pow, e.map_eq_one_iff]
  rw [Nat.card_congr he, natCard_char_pow_eq_one M A m]

end CharacterCount

universe u v w

end SchemeTheory.HopfGroupLike

namespace AddMonoidAlgebra

universe u v w

open SchemeTheory.HopfGroupLike
open SchemeTheory.HopfGroupLike.CharacterCount

theorem natCard_withConv_algHom_pow_eq_one
    (k : Type u) [CommRing k] (M : Type v) [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (A : Type w) [CommRing A] [Algebra k A]
    (m : ℕ) [NeZero m] [HasEnoughRootsOfUnity A m] :
    Nat.card {φ : WithConv (AddMonoidAlgebra k M →ₐ[k] A) // φ ^ m = 1} =
      m ^ Module.finrank ℤ M :=
  CharacterCount.main k M A m

end AddMonoidAlgebra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_AddMonoidAlgebra_ringKrullDim_pi_fin_int_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.HopfGroupLike

open Polynomial

namespace LaurentDimension

theorem ringKrullDim_laurentPolynomial (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    ringKrullDim (LaurentPolynomial R) = ringKrullDim R + 1 := by
  apply le_antisymm
  · calc ringKrullDim (LaurentPolynomial R) ≤ ringKrullDim R[X] :=
          ringKrullDim_localization_le (S := LaurentPolynomial R) (.powers (X : R[X]))
      _ = ringKrullDim R + 1 := Polynomial.ringKrullDim_of_isNoetherianRing
  · let φ : LaurentPolynomial R →ₐ[R] R := AddMonoidAlgebra.lift R R ℤ 1
    have hφT : φ (LaurentPolynomial.T 1) = 1 := by
      change AddMonoidAlgebra.lift R R ℤ 1 (AddMonoidAlgebra.single 1 1) = 1
      rw [AddMonoidAlgebra.lift_single, MonoidHom.one_apply, one_smul]
    have hsurj : Function.Surjective φ := fun r => ⟨algebraMap R _ r, φ.commutes r⟩
    have hne : (LaurentPolynomial.T 1 - 1 : LaurentPolynomial R) ≠ 0 := by
      refine sub_ne_zero.mpr (fun h => ?_)
      have hd := congrArg LaurentPolynomial.degree h
      rw [LaurentPolynomial.degree_T, ← LaurentPolynomial.T_zero, LaurentPolynomial.degree_T] at hd
      exact one_ne_zero (WithBot.coe_injective hd)
    have hr : (LaurentPolynomial.T 1 - 1 : LaurentPolynomial R) ∈
        nonZeroDivisors (LaurentPolynomial R) :=
      mem_nonZeroDivisors_of_ne_zero hne
    have hφzero : φ (LaurentPolynomial.T 1 - 1) = 0 := by
      rw [map_sub, hφT, map_one, sub_self]
    exact ringKrullDim_succ_le_of_surjective φ.toRingHom hsurj hr hφzero

end LaurentDimension

namespace LaurentDimension

theorem noeth_and_dim (κ : Type*) [Field κ] :
    ∀ t : ℕ, IsNoetherianRing (AddMonoidAlgebra κ (Fin t → ℤ)) ∧
      ringKrullDim (AddMonoidAlgebra κ (Fin t → ℤ)) = t
  | 0 => by
      let e : AddMonoidAlgebra κ (Fin 0 → ℤ) ≃+* κ := AddMonoidAlgebra.uniqueRingEquiv (Fin 0 → ℤ)
      refine ⟨isNoetherianRing_of_ringEquiv κ e.symm, ?_⟩
      rw [ringKrullDim_eq_of_ringEquiv e, ringKrullDim_eq_zero_of_field]
      rfl
  | (t + 1) => by
      obtain ⟨hN, hd⟩ := noeth_and_dim κ t
      let e1 : (Fin (t + 1) → ℤ) ≃+ ℤ × (Fin t → ℤ) :=
        { (Fin.consEquiv fun _ : Fin (t + 1) => ℤ).symm with
          map_add' := fun f g => rfl }
      let E : AddMonoidAlgebra κ (Fin (t + 1) → ℤ) ≃+*
          LaurentPolynomial (AddMonoidAlgebra κ (Fin t → ℤ)) :=
        (AddMonoidAlgebra.domCongr κ κ e1).toRingEquiv.trans AddMonoidAlgebra.curryRingEquiv
      have : IsNoetherianRing (AddMonoidAlgebra κ (Fin t → ℤ)) := hN
      have : IsNoetherianRing (LaurentPolynomial (AddMonoidAlgebra κ (Fin t → ℤ))) :=
        IsLocalization.isNoetherianRing
          (.powers (X : (AddMonoidAlgebra κ (Fin t → ℤ))[X])) _ inferInstance
      refine ⟨isNoetherianRing_of_ringEquiv _ E.symm, ?_⟩
      rw [ringKrullDim_eq_of_ringEquiv E, ringKrullDim_laurentPolynomial, hd]
      rfl

end LaurentDimension

end SchemeTheory.HopfGroupLike

namespace AddMonoidAlgebra

universe u v w

open SchemeTheory.HopfGroupLike
open SchemeTheory.HopfGroupLike.LaurentDimension

theorem ringKrullDim_pi_fin_int_eq (κ : Type*) [Field κ] (t : ℕ) :
    ringKrullDim (AddMonoidAlgebra κ (Fin t → ℤ)) = t := (LaurentDimension.noeth_and_dim κ t).2

end AddMonoidAlgebra
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_HopfAlgebra_free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

namespace SchemeTheory.HopfGroupLike

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.Coalgebra
open scoped TensorProduct
open scoped Coalgebra.TensorProduct

universe u v

namespace CharacterLattice

section Plumbing

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [Algebra k H] (h : ℕ)
  (hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H))

include hsm

theorem smoothOfRelativeDimension_specMap :
    SmoothOfRelativeDimension h (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
  (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension h)).mpr hsm

theorem finiteType : Algebra.FiniteType k H := by
  have : SmoothOfRelativeDimension h (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
    smoothOfRelativeDimension_specMap k H h hsm
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
    SmoothOfRelativeDimension.smooth h _
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k H))) := inferInstance
  have hft : RingHom.FiniteType (algebraMap k H) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  exact RingHom.finiteType_algebraMap.mp hft

theorem isReduced : IsReduced H := by
  have : SmoothOfRelativeDimension h (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
    smoothOfRelativeDimension_specMap k H h hsm
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
    SmoothOfRelativeDimension.smooth h _
  have := AlgebraicGeometry.isReduced_of_smooth_of_field
    (Spec.map (CommRingCat.ofHom (algebraMap k H)))
  exact (affine_isReduced_iff (CommRingCat.of H)).mp this

theorem ringKrullDim_le : ringKrullDim H ≤ h := by
  have : SmoothOfRelativeDimension h (Spec.map (CommRingCat.ofHom (algebraMap k H))) :=
    smoothOfRelativeDimension_specMap k H h hsm
  have := AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le
    (Spec.map (CommRingCat.ofHom (algebraMap k H))) h
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact this

end Plumbing

section Hopf

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]

theorem linearIndependent_pow_of_orderOf (g : GroupLike k H) :
    LinearIndependent k (fun i : Fin (orderOf g) => (g ^ (i : ℕ)).val) := by
  have hinj : Function.Injective (fun i : Fin (orderOf g) => g ^ (i : ℕ)) := by
    intro i j hij
    apply Fin.ext
    have := pow_inj_mod.mp hij
    rwa [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at this
  exact (linearIndep_groupLikeVal (R := k) (A := H)).comp _ hinj

theorem orderOf_ne_of_cast_eq_zero [IsReduced H] (g : GroupLike k H) {q : ℕ} (hq : q.Prime)
    (hqk : (q : k) = 0) : orderOf g ≠ q := by
  intro hord
  have : Fact q.Prime := ⟨hq⟩
  have hchar : CharP k q := by
    have := (CharP.cast_eq_zero_iff k (ringChar k) q).mp hqk
    rcases (Nat.dvd_prime hq).mp this with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one)
    · exact h1 ▸ (inferInstance : CharP k (ringChar k))
  have : Nontrivial H := Bialgebra.nontrivial k
  have : CharP H q := charP_of_injective_algebraMap (algebraMap k H).injective q
  have hpow : g.val ^ q = 1 := by
    have := pow_orderOf_eq_one g
    rw [hord] at this
    exact congrArg GroupLike.val this
  have hnil : IsNilpotent (g.val - 1) := ⟨q, by rw [sub_pow_char, hpow, one_pow, sub_self]⟩
  have h1 : g.val = 1 := sub_eq_zero.mp hnil.eq_zero
  have hg1 : g = 1 := GroupLike.ext h1
  rw [hg1, orderOf_one] at hord
  exact hq.one_lt.ne hord

theorem orderOf_ne_of_cast_ne_zero [ConnectedSpace (PrimeSpectrum H)] (g : GroupLike k H) {q : ℕ}
    (hq : q.Prime) (hqk : (q : k) ≠ 0) : orderOf g ≠ q := by
  intro hord
  have : Nontrivial H := Bialgebra.nontrivial k
  have : NeZero q := ⟨hq.ne_zero⟩
  let x : H := g.val
  have hxq : x ^ q = 1 := by
    have := pow_orderOf_eq_one g
    rw [hord] at this
    exact congrArg GroupLike.val this
  let s : H := ∑ i : Fin q, x ^ (i : ℕ)
  have hxs : ∀ j : Fin q, x ^ (j : ℕ) * s = s := by
    intro j
    simp only [s, Finset.mul_sum]
    have : ∀ i : Fin q, x ^ (j : ℕ) * x ^ (i : ℕ) = x ^ ((j + i : Fin q) : ℕ) := by
      intro i
      rw [← pow_add, Fin.val_add]
      conv_lhs => rw [← Nat.mod_add_div ((j : ℕ) + i) q, pow_add, pow_mul, hxq, one_pow, mul_one]
    simp_rw [this]
    exact Fintype.sum_equiv (Equiv.addLeft j) _ _ (fun i => rfl)
  have hss : s * s = (q : H) * s := by
    calc s * s = ∑ j : Fin q, x ^ (j : ℕ) * s := by rw [Finset.sum_mul]
      _ = ∑ _j : Fin q, s := Finset.sum_congr rfl fun j _ => hxs j
      _ = (q : H) * s := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : Invertible (q : H) := invertibleOfNonzero (α := k) hqk |>.map (algebraMap k H) |>.copy _
    (by rw [map_natCast])
  let e : H := ⅟(q : H) * s
  have he : IsIdempotentElem e := by
    change ⅟(q : H) * s * (⅟(q : H) * s) = ⅟(q : H) * s
    calc ⅟(q : H) * s * (⅟(q : H) * s) = ⅟(q : H) * ⅟(q : H) * (s * s) := by ring
      _ = ⅟(q : H) * ⅟(q : H) * ((q : H) * s) := by rw [hss]
      _ = ⅟(q : H) * s := by
          rw [← mul_assoc, mul_assoc (⅟(q : H)), invOf_mul_self, mul_one]
  have hli := linearIndependent_pow_of_orderOf g
  rw [hord] at hli
  have hq1 : 1 < q := hq.one_lt
  rcases eq_zero_or_eq_one_of_isIdempotentElem he with h0 | h1
  · have hs0 : s = 0 := by
      have := congrArg (fun y => (q : H) * y) h0
      simpa only [e, ← mul_assoc, mul_invOf_self, one_mul, mul_zero] using this
    have := (Fintype.linearIndependent_iff.mp hli) (fun _ => (1 : k)) (by
      simpa only [one_smul, GroupLike.val_pow] using hs0) ⟨0, hq.pos⟩
    exact one_ne_zero this
  · have hs1 : s = (q : H) := by
      have := congrArg (fun y => (q : H) * y) h1
      simpa only [e, ← mul_assoc, mul_invOf_self, one_mul, mul_one] using this
    let c : Fin q → k := fun i => if i = 0 then 1 - (q : k) else 1
    have hsum : ∑ i : Fin q, c i • x ^ (i : ℕ) = 0 := by
      have hsplit : ∀ i : Fin q, c i • x ^ (i : ℕ) =
          (1 : k) • x ^ (i : ℕ) - (if i = 0 then (q : k) • x ^ (i : ℕ) else 0) := by
        intro i
        by_cases hi : i = 0
        · simp only [c, ite_eq_left hi, sub_smul]
        · simp only [c, ite_eq_right hi, sub_zero]
      simp_rw [hsplit, Finset.sum_sub_distrib, one_smul]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.filter_eq' Finset.univ (0 : Fin q),
        ite_eq_left (Finset.mem_univ _), Finset.sum_singleton]
      change s - (q : k) • x ^ ((0 : Fin q) : ℕ) = 0
      rw [hs1, Fin.val_zero, pow_zero, Algebra.smul_def, mul_one, map_natCast, sub_self]
    have := (Fintype.linearIndependent_iff.mp hli) c hsum ⟨1, hq1⟩
    have hne : (⟨1, hq1⟩ : Fin q) ≠ 0 := fun h => Nat.one_ne_zero (congrArg Fin.val h)
    simp only [c, ite_eq_right hne] at this
    exact one_ne_zero this

theorem groupLike_eq_one_of_pow_eq_one [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
    (g : GroupLike k H) {n : ℕ} (hn : 0 < n) (hg : g ^ n = 1) : g = 1 := by
  have hfin : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hg⟩
  have hne : orderOf g ≠ 0 := hfin.orderOf_pos.ne'
  by_contra hg1
  have hord1 : orderOf g ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hord1
  have hordq : orderOf (g ^ (orderOf g / q)) = q := orderOf_pow_orderOf_div hne hqd
  by_cases hqk : (q : k) = 0
  · exact orderOf_ne_of_cast_eq_zero _ hq hqk hordq
  · exact orderOf_ne_of_cast_ne_zero _ hq hqk hordq

theorem isMulTorsionFree [IsReduced H] [ConnectedSpace (PrimeSpectrum H)] :
    IsMulTorsionFree (GroupLike k H) := by
  refine ⟨fun n hn a b _ hab => ?_⟩
  change a ^ n = b ^ n at hab
  have h : (a * b⁻¹) ^ n = 1 := by rw [mul_pow, hab, ← mul_pow, mul_inv_cancel, one_pow]
  have := groupLike_eq_one_of_pow_eq_one (a * b⁻¹) (Nat.pos_of_ne_zero hn) h
  exact mul_inv_eq_one.mp this

end Hopf

section GroupAlgebra

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]

/-- The additive character lattice of group-like elements. -/
abbrev CharLat : Type u := Additive (GroupLike k H)

variable {k H} in
/-- The underlying Hopf-algebra element of a character. -/
def gl (m : CharLat k H) : H := (Additive.toMul m : GroupLike k H).val

/-- The canonical inclusion of group-like elements with additive tags removed. -/
noncomputable def inclHom : Multiplicative (CharLat k H) →* H :=
  AddMonoidHom.toMultiplicativeLeft (MonoidHom.toAdditive (GroupLike.valMonoidHom k H))

/-- The group-algebra map induced by the character lattice. -/
noncomputable def φ : AddMonoidAlgebra k (CharLat k H) →ₐ[k] H :=
  AddMonoidAlgebra.lift k H (CharLat k H) (inclHom k H)

variable {k H}

theorem isGroupLikeElem_gl (m : CharLat k H) : IsGroupLikeElem k (gl m) :=
  (Additive.toMul m : GroupLike k H).2

theorem gl_add (m n : CharLat k H) : gl (m + n) = gl m * gl n := rfl

theorem gl_zero : gl (0 : CharLat k H) = 1 := rfl

theorem gl_neg (m : CharLat k H) : gl (-m) = HopfAlgebra.antipode k (gl m) := rfl

theorem φ_single (m : CharLat k H) (c : k) :
    φ k H (AddMonoidAlgebra.single m c) = c • gl m := by
  rw [φ, AddMonoidAlgebra.lift_single]
  rfl

theorem φ_apply (f : AddMonoidAlgebra k (CharLat k H)) :
    φ k H f = f.coeff.sum fun m c => c • gl m := by
  rw [φ, AddMonoidAlgebra.lift_apply]
  rfl

theorem φ_injective : Function.Injective (φ k H) := by
  have hli : LinearIndependent k (gl : CharLat k H → H) :=
    (linearIndep_groupLikeVal (R := k) (A := H)).comp _ Additive.toMul.injective
  intro f g hfg
  have : Finsupp.linearCombination k (gl : CharLat k H → H) f.coeff =
      Finsupp.linearCombination k (gl : CharLat k H → H) g.coeff := by
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, ← φ_apply, ← φ_apply]
    exact hfg
  exact AddMonoidAlgebra.coeff_injective (hli this)

variable (k H)

/-- The subalgebra spanned by group-like elements. -/
noncomputable def K : Subalgebra k H := (φ k H).range

variable {k H}

theorem mem_K_iff (x : H) : x ∈ K k H ↔ ∃ f : AddMonoidAlgebra k (CharLat k H), φ k H f = x :=
  AlgHom.mem_range _

theorem gl_mem (m : CharLat k H) : gl m ∈ K k H :=
  (mem_K_iff _).mpr ⟨AddMonoidAlgebra.single m 1, by rw [φ_single, one_smul]⟩

theorem comul_mem (x : H) (hx : x ∈ K k H) :
    comul (R := k) x ∈ Submodule.span k
      {t : H ⊗[k] H | ∃ a ∈ K k H, ∃ b ∈ K k H, t = a ⊗ₜ[k] b} := by
  obtain ⟨f, rfl⟩ := (mem_K_iff _).mp hx
  rw [φ_apply, map_finsuppSum]
  refine Submodule.sum_mem _ fun m _ => ?_
  dsimp only
  rw [map_smul]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨gl m, gl_mem m, gl m, gl_mem m, (isGroupLikeElem_gl m).comul_eq_tmul_self⟩

theorem antipode_mem (x : H) (hx : x ∈ K k H) : HopfAlgebra.antipode k x ∈ K k H := by
  obtain ⟨f, rfl⟩ := (mem_K_iff _).mp hx
  rw [φ_apply, map_finsuppSum]
  refine Subalgebra.sum_mem _ fun m _ => ?_
  dsimp only
  rw [map_smul, ← gl_neg]
  exact Subalgebra.smul_mem _ (gl_mem (-m)) _

theorem faithfullyFlat_K [Algebra.FiniteType k H] : Module.FaithfullyFlat (K k H) H :=
  HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem (K k H)
    (comul_mem (k := k) (H := H)) (antipode_mem (k := k) (H := H))

/-- The augmentation ideal generated by a chosen set of characters. -/
def augI (S : Set (CharLat k H)) : Ideal H := Ideal.span ((fun m => gl m - 1) '' S)

theorem augI_mono {S T : Set (CharLat k H)} (h : S ⊆ T) : augI S ≤ augI T :=
  Ideal.span_mono (Set.image_mono h)

theorem sub_one_mem_augI {S : Set (CharLat k H)} {m : CharLat k H} (hm : m ∈ S) :
    gl m - 1 ∈ augI S :=
  Ideal.subset_span ⟨m, hm, rfl⟩

/-- A character as an element of the group-like subalgebra. -/
noncomputable def glK (m : CharLat k H) : K k H := ⟨gl m, gl_mem m⟩

/-- The character augmentation ideal inside the group-like subalgebra. -/
noncomputable def augJ (S : Set (CharLat k H)) : Ideal (K k H) :=
  Ideal.span ((fun m => glK m - 1) '' S)

theorem map_augJ (S : Set (CharLat k H)) :
    (augJ S).map (algebraMap (K k H) H) = augI S := by
  rw [augJ, Ideal.map_span, ← Set.image_comp]
  rfl

/-- The quotient character map induced by a lattice quotient. -/
noncomputable def ψ (N : Submodule ℤ (CharLat k H)) :
    K k H →ₐ[k] AddMonoidAlgebra k (CharLat k H ⧸ N) :=
  (AddMonoidAlgebra.mapDomainAlgHom k k N.mkQ.toAddMonoidHom).comp
    (AlgEquiv.ofInjective (φ k H) φ_injective).symm.toAlgHom

theorem ψ_glK (N : Submodule ℤ (CharLat k H)) (m : CharLat k H) :
    ψ N (glK m) = AddMonoidAlgebra.single (N.mkQ m) 1 := by
  have h1 : (AlgEquiv.ofInjective (φ k H) φ_injective) (AddMonoidAlgebra.single m 1) = glK m := by
    apply Subtype.ext
    rw [AlgEquiv.ofInjective_apply, φ_single, one_smul]
    rfl
  have h2 : (AlgEquiv.ofInjective (φ k H) φ_injective).symm (glK m) =
      AddMonoidAlgebra.single m 1 := by
    rw [← h1, AlgEquiv.symm_apply_apply]
  change AddMonoidAlgebra.mapDomainAlgHom k k N.mkQ.toAddMonoidHom
    ((AlgEquiv.ofInjective (φ k H) φ_injective).symm (glK m)) = _
  rw [h2, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  rfl

theorem augJ_le_ker (N : Submodule ℤ (CharLat k H)) :
    augJ (N : Set (CharLat k H)) ≤ RingHom.ker (ψ N) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one]
  change ψ N (glK m) - 1 = 0
  rw [ψ_glK, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).mpr hm,
    AddMonoidAlgebra.one_def,
    sub_self]

theorem mem_of_sub_one_mem_augI [Algebra.FiniteType k H] (N : Submodule ℤ (CharLat k H))
    (m : CharLat k H) (hm : gl m - 1 ∈ augI (N : Set (CharLat k H))) : m ∈ N := by
  have : Module.FaithfullyFlat (K k H) H := faithfullyFlat_K
  have hJ : glK m - 1 ∈ augJ (N : Set (CharLat k H)) := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := H) (augJ (N : Set (CharLat k H))),
      Ideal.mem_comap, map_augJ, map_sub, map_one]
    exact hm
  have h0 : ψ N (glK m - 1) = 0 := augJ_le_ker N hJ
  rw [map_sub, map_one, ψ_glK, AddMonoidAlgebra.one_def, sub_eq_zero] at h0
  have : N.mkQ m = 0 :=
    (Finsupp.single_left_inj one_ne_zero).mp (congrArg AddMonoidAlgebra.coeff h0)
  rw [Submodule.mkQ_apply] at this
  exact (Submodule.Quotient.mk_eq_zero N).mp this

theorem moduleFinite_charLat [Algebra.FiniteType k H] : Module.Finite ℤ (CharLat k H) := by
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let e : Submodule ℤ (CharLat k H) ↪o Ideal H :=
    OrderEmbedding.ofMapLEIff (fun N => augI (N : Set (CharLat k H))) fun N₁ N₂ =>
      ⟨fun h m hm => mem_of_sub_one_mem_augI N₂ m (h (sub_one_mem_augI hm)),
        fun h => augI_mono h⟩
  have : WellFoundedGT (Submodule ℤ (CharLat k H)) := e.strictMono.wellFoundedGT
  have : IsNoetherian ℤ (CharLat k H) := isNoetherian_mk inferInstance
  infer_instance

theorem ringKrullDim_K [Module.Free ℤ (CharLat k H)] [Module.Finite ℤ (CharLat k H)] :
    ringKrullDim (K k H) = Module.finrank ℤ (CharLat k H) := by
  set r := Module.finrank ℤ (CharLat k H)
  let b : Module.Basis (Fin r) ℤ (CharLat k H) := Module.finBasis ℤ (CharLat k H)
  let e : CharLat k H ≃+ (Fin r → ℤ) := b.equivFun.toAddEquiv
  have h1 : ringKrullDim (K k H) = ringKrullDim (AddMonoidAlgebra k (CharLat k H)) :=
    ringKrullDim_eq_of_ringEquiv (AlgEquiv.ofInjective (φ k H) φ_injective).symm.toRingEquiv
  have h2 : ringKrullDim (AddMonoidAlgebra k (CharLat k H)) =
      ringKrullDim (AddMonoidAlgebra k (Fin r → ℤ)) :=
    ringKrullDim_eq_of_ringEquiv (AddMonoidAlgebra.domCongr k k e).toRingEquiv
  rw [h1, h2, AddMonoidAlgebra.ringKrullDim_pi_fin_int_eq]

theorem finrank_le_ringKrullDim [Algebra.FiniteType k H] [Module.Free ℤ (CharLat k H)]
    [Module.Finite ℤ (CharLat k H)] :
    (Module.finrank ℤ (CharLat k H) : WithBot ℕ∞) ≤ ringKrullDim H := by
  have : Module.FaithfullyFlat (K k H) H := faithfullyFlat_K
  rw [← ringKrullDim_K (k := k) (H := H)]
  exact ringKrullDim_le_of_faithfullyFlat (K k H) H

end GroupAlgebra

end CharacterLattice

end SchemeTheory.HopfGroupLike

namespace HopfAlgebra

universe u v w

open SchemeTheory.HopfGroupLike
open SchemeTheory.HopfGroupLike.CharacterLattice

theorem free_and_finite_and_finrank_groupLike_le_of_locally_isStandardSmoothOfRelativeDimension
    (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]
    [ConnectedSpace (PrimeSpectrum H)] (h : ℕ)
    (hsm : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension h) (algebraMap k H)) :
    Module.Free ℤ (Additive (GroupLike k H)) ∧ Module.Finite ℤ (Additive (GroupLike k H)) ∧
      Module.finrank ℤ (Additive (GroupLike k H)) ≤ h := by
  have : Algebra.FiniteType k H := finiteType k H h hsm
  have : IsReduced H := isReduced k H h hsm
  have hfin : Module.Finite ℤ (CharLat k H) := moduleFinite_charLat
  have : IsMulTorsionFree (GroupLike k H) := isMulTorsionFree
  have : HasUniqueRoots (GroupLike k H) :=
    ⟨fun _ hn a b hab => eq_of_pow_eq_pow_of_commute hn (Commute.all a b) hab⟩
  have hfree : Module.Free ℤ (CharLat k H) := Module.free_of_finite_type_torsion_free'
  refine ⟨hfree, hfin, ?_⟩
  have h1 := finrank_le_ringKrullDim (k := k) (H := H)
  have h2 := ringKrullDim_le k H h hsm
  exact_mod_cast h1.trans h2

end HopfAlgebra
end
