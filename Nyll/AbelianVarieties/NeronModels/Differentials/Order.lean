/-
Anthropic FLT source port.
Original copyright, authors, license and pinned sources are retained per unit below.
-/

module

public import Mathlib.Data.Set.PowersetCard
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Nyll.AbelianVarieties.NeronModels.Differentials.Localization
public import Nyll.SchemeTheory.RingTheory.Differentials.TopForms
public import Nyll.SchemeTheory.Modules.Frames.IsFrameOnSheafificationAdjunctionUnitIotaMulti
public import Nyll.ValuedFieldTheory.Valuation.ResidueTranscendence

/-!
# Orders of top differential forms

Compare integral top-form lattices under base change, express their generators by
basis determinants, and characterize equality of orders by invertibility of the differential map.
-/

@[expose] public section

open AbelianVarieties.NOSProofs.TopFormComposition.BenchOTFMComp
open AbelianVarieties.NOSProofs.TopFormValuation
open AlgebraicCurves.Geometry.Sheaves.Proofs.SheafifiedExteriorFrame
open AlgebraicGeometry.Scheme.Modules.Ws31H1

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_TopFormOrder_integralTopForms_eq_span_and_ord_smul_of_basis.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

open NeronModelInfra.TopFormOrder

namespace NeronModelInfra.TopFormOrder

theorem integralTopForms_eq_span_and_ord_smul_of_basis
    (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    (d : ℕ) (b : Module.Basis (Fin d) O (Ω[O⁄R'])) :
    let _ : Module O (⋀[F]^d (Ω[F⁄K'])) := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
    integralTopForms R' K' O F d =
        Submodule.span O {topFormMap R' K' O F d (exteriorPower.ιMulti O d b)} ∧
      ∀ a : F, a ≠ 0 → topFormMap R' K' O F d (exteriorPower.ιMulti O d b) ≠ 0 →
        ord R' K' O d F (a • topFormMap R' K' O F d (exteriorPower.ιMulti O d b)) = addOrd O F a :=
          by
  classical
  intro moduleO
  have h1 : integralTopForms R' K' O F d =
      Submodule.span O {topFormMap R' K' O F d (exteriorPower.ιMulti O d b)} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      obtain ⟨r, rfl⟩ := exists_eq_smul_ιMulti b x
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact ⟨_, rfl⟩
  refine ⟨h1, ?_⟩
  intro a ha hρ
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ⋀[F]^d (Ω[F⁄K']), ρ = topFormMap R' K' O F d (exteriorPower.ιMulti O d
    b) := ⟨_, rfl⟩
  rw [← hρdef] at h1 hρ ⊢
  have hex : ∃ ρ' : ⋀[F]^d (Ω[F⁄K']), integralTopForms R' K' O F d = Submodule.span O {ρ'} ∧
      ∃ a' : F, a • ρ = a' • ρ' := ⟨ρ, h1, a, rfl⟩
  change (if h : ∃ ρ' : ⋀[F]^d (Ω[F⁄K']), integralTopForms R' K' O F d = Submodule.span O {ρ'} ∧
      ∃ a' : F, a • ρ = a' • ρ' then addOrd O F h.choose_spec.2.choose else 0) = addOrd O F a
  rw [dite_eq_left hex]
  have hΛ₁ : integralTopForms R' K' O F d = Submodule.span O {hex.choose} := hex.choose_spec.1
  have hω₁ : a • ρ = hex.choose_spec.2.choose • hex.choose := hex.choose_spec.2.choose_spec
  have hspan : Submodule.span O {ρ} = Submodule.span O {hex.choose} := h1.symm.trans hΛ₁
  obtain ⟨c, hc⟩ : ∃ c : O, c • ρ = hex.choose :=
    Submodule.mem_span_singleton.mp (hspan.ge (Submodule.mem_span_singleton_self _))
  obtain ⟨c', hc'⟩ : ∃ c' : O, c' • hex.choose = ρ :=
    Submodule.mem_span_singleton.mp (hspan.le (Submodule.mem_span_singleton_self _))
  have hsmul : ∀ (r : O) (v : ⋀[F]^d (Ω[F⁄K'])), r • v = algebraMap O F r • v := fun r v => rfl
  have hinj : Function.Injective fun x : F => x • ρ := smul_left_injective F hρ
  have hcc : c' * c = 1 := by
    apply IsFractionRing.injective O F
    rw [map_one]
    apply hinj
    change algebraMap O F (c' * c) • ρ = (1 : F) • ρ
    rw [one_smul, map_mul, mul_smul, ← hsmul c, hc, ← hsmul, hc']
  have hcu : IsUnit c := ⟨⟨c, c', by rw [mul_comm]; exact hcc, hcc⟩, rfl⟩
  have hc0 : c ≠ 0 := hcu.ne_zero
  have haeq : a = hex.choose_spec.2.choose * algebraMap O F c := by
    apply hinj
    change a • ρ = (hex.choose_spec.2.choose * algebraMap O F c) • ρ
    rw [mul_smul, ← hsmul, hc, ← hω₁]
  have ha₁ : hex.choose_spec.2.choose ≠ 0 := by
    intro h0; apply ha; rw [haeq, h0, zero_mul]
  have hcF : algebraMap O F c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O F)).mpr hc0
  conv_rhs => rw [haeq]
  rw [OCA.addOrd_mul O F ha₁ hcF, (OCA.addOrd_algebraMap_eq_zero_iff O F hc0).mpr hcu, add_zero]

end NeronModelInfra.TopFormOrder
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_TopFormOrder_exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

open NeronModelInfra.TopFormOrder

open scoped TensorProduct

namespace AbelianVarieties.NOSProofs.TopFormDeterminants

namespace Determinants

lemma ιMulti_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {n : ℕ}
    (b : Module.Basis (Fin n) A M) (w : Fin n → M) :
    exteriorPower.ιMulti A n w = b.det w • exteriorPower.ιMulti A n b := by
  classical
  obtain ⟨r, hr⟩ := exists_eq_smul_ιMulti b (exteriorPower.ιMulti A n w)
  have h := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) hr
  rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self, smul_eq_mul,
      mul_one] at h
  rw [hr, h]

lemma map_map (R' K' O' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O'] [Algebra R' O'] [CommRing O] [Algebra R' O] [Algebra O' O] [IsScalarTower R' O' O]
    [CommRing F] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    (x : Ω[O'⁄R']) :
    KaehlerDifferential.map R' K' O F (KaehlerDifferential.map R' R' O' O x) =
      KaehlerDifferential.map R' K' O' F x :=
  kaehlerMap_kaehlerMap R' R' K' O' O F x

end Determinants

end AbelianVarieties.NOSProofs.TopFormDeterminants

open AbelianVarieties.NOSProofs.TopFormDeterminants

namespace NeronModelInfra.TopFormOrder

theorem exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange
    (R' K' O' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O'] [Algebra R' O'] [CommRing O] [Algebra R' O] [Algebra O' O] [IsScalarTower R' O' O]
    [CommRing F] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    (d : ℕ) (b' : Module.Basis (Fin d) O' (Ω[O'⁄R'])) (b : Module.Basis (Fin d) O (Ω[O⁄R'])) :
    ∃ h : O,
      (let _ : Module O' (⋀[F]^d (Ω[F⁄K'])) := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
       let _ : Module O (⋀[F]^d (Ω[F⁄K'])) := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
       topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') =
         algebraMap O F h • topFormMap R' K' O F d (exteriorPower.ιMulti O d b)) ∧
      (IsUnit h ↔ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O)) := by
  classical
  let φ : Ω[O'⁄R'] →ₗ[O'] Ω[O⁄R'] := KaehlerDifferential.map R' R' O' O
  let w : Fin d → Ω[O⁄R'] := fun j => φ (b' j)
  refine ⟨b.det w, ?_, ?_⟩
  · have h1 : topFormMap R' K' O F d (exteriorPower.ιMulti O d w) =
        b.det w • topFormMap R' K' O F d (exteriorPower.ιMulti O d b) := by
      rw [Determinants.ιMulti_eq_det_smul b w, map_smul]
    have h2 : topFormMap R' K' O F d (exteriorPower.ιMulti O d w) =
        topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') := by
      change exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O F d) (exteriorPower.ιMulti
        O d w) =
        exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O' F d) (exteriorPower.ιMulti O'
          d b')
      rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      change exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map R' K' O F (w i)) =
        exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map R' K' O' F (b' i))
      congr 1
      funext i
      exact Determinants.map_map R' K' O' O F (b' i)
    rw [← h2, h1]
    rfl
  · let Φ := KaehlerDifferential.mapBaseChange R' O' O
    let bO := Algebra.TensorProduct.basis O b'
    have hmat : b.toMatrix w = LinearMap.toMatrix bO b Φ := by
      ext i j
      rw [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
      congr 2
      change φ (b' j) = KaehlerDifferential.mapBaseChange R' O' O (Algebra.TensorProduct.basis O b'
        j)
      rw [Algebra.TensorProduct.basis_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]
    rw [Module.Basis.det_apply, hmat]
    constructor
    · intro hu
      have hcoe : ((LinearEquiv.ofIsUnitDet (f := Φ) (v := bO) (v' := b) hu : O ⊗[O'] Ω[O'⁄R'] ≃ₗ[O]
        Ω[O⁄R']) :
          O ⊗[O'] Ω[O'⁄R'] →ₗ[O] Ω[O⁄R']) = Φ := LinearEquiv.coe_ofIsUnitDet hu
      have : Function.Bijective (LinearEquiv.ofIsUnitDet (f := Φ) (v := bO) (v' := b) hu) :=
        (LinearEquiv.ofIsUnitDet (f := Φ) (v := bO) (v' := b) hu).bijective
      rwa [← LinearEquiv.coe_coe, hcoe] at this
    · intro hb
      have := LinearEquiv.isUnit_det (LinearEquiv.ofBijective Φ hb) bO b
      exact this

end NeronModelInfra.TopFormOrder
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_TopFormOrder_ord_topFormMap_eq_ord_of_map_maximalIdeal_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

open NeronModelInfra.TopFormOrder
open scoped TensorProduct

namespace AbelianVarieties.NOSProofs.TopFormOrderBaseChange

namespace OrderBaseChange

lemma map_two_towers (R R' K K' O₀ O F₀ F : Type u)
    [CommRing R] [CommRing R'] [Algebra R R']
    [Field K] [Algebra R K] [Field K'] [Algebra R' K']
    [Algebra K K'] [Algebra R K'] [IsScalarTower R K K'] [IsScalarTower R R' K']
    [CommRing O₀] [Algebra R O₀]
    [Field F₀] [Algebra O₀ F₀] [Algebra K F₀] [Algebra R F₀] [IsScalarTower R O₀ F₀] [IsScalarTower
      R K F₀]
    [CommRing O] [Algebra R' O]
    [Field F] [Algebra O F] [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R'
      K' F]
    [Algebra O₀ O] [Algebra R O] [IsScalarTower R O₀ O] [IsScalarTower R R' O]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F]
    [Algebra K F] [IsScalarTower K K' F] [IsScalarTower K F₀ F]
    (x : Ω[O₀⁄R]) :
    KaehlerDifferential.map K K' F₀ F (KaehlerDifferential.map R K O₀ F₀ x) =
      KaehlerDifferential.map R' K' O F (KaehlerDifferential.map R R' O O (KaehlerDifferential.map R
        R O₀ O x)) := by
  have key : ∀ x ∈ Submodule.span O₀ (Set.range (KaehlerDifferential.D R O₀)),
      KaehlerDifferential.map K K' F₀ F (KaehlerDifferential.map R K O₀ F₀ x) =
      KaehlerDifferential.map R' K' O F (KaehlerDifferential.map R R' O O (KaehlerDifferential.map R
        R O₀ O x)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, rfl⟩ := hy
      simp only [KaehlerDifferential.map_D]
      congr 1
      rw [← IsScalarTower.algebraMap_apply O₀ F₀ F, Algebra.algebraMap_self, RingHom.id_apply,
        ← IsScalarTower.algebraMap_apply O₀ O F]
    | zero => simp only [map_zero]
    | add y z _ _ hy hz => simp only [map_add, hy, hz]
    | smul s y _ hy =>
      rw [(KaehlerDifferential.map R K O₀ F₀).map_smul s y, (KaehlerDifferential.map R R O₀
        O).map_smul s y,
        ← IsScalarTower.algebraMap_smul F₀ s ((KaehlerDifferential.map R K O₀ F₀) y),
        (KaehlerDifferential.map K K' F₀ F).map_smul, hy,
        ← IsScalarTower.algebraMap_smul O s ((KaehlerDifferential.map R R O₀ O) y),
        (KaehlerDifferential.map R R' O O).map_smul, (KaehlerDifferential.map R' K' O F).map_smul,
        ← IsScalarTower.algebraMap_smul F (algebraMap O₀ F₀ s),
        ← IsScalarTower.algebraMap_smul F (algebraMap O₀ O s),
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  exact key x (by rw [KaehlerDifferential.span_range_derivation]; trivial)

lemma addOrd_pow (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L] {x : L} (hx : x ≠ 0) (n : ℕ) :
    addOrd O L (x ^ n) = n * addOrd O L x := by
  obtain ⟨hmul, -, hunit, -⟩ := addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer O L
  induction n with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, ← map_one (algebraMap O L)]
    exact (hunit 1 one_ne_zero).mpr isUnit_one
  | succ n ih => rw [pow_succ, hmul _ _ (pow_ne_zero n hx) hx, ih]; push_cast; ring

end OrderBaseChange

end AbelianVarieties.NOSProofs.TopFormOrderBaseChange

open AbelianVarieties.NOSProofs.TopFormOrderBaseChange

namespace NeronModelInfra.TopFormOrder

theorem ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
    (R R' K K' O₀ O F₀ F : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap
      R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K] [Algebra R K] [IsFractionRing R K] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra K K'] [Algebra R K'] [IsScalarTower R K K'] [IsScalarTower R R' K']
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap
      R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R'
      O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' K' F]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [Algebra R O] [IsScalarTower R O₀ O]
      [IsScalarTower R R' O]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F]
    [Algebra K F] [IsScalarTower K K' F] [IsScalarTower K F₀ F]
    (d : ℕ) (b : Module.Basis (Fin d) O₀ (Ω[O₀⁄R]))
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R
        O₀ O))
    (hρ : (let _ : Module O (⋀[F]^d (Ω[F⁄K'])) := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
      topFormMap R' K' O F d (exteriorPower.ιMulti O d
        (fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b i))))) ≠ 0)
    (a : F₀) (ha : a ≠ 0) :
    let _ : Module O₀ (⋀[F₀]^d (Ω[F₀⁄K])) := moduleAlong O₀ F₀ (⋀[F₀]^d (Ω[F₀⁄K]))
    let _ : Module F₀ (⋀[F]^d (Ω[F⁄K'])) := moduleAlong F₀ F (⋀[F]^d (Ω[F⁄K']))
    ord R' K' O d F (topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d
      b))) =
      ord R K O₀ d F₀ (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b)) := by
  intro moduleO₀ moduleF₀
  classical
  let _ : Module O (⋀[F]^d (Ω[F⁄K'])) := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  obtain ⟨hmul₀, hnn₀, hunit₀, hunif₀⟩ := addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer O₀
    F₀
  obtain ⟨hmul, hnn, hunit, hunif⟩ := addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer O F
  let e : (O ⊗[O₀] Ω[O₀⁄R]) ≃ₗ[O] Ω[O⁄R'] := LinearEquiv.ofBijective _ hbc
  let c : Module.Basis (Fin d) O (Ω[O⁄R']) := (Algebra.TensorProduct.basis O b).map e
  have hc : (c : Fin d → Ω[O⁄R']) =
      fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b i)) := by
    funext i
    change e (Algebra.TensorProduct.basis O b i) = _
    rw [Algebra.TensorProduct.basis_apply]
    change ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ
      KaehlerDifferential.mapBaseChange R O₀ O)
      ((1 : O) ⊗ₜ[O₀] b i) = _
    rw [LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      LinearMap.restrictScalars_apply]
  obtain ⟨ρ₀, hρ₀def⟩ : ∃ ρ₀ : ⋀[F₀]^d (Ω[F₀⁄K]), ρ₀ = topFormMap R K O₀ F₀ d (exteriorPower.ιMulti
    O₀ d b) :=
    ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ⋀[F]^d (Ω[F⁄K']), ρ = topFormMap R' K' O F d (exteriorPower.ιMulti O d
    c) := ⟨_, rfl⟩
  have hT : topFormMap K K' F₀ F d ρ₀ = ρ := by
    rw [hρ₀def, hρdef]
    change exteriorPower.alternatingMapLinearEquiv (ιMultiAlong K K' F₀ F d)
        (exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R K O₀ F₀ d) (exteriorPower.ιMulti O₀
          d b)) =
      exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O F d) (exteriorPower.ιMulti O d c)
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change exteriorPower.alternatingMapLinearEquiv (ιMultiAlong K K' F₀ F d)
        (exteriorPower.ιMulti F₀ d (fun i => KaehlerDifferential.map R K O₀ F₀ (b i))) = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map K K' F₀ F
      (KaehlerDifferential.map R K O₀ F₀ (b i))) =
      exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map R' K' O F (c i))
    congr 1
    funext i
    rw [hc]
    exact OrderBaseChange.map_two_towers R R' K K' O₀ O F₀ F (b i)
  have hρ' : ρ ≠ 0 := by rw [hρdef, hc]; exact hρ
  have hρ₀ : ρ₀ ≠ 0 := by
    intro h0; apply hρ'; rw [← hT, h0, map_zero]
  have hω : topFormMap K K' F₀ F d (a • ρ₀) = algebraMap F₀ F a • ρ := by
    rw [map_smul, hT]; rfl
  have haF : algebraMap F₀ F a ≠ 0 := (map_ne_zero_iff _ (algebraMap F₀ F).injective).mpr ha
  have hω' : topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b)) =
      algebraMap F₀ F a • topFormMap R' K' O F d (exteriorPower.ιMulti O d c) := by
    rw [← hρ₀def, hω, hρdef]
  have hρc : topFormMap R' K' O F d (exteriorPower.ιMulti O d c) ≠ 0 := by rw [← hρdef]; exact hρ'
  have hρb : topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b) ≠ 0 := by rw [← hρ₀def]; exact hρ₀
  rw [hω', (integralTopForms_eq_span_and_ord_smul_of_basis R' K' O F d c).2 _ haF hρc,
    (integralTopForms_eq_span_and_ord_smul_of_basis R K O₀ F₀ d b).2 _ ha hρb]
  have key : ∀ x : O₀, x ≠ 0 →
      addOrd O F (algebraMap F₀ F (algebraMap O₀ F₀ x)) = addOrd O₀ F₀ (algebraMap O₀ F₀ x) := by
    intro x hx
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hπm : IsLocalRing.maximalIdeal R = Ideal.span {π} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
    have hπO₀ : IsLocalRing.maximalIdeal O₀ = Ideal.span {algebraMap R O₀ π} := by
      rw [← hO₀, hπm, Ideal.map_span, Set.image_singleton]
    have hπR' : IsLocalRing.maximalIdeal R' = Ideal.span {algebraMap R R' π} := by
      rw [← hRR', hπm, Ideal.map_span, Set.image_singleton]
    have h1O₀ : addOrd O₀ F₀ (algebraMap O₀ F₀ (algebraMap R O₀ π)) = 1 := hunif₀ R hO₀ π hπm
    have h1O : addOrd O F (algebraMap O F (algebraMap R' O (algebraMap R R' π))) = 1 := hunif R' hO
      _ hπR'
    have hirr₀ : Irreducible (algebraMap R O₀ π) :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hπO₀
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hirr₀
    have hπ₀F₀ : algebraMap O₀ F₀ (algebraMap R O₀ π) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O₀ F₀)).mpr hirr₀.ne_zero
    have hxF₀ : algebraMap O₀ F₀ x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O₀ F₀)).mpr
      hx
    have huF₀ : algebraMap O₀ F₀ (u : O₀) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O₀
      F₀)).mpr u.ne_zero
    have e₀ : addOrd O₀ F₀ (algebraMap O₀ F₀ x) = n := by
      have := congrArg (fun y => addOrd O₀ F₀ (algebraMap O₀ F₀ y)) hu
      simp only [map_mul, map_pow] at this
      rw [hmul₀ _ _ hxF₀ huF₀, (hunit₀ _ u.ne_zero).mpr u.isUnit, add_zero,
        OrderBaseChange.addOrd_pow O₀ F₀ hπ₀F₀, h1O₀, mul_one] at this
      exact this
    have hOF : ∀ y : O₀, algebraMap F₀ F (algebraMap O₀ F₀ y) = algebraMap O F (algebraMap O₀ O y)
      := by
      intro y
      rw [← IsScalarTower.algebraMap_apply O₀ F₀ F, ← IsScalarTower.algebraMap_apply O₀ O F]
    have huO : algebraMap O₀ O x * algebraMap O₀ O (u : O₀) = (algebraMap R' O (algebraMap R R' π))
      ^ n := by
      rw [← map_mul, hu, map_pow, ← IsScalarTower.algebraMap_apply R O₀ O,
        IsScalarTower.algebraMap_apply R R' O]
    have hπO : algebraMap R' O (algebraMap R R' π) ≠ 0 := by
      intro h0
      apply IsDiscreteValuationRing.not_a_field O
      rw [← hO, hπR', Ideal.map_span, Set.image_singleton, h0, Ideal.span_singleton_eq_bot]
    have huOunit : IsUnit (algebraMap O₀ O (u : O₀)) := u.isUnit.map _
    have hxO : algebraMap O₀ O x ≠ 0 := by
      intro h0
      have : (algebraMap R' O (algebraMap R R' π)) ^ n = 0 := by rw [← huO, h0, zero_mul]
      exact pow_ne_zero n hπO this
    have hπOF : algebraMap O F (algebraMap R' O (algebraMap R R' π)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O F)).mpr hπO
    have hxOF : algebraMap O F (algebraMap O₀ O x) ≠ 0 := (map_ne_zero_iff _
      (IsFractionRing.injective O F)).mpr hxO
    have huOF : algebraMap O F (algebraMap O₀ O (u : O₀)) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O F)).mpr huOunit.ne_zero
    have e₁ : addOrd O F (algebraMap O F (algebraMap O₀ O x)) = n := by
      have := congrArg (fun y => addOrd O F (algebraMap O F y)) huO
      simp only [map_mul, map_pow] at this
      rw [hmul _ _ hxOF huOF, (hunit _ huOunit.ne_zero).mpr huOunit, add_zero,
        OrderBaseChange.addOrd_pow O F hπOF, h1O, mul_one] at this
      exact this
    rw [hOF, e₁, e₀]
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := O₀) a
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hyF₀ : algebraMap O₀ F₀ y ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O₀ F₀)).mpr hy0
  have hx0 : x ≠ 0 := by
    intro h0; apply ha; rw [← hxy, h0, map_zero, zero_div]
  have hxF₀ : algebraMap O₀ F₀ x ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O₀ F₀)).mpr hx0
  have hay : a * algebraMap O₀ F₀ y = algebraMap O₀ F₀ x := by
    rw [← hxy, div_mul_cancel₀ _ hyF₀]
  have e₂ : addOrd O₀ F₀ a + addOrd O₀ F₀ (algebraMap O₀ F₀ y) = addOrd O₀ F₀ (algebraMap O₀ F₀ x)
    := by
    rw [← hmul₀ _ _ ha hyF₀, hay]
  have hyF : algebraMap F₀ F (algebraMap O₀ F₀ y) ≠ 0 := (map_ne_zero_iff _ (algebraMap F₀
    F).injective).mpr hyF₀
  have e₃ : addOrd O F (algebraMap F₀ F a) + addOrd O F (algebraMap F₀ F (algebraMap O₀ F₀ y)) =
      addOrd O F (algebraMap F₀ F (algebraMap O₀ F₀ x)) := by
    rw [← hmul _ _ haF hyF, ← map_mul, hay]
  rw [key x hx0, key y hy0] at e₃
  linarith

end NeronModelInfra.TopFormOrder
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_TopFormOrder_le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

open NeronModelInfra.TopFormOrder

namespace AbelianVarieties.NOSProofs.TopFormOrderComparison

namespace OrderComparison

theorem addOrd_zpow (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L]
    (hmul : ∀ a b : L, a ≠ 0 → b ≠ 0 → addOrd O L (a * b) = addOrd O L a + addOrd O L b)
    (x : L) (hx : x ≠ 0) (m : ℤ) : addOrd O L (x ^ m) = m * addOrd O L x := by
  have h1 : addOrd O L 1 = 0 := by
    have := hmul 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  have hnat : ∀ n : ℕ, addOrd O L (x ^ n) = n * addOrd O L x := by
    intro n
    induction n with
    | zero => rw [pow_zero, h1, Nat.cast_zero, zero_mul]
    | succ n ih =>
      rw [pow_succ, hmul _ _ (pow_ne_zero n hx) hx, ih]
      push_cast; ring
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, hnat]
  · have hinv : addOrd O L (x ^ (-(n : ℤ))) + addOrd O L (x ^ (n : ℤ)) = 0 := by
      rw [← hmul _ _ (zpow_ne_zero _ hx) (zpow_ne_zero _ hx), ← zpow_add₀ hx, neg_add_cancel,
        zpow_zero, h1]
    rw [zpow_natCast, hnat] at hinv
    linarith

theorem main
    (R' K' O' O F : Type u)
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K']
      [IsFractionRing R' K']
    (ϖ : R') (hϖ : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ})
    [CommRing O'] [IsDomain O'] [Algebra R' O']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R'
      O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra O' O] [IsScalarTower R' O' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F]
      [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R'
      K' F]
    (d : ℕ) (b' : Module.Basis (Fin d) O' (Ω[O'⁄R'])) (b : Module.Basis (Fin d) O (Ω[O⁄R']))
    (m : ℤ) (u : O'ˣ) (σ : ⋀[F]^d (Ω[F⁄K']))
    (hσ : let _ : Module O' (⋀[F]^d (Ω[F⁄K'])) := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
      σ = (algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ) ^ m) •
        topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b')) :
    m ≤ ord R' K' O d F σ ∧
    (ord R' K' O d F σ = m ↔ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O)) := by
  obtain ⟨h, hρ', hunit⟩ :=
    exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange
      R' K' O' O F d b' b
  obtain ⟨hρne, -⟩ :=
    topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq R' K' O F d b
  obtain ⟨hρ'ne, -⟩ :=
    topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq R' K' O' F d b'
  obtain ⟨-, hordsmul⟩ :=
    integralTopForms_eq_span_and_ord_smul_of_basis R' K' O F d b
  obtain ⟨hmul, hnonneg, hzero, hunif⟩ :=
    addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer O F
  have hϖ1 : addOrd O F (algebraMap O F (algebraMap R' O ϖ)) = 1 := hunif R' hO ϖ hϖ
  set ρ := (let _ : Module O (⋀[F]^d (Ω[F⁄K'])) := moduleAlong O F (⋀[F]^d (Ω[F⁄K'])); topFormMap R'
    K' O F d (exteriorPower.ιMulti O d b)) with hρdef
  set ρ' := (let _ : Module O' (⋀[F]^d (Ω[F⁄K'])) := moduleAlong O' F (⋀[F]^d (Ω[F⁄K'])); topFormMap
    R' K' O' F d (exteriorPower.ιMulti O' d b')) with hρ'def
  have hh0 : h ≠ 0 := by
    intro h0
    apply hρ'ne
    have : ρ' = algebraMap O F h • ρ := hρ'
    rw [this, h0, map_zero, zero_smul]
  have hhF : algebraMap O F h ≠ 0 := fun e => hh0 ((IsFractionRing.injective O F) (by rw [e,
    map_zero]))
  have hϖF : algebraMap O' F (algebraMap R' O' ϖ) = algebraMap O F (algebraMap R' O ϖ) := by
    rw [← IsScalarTower.algebraMap_apply R' O' F, ← IsScalarTower.algebraMap_apply R' O F]
  have hϖne : algebraMap O F (algebraMap R' O ϖ) ≠ 0 := by
    intro e
    have : addOrd O F (algebraMap O F (algebraMap R' O ϖ)) = 0 := by
      rw [e]; unfold addOrd; rw [dite_eq_left rfl]
    rw [hϖ1] at this
    exact one_ne_zero this
  have huF : algebraMap O' F (u : O') = algebraMap O F (algebraMap O' O (u : O')) :=
    IsScalarTower.algebraMap_apply O' O F _
  have huO : IsUnit (algebraMap O' O (u : O')) := (Units.isUnit u).map _
  have huO0 : algebraMap O' O (u : O') ≠ 0 := huO.ne_zero
  have huFne : algebraMap O F (algebraMap O' O (u : O')) ≠ 0 :=
    fun e => huO0 ((IsFractionRing.injective O F) (by rw [e, map_zero]))
  have hu0 : addOrd O F (algebraMap O F (algebraMap O' O (u : O'))) = 0 := (hzero _ huO0).mpr huO
  set a : F := algebraMap O F (algebraMap O' O (u : O')) * algebraMap O F (algebraMap R' O ϖ) ^ m *
    algebraMap O F h
    with ha
  have hσa : σ = a • ρ := by
    have e1 : σ = (algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ) ^ m) • ρ' := hσ
    have e2 : ρ' = algebraMap O F h • ρ := hρ'
    rw [e1, e2, smul_smul, huF, hϖF]
  have hane : a ≠ 0 := mul_ne_zero (mul_ne_zero huFne (zpow_ne_zero _ hϖne)) hhF
  have hord : ord R' K' O d F σ = m + addOrd O F (algebraMap O F h) := by
    rw [hσa]
    have := hordsmul a hane hρne
    change ord R' K' O d F (a • ρ) = addOrd O F a at this
    rw [this, ha, hmul _ _ (mul_ne_zero huFne (zpow_ne_zero _ hϖne)) hhF,
      hmul _ _ huFne (zpow_ne_zero _ hϖne), hu0, addOrd_zpow O F hmul _ hϖne, hϖ1]
    ring
  refine ⟨?_, ?_⟩
  · rw [hord]; have := hnonneg h; omega
  · rw [hord, ← hunit, ← hzero h hh0]
    constructor
    · intro e; omega
    · intro e; omega

end OrderComparison

end AbelianVarieties.NOSProofs.TopFormOrderComparison

open AbelianVarieties.NOSProofs.TopFormOrderComparison

namespace NeronModelInfra.TopFormOrder

theorem le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
    (R' K' O' O F : Type u)
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Field K'] [Algebra R' K']
      [IsFractionRing R' K']
    (ϖ : R') (hϖ : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ})
    [CommRing O'] [IsDomain O'] [Algebra R' O']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R'
      O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra O' O] [IsScalarTower R' O' O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F]
      [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R'
      K' F]
    (d : ℕ) (b' : Module.Basis (Fin d) O' (Ω[O'⁄R'])) (b : Module.Basis (Fin d) O (Ω[O⁄R']))
    (m : ℤ) (u : O'ˣ) (σ : ⋀[F]^d (Ω[F⁄K']))
    (hσ : let _ : Module O' (⋀[F]^d (Ω[F⁄K'])) := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
      σ = (algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ) ^ m) •
        topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b')) :
    m ≤ ord R' K' O d F σ ∧
    (ord R' K' O d F σ = m ↔ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O)) :=
  OrderComparison.main R' K' O' O F ϖ hϖ hO d b' b m u σ hσ

end NeronModelInfra.TopFormOrder
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_TopFormOrder_exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

open _root_.NeronModelInfra
open _root_.NeronModelInfra.TopFormOrder

universe u

namespace NeronModelInfra.TopFormOrder

theorem exists_basis_units_int_forall_topFormMap_eq_mul_zpow_smul_of_span_singleton_eq_top
    (R K B B' O : Type u) [CommRing R] [CommRing K] [Algebra R K] (ϖ : R) [IsLocalization.Away ϖ K]
    [CommRing B] [Algebra R B] [CommRing B'] [Algebra B B'] [Algebra K B'] [Algebra R B']
    [IsScalarTower R B B'] [IsScalarTower R K B'] [IsLocalization.Away (algebraMap R B ϖ) B']
    (d : ℕ) (β : Module.Basis (Fin d) B (Ω[B⁄R]))
    (σ : ⋀[B']^d (Ω[B'⁄K])) (hσ : Submodule.span B' {σ} = ⊤)
    [CommRing O] [IsDomain O] [IsNoetherianRing O] [Algebra B O] [Algebra R O] [IsScalarTower R B O]
    (M : Submonoid B) [IsLocalization M O]
    (hϖ0 : algebraMap R O ϖ ≠ 0) (hϖ : (Ideal.span {algebraMap R O ϖ}).IsPrime) :
    ∃ (b' : Module.Basis (Fin d) O (Ω[O⁄R])) (w : Oˣ) (m : ℤ),
      (∀ i, b' i = KaehlerDifferential.map R R B O (β i)) ∧
      ∀ (F : Type u) [Field F] [Algebra O F] [Algebra R F] [Algebra K F] [Algebra B F] [Algebra B'
        F]
        [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower B O F] [IsScalarTower R B F]
        [IsScalarTower B B' F] [IsScalarTower K B' F],
        topFormMap K K B' F d σ =
          (algebraMap O F (w : O) * algebraMap O F (algebraMap R O ϖ) ^ m) •
            topFormMap R K O F d (exteriorPower.ιMulti O d b') := by
  classical
  have hloc : IsLocalizedModule M (KaehlerDifferential.map R R B O) :=
    KaehlerDifferential.isLocalizedModule_map R B O M
  let b' : Module.Basis (Fin d) O (Ω[O⁄R]) := β.ofIsLocalizedModule O M (KaehlerDifferential.map R R
    B O)
  have hb' : ∀ i, b' i = KaehlerDifferential.map R R B O (β i) := fun i =>
    β.ofIsLocalizedModule_apply O M (KaehlerDifferential.map R R B O) i
  obtain ⟨-, hlaur⟩ :=
    span_topFormMap_iotaMulti_eq_top_and_exists_units_eq_smul_of_isLocalization_away
      R K B B' ϖ d β
  obtain ⟨u, hu⟩ := hlaur σ hσ
  obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hbk⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R B ϖ)) (u :
    B')
  obtain ⟨⟨c, ⟨_, l, rfl⟩⟩, hcl⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R B ϖ)) ((u⁻¹
    : B'ˣ) : B')
  simp only at hbk hcl
  have hbc' : algebraMap B B' (b * c) = algebraMap B B' (algebraMap R B ϖ ^ (k + l)) := by
    have hu1 : (u : B') * ((u⁻¹ : B'ˣ) : B') = 1 := Units.mul_inv u
    rw [map_mul, ← hbk, ← hcl]
    simp only [map_pow, map_mul, pow_add]
    linear_combination (algebraMap B B' (algebraMap R B ϖ) ^ k * algebraMap B B' (algebraMap R B ϖ)
      ^ l) * hu1
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R B ϖ))
    hbc'
  simp only at hN
  set π : O := algebraMap R O ϖ with hπ
  have hπB : algebraMap B O (algebraMap R B ϖ) = π := (IsScalarTower.algebraMap_apply R B O ϖ).symm
  have hbc : algebraMap B O b * algebraMap B O c = π ^ (k + l) := by
    have := congrArg (algebraMap B O) hN
    rw [map_mul, map_mul, map_mul, map_pow, map_pow, hπB] at this
    exact mul_left_cancel₀ (pow_ne_zero N hϖ0) this
  have hb0 : algebraMap B O b ≠ 0 := by
    intro h0; apply pow_ne_zero (k + l) hϖ0; rw [← hbc, h0, zero_mul]
  let L := FractionRing O
  have hπL : algebraMap O L π ≠ 0 := fun e => hϖ0 ((IsFractionRing.injective O L) (by rw [e,
    map_zero]))
  have hbL : algebraMap O L (algebraMap B O b) ≠ 0 :=
    fun e => hb0 ((IsFractionRing.injective O L) (by rw [e, map_zero]))
  set a : L := algebraMap O L (algebraMap B O b) / algebraMap O L π ^ k with ha
  have ha0 : a ≠ 0 := div_ne_zero hbL (pow_ne_zero _ hπL)
  obtain ⟨n, w, hw⟩ :=
    IsNoetherianRing.exists_unit_mul_zpow_eq_of_span_singleton_isPrime π hϖ hϖ0 a
      ⟨k, algebraMap B O b, by rw [ha, div_mul_cancel₀ _ (pow_ne_zero _ hπL)]⟩
      ⟨l, algebraMap B O c, by
        rw [ha, inv_div, div_mul_eq_mul_div, ← pow_add, div_eq_iff hbL, ← map_pow, ← hbc, map_mul]
        exact mul_comm _ _⟩
      ha0
  have hO : algebraMap B O b * π ^ (-(n + k)).toNat = (w : O) * π ^ (n + k).toNat := by
    apply IsFractionRing.injective O L
    rw [map_mul, map_mul, map_pow, map_pow]
    have e1 : algebraMap O L (algebraMap B O b) = a * algebraMap O L π ^ k := by
      rw [ha, div_mul_cancel₀ _ (pow_ne_zero _ hπL)]
    rw [e1, hw]
    rw [← zpow_natCast (algebraMap O L π) k, ← zpow_natCast (algebraMap O L π) (-(n+k)).toNat,
      ← zpow_natCast (algebraMap O L π) (n+k).toNat, mul_assoc, mul_assoc, ← zpow_add₀ hπL, ←
        zpow_add₀ hπL]
    congr 2
    have := (n + k).toNat_sub_toNat_neg
    omega
  refine ⟨b', w, n, hb', ?_⟩
  intro F _ _ _ _ _ _ _ _ _ _ _ _
  let _ : Module B' (⋀[F]^d (Ω[F⁄K])) := moduleAlong B' F (⋀[F]^d (Ω[F⁄K]))
  let _ : Module O (⋀[F]^d (Ω[F⁄K])) := moduleAlong O F (⋀[F]^d (Ω[F⁄K]))
  let _ : Module B (⋀[B']^d (Ω[B'⁄K])) := moduleAlong B B' (⋀[B']^d (Ω[B'⁄K]))
  have hϖF : algebraMap O F (algebraMap R O ϖ) = algebraMap K F (algebraMap R K ϖ) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hϖF0 : algebraMap O F (algebraMap R O ϖ) ≠ 0 := by
    rw [hϖF]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := K) ϖ).map (algebraMap K F)).ne_zero
  have hρ : topFormMap K K B' F d (topFormMap R K B B' d (exteriorPower.ιMulti B d β)) =
      topFormMap R K O F d (exteriorPower.ιMulti O d b') := by
    rw [topFormMap_topFormMap, topFormMap_ιMulti,
      topFormMap_ιMulti]
    congr 1
    funext i
    rw [hb', kaehlerMap_kaehlerMap R R K B O F]
  have huF : algebraMap B' F (u : B') = algebraMap O F (w : O) * algebraMap O F (algebraMap R O ϖ) ^
    n := by
    set p := algebraMap O F π with hp
    have hp0 : p ≠ 0 := hϖF0
    have e1 : algebraMap B' F (u : B') * p ^ k = algebraMap O F (algebraMap B O b) := by
      have := congrArg (algebraMap B' F) hbk
      simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply B B' F] at this
      simp only [IsScalarTower.algebraMap_apply B O F, hπB] at this
      exact this
    have e2 := congrArg (algebraMap O F) hO
    rw [map_mul, map_mul, map_pow, map_pow] at e2
    have e3 : algebraMap B' F (u : B') * p ^ (k + (-(n + k)).toNat) = algebraMap O F (w : O) * p ^
      (n + k).toNat := by
      rw [pow_add, ← mul_assoc, e1, e2]
    have h3 : algebraMap B' F (u : B') =
        algebraMap O F (w : O) * p ^ (n + k).toNat * (p ^ (k + (-(n + k)).toNat))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ hp0), e3]
    rw [h3, ← zpow_natCast p (n + k).toNat, ← zpow_natCast p (k + (-(n + k)).toNat), ← zpow_neg,
      mul_assoc,
      ← zpow_add₀ hp0]
    congr 2
    have := (n + k).toNat_sub_toNat_neg
    push_cast
    omega
  have hσ' : σ = (u : B') • topFormMap R K B B' d (exteriorPower.ιMulti B d β) := hu
  rw [hσ', LinearMap.map_smul]
  change algebraMap B' F (u : B') • topFormMap K K B' F d (topFormMap R K B B' d
    (exteriorPower.ιMulti B d β)) = _
  rw [hρ, huF]

end NeronModelInfra.TopFormOrder
end

section
/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned revision):
https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_NeronModelInfra_TopFormOrder_eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/ATTRIBUTION.md
Copies of these notices are retained in the AbelianVarieties directory.
Existing upstream author/copyright comments in the source are retained below.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

universe u

open TensorProduct NeronModelInfra.TopFormOrder

namespace NeronModelInfra.TopFormOrder

theorem eq_addOrd_and_bijective_mapBaseChange_of_topFormMap_eq_of_addOrd_le
    (R K R' K' : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R =
      Ideal.span {ϖ})
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap
      R R')]
    (hRR' : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    [Field K'] [Algebra R' K'] [IsFractionRing R' K'] [Algebra K K'] [Algebra R K']
    [IsScalarTower R K K'] [IsScalarTower R R' K']
    (O₀ F₀ : Type u)
    [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Algebra R O₀] [IsLocalHom (algebraMap
      R O₀)]
    (hO₀ : Ideal.map (algebraMap R O₀) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal O₀)
    [Field F₀] [Algebra O₀ F₀] [IsFractionRing O₀ F₀] [Algebra K F₀] [Algebra R F₀]
    [IsScalarTower R O₀ F₀] [IsScalarTower R K F₀]
    (d : ℕ) (b₀ : Module.Basis (Fin d) O₀ (Ω[O₀⁄R])) (a : F₀) (ha : a ≠ 0)
    (O₁ O' : Type u)
    [CommRing O₁] [Algebra R O₁]
    [CommRing O'] [IsDomain O'] [Algebra R' O'] [Algebra O₁ O'] [Algebra R O']
    [IsScalarTower R O₁ O'] [IsScalarTower R R' O']
    (b₁ : Module.Basis (Fin d) O₁ (Ω[O₁⁄R])) (w₁ : O₁ˣ) (m : ℤ)
    (hbc' : Function.Bijective
      ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ KaehlerDifferential.mapBaseChange
        R O₁ O'))
    (O F : Type u)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra R' O] [IsLocalHom (algebraMap R'
      O)]
    (hO : Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O)
    [Algebra R O] [IsScalarTower R R' O]
    [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)] [IsScalarTower R O₀ O]
    [Algebra O' O] [IsScalarTower R' O' O] [Algebra O₁ O] [IsScalarTower O₁ O' O] [IsScalarTower R
      O₁ O]
    (hbc : Function.Bijective
      ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ KaehlerDifferential.mapBaseChange R
        O₀ O))
    [Field F] [Algebra O F] [IsFractionRing O F] [Algebra O' F] [IsScalarTower O' O F]
      [IsFractionRing O' F]
    [Algebra K' F] [Algebra R' F] [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R'
      K' F]
    [Algebra K F] [Algebra R F] [IsScalarTower R O F] [IsScalarTower R K F] [IsScalarTower K K' F]
    [Algebra F₀ F] [Algebra O₀ F] [IsScalarTower O₀ O F] [IsScalarTower O₀ F₀ F] [IsScalarTower K F₀
      F]
    [Algebra O₁ F] [IsScalarTower O₁ O F] [IsScalarTower R O₁ F]
    (σ : ⋀[F]^d (Ω[F⁄K]))
    (hT : σ = (algebraMap O₁ F (w₁ : O₁) * algebraMap O₁ F (algebraMap R O₁ ϖ) ^ m) •
        topFormMap R K O₁ F d (exteriorPower.ιMulti O₁ d b₁))
    (hX : topFormMap K K' F F d σ =
        topFormMap K K' F₀ F d (a • topFormMap R K O₀ F₀ d (exteriorPower.ιMulti O₀ d b₀)))
    (hmin : addOrd O₀ F₀ a ≤ m) :
    m = addOrd O₀ F₀ a ∧ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O) := by
  classical
  have : IsScalarTower R K' F := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R K F, IsScalarTower.algebraMap_eq R K K', ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq K K' F])
  have : IsScalarTower O₁ O' F := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq O₁ O F, IsScalarTower.algebraMap_eq O₁ O' O,
      IsScalarTower.algebraMap_eq O' O F, RingHom.comp_assoc])
  have : IsScalarTower R O' F := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R O F, IsScalarTower.algebraMap_eq R R' O, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R' O F, IsScalarTower.algebraMap_eq R' O' F, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq R R' O'])
  set ϖ' : R' := algebraMap R R' ϖ with hϖ'def
  have hϖ' : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ'} := by
    rw [← hRR', hϖ, Ideal.map_span, Set.image_singleton]
  let eO : (O ⊗[O₀] Ω[O₀⁄R]) ≃ₗ[O] Ω[O⁄R'] := LinearEquiv.ofBijective _ hbc
  let b : Module.Basis (Fin d) O (Ω[O⁄R']) := (Algebra.TensorProduct.basis O b₀).map eO
  have hbcoe : (b : Fin d → Ω[O⁄R']) =
      fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b₀ i)) := by
    funext i
    change eO (Algebra.TensorProduct.basis O b₀ i) = _
    rw [Algebra.TensorProduct.basis_apply]
    change ((KaehlerDifferential.map R R' O O).restrictScalars O ∘ₗ
      KaehlerDifferential.mapBaseChange R O₀ O)
      ((1 : O) ⊗ₜ[O₀] b₀ i) = _
    rw [LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      LinearMap.restrictScalars_apply]
  let eO' : (O' ⊗[O₁] Ω[O₁⁄R]) ≃ₗ[O'] Ω[O'⁄R'] := LinearEquiv.ofBijective _ hbc'
  let b' : Module.Basis (Fin d) O' (Ω[O'⁄R']) := (Algebra.TensorProduct.basis O' b₁).map eO'
  have hb'coe : ∀ i, b' i = KaehlerDifferential.map R R' O₁ O' (b₁ i) := by
    intro i
    change eO' (Algebra.TensorProduct.basis O' b₁ i) = _
    rw [Algebra.TensorProduct.basis_apply]
    change ((KaehlerDifferential.map R R' O' O').restrictScalars O' ∘ₗ
      KaehlerDifferential.mapBaseChange R O₁ O')
      ((1 : O') ⊗ₜ[O₁] b₁ i) = _
    rw [LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul,
      LinearMap.restrictScalars_apply]
    exact kaehlerMap_kaehlerMap R R R' O₁ O' O' (b₁ i)
  have hgen : topFormMap K K' F F d (topFormMap R K O₁ F d (exteriorPower.ιMulti O₁ d b₁)) =
      topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') := by
    rw [topFormMap_topFormMap R K K' O₁ F F d, ← topFormMap_topFormMap R R' K' O₁ O' F d,
      topFormMap_ιMulti R R' O₁ O' d,
      show (⇑b' : Fin d → Ω[O'⁄R']) = fun i => KaehlerDifferential.map R R' O₁ O' (b₁ i) from funext
        hb'coe]
  set u : O'ˣ := Units.map (algebraMap O₁ O').toMonoidHom w₁ with hudef
  have hu : (u : O') = algebraMap O₁ O' (w₁ : O₁) := rfl
  have hcoef : algebraMap O₁ F (w₁ : O₁) * algebraMap O₁ F (algebraMap R O₁ ϖ) ^ m =
      algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ') ^ m := by
    rw [hu, ← IsScalarTower.algebraMap_apply O₁ O' F, hϖ'def, ← IsScalarTower.algebraMap_apply R R'
      O',
      ← IsScalarTower.algebraMap_apply R O' F, ← IsScalarTower.algebraMap_apply R O₁ F]
  have hσ' : topFormMap K K' F F d σ =
      (algebraMap O' F (u : O') * algebraMap O' F (algebraMap R' O' ϖ') ^ m) •
        topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') := by
    rw [hT, LinearMap.map_smul, hgen, hcoef]
  obtain ⟨hle, hiff⟩ :=
    le_ord_and_ord_eq_iff_bijective_mapBaseChange_of_eq_unit_mul_zpow_smul
      R' K' O' O F ϖ' hϖ' hO d b' b m u (topFormMap K K' F F d σ) hσ'
  have hρO : topFormMap R' K' O F d (exteriorPower.ιMulti O d
      (fun i => KaehlerDifferential.map R R' O O (KaehlerDifferential.map R R O₀ O (b₀ i)))) ≠ 0 :=
        by
    rw [← hbcoe]
    exact (topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq R' K' O F d b).1
  have hord1 := ord_topFormMap_eq_ord_of_map_maximalIdeal_eq
    R R' K K' O₀ O F₀ F hRR' hO₀ hO d b₀ hbc hρO a ha
  have hρ₀ := (topFormMap_iotaMulti_ne_zero_and_forall_exists_smul_eq R K O₀ F₀ d b₀).1
  have hord2 := (integralTopForms_eq_span_and_ord_smul_of_basis R K O₀ F₀ d b₀).2 a ha hρ₀
  have hordσ : ord R' K' O d F (topFormMap K K' F F d σ) = addOrd O₀ F₀ a := by
    rw [hX]
    exact hord1.trans hord2
  have hm : m = addOrd O₀ F₀ a := le_antisymm (hordσ ▸ hle) hmin
  exact ⟨hm, hiff.mp (by rw [hordσ, hm])⟩

end NeronModelInfra.TopFormOrder
end
