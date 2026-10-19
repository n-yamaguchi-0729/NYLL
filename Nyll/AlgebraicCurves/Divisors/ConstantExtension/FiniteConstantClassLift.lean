/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.Principal.PrincipalHom
import Nyll.GaloisCohomology.FieldTheory.FiniteActionHilbert90
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.Abel

/-!
# Fixed representatives over finite constant fields

For an actual semilinear action extending the full finite constant-field Galois
action, an invariant divisor class has an invariant divisor representative.
The obstruction is removed using the finite-field norm and field Hilbert 90.
-/

noncomputable section

namespace AlgebraicCurve.Divisor

open CyclicCohomology.ProfiniteCohomology.Herbrand

attribute [local instance] Units.mulDistribMulActionRight
  SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor

variable {k K F : Type*} [Field k] [Field K] [Field F] [Finite K]
    [Algebra k K] [Algebra K F] [HasPrincipalDivisors K F]

/-- Finite constant-field norms remove the obstruction to a fixed divisor representative. -/
theorem exists_fixed_representative_of_finite_constants
    (ρ : (K ≃ₐ[k] K) →* SemilinearAut K F)
    (hρ : ∀ g : K ≃ₐ[k] K, SemilinearAut.baseAut (ρ g) = g.toRingEquiv)
    (hC : ConstantsAreBase K F) (σ : K ≃ₐ[k] K)
    (hσ : ∀ g : K ≃ₐ[k] K, g ∈ Subgroup.zpowers σ)
    (D : Divisor K F) (hD : (ρ σ • D - D).IsPrincipal) :
    ∃ E : Divisor K F, (D - E).IsPrincipal ∧ degree E = degree D ∧ ρ σ • E = E := by
  classical
  let G := K ≃ₐ[k] K
  let : MulSemiringAction G F := MulSemiringAction.compHom F ρ
  have : FaithfulSMul G F := ⟨fun {g h} he => by
    ext a
    apply (algebraMap K F).injective
    have ha := he (algebraMap K F a)
    change SemilinearAut.toRingAut (ρ g) (algebraMap K F a) =
      SemilinearAut.toRingAut (ρ h) (algebraMap K F a) at ha
    rwa [SemilinearAut.commutes, SemilinearAut.commutes, hρ, hρ] at ha⟩
  let ι : Kˣ →* Fˣ := Units.map (algebraMap K F).toMonoidHom
  have hι (g : G) (c : Kˣ) : ι (g • c) = g • ι c := by
    apply Units.ext
    change algebraMap K F (g (c : K)) = SemilinearAut.toRingAut (ρ g) (algebraMap K F (c : K))
    rw [SemilinearAut.commutes, hρ]
    rfl
  obtain ⟨x, hx⟩ := (show ρ σ • D - D ∈ (principalHom (K := K) (F := F)).range by
    rw [range_principalHom]
    exact hD)
  let N : Fˣ := tateNorm G Fˣ x.toMul
  have hN : principalHom (K := K) (Additive.ofMul N) = 0 := by
    change principalHom (K := K) (Additive.ofMul (∏ g : G, g • x.toMul)) = 0
    rw [ofMul_prod, map_sum]
    have hf (g : G) : principalHom (K := K) (Additive.ofMul (g • x.toMul)) =
        ρ g • (ρ σ • D - D) := by
      exact (principalHom_smul (ρ g) x).trans (congrArg (fun E => ρ g • E) hx)
    simp only [hf, smul_sub, ← mul_smul, ← map_mul, Finset.sum_sub_distrib]
    have he := Fintype.sum_equiv (Equiv.mulRight σ)
      (fun g : G => ρ (g * σ) • D) (fun g : G => ρ g • D) (fun _ => rfl)
    exact sub_eq_zero.mpr he
  obtain ⟨z, hz⟩ := (principalHom_eq_zero_iff hC (Additive.ofMul N)).mp hN
  change ι z = N at hz
  have hzfix (g : G) : g • z = z := by
    apply Units.map_injective (algebraMap K F).injective
    change ι (g • z) = ι z
    rw [hι, hz]
    exact smul_tateNorm_eq g x.toMul
  obtain ⟨a, ha⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := k) (z : K)).mpr
    (fun g => congrArg Units.val (hzfix g))
  have ha0 : a ≠ 0 := by
    intro hzero
    apply z.ne_zero
    rw [← ha, hzero, map_zero]
  obtain ⟨c, hc⟩ := FiniteField.unitsMap_norm_surjective k K (Units.mk0 a ha0)
  have hNc : tateNorm G Kˣ c = z := by
    apply Units.ext
    change ((∏ g : G, g • c : Kˣ) : K) = (z : K)
    rw [Units.coe_prod]
    change (∏ g : K ≃ₐ[k] K, g (c : K)) = (z : K)
    rw [← Algebra.norm_eq_prod_automorphisms]
    have hca : Algebra.norm k (c : K) = a := congrArg Units.val hc
    rw [hca, ha]
  have hNcF : tateNorm G Fˣ (ι c) = N :=
    (map_tateNorm ι hι c).symm.trans ((congrArg ι hNc).trans hz)
  have hunit : tateNorm G Fˣ (x.toMul / ι c) = 1 := by
    change tateNormHom (G := G) (A := Fˣ) (x.toMul / ι c) = 1
    rw [map_div]
    change N / tateNorm G Fˣ (ι c) = 1
    rw [hNcF, div_self']
  obtain ⟨y, hy⟩ := CyclicCohomology.exists_unit_coboundary_of_finite_action_norm_eq_one
    σ hσ (x.toMul / ι c) hunit
  let P := principalHom (K := K) (Additive.ofMul y)
  have hP : ρ σ • P - P = principalHom x := by
    rw [← principalHom_smul (ρ σ) (Additive.ofMul y), ← map_sub]
    change principalHom (K := K) (Additive.ofMul ((σ • y) / y)) = principalHom x
    rw [hy]
    change principalHom (K := K) (x - Additive.ofMul (ι c)) = principalHom x
    rw [map_sub, principalHom_algebraMap, sub_zero]
  refine ⟨D - P, ?_, ?_, ?_⟩
  · have hprincipal : P ∈ principal (K := K) (F := F) := by
      rw [← range_principalHom]
      exact ⟨Additive.ofMul y, rfl⟩
    rw [sub_sub_cancel]
    exact hprincipal
  · rw [map_sub, degree_principalHom, sub_zero]
  · apply sub_eq_zero.mp
    calc
      ρ σ • (D - P) - (D - P) = (ρ σ • D - D) - (ρ σ • P - P) := by
        rw [smul_sub]
        abel
      _ = 0 := by rw [hP, hx, sub_self]

end AlgebraicCurve.Divisor
