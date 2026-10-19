/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.

The original local additions in the following modules have no established direct
Anthropic source-file match:
- Divisor_correspondence_correspondence
Adapted Anthropic FLT sources (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_correspondence_comm_of_exchange.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences.Correspondences
import Nyll.AlgebraicCurves.Divisors.Maps.MapComposition
import Nyll.AlgebraicCurves.Divisors.Correspondences.CorrespondenceFibers
import Nyll.AlgebraicCurves.FunctionFields.Transcendence.CurveOver
import Nyll.AlgebraicCurves.Divisors.Norm.PushforwardPullbackFinite
import Nyll.AlgebraicCurves.Places.Ramification.SumRamificationInertia
import Nyll.AlgebraicCurves.Geometry.FundamentalIdentityAlong
import Nyll.AlgebraicCurves.Geometry.OneLeDeg

/-!
# Correspondence Composition
-/

section

/-!
# Divisor correspondence correspondence
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_correspondence

open IsDedekindDomain AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.correspondence_correspondence {K F F₁ F₂ Z : Type*} [Field K]
  [Field F] [Field F₁] [Field F₂] [Field Z] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K
  Z] [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] [HasPrincipalDivisors K Z] (φ ψ : F
  →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z) (hφ : φ.toRingHom.IsIntegral)
  (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (hu
  : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral) (huφ' : (u'.comp
  φ').toRingHom.IsIntegral) (huψ : (u.comp ψ).toRingHom.IsIntegral) (hex : ∀ D : Divisor K F₂,
  Divisor.pullbackAlong φ hφ (Divisor.pushforwardAlong ψ' hψ' D) = Divisor.pushforwardAlong u hu
  (Divisor.pullbackAlong u' hu' D)) (D : Divisor K F) : Divisor.correspondence φ ψ hφ hψ
  (Divisor.correspondence φ' ψ' hφ' hψ' D) = Divisor.correspondence (u'.comp φ') (u.comp ψ) huφ'
  huψ D := by
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply, Divisor.correspondence_apply,
    hex (Divisor.pullbackAlong φ' hφ' D),
    AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong ψ u hψ hu huψ,
    AlgebraicCurve.Divisor.pullbackAlong_pullbackAlong φ' u' hφ' hu' huφ']
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_correspondence
end ProofImplementation

end

section

/-!
# Divisor correspondence comm of exchange
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_comm_of_exchange

open AlgebraicCurve

namespace AL4Sol

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [HasPrincipalDivisors K F']

theorem comm_of_exchange (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ :
  ψ.toRingHom.IsIntegral)
    (g : F' →ₐ[K] F') (hg : g.toRingHom.IsIntegral) (hgs : Function.Surjective g)
    (h1 : g.comp φ = ψ) (h2 : g.comp ψ = φ) :
    Divisor.correspondence φ ψ hφ hψ = Divisor.correspondence ψ φ hψ hφ := by
  have hgψ : (g.comp ψ).toRingHom.IsIntegral := by rw [h2]; exact hφ
  have hgφ : (g.comp φ).toRingHom.IsIntegral := by rw [h1]; exact hψ
  refine AddMonoidHom.ext (fun D => ?_)
  rw [Divisor.correspondence_congr h2.symm h1.symm hφ hψ hgψ hgφ D]
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply]
  rw [← Divisor.pullbackAlong_pullbackAlong ψ g hψ hg hgψ D]
  rw [← Divisor.pushforwardAlong_pushforwardAlong φ g hφ hg hgφ]
  rw [Divisor.pushforwardAlong_pullbackAlong_of_surjective g hg hgs]

end AL4Sol

theorem _root_.AlgebraicCurve.Divisor.correspondence_comm_of_exchange {K F F' : Type*} [Field K]
  [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
  (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (g : F' →ₐ[K] F') (hg :
  g.toRingHom.IsIntegral) (hgs : Function.Surjective g) (h1 : g.comp φ = ψ) (h2 : g.comp ψ = φ) :
  AlgebraicCurve.Divisor.correspondence φ ψ hφ hψ = AlgebraicCurve.Divisor.correspondence ψ φ hψ hφ
  :=
  AL4Sol.comm_of_exchange φ ψ hφ hψ g hg hgs h1 h2
end AlgebraicCurves.Divisors.Proofs.Divisor_correspondence_comm_of_exchange
end ProofImplementation

end

section

/-!
# Divisor correspondence eq finrank Along smul correspondence of comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
    {K F₀ E F : Type*} [Field K] [Field F₀] [Field E] [Field F]
    [Algebra K F₀] [Algebra K E] [Algebra K F] [IsCurveOver K E] [IsCurveOver K F]
    (φ₀ φ₁ : F₀ →ₐ[K] F) (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (ψ₀ ψ₁ : F₀ →ₐ[K] E) (hψ₀ : ψ₀.toRingHom.IsIntegral) (hψ₁ : ψ₁.toRingHom.IsIntegral)
    (ι : E →ₐ[K] F) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) (hsep : SeparableAlong K
      ι)
    (h₀ : ι.comp ψ₀ = φ₀) (h₁ : ι.comp ψ₁ = φ₁) (D : Divisor K F₀) :
    Divisor.correspondence φ₀ φ₁ hφ₀ hφ₁ D = finrankAlong K ι • Divisor.correspondence ψ₀ ψ₁ hψ₀
      hψ₁ D := by
  subst h₀ h₁
  have key : ∀ X : Divisor K E, Divisor.pushforwardAlong ι hι (Divisor.pullbackAlong ι hι X) =
    finrankAlong K ι • X := by
    intro X
    let := algebraAlong ι
    have := isScalarTower_along ι
    have := isIntegral_along ι hι
    have : FundamentalIdentity K E F := AlgebraicCurve.fundamentalIdentityAlong ι hι hfin hsep
    have : SumRamificationInertia K E F :=
      AlgebraicCurve.sumRamificationInertia_of_fundamentalIdentity (fun v =>
        Nat.one_le_iff_ne_zero.mp (AlgebraicCurve.one_le_deg v))
    have : Module.Finite E F := hfin
    have := AlgebraicCurve.Divisor.pushforward_pullback_of_finite (K := K) (F := E) (F' := F) X
    rw [← natCast_zsmul]
    exact this
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    ← Divisor.pullbackAlong_pullbackAlong ψ₀ ι hψ₀ hι hφ₀ D,
    ← Divisor.pushforwardAlong_pushforwardAlong ψ₁ ι hψ₁ hι hφ₁, key, map_nsmul]
end Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
end AlgebraicCurves.Divisors.Proofs
end ProofImplementation

end
