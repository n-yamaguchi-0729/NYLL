/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Cohomology.Sheaves.EulerCharacteristic.InvertibleIdealEulerCharSectionsOfTensorInvModuleEq
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomFiniteFinrankSubschemeIotaKerPow
import Nyll.AlgebraicCurves.Geometry.Schemes.Cohomology.TwoAffineCoverLinearEquivSectionsOfH0
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPow
import Nyll.SchemeTheory.Modules.Frames.PullbackFrame
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.SectionZeroScheme

/-! # A point twist of every line bundle has a nonzero section -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicCurves.Geometry.Sheaves.Proofs
  Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

/-- Positive Euler characteristic of a sufficiently large actual point twist
supplies a nonzero global section, including when there is no modulus. -/
theorem exists_nonzero_pointTwistSection
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (c : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (𝒱 : X.TwoAffineOpenCover) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (ε : Spec (CommRingCat.of K) ⟶ X) (hε : ε ≫ c = 𝟙 _) :
    ∃ n : ℕ, ∃ s : 𝟙_ X.Modules ⟶ L ⊗ (ε.ker ^ (n + 1)).invModule, s ≠ 0 := by
  let χ : ℤ := (Module.finrank K (𝒱.sectionsOf c L).H0 : ℤ) -
    Module.finrank K (𝒱.sectionsOf c L).H1
  let n := (-χ).toNat
  let T := L ⊗ (ε.ker ^ (n + 1)).invModule
  have hp := Scheme.Hom.isInvertible_ker_of_comp_eq_id ε hε
  have hd := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id ε hε (n + 1)
  have hχ := (hp.pow (n + 1)).eulerChar_sectionsOf_tensor_invModule_eq
    c hd.1 hd.2.1 L hL 𝒱
  have hpos : 0 < Module.finrank K (𝒱.sectionsOf c T).H0 := by
    change (Module.finrank K (𝒱.sectionsOf c T).H0 : ℤ) -
      Module.finrank K (𝒱.sectionsOf c T).H1 = χ + (n + 1 : ℕ) at hχ
    dsimp only [n] at hχ
    omega
  have : Nontrivial (𝒱.sectionsOf c T).H0 := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨e, _he⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 c T
  have : Nontrivial Γ(T, ⊤) := e.toEquiv.nontrivial
  obtain ⟨m, hm⟩ := exists_ne (0 : Γ(T, ⊤))
  let s : 𝟙_ X.Modules ⟶ T := FramePullback.smulHom T m
  have heval : s.app ⊤ (toUnitSection ⊤ 1) = m := by
    change (FramePullback.smulHom T m).app ⊤ (1 : Γ(X, ⊤)) = m
    rw [FramePullback.smulHom_app_apply, one_smul]
    change T.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op m = m
    rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 _)]
    change T.presheaf.map (𝟙 _) m = m
    rw [CategoryTheory.Functor.map_id]
    rfl
  refine ⟨n, s, fun hs => hm ?_⟩
  have hz : s.app ⊤ (toUnitSection ⊤ 1) = 0 := by
    rw [hs, Hom.zero_app]
    rfl
  exact heval.symm.trans hz

end AlgebraicGeometry.Scheme.Modules.IsInvertible
