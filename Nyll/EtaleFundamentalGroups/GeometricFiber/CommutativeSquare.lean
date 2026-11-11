/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality
public import Nyll.EtaleFundamentalGroups.GaloisCategories.AutFunctorComparison

/-!
# Original group maps of a commutative scheme square

The actual pullback comparison for a commuting square identifies its two
composite finite-cover functors. Arbitrary specified pointings then differ
by one explicitly constructed inner automorphism of the original target
fundamental group. The result allows different closure fields at all four
points and does not assume a comparison of group maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleStableUnderBaseChangeAlongFunctoriality
  finiteEtaleHasPullbacksAlongFunctoriality

/-- A commuting square of actual scheme maps determines the comparison of
its original pointed fundamental-group maps up to one full inner correction.
All four pointings are comparisons of the actual pullback fiber functors. -/
theorem fundamentalGroupHom_square_inner
    {U V S T : Scheme.{u}} (v : U ⟶ S) (w : V ⟶ T)
    (f : U ⟶ V) (I : S ⟶ T) (hsquare : v ≫ I = f ≫ w)
    {ΩU ΩV ΩS ΩT : Type u} [Field ΩU] [Field ΩV] [Field ΩS] [Field ΩT]
    (x : Spec (.of ΩU) ⟶ U) (y : Spec (.of ΩV) ⟶ V)
    (s : Spec (.of ΩS) ⟶ S) (t : Spec (.of ΩT) ⟶ T)
    (tv : pullback v ⋙ fiber x ≅ fiber s)
    (tw : pullback w ⋙ fiber y ≅ fiber t)
    (tf : pullback f ⋙ fiber x ≅ fiber y)
    (tI : pullback I ⋙ fiber s ≅ fiber t) :
    ∃ δ : π₁ᵉᵗ(t), ∀ z : π₁ᵉᵗ(x),
      autHomOfCompIso (pullback I) tI (autHomOfCompIso (pullback v) tv z) =
        δ * autHomOfCompIso (pullback w) tw
          (autHomOfCompIso (pullback f) tf z) * δ⁻¹ := by
  let α : pullback I ⋙ pullback v ≅ pullback w ⋙ pullback f :=
    (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) v I).symm ≪≫
      eqToIso (congrArg pullback hsquare) ≪≫
      MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) f w
  let a : (pullback I ⋙ pullback v) ⋙ fiber x ≅ fiber t :=
    Functor.associator (pullback I) (pullback v) (fiber x) ≪≫
      Functor.isoWhiskerLeft (pullback I) tv ≪≫ tI
  let b : (pullback w ⋙ pullback f) ⋙ fiber x ≅ fiber t :=
    Functor.associator (pullback w) (pullback f) (fiber x) ≪≫
      Functor.isoWhiskerLeft (pullback w) tf ≪≫ tw
  let b' := Functor.isoWhiskerRight α (fiber x) ≪≫ b
  refine ⟨Aut.of (b'.symm ≪≫ a), ?_⟩
  intro z
  have hc := autHomOfCompIso_eq_conj (pullback I ⋙ pullback v) b' a z
  have hb : autHomOfCompIso (pullback I ⋙ pullback v) b' z =
      autHomOfCompIso (pullback w) tw (autHomOfCompIso (pullback f) tf z) :=
    (autHomOfCompIso_isoFunctor α b z).trans
      (autHomOfCompIso_comp (pullback w) (pullback f) tf tw z)
  have ha : autHomOfCompIso (pullback I ⋙ pullback v) a z =
      autHomOfCompIso (pullback I) tI (autHomOfCompIso (pullback v) tv z) :=
    autHomOfCompIso_comp (pullback I) (pullback v) tv tI z
  rw [ha, hb] at hc
  exact hc

end AlgebraicGeometry.FiniteEtale
