/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.Tsen.AbsoluteModPTwoCocycleOfTsen
import Nyll.EtaleCohomology.Classical.FieldEtaleDimensionShift
import Nyll.EtaleCohomology.Classical.KummerSequence

/-!
# Actual derived etale Tsen vanishing

The proved function-field continuous cohomology vanishing is transported
through the existing actual field comparison. This gives vanishing of
derived Sheaf.H for every bounded-torsion abelian etale sheaf in degrees
at least two. No field comparison or vanishing hypothesis is assumed.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicCurve

/-- Actual derived etale cohomology of a characteristic-zero function
field over an algebraically closed field vanishes above degree one
for every abelian coefficient sheaf killed by a nonzero integer. -/
theorem fieldEtale_cohomology_eq_zero_of_tsen
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (S : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{0})
    (m : ℤ) (hm0 : m ≠ 0) (hm : m • 𝟙 S = 0)
    (n : ℕ) (v : Sheaf.H.{0} S (n + 2)) : v = 0 := by
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let T := EtaleCohomology.finiteGaloisSectionColimitTopRepFunctor F
  let X := T.obj S
  have : DiscreteTopology X := ⟨rfl⟩
  have hX : Continuous
      (fun gx : Field.absoluteGaloisGroup F × X => X.ρ gx.1 gx.2) := by
    let : TopologicalSpace (EtaleCohomology.finiteGaloisSectionColimit F S) := ⊥
    have : DiscreteTopology (EtaleCohomology.finiteGaloisSectionColimit F S) := ⟨rfl⟩
    exact EtaleCohomology.finiteGaloisSectionColimitAction_continuous F S
  have hmX : ∀ a : X, m • a = 0 := by
    intro a
    have he := congrArg (fun f : S ⟶ S => T.map f) hm
    rw [T.map_zsmul, T.map_id, T.map_zero] at he
    exact congrArg (fun f : X ⟶ X => f.hom.toContinuousLinearMap a) he
  have hz := absoluteGalois_boundedContinuousModule_isZero_of_tsen
    K x hx hfin X hX m hm0 hmX n
  let e := EtaleCohomology.fieldEtaleContinuousModuleEquiv F (n + 2) S
  have hid : 𝟙 (((TopRep.continuousModuleComplexFunctor
      (Field.absoluteGaloisGroup F)).obj X).homology (n + 2)) = 0 :=
    hz.eq_of_src _ _
  have he : e v = 0 := ConcreteCategory.congr_hom hid (e v)
  apply e.injective
  exact he.trans (map_zero e).symm

/-- Actual roots-of-unity cohomology vanishes in every degree at least two
over a characteristic-zero function field over an algebraically closed field. -/
theorem fieldEtale_rootsOfUnity_cohomology_eq_zero_of_tsen
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    {F : Type} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (m : ℕ) (hm : 0 < m) (n : ℕ)
    (v : Sheaf.H.{0}
      (EtaleCohomology.etaleRootsOfUnitySheaf (Spec (.of F)) m) (n + 2)) :
    v = 0 := by
  let X := Spec (.of F)
  let f := EtaleCohomology.etaleMultiplicativeGroupPower X m
  have hk : m • 𝟙 (kernel f) = 0 := by
    apply (cancel_mono (kernel.ι f)).mp
    calc
      (m • 𝟙 (kernel f)) ≫ kernel.ι f = m • kernel.ι f := by
        rw [Preadditive.nsmul_comp, Category.id_comp]
      _ = kernel.ι f ≫ f := by
        change m • kernel.ι f = kernel.ι f ≫ (m • 𝟙 _)
        rw [Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 ≫ kernel.ι f := (kernel.condition f).trans (zero_comp).symm
  apply fieldEtale_cohomology_eq_zero_of_tsen K x hx hfin
    (EtaleCohomology.etaleRootsOfUnitySheaf X m) (m : ℤ)
    (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hm)) ?_ n v
  simpa only [natCast_zsmul] using hk

end AlgebraicCurve
