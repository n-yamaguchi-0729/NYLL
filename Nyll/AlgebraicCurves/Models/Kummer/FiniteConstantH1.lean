/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.AlgebraicCurves.Models.Construction.Basic
public import Nyll.AlgebraicCurves.Models.Kummer.FiniteH1
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteH1Comparison
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Finiteness of H¹ with finite constant coefficients

Characters of a finite abelian group into the ground field's units separate
its elements. Each character lands in the roots of unity of the group's
order. The original cohomology coefficient maps therefore embed H¹ into a
finite product of the actual Kummer H¹ groups.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra
open EtaleFundamentalGroups.Cohomology

namespace AlgebraicCurve.CurveModel

/-- Actual étale H¹ of a smooth proper curve is finite for every finite
constant abelian coefficient group of order invertible in the ground field. -/
theorem finite_constantH1_of_isUnit_natCard
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) [GeometricallyIntegral M.toBase]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (A : AddCommGrpCat.{0}) [Finite A] (hA : IsUnit ((Nat.card A : ℕ) : K))
    {Ω : Type} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ M.C) :
    Finite (Sheaf.H.{0}
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1) := by
  have : IsIntegral M.C := M.isIntegral
  let n : ℕ+ := ⟨Nat.card (Multiplicative A), Nat.card_pos⟩
  have hcard : (n : ℕ) = Nat.card A := Nat.card_congr Multiplicative.toAdd
  have hn : IsUnit ((n : ℕ) : K) := by
    rw [hcard]
    exact hA
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have : NeZero ((n : ℕ) : K) := ⟨hn.ne_zero⟩
  have : HasEnoughRootsOfUnity K (n : ℕ) :=
    IsSepClosed.hasEnoughRootsOfUnity K (n : ℕ)
  have : HasEnoughRootsOfUnity K (Monoid.exponent (Multiplicative A)) :=
    HasEnoughRootsOfUnity.of_dvd K (n := (n : ℕ))
      (Group.exponent_dvd_nat_card (G := Multiplicative A))
  let I := Multiplicative A →* Kˣ
  let B := AddCommGrpCat.of (Additive (rootsOfUnity (n : ℕ) K))
  let α : I → (A ⟶ B) := fun φ => AddCommGrpCat.ofHom
    (φ.codRestrict (rootsOfUnity (n : ℕ) K) fun x => by
      rw [mem_rootsOfUnity, ← map_pow]
      change φ (x ^ Nat.card (Multiplicative A)) = 1
      rw [pow_card_eq_one', map_one]).toAdditiveRight
  have : Finite (Sheaf.H.{0}
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj B) 1) :=
    M.finiteH1_of_isUnit ε n hn ξ
  let j : Sheaf.H.{0}
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj A) 1 →
      (I → Sheaf.H.{0}
        ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).obj B) 1) :=
    fun x φ => Sheaf.H.map
      ((constantSheaf M.C.smallEtaleTopology AddCommGrpCat.{0}).map (α φ)) 1 x
  apply Finite.of_injective j
  intro x y h
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  let : TopologicalSpace (Multiplicative B) := ⊥
  have : DiscreteTopology (Multiplicative B) := ⟨rfl⟩
  apply (finiteH1CharacterEquiv A ξ).injective
  apply ContinuousMonoidHom.ext
  intro g
  apply (CommGroup.forall_apply_eq_apply_iff (Multiplicative A) (M := K)).mp
  intro φ
  let ev : (Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative B) → Kˣ :=
    fun χ => (Additive.toMul (α := rootsOfUnity (n : ℕ) K) (χ g).toAdd).val
  have hx := congrArg ev (finiteH1CharacterEquiv_naturality A ξ (α φ) x)
  have hy := congrArg ev (finiteH1CharacterEquiv_naturality A ξ (α φ) y)
  have hxy := congrArg (fun z => ev (finiteH1CharacterEquiv B ξ z).toMul)
    (congrFun h φ)
  exact hx.trans (hxy.trans hy.symm)

end AlgebraicCurve.CurveModel
