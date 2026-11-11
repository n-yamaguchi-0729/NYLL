/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.CupAbelianExtensionCocycle
public import Nyll.EtaleCohomology.Classical.FiniteLevelCup
public import Nyll.EtaleCohomology.Classical.FreeModuleSheafCochains
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberCechDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberCechLift
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteModuleGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.FiniteModuleGenericKummerDivisorRoots

/-!
# Actual finite divisor Cech classes and their original rational roots

The genuine finite étale divisor cover carries its original universal
lift. Its actual free-source cocycle represents the unchanged original
finite-level H¹ class. Every actual edge coefficient computes the ratio
of the two original restrictions of that same universal rational root.
These are inputs to the original Cech cup calculation, with no supplied
cup comparison and no connectedness hypothesis on the overlaps.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology EtaleCohomology.Classical

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : K)) (n : ℕ)
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = ℓ ^ (n + 1) • d)

local notation "N" => ℓ ^ (n + 1)
local notation "R" => ULift (ZMod N)
local notation "C" =>
  (CategoryTheory.Functor.obj (constantSheaf X.smallEtaleTopology (ModuleCat R))) (ModuleCat.of R R)
local notation "Q" => finiteModuleGenericKummerDivisorExtension c ℓ hℓ n d b hb
local notation "hQ" => finiteModuleGenericKummerDivisorExtension_shortExact c ℓ hℓ n d b hb
local notation "V" => (CategoryTheory.Functor.obj (finiteEtaleToEtale X))
  (finiteModuleGenericKummerDivisorCover c ℓ hℓ n d b hb)
local notation "s" => finiteModuleGenericKummerDivisorUniversalSection c ℓ hℓ n d b hb

variable {T : X.Etale} (hT : IsTerminal T)

local notation "f" => hT.from V
local notation "β" =>
  extensionFiberCechLift R (ShortComplex.f Q) (ShortComplex.g Q) (ShortComplex.zero Q) s
local notation "hβ" =>
  extensionFiberCechLift_projection R (ShortComplex.f Q) (ShortComplex.g Q)
    (ShortComplex.zero Q) s hT f
local notation "hf" => finiteModuleGenericKummerDivisorCover_covering c ℓ hℓ n d b hb hT

/-- The actual module cocycle of the original universal divisor
root lift on its genuine original finite étale cover. -/
def finiteGenericKummerDivisorCechCocycle :
    (freeModuleSheafFunctor X R).obj (cechEdgeFunctor (yoneda.map f)) ⟶ C :=
  abelianExtensionModuleCechCocycle X R hT f (ShortComplex.f Q) (ShortComplex.g Q)
    (ShortComplex.zero Q) hQ β hβ

/-- The original triangle relation kills the actual divisor cocycle. -/
theorem finiteGenericKummerDivisorCechCocycle_cocycle :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u} R)).map
        (freeModuleCechTriangleBoundaryNat R (yoneda.map f)) ≫
      finiteGenericKummerDivisorCechCocycle c ℓ hℓ n d b hb hT = 0 :=
  abelianExtensionModuleCechCocycle_cocycle X R hT f (ShortComplex.f Q) (ShortComplex.g Q)
    (ShortComplex.zero Q) hQ β hβ

/-- The actual universal-root cocycle represents the unchanged
original finite-level divisor class under the original comparison
used to define the finite cup product. -/
theorem finiteGenericKummerDivisorCechCocycle_class :
    finiteLevelConstantModuleEquiv X ℓ n 1
        (etaleCechH1Class X R hT f hf
          (finiteGenericKummerDivisorCechCocycle c ℓ hℓ n d b hb hT)
          (finiteGenericKummerDivisorCechCocycle_cocycle c ℓ hℓ n d b hb hT)) =
      finiteGenericKummerDivisorClass c ℓ hℓ n d b hb := by
  calc
    _ = finiteLevelConstantModuleEquiv X ℓ n 1
        (finiteModuleGenericKummerDivisorClass c ℓ hℓ n d b hb) :=
      congrArg (finiteLevelConstantModuleEquiv X ℓ n 1)
        (extensionFiberCechLift_class R (ShortComplex.f Q) (ShortComplex.g Q)
          (ShortComplex.zero Q) s hQ hT f hf)
    _ = _ := finiteModuleGenericKummerDivisorClass_forget c ℓ hℓ n d b hb

/-- The actual edge values of the module cocycle are the original
coefficient differences of the same original universal root lift. -/
theorem finiteGenericKummerDivisorCechCocycle_firstDifference
    (W : X.Etale) (a : (cechEdgeFunctor (yoneda.map f)).obj (op W)) :
    (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) C
        (finiteGenericKummerDivisorCechCocycle c ℓ hℓ n d b hb hT)).app (op W) a =
      extensionFiberSectionDifference Q (integerUnitSection X) hQ (op W)
        ((extensionFiber Q (integerUnitSection X)).obj.map a.first.op s)
        ((extensionFiber Q (integerUnitSection X)).obj.map a.second.op s) :=
  extensionFiberCechCocycle_firstDifference R (ShortComplex.f Q) (ShortComplex.g Q)
    (ShortComplex.zero Q) s hQ hT f W a

/-- Every original edge of the genuine finite étale cover computes
the ratio of its two original restrictions of the universal root.
The coefficient is the actual cocycle section on that edge. -/
theorem finiteGenericKummerDivisorCechCocycle_rootRatio
    (W : X.Etale) (a : (cechEdgeFunctor (yoneda.map f)).obj (op W)) :
    let j := X.fromSpecStalk (genericPoint X)
    let δ := (etaleConstantModuleForgetIso X R).app (ModuleCat.of R R)
    let κ := (ellPowerConstantKummerKernelIso c ℓ hℓ n).hom ≫
      kernel.ι (etaleMultiplicativeGroupPower X N)
    let η := (freeModuleSheafHomEquiv X R (cechEdgeFunctor (yoneda.map f)) C
      (finiteGenericKummerDivisorCechCocycle c ℓ hℓ n d b hb hT)).app (op W) a
    Units.map (((etaleBaseChange j).map a.second).left.appTop.hom.toMonoidHom)
        (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s) /
      Units.map (((etaleBaseChange j).map a.first).left.appTop.hom.toMonoidHom)
        (finiteModuleGenericKummerDivisorRootSection c ℓ hℓ n d b hb V s) =
      Units.map (pullback.fst W.hom j).appTop.hom.toMonoidHom
        (κ.hom.app (op W) (δ.hom.hom.app (op W) η)).toMul := by
  intro j δ κ η
  have hη : η = extensionFiberSectionDifference Q (integerUnitSection X) hQ (op W)
      ((extensionFiber Q (integerUnitSection X)).obj.map a.first.op s)
      ((extensionFiber Q (integerUnitSection X)).obj.map a.second.op s) :=
    finiteGenericKummerDivisorCechCocycle_firstDifference c ℓ hℓ n d b hb hT W a
  rw [hη]
  exact finiteModuleGenericKummerDivisorRootSection_edgeDifference
    c ℓ hℓ n d b hb a.first a.second s

end EtaleFundamentalGroups.Cohomology
