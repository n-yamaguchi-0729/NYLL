/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionFiberSectionDifference
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorRoots
public import Nyll.EtaleCohomology.Classical.MultiplicativeGroupPushforward

/-!
# Actual root ratios on arbitrary original étale overlaps

The difference of two original extension lifts is an actual section of
the original constant coefficient sheaf. Its image under the original
root-of-unity coefficient map is the ratio of their actual rational
roots. No connectedness of the étale overlap, and no identification of
its coefficient section with one constant value, is used.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits Opposite
open EtaleCohomology

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  {n : ℕ} (hn : 0 < n) (hnK : IsUnit (n : K))
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = n • d)

local notation "j" => X.fromSpecStalk (genericPoint X)
local notation "P" => constantGenericKummerDivisorExtension c hn hnK d b hb
local notation "hP" => constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb
local notation "r" => constantGenericKummerDivisorRoot c hn hnK d b hb
local notation "T" => extensionFiber P (integerUnitSection X)
local notation "q" => (Iso.hom (constantRootsOfUnityKummerKernelIso c hn hnK)) ≫
  kernel.ι (etaleMultiplicativeGroupPower X n)

/-- An arbitrary original coefficient section acts on the actual
rational root through its original inclusion in multiplicative units. -/
theorem constantGenericKummerDivisorRoot_coefficient_section
    (V : X.Etale) (η : (P).X₁.obj.obj (op V)) :
    (r).hom.app (op V) ((P).f.hom.app (op V) η) =
      Additive.ofMul
        (Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
          ((q).hom.app (op V) η).toMul) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f : (P).X₁ ⟶ (etaleGenericUnitShortComplex X).X₂ =>
      f.hom.app (op V))
      (constantGenericKummerDivisorRoot_inclusion c hn hnK d b hb)) η
  change (r).hom.app (op V) ((P).f.hom.app (op V) η) =
    (etaleMultiplicativeGroupToPushforward j).hom.app (op V)
      ((q).hom.app (op V) η) at h
  exact h.trans (etaleMultiplicativeGroupToPushforward_apply j V
    ((q).hom.app (op V) η))

/-- The actual coefficient section measuring two extension lifts
maps to the ratio of their original rational roots. -/
theorem genericKummerDivisorRootSection_difference
    (V : X.Etale) (s₀ s₁ : (T).obj.obj (op V)) (η : (P).X₁.obj.obj (op V))
    (hη : (P).f.hom.app (op V) η = s₁.val - s₀.val) :
    genericKummerDivisorRootSection c hn hnK d b hb V s₁ /
        genericKummerDivisorRootSection c hn hnK d b hb V s₀ =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        ((q).hom.app (op V) η).toMul := by
  have h := congrArg ((r).hom.app (op V)).hom hη
  have hsub := map_sub ((r).hom.app (op V)).hom
    (show (P).X₂.obj.obj (op V) from s₁.val)
    (show (P).X₂.obj.obj (op V) from s₀.val)
  change ((r).hom.app (op V) s₁.val - (r).hom.app (op V) s₀.val).toMul = _
  exact congrArg Additive.toMul
    (hsub.symm.trans (h.symm.trans
      (constantGenericKummerDivisorRoot_coefficient_section c hn hnK d b hb V η)))

/-- The original short exact extension supplies the coefficient
section, so the actual root-ratio formula needs no supplied difference. -/
theorem genericKummerDivisorRootSection_firstDifference
    (V : X.Etale) (s₀ s₁ : (T).obj.obj (op V)) :
    let η := extensionFiberSectionDifference P (integerUnitSection X) hP (op V) s₀ s₁
    genericKummerDivisorRootSection c hn hnK d b hb V s₁ /
        genericKummerDivisorRootSection c hn hnK d b hb V s₀ =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        ((q).hom.app (op V) η).toMul := by
  intro η
  exact genericKummerDivisorRootSection_difference c hn hnK d b hb V s₀ s₁ η
    (extensionFiberSectionDifference_inclusion P (integerUnitSection X) hP (op V) s₀ s₁)

/-- On an original overlap, restricting the same original lift
along its two maps gives the actual first coefficient difference and
the ratio of the two actual base-changed rational roots. -/
theorem genericKummerDivisorRootSection_edgeDifference
    {V W : X.Etale} (m₀ m₁ : V ⟶ W) (s : (T).obj.obj (op W)) :
    let η := extensionFiberSectionDifference P (integerUnitSection X) hP (op V)
      ((T).obj.map m₀.op s) ((T).obj.map m₁.op s)
    Units.map (((etaleBaseChange j).map m₁).left.appTop.hom.toMonoidHom)
        (genericKummerDivisorRootSection c hn hnK d b hb W s) /
      Units.map (((etaleBaseChange j).map m₀).left.appTop.hom.toMonoidHom)
        (genericKummerDivisorRootSection c hn hnK d b hb W s) =
      Units.map (pullback.fst V.hom j).appTop.hom.toMonoidHom
        ((q).hom.app (op V) η).toMul := by
  intro η
  calc
    _ = genericKummerDivisorRootSection c hn hnK d b hb V ((T).obj.map m₁.op s) /
        genericKummerDivisorRootSection c hn hnK d b hb V ((T).obj.map m₀.op s) := by
      rw [genericKummerDivisorRootSection_naturality,
        genericKummerDivisorRootSection_naturality]
      rfl
    _ = _ := genericKummerDivisorRootSection_firstDifference c hn hnK d b hb V
      ((T).obj.map m₀.op s) ((T).obj.map m₁.op s)

end EtaleFundamentalGroups.Cohomology
