/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.EtaleCohomology.Classical.GenericUnitCohomology
public import Nyll.EtaleFundamentalGroups.Cohomology.ConstantGenericKummerDivisorExtension
public import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
public import Nyll.EtaleFundamentalGroups.Cohomology.GenericKummerDivisorMonodromyRoots
public import Nyll.EtaleFundamentalGroups.Cohomology.H1FiniteCover
public import Nyll.EtaleFundamentalGroups.Kummer.AdjoinRoot.RootFiberTransitivity
public import Mathlib.Algebra.Torsor.Basic
public import Mathlib.Logic.Equiv.Defs

/-!
# All actual roots of the original generic divisor extension

The original universal root identifies the original monodromy fiber
with all roots of its original function-field equation. Injectivity
uses the original free coefficient action. Surjectivity uses the
existing unique root-scaling theorem and that same action, without
assuming an identification of the original torsor with a root scheme.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits
open EtaleCohomology
open scoped FintypeCatDiscrete

namespace EtaleFundamentalGroups.Cohomology

variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K))
  {n : ℕ} [NeZero n] (hn : 0 < n) (hnK : IsUnit (n : K))
  (d : Sheaf.H.{u} (etaleGenericUnitQuotient X) 0)
  (b : Sheaf.H.{u} (etaleGenericUnitShortComplex X).X₂ 0)
  (hb : Sheaf.H.map (etaleGenericUnitShortComplex X).g 0 b = n • d)
  (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] [IsSepClosed Ω]

local notation "ξ" => Spec.algebraMap X.functionField Ω ≫ X.fromSpecStalk (genericPoint X)
local notation "A" => AddCommGrpCat.of (Additive (rootsOfUnity n K))
local notation "P" => constantGenericKummerDivisorExtension c hn hnK d b hb
local notation "hP" => constantGenericKummerDivisorExtension_shortExact c hn hnK d b hb
local notation "r" => genericKummerDivisorMonodromyRoot c hn hnK d b hb Ω
local notation "ι" =>
  CommRingCat.Hom.hom
    (Iso.inv (Scheme.ΓSpecIso (CommRingCat.of K)) ≫ Scheme.Hom.appTop (ξ ≫ c) ≫
      Iso.hom (Scheme.ΓSpecIso (CommRingCat.of Ω)))
local notation "a" => Units.map (RingHom.toMonoidHom (algebraMap X.functionField Ω))
  (Additive.toMul (genericPointUnitsH0Equiv X b))

/-- The original root distinguishes the actual monodromy points:
its original coefficient translations are faithful. -/
theorem genericKummerDivisorMonodromyRoot_injective : Function.Injective r := by
  let coefficientTorsor :=
    extensionMonodromyTorsor A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
  intro q₀ q₁ h
  let ζ : rootsOfUnity n K := (q₀ /ₛ q₁ : Multiplicative A).toAdd.toMul
  have hs := genericKummerDivisorMonodromyRoot_translation c hn hnK d b hb Ω ζ q₁
  change r ((q₀ /ₛ q₁ : Multiplicative A) • q₁) =
    Units.map (ι).toMonoidHom (ζ : Kˣ) * r q₁ at hs
  rw [sdiv_smul] at hs
  have hζ : Units.map (ι).toMonoidHom (ζ : Kˣ) = 1 :=
    mul_right_cancel (hs.symm.trans (h.trans (one_mul (r q₁)).symm))
  have hz : (q₀ /ₛ q₁ : Multiplicative A) = 1 := by
    change ζ = 1
    apply rootsOfUnity.coe_injective
    apply (ι).injective
    exact (congrArg Units.val hζ).trans (map_one ι).symm
  exact sdiv_eq_one_iff_eq.mp hz

/-- Every root of the unchanged rational equation occurs at an
actual point of the unchanged monodromy fiber. -/
theorem genericKummerDivisorMonodromyRoot_surjective :
    Function.Surjective (fun q :
      (extensionMonodromy A (ShortComplex.f P) (ShortComplex.g P) (ShortComplex.zero P)
        hP (integerUnitSection X) ξ).obj.V =>
      (⟨r q, genericKummerDivisorMonodromyRoot_pow c hn hnK d b hb Ω q⟩ :
        { β : Ωˣ // β ^ n = a })) := by
  let coefficientTorsor :=
    extensionMonodromyTorsor A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
  let q₀ :
      (extensionMonodromy A (ShortComplex.f P) (ShortComplex.g P) (ShortComplex.zero P)
        hP (integerUnitSection X) ξ).obj.V :=
    Classical.choice coefficientTorsor.nonempty
  intro β
  have hp : (r q₀ : Ω) ^ n = (β.val : Ω) ^ n :=
    congrArg Units.val
      ((genericKummerDivisorMonodromyRoot_pow c hn hnK d b hb Ω q₀).trans
        β.property.symm)
  obtain ⟨ζ, hζ, _⟩ := EtaleFundamentalGroups.Kummer.existsUnique_rootScale
    ι ⟨n, hn⟩ hnK (r q₀ : Ω) (β.val : Ω) (Units.ne_zero (r q₀)) hp
  let coefficient : Multiplicative A := Multiplicative.ofAdd (Additive.ofMul ζ)
  refine ⟨coefficient • q₀, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact (congrArg Units.val
    (genericKummerDivisorMonodromyRoot_translation c hn hnK d b hb Ω ζ q₀)).trans hζ

/-- The actual monodromy fiber and the actual roots of its original
equation are equivalent through the original universal root itself. -/
def genericKummerDivisorRootFiberEquiv :
    (extensionMonodromy A (ShortComplex.f P) (ShortComplex.g P) (ShortComplex.zero P)
      hP (integerUnitSection X) ξ).obj.V ≃ { β : Ωˣ // β ^ n = a } :=
  Equiv.ofBijective
    (fun q => ⟨r q, genericKummerDivisorMonodromyRoot_pow c hn hnK d b hb Ω q⟩)
    ⟨fun _ _ h => genericKummerDivisorMonodromyRoot_injective c hn hnK d b hb Ω
      (congrArg Subtype.val h),
      genericKummerDivisorMonodromyRoot_surjective c hn hnK d b hb Ω⟩

/-- The forward equivalence is the original root evaluation. -/
theorem genericKummerDivisorRootFiberEquiv_apply
    (q : (extensionMonodromy A (ShortComplex.f P) (ShortComplex.g P) (ShortComplex.zero P)
      hP (integerUnitSection X) ξ).obj.V) :
    (genericKummerDivisorRootFiberEquiv c hn hnK d b hb Ω q).val = r q :=
  rfl

/-- The inverse constructs an actual original fiber point with
exactly the specified root, not merely an isomorphic torsor. -/
theorem genericKummerDivisorRootFiberEquiv_symm_root
    (β : { β : Ωˣ // β ^ n = a }) :
    r ((genericKummerDivisorRootFiberEquiv c hn hnK d b hb Ω).symm β) = β.val :=
  congrArg Subtype.val
    ((genericKummerDivisorRootFiberEquiv c hn hnK d b hb Ω).apply_symm_apply β)

/-- Original torsor displacement is computed by the quotient of
the two original root values, with the second-over-first orientation. -/
theorem genericKummerDivisorMonodromyRoot_displacement
    (q₀ q₁ : (extensionMonodromy A (ShortComplex.f P) (ShortComplex.g P) (ShortComplex.zero P)
      hP (integerUnitSection X) ξ).obj.V) :
    let _ := extensionMonodromyTorsor A (P).f (P).g (P).zero hP (integerUnitSection X) ξ
    Units.map (ι).toMonoidHom
        ((rootsOfUnity n K).subtype (Additive.toMul (α := rootsOfUnity n K)
          (q₁ /ₛ q₀ : Multiplicative A).toAdd)) =
      r q₁ / r q₀ := by
  intro coefficientTorsor
  let ζ : rootsOfUnity n K := (q₁ /ₛ q₀ : Multiplicative A).toAdd.toMul
  have hs := genericKummerDivisorMonodromyRoot_translation c hn hnK d b hb Ω ζ q₀
  change r ((q₁ /ₛ q₀ : Multiplicative A) • q₀) =
    Units.map (ι).toMonoidHom (ζ : Kˣ) * r q₀ at hs
  rw [sdiv_smul] at hs
  change Units.map (ι).toMonoidHom (ζ : Kˣ) = r q₁ / r q₀
  exact (eq_div_iff_mul_eq').2 hs.symm

end EtaleFundamentalGroups.Cohomology
